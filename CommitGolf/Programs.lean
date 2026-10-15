import CommitGolf.Riscv

/-! Submitted machine images, canonical input loading, execution, and output decoding.
The three algorithms are derived here; a solver cannot substitute abstract implementations. -/
namespace CommitGolf.VectorCommit
open OracleComp RiscvZkvm.Rv64

structure Submission where
  family : OracleFamily
  sizes : Sizes
  layout : Layout
  image : Program → Riscv.Image
  steps : Program → Nat
  openingBytes : Nat
  bindingBits : Nat

/-- A byte view avoids materializing a full vector or a whole address space during loading. -/
structure InputBuffer where
  address : Nat
  length : Nat
  byteAt : Nat → Byte

def fixedBuffer {n : Nat} (address : Nat) (value : Bytes n) : InputBuffer :=
  ⟨address, n, fun i => BitVec.ofNat 8 (value.toNat / 2 ^ (8 * i))⟩

def vectorBuffer (address : Nat) (m : MessageVector) : InputBuffer :=
  ⟨address, VECTOR_LENGTH * MESSAGE_BYTES, fun j =>
    if h : j / MESSAGE_BYTES < VECTOR_LENGTH then
      BitVec.ofNat 8 ((m ⟨j / MESSAGE_BYTES, h⟩).toNat / 2 ^ (8 * (j % MESSAGE_BYTES)))
    else 0⟩

/-- Positions are serialized in increasing order, as little-endian 64-bit integers. -/
def positionsBuffer (address : Nat) (I : Positions) : InputBuffer :=
  let indices := I.sort (· ≤ ·)
  ⟨address, 8 * indices.length, fun j =>
    match indices[j / 8]? with
    | none => 0
    | some i => BitVec.ofNat 8 (i.val / 2 ^ (8 * (j % 8)))⟩

def valuesBuffer (address : Nat) (I : Positions) (a : ∀ _ : I, Message) : InputBuffer :=
  let indices := I.attach.sort (fun i j => i.val ≤ j.val)
  ⟨address, MESSAGE_BYTES * indices.length, fun j =>
    match indices[j / MESSAGE_BYTES]? with
    | none => 0
    | some i => BitVec.ofNat 8 ((a i).toNat / 2 ^ (8 * (j % MESSAGE_BYTES)))⟩

def inputBuffers (s : Submission) : (p : Program) → Input s.sizes p → List InputBuffer
  | .commit, m => [vectorBuffer s.layout.message m]
  | .opening, (td, I) =>
      [fixedBuffer s.layout.trapDoor td, positionsBuffer s.layout.indices I]
  | .check, input =>
      [fixedBuffer s.layout.commitment input.commitment, positionsBuffer s.layout.indices input.indices,
       valuesBuffer s.layout.claimedValues input.indices input.claimedValues,
       ⟨s.layout.openingProof, input.proof.length, fun j => input.proof[j]?.getD 0⟩]

def inputValid (s : Submission) : (p : Program) → Input s.sizes p → Bool
  | .check, input => decide (input.proof.length ≤ s.sizes.openingProof)
  | _, _ => true

def inputCount (s : Submission) : (p : Program) → Input s.sizes p → Nat
  | .commit, _ => VECTOR_LENGTH
  | .opening, (_, I) => I.card
  | .check, input => input.indices.card

def proofLength (s : Submission) : (p : Program) → Input s.sizes p → Nat
  | .check, input => input.proof.length
  | _, _ => s.sizes.openingProof

/-- Input buffers take precedence over image data; Admission proves they are disjoint.
All other bytes are zero. Each stored machine word packs eight consecutive bytes. -/
def initialState (s : Submission) (p : Program) (input : Input s.sizes p) : MachineState :=
  let image := s.image p
  let inputs := inputBuffers s p input
  let byteAt := fun address =>
    match inputs.find? (fun b => decide (b.address ≤ address ∧ address < b.address + b.length)) with
    | some b => b.byteAt (address - b.address)
    | none => if Riscv.dataBase image ≤ address then
        image.data[address - Riscv.dataBase image]?.getD 0 else 0
  let state : MachineState := { Riscv.initialMachine with
    mem := fun address => BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (byteAt (address.toNat + j)).toNat * 2 ^ (8 * j)) }
  let state := state.setReg .x2 (BitVec.ofNat 64 (Riscv.dataBase image))
  let state := state.setReg .x10 (BitVec.ofNat 64 s.layout.message)
  let state := state.setReg .x11 (BitVec.ofNat 64 s.layout.commitment)
  let state := state.setReg .x12 (BitVec.ofNat 64 s.layout.trapDoor)
  let state := state.setReg .x13 (BitVec.ofNat 64 s.layout.indices)
  let state := state.setReg .x14 (BitVec.ofNat 64 s.layout.claimedValues)
  let state := state.setReg .x15 (BitVec.ofNat 64 s.layout.openingProof)
  let state := state.setReg .x16 (BitVec.ofNat 64 (inputCount s p input))
  state.setReg .x17 (BitVec.ofNat 64 (proofLength s p input))

/-- Oversized adversarial proofs reject before loading; all other inputs execute the image. -/
def Submission.run (s : Submission) (p : Program) (input : Input s.sizes p) :
    OracleComp (World s.family) Riscv.Execution :=
  if inputValid s p input then
    Riscv.execute s.family (s.image p) (s.steps p) (initialState s p input)
  else pure ⟨.failure, Riscv.initialMachine, 0, 0⟩

def readOutput (s : Submission) : (p : Program) → Riscv.Execution → Option (Output s.sizes p)
  | .commit, result => if result.exit = .success then
      some (Riscv.readBuffer result.state s.layout.commitment COMMITMENT_BYTES,
        Riscv.readBuffer result.state s.layout.trapDoor s.sizes.trapDoor) else none
  | .opening, result =>
      let n := (result.state.getReg .x11).toNat
      if result.exit = .success ∧ n ≤ s.sizes.openingProof then
        some ((List.range n).map fun j => result.state.getByte
          (BitVec.ofNat 64 (s.layout.openingProof + j))) else none
  | .check, result => if result.exit = .success then some () else none

def Submission.commit (s : Submission) (m : MessageVector) :
    OracleComp (World s.family) (Option (Commitment × TrapDoor s.sizes)) :=
  readOutput s .commit <$> s.run .commit m

def Submission.opening (s : Submission) (td : TrapDoor s.sizes) (I : Positions) :
    OracleComp (World s.family) (Option (List Byte)) :=
  readOutput s .opening <$> s.run .opening (td, I)

def Submission.check (s : Submission) (c : Commitment) (I : Positions)
    (a : ∀ _ : I, Message) (pf : List Byte) : OracleComp (World s.family) Bool :=
  (fun result => (readOutput s .check result).isSome) <$> s.run .check ⟨c, I, a, pf⟩
end CommitGolf.VectorCommit
