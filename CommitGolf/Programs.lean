import CommitGolf.Riscv
import CommitGolf.Scheme

/-! # Submitted programs

The scheme used in the security games is derived from the submitted machine images.
Inputs are loaded into fresh zeroed memory; only the serialized trapdoor passes from
commitment to opening. Verification cannot request private randomness. The certificate
requires successful honest machine runs, so fallback values on machine failure cannot
serve as a shortcut to a valid submission. -/

namespace CommitGolf
open OracleComp OracleSpec RiscvZkvm.Rv64

inductive Program where
  | commit | opening | check
  deriving DecidableEq

/-- Solver-declared byte capacities, not scored lengths. -/
structure Sizes where
  trapdoor : Nat
  proof : Nat

structure Layout where
  message : Nat
  commitment : Nat
  trapdoor : Nat
  indices : Nat
  values : Nat
  proof : Nat

structure Submission where
  sizes : Sizes
  layout : Layout
  image : Program → Riscv.Image
  steps : Program → Nat

def Layout.buffers (layout : Layout) (sizes : Sizes) : List (Nat × Nat) :=
  [(layout.message, LENGTH * (LEAF_SIZE / 8)), (layout.commitment, DIGEST_BYTES),
   (layout.trapdoor, sizes.trapdoor), (layout.indices, LENGTH * 8),
   (layout.values, LENGTH * (LEAF_SIZE / 8)), (layout.proof, sizes.proof)]

/-- A functional byte view avoids allocating the entire vector during loading. -/
structure InputBuffer where
  address : Nat
  length : Nat
  byteAt : Nat → Byte

def fixedBuffer {bits : Nat} (address : Nat) (value : BitVec bits) : InputBuffer :=
  ⟨address, (bits + 7) / 8, fun i => value.extractLsb' (8 * i) 8⟩

def messageBuffer (address : Nat) (message : Message) : InputBuffer :=
  ⟨address, LENGTH * (LEAF_SIZE / 8), fun j =>
    if h : j / (LEAF_SIZE / 8) < LENGTH then
      (message ⟨j / (LEAF_SIZE / 8), h⟩).extractLsb' (8 * (j % (LEAF_SIZE / 8))) 8
    else 0⟩

/-- Positions are serialized in increasing order as little-endian 64-bit integers. -/
def positionsBuffer (address : Nat) (positions : Positions) : InputBuffer :=
  let indices := positions.sort (· ≤ ·)
  ⟨address, 8 * indices.length, fun j =>
    match indices[j / 8]? with
    | none => 0
    | some i => BitVec.ofNat 8 (i.val / 2 ^ (8 * (j % 8)))⟩

def valuesBuffer (address : Nat) (positions : Positions) (values : Values positions) : InputBuffer :=
  let indices := positions.attach.sort (fun i j => i.val ≤ j.val)
  ⟨address, (LEAF_SIZE / 8) * indices.length, fun j =>
    match indices[j / (LEAF_SIZE / 8)]? with
    | none => 0
    | some i => (values i).extractLsb' (8 * (j % (LEAF_SIZE / 8))) 8⟩

structure CheckInput where
  commitment : Commitment
  positions : Positions
  values : Values positions
  proof : Proof

def Input (sizes : Sizes) : Program → Type
  | .commit => Message
  | .opening => BitVec (8 * sizes.trapdoor) × Positions
  | .check => CheckInput

def Submission.inputBuffers (s : Submission) : (p : Program) → Input s.sizes p → List InputBuffer
  | .commit, message => [messageBuffer s.layout.message message]
  | .opening, (trapdoor, positions) =>
      [fixedBuffer s.layout.trapdoor trapdoor, positionsBuffer s.layout.indices positions]
  | .check, input =>
      [fixedBuffer s.layout.commitment input.commitment,
       positionsBuffer s.layout.indices input.positions,
       valuesBuffer s.layout.values input.positions input.values,
       ⟨s.layout.proof, input.proof.length, fun j => input.proof[j]?.getD 0⟩]

def inputCount {sizes : Sizes} : (p : Program) → Input sizes p → Nat
  | .commit, _ => LENGTH
  | .opening, (_, positions) => positions.card
  | .check, input => input.positions.card

def inputProofLength (sizes : Sizes) : (p : Program) → Input sizes p → Nat
  | .check, input => input.proof.length
  | _, _ => sizes.proof

/-- Load bytes little-endian. a0–a5 hold buffer addresses, a6 the number of positions,
a7 the proof length (check) or capacity (commit/opening). sp points below image data.
Input buffers and image data are disjoint for admitted submissions; all other memory is zero. -/
def Submission.initialState (s : Submission) (p : Program) (input : Input s.sizes p) : MachineState :=
  let image := s.image p
  let inputs := s.inputBuffers p input
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
  let state := state.setReg .x12 (BitVec.ofNat 64 s.layout.trapdoor)
  let state := state.setReg .x13 (BitVec.ofNat 64 s.layout.indices)
  let state := state.setReg .x14 (BitVec.ofNat 64 s.layout.values)
  let state := state.setReg .x15 (BitVec.ofNat 64 s.layout.proof)
  let state := state.setReg .x16 (BitVec.ofNat 64 (inputCount p input))
  state.setReg .x17 (BitVec.ofNat 64 (inputProofLength s.sizes p input))

/-- Oversized adversarial proofs reject without loading. Check forbids RANDOM syscalls. -/
def Submission.run (s : Submission) (p : Program) (input : Input s.sizes p) :
    OracleComp World Riscv.Execution :=
  let valid := match p, input with
    | .check, input => decide (input.proof.length ≤ s.sizes.proof)
    | _, _ => true
  if valid then Riscv.execute (s.image p) (s.steps p) (s.initialState p input) (p != .check)
  else pure ⟨.failure, Riscv.initialMachine, 0, 0⟩

def Submission.readCommit (s : Submission) (result : Riscv.Execution) :
    Commitment × BitVec (8 * s.sizes.trapdoor) :=
  (Riscv.readBuffer result.state s.layout.commitment DIGEST_BYTES,
   Riscv.readBuffer result.state s.layout.trapdoor s.sizes.trapdoor)

/-- An opening reports its byte length in a1 when halting. -/
def Submission.openingSucceeded (s : Submission) (result : Riscv.Execution) : Bool :=
  result.exit == .success && decide ((result.state.getReg .x11).toNat ≤ s.sizes.proof)

def Submission.readProof (s : Submission) (result : Riscv.Execution) : Proof :=
  if s.openingSucceeded result then
    (List.range (result.state.getReg .x11).toNat).map fun j =>
      result.state.getByte (BitVec.ofNat 64 (s.layout.proof + j))
  else []

/-- Check execution rejects RANDOM before making any coin query. This handler embeds its
public calls in `PublicSpec`; the coin arm is unreachable during check execution. -/
def checkHandler : QueryImpl World (OracleComp PublicSpec)
  | .inl n => pure (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inr q => PublicSpec.query q

/-- The actual machine programs define the scheme used by every security property. -/
def Submission.scheme (s : Submission) : Scheme where
  Trapdoor := BitVec (8 * s.sizes.trapdoor)
  commit message := s.readCommit <$> s.run .commit message
  opening trapdoor positions := s.readProof <$> s.run .opening (trapdoor, positions)
  check root positions values proof :=
    (fun result => result.exit == .success) <$>
      simulateQ checkHandler (s.run .check ⟨root, positions, values, proof⟩)

structure MachineResult where
  success : Bool
  commitCycles : Nat
  openingCycles : Nat
  proofBytes : Nat

/-- One full commitment followed by one opening. The same oracle is shared throughout.
The trapdoor is private, not transmitted or counted as proof bytes. -/
def Submission.honestMachine (s : Submission) (message : Message) (positions : Positions) :
    OracleComp World MachineResult := do
  let committed ← s.run .commit message
  let (_, trapdoor) := s.readCommit committed
  let opened ← s.run .opening (trapdoor, positions)
  return {
    success := committed.exit == Riscv.Exit.success && s.openingSucceeded opened
    commitCycles := committed.cycles
    openingCycles := opened.cycles
    proofBytes := (s.readProof opened).length }

/-- Score uses certified bounds for a full commit and one batch opening; lower is better. -/
def score (proofBytes commitCycles openingCycles : Nat) : Nat :=
  (commitCycles + openingCycles) * proofBytes

end CommitGolf
