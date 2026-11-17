import CommitGolfCandidate.CommitInput
import CommitGolfCandidate.S3Leaf

/-! Stage-3 commitment: reference state transformer of the appended leaf phase.
Definitions only. The execution proofs (image fetches, cycles) and the memory
refinement (digests, nonce repair) are both stated against these definitions.

Appended code (word index 251827, PC 1011404, entered by the jump at word 54):
five entry instructions, eight segments of 64 unrolled leaves (14 instructions each),
two pointer advances per segment, a two-instruction long transfer per eight segments,
the 42-instruction nonce repair, three exit instructions
ending in the jump to parent setup (PC 4364). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- x10 := message-16, permutation width and selector, x7 := 2048 (heap bytes per group). -/
def s3EntryInstructions : List Instr :=
  [.ADDI .x10 .x10 16, .ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x7 .x0 2047, .ADDI .x7 .x7 1]

def s3EntryState (state : MachineState) : MachineState :=
  s3EntryInstructions.foldl execInstrBr state

/-- Zero the 16 capacity bytes below the leaf; the first call is in place. -/
def s3LeafHeadInstructions : List Instr :=
  [.SD .x10 .x0 0, .SD .x10 .x0 8, .ADDI .x12 .x10 0]

def s3LeafHead (state : MachineState) : MachineState :=
  s3LeafHeadInstructions.foldl execInstrBr state

/-- Copy the three nonce words of leaf `u` of the group over reply bytes 72..96,
move the input to that window, and aim the reply at the leaf's heap slot. -/
def s3LeafMidInstructions (u : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofNat 12 (24*u)), .SD .x10 .x6 72,
   .LD .x6 .x18 (BitVec.ofNat 12 (24*u+8)), .SD .x10 .x6 80,
   .LD .x6 .x18 (BitVec.ofNat 12 (24*u+16)), .SD .x10 .x6 88,
   .ADDI .x10 .x10 72, .ADDI .x12 .x23 (BitVec.ofNat 12 (32*u))]

def s3LeafMid (u : Nat) (state : MachineState) : MachineState :=
  (s3LeafMidInstructions u).foldl execInstrBr state

def s3LeafTail (state : MachineState) : MachineState :=
  execInstrBr state (.ADDI .x10 .x10 184)

/-- The 200-byte permutation input addressed by x10. -/
def s3PermInput (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  readBuffer state (state.getReg .x10).toNat 200

/-- The 200-byte reply written at x12 (the syscall also advances the PC). -/
def s3PermReply (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) : MachineState :=
  writeBits state (state.getReg .x12) answer

/-- One leaf: fourteen instructions, two forward permutation queries. -/
def s3Leaf (u : Nat) (state : MachineState) : OracleComp World MachineState := do
  let head := s3LeafHead state
  let first ← World.query (.inr (.inr (.inl (s3PermInput head))))
  let mid := s3LeafMid u (s3PermReply head first)
  let second ← World.query (.inr (.inr (.inl (s3PermInput mid))))
  return s3LeafTail (s3PermReply mid second)

/-- Leaves `u, u+1, ..., u+count-1` of one group. -/
def s3GroupLeaves : MachineState → Nat → Nat → OracleComp World MachineState
  | state, _, 0 => pure state
  | state, u, count + 1 => do
      let next ← s3Leaf u state
      s3GroupLeaves next (u + 1) count

/-- Advance the nonce and heap bases by one group and branch back while leaf slots remain. -/
def s3LatchInstructions : List Instr :=
  [.ADDI .x18 .x18 1536, .ADD .x23 .x23 .x7, .BLTU .x23 .x22 4600]

def s3LatchState (state : MachineState) : MachineState :=
  let advanced := (s3LatchInstructions.take 2).foldl execInstrBr state
  if advanced.pc = 1040160 then
    advanced.setPC (if BitVec.ult (advanced.getReg .x23) (advanced.getReg .x22)
      then 1011424 else 1040172)
  else advanced

def s3Group (state : MachineState) : OracleComp World MachineState := do
  let leaves ← s3GroupLeaves state 0 64
  return s3LatchState leaves

def s3Groups : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, groups + 1 => do
      let next ← s3Group state
      s3Groups next groups

/-- The last leaf's 200-byte reply covers nonces 0..6. Their copies are still in the
message windows of leaves 0..6 (x8 = message base); copy them back (x22 = nonce base). -/
def s3RepairInstructions : List Instr :=
  (List.range 7).flatMap fun leaf => (List.range 3).flatMap fun word =>
    [.LD .x6 .x8 (BitVec.ofNat 12 (256*leaf+56+8*word)),
     .SD .x22 .x6 (BitVec.ofNat 12 (24*leaf+8*word))]

/-- Restore the compression width and selector and jump to parent setup (PC 4364). -/
def s3ExitInstructions : List Instr :=
  [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .JAL .x0 1061168]

def s3FinishState (state : MachineState) : MachineState :=
  (s3RepairInstructions ++ s3ExitInstructions).foldl execInstrBr state

/-- The whole appended leaf phase for `64 * groups` leaves, from PC 1011404 to PC 4364. -/
def s3Leaves (state : MachineState) (groups : Nat) : OracleComp World MachineState := do
  let hashed ← s3Groups (s3EntryState state) groups
  return s3FinishState hashed

/-- Leaf phase, the testers' parent schedule, root copy and exit. -/
def s3CommitBody (state : MachineState) (groups : Nat) : OracleComp World MachineState := do
  let leaves ← s3Leaves state groups
  let parents ← commitParents (commitParentsStartState leaves) (64 * groups - 1)
  return commitExitState (commitCopyState parents 79)

/-- State at the first appended instruction, for any private random answer. -/
def s3CommitReady (message : Message) {bits : Nat} (answer : BitVec bits) : MachineState :=
  ((commitInputReady message answer).setReg .x1 4316).setPC 1011404

/-- Exact distribution of the stage-3 commitment machine, including private nonces. -/
def s3CommitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← s3CommitBody (s3CommitReady message answer) (2 ^ 18)
  return ⟨.success, finished, 688456165, 3 * 2 ^ 24 - 1⟩

end CommitGolfCandidate
