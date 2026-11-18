import CommitGolfCandidate.CommitInput
import CommitGolfCandidate.S3Leaf

/-! Commitment reference: the state transformer of the appended code. Definitions only. The
execution proofs (image fetches, cycles) and the memory refinement (nonces, leaf digests, group
digests, internal nodes) are both stated against these definitions.

Appended code (word 251827, PC 1011404, entered by the jump at word 54):
* the nonce generator: nine setup instructions, then 23,832 passes of 64 unrolled forward
  permutation calls closed by a branch; reply `k` goes to `6106910984 + 176 k`;
* five stores that clear the seed block, nine leaf-phase setup instructions;
* 2^18 blocks of 64 leaves: two cell-base instructions, 64 unrolled leaves of eleven instructions
  (two calls each), 16 group calls of three instructions (one call each), five restore and latch
  instructions;
* the parent sweep: seven setup instructions (ending in a jump into the loop body), loop passes of
  256 unrolled parents (compression call, two pointer steps) closed by a branch, and the jump to
  the root copy at PC 4412.

Memory: heap node `n` at `T + 32 n` (`T` = x9), group `g` at node `2^22 + g`; cell `g` at
`T + 2^28 + 256 + 368 g`; nonce `i` at `6106911008 + 16 i`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The 200-byte permutation input addressed by x10. -/
def s3PermInput (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  readBuffer state (state.getReg .x10).toNat 200

/-- The 200-byte reply written at x12 (the syscall also advances the PC). -/
def s3PermReply (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) : MachineState :=
  writeBits state (state.getReg .x12) answer

/-! ### Nonce generator: forward permutation calls in counter mode under the 32-byte seed

The seed sits at x18 = 5368713248. Call `k` (from 1525247 down to 0) reads the block
`[x18 - 168, x18 + 32)`: the counter word (the call's reply address, stored by the call), 160 zero
bytes and the seed; its reply goes to `6106910984 + 176 k`. -/

/-- Permutation width and selector, input block `x10 = x18 - 168`, loop bound
`x6 = T + 1811939560 = 6106910984`, and the top call's reply address
`x12 = T + 2080383032 = 6106910984 + 176 * 1525247`. -/
def s4GenSetupInstructions : List Instr :=
  [.ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x10 .x18 (BitVec.ofNat 12 3928),
   .LUI .x6 442368, .ADD .x6 .x6 .x9, .ADDI .x6 .x6 232,
   .LUI .x12 507906, .ADD .x12 .x12 .x9, .ADDI .x12 .x12 56]

def s4GenSetup (state : MachineState) : MachineState :=
  s4GenSetupInstructions.foldl execInstrBr state

/-- One generator call: store the reply address as the counter word at x10, forward query on
`[x10, x10 + 200)`, reply at x12, then the next reply address 176 bytes lower. -/
def s4GenCall (state : MachineState) : OracleComp World MachineState := do
  let stored := execInstrBr state (.SD .x10 .x12 0)
  let reply ← World.query (.inr (.inr (.inl (s3PermInput stored))))
  return execInstrBr (s3PermReply stored reply) (.ADDI .x12 .x12 (BitVec.ofNat 12 3920))

/-- `count` consecutive generator calls. -/
def s4GenCalls : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, count + 1 => do
      let next ← s4GenCall state
      s4GenCalls next count

/-- One pass: 64 unrolled calls, then back to the first call while the reply address is at least
x6 (unsigned). -/
def s4GenPass (state : MachineState) : OracleComp World MachineState := do
  let called ← s4GenCalls state 64
  return execInstrBr called (.BGEU .x12 .x6 (BitVec.ofNat 13 7424))

def s4GenPasses : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, passes + 1 => do
      let next ← s4GenPass state
      s4GenPasses next passes

/-- The generator: setup, then `passes` passes (the image makes 23,832, i.e. 1,525,248 calls). -/
def s4Generator (state : MachineState) (passes : Nat) : OracleComp World MachineState :=
  s4GenPasses (s4GenSetup state) passes

/-- Clear the seed block `[x10, x10 + 200)`: its counter word and the 32-byte seed. -/
def s6GenClearInstructions : List Instr :=
  [.SD .x10 .x0 0, .SD .x10 .x0 168, .SD .x10 .x0 176, .SD .x10 .x0 184, .SD .x10 .x0 192]

def s6GenClear (state : MachineState) : MachineState :=
  s6GenClearInstructions.foldl execInstrBr state

/-! ### Leaf phase -/

/-- x18 := nonce base (x6 + 24), x22 := T + 2^28 (end of the heap), x23 := first cell
(T + 2^28 + 256), x24 := first group node (T + 2^27), x7 := 5888 (16 cells), x10 := the first
leaf's window (message - 24). -/
def s6LeafSetupInstructions : List Instr :=
  [.ADDI .x18 .x6 24, .LUI .x7 65536, .ADD .x22 .x9 .x7, .ADDI .x23 .x22 256,
   .LUI .x7 32768, .ADD .x24 .x9 .x7, .LUI .x7 1, .ADDI .x7 .x7 1792,
   .ADDI .x10 .x8 (BitVec.ofNat 12 4072)]

def s6LeafSetup (state : MachineState) : MachineState :=
  s6LeafSetupInstructions.foldl execInstrBr state

/-- Bases of cells 5 and 10 of the block: x25 := x23 + 1840, x27 := x25 + 1840. -/
def s6BlockBaseInstructions : List Instr :=
  [.ADDI .x25 .x23 1840, .ADDI .x27 .x25 1840]

def s6BlockBase (state : MachineState) : MachineState :=
  s6BlockBaseInstructions.foldl execInstrBr state

/-- Base register of cell `c` of a block. -/
def s6CellRegister (c : Nat) : Reg :=
  if c < 5 then .x23 else if c < 10 then .x25 else .x27

/-- Offset of cell `c` from its base register. -/
def s6CellOffset (c : Nat) : Nat :=
  if c < 5 then 368 * c else if c < 10 then 368 * (c - 5) else 368 * (c - 10)

/-- Leaf `l` of the block (x10 = leaf address - 24): copy its nonce (two words from the nonce
block at x18) to `[x10, x10 + 16)`, store the tag x10 at `x10 + 16`, aim the first reply 56 bytes
below the window. -/
def s3LeafHeadInstructions (l : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofNat 12 (16 * l)), .SD .x10 .x6 0,
   .LD .x6 .x18 (BitVec.ofNat 12 (16 * l + 8)), .SD .x10 .x6 8,
   .SD .x10 .x10 16, .ADDI .x12 .x10 (BitVec.ofNat 12 4040)]

def s3LeafHead (l : Nat) (state : MachineState) : MachineState :=
  (s3LeafHeadInstructions l).foldl execInstrBr state

/-- Move the window up by 80 bytes (first-reply bytes 136..200, then leaf bytes 120..256) and aim
the second reply at the leaf's digest slot in its cell (`72 + 32 (l % 4)` above the cell base). -/
def s3LeafMidInstructions (l : Nat) : List Instr :=
  [.ADDI .x10 .x10 80,
   .ADDI .x12 (s6CellRegister (l / 4)) (BitVec.ofNat 12 (s6CellOffset (l / 4) + 72 + 32 * (l % 4)))]

def s3LeafMid (l : Nat) (state : MachineState) : MachineState :=
  (s3LeafMidInstructions l).foldl execInstrBr state

/-- Where the next leaf's window goes: x10, except after the last leaf of the block, which parks
it in x21 (x10 then addresses the group calls). -/
def s3LeafNextRegister (l : Nat) : Reg :=
  if l = 63 then .x21 else .x10

def s3LeafTailInstruction (l : Nat) : Instr :=
  .ADDI (s3LeafNextRegister l) .x10 176

def s3LeafTail (l : Nat) (state : MachineState) : MachineState :=
  execInstrBr state (s3LeafTailInstruction l)

/-- One leaf: eleven instructions, two forward permutation queries. -/
def s3Leaf (l : Nat) (state : MachineState) : OracleComp World MachineState := do
  let head := s3LeafHead l state
  let first ← World.query (.inr (.inr (.inl (s3PermInput head))))
  let mid := s3LeafMid l (s3PermReply head first)
  let second ← World.query (.inr (.inr (.inl (s3PermInput mid))))
  return s3LeafTail l (s3PermReply mid second)

/-- Leaves `l, l+1, ..., l+count-1` of one block. -/
def s3GroupLeaves : MachineState → Nat → Nat → OracleComp World MachineState
  | state, _, 0 => pure state
  | state, l, count + 1 => do
      let next ← s3Leaf l state
      s3GroupLeaves next (l + 1) count

/-- Group call `c`: window = cell `c` (72 zero bytes, four leaf digests), reply at the group's
heap node `x24 + 32 c`. -/
def s6GroupCallInstructions (c : Nat) : List Instr :=
  [.ADDI .x10 (s6CellRegister c) (BitVec.ofNat 12 (s6CellOffset c)),
   .ADDI .x12 .x24 (BitVec.ofNat 12 (32 * c))]

def s6GroupCallHead (c : Nat) (state : MachineState) : MachineState :=
  (s6GroupCallInstructions c).foldl execInstrBr state

/-- One group call: three instructions, one forward permutation query. -/
def s6GroupCall (c : Nat) (state : MachineState) : OracleComp World MachineState := do
  let head := s6GroupCallHead c state
  let reply ← World.query (.inr (.inr (.inl (s3PermInput head))))
  return s3PermReply head reply

/-- Group calls `c, c+1, ..., c+count-1` of one block. -/
def s6GroupCalls : MachineState → Nat → Nat → OracleComp World MachineState
  | state, _, 0 => pure state
  | state, c, count + 1 => do
      let next ← s6GroupCall c state
      s6GroupCalls next (c + 1) count

/-- Restore the leaf window from x21, advance the nonce block (1024 bytes), the group nodes
(512 bytes) and the cells (x7 = 5888 bytes), and branch back while group nodes remain. -/
def s3LatchInstructions : List Instr :=
  [.ADDI .x10 .x21 0, .ADDI .x18 .x18 1024, .ADDI .x24 .x24 512, .ADD .x23 .x23 .x7,
   .BLTU .x24 .x22 (BitVec.ofNat 13 5160)]

def s3LatchState (state : MachineState) : MachineState :=
  s3LatchInstructions.foldl execInstrBr state

/-- One block: cell bases, 64 leaves, 16 group calls, restore and latch. -/
def s3Group (state : MachineState) : OracleComp World MachineState := do
  let leaves ← s3GroupLeaves (s6BlockBase state) 0 64
  let grouped ← s6GroupCalls leaves 0 16
  return s3LatchState grouped

def s3Groups : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, groups + 1 => do
      let next ← s3Group state
      s3Groups next groups

/-! ### Parent sweep: every internal node keeps the whole 256-bit compression reply -/

/-- Compression width and selector, x10 := the children of node 2^22 - 1 (`x22 - 64`),
x12 := its slot (`T + 2^27 - 32`), then the jump to the second parent of the loop body. -/
def s6ParentSetupInstructions : List Instr :=
  [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x10 .x22 (BitVec.ofNat 12 4032),
   .LUI .x7 32768, .ADD .x12 .x9 .x7, .ADDI .x12 .x12 (BitVec.ofNat 12 4064), .JAL .x0 16]

def s6ParentSetup (state : MachineState) : MachineState :=
  s6ParentSetupInstructions.foldl execInstrBr state

/-- The 64-byte compression input addressed by x10 (the two children). -/
def s6ParentInput (state : MachineState) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (state.getReg .x10).toNat 64

/-- The 32-byte compression reply written at x12 (the syscall also advances the PC). -/
def s6ParentReply (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  writeBits state (state.getReg .x12) answer

/-- After the call: step both pointers down by one node. -/
def s6ParentStepInstructions : List Instr :=
  [.ADDI .x10 .x10 (BitVec.ofNat 12 4032), .ADDI .x12 .x12 (BitVec.ofNat 12 4064)]

def s6ParentStep (state : MachineState) : MachineState :=
  s6ParentStepInstructions.foldl execInstrBr state

/-- One parent: compression query on the 64 bytes at x10, reply at x12, two pointer steps.
Three instructions, ten cycles, one query. -/
def s6Parent (state : MachineState) : OracleComp World MachineState := do
  let reply ← World.query (.inr (.inl (s6ParentInput state)))
  return s6ParentStep (s6ParentReply state reply)

/-- `count` consecutive parents. -/
def s6ParentRun : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, count + 1 => do
      let next ← s6Parent state
      s6ParentRun next count

/-- The loop branch: back to the first parent of the body while x12 has not reached x9. -/
def s6ParentBranch : Instr := .BNE .x12 .x9 (BitVec.ofNat 13 5120)

/-- `count` parents and the loop branch (a full pass has 256; the first one, entered at the
body's second parent, has 255). -/
def s6ParentPass (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let swept ← s6ParentRun state count
  return execInstrBr swept s6ParentBranch

def s6ParentPasses : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, passes + 1 => do
      let next ← s6ParentPass state 256
      s6ParentPasses next passes

/-- The jump from the end of the sweep to the root copy (PC 4412). -/
def s6ParentExit : Instr := .JAL .x0 (BitVec.ofNat 21 1083156)

/-- The whole parent sweep from PC 1015304: setup, a first pass of 255 parents, 16,383 passes of
256 parents (4,194,303 internal nodes in all, from node 2^22 - 1 down to node 1) and the jump to
PC 4412. -/
def s6Parents (state : MachineState) : OracleComp World MachineState := do
  let first ← s6ParentPass (s6ParentSetup state) 255
  let swept ← s6ParentPasses first 16383
  return execInstrBr swept s6ParentExit

/-! ### The whole appended code -/

/-- From PC 1011404 to the parent setup (PC 1015304) for `groups` blocks of 64 leaves: the nonce
generator, the seed-block clearing, the leaf-phase setup and the blocks. -/
def s3Leaves (state : MachineState) (groups : Nat) : OracleComp World MachineState := do
  let filled ← s4Generator state 23832
  s3Groups (s6LeafSetup (s6GenClear filled)) groups

/-- Leaf phase, parent sweep, root copy and exit. -/
def s3CommitBody (state : MachineState) (groups : Nat) : OracleComp World MachineState := do
  let leaves ← s3Leaves state groups
  let parents ← s6Parents leaves
  return commitExitState (commitCopyState parents 79)

/-- State at the first appended instruction, for any private random answer (the seed). -/
def s3CommitReady (message : Message) {bits : Nat} (answer : BitVec bits) : MachineState :=
  ((commitInputReady message answer).setReg .x1 4316).setPC 1011404

/-- Exact distribution of the commitment machine: one private seed from the RANDOM syscall
(`x11 = 32` bytes after setup, `Commit.commit_setup_registers`), then the deterministic body. -/
def s3CommitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← s3CommitBody (s3CommitReady message answer) (2 ^ 18)
  return ⟨.success, finished, 520444244, 43468287⟩

end CommitGolfCandidate
