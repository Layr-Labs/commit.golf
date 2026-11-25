import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! Parent construction on the gap heap. Every parent is one direct 96-byte
compression of the contiguous pair `[left | right | zero gap]`; two parents per loop
iteration, then the root, the root copy and the successful return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The three direct parent calls: `j = 0` (odd parent of an iteration), `j = 1` (even
parent of an iteration) and `j = 2` (the root). -/
def parentCallIndex (j : Nat) : Nat := if j = 0 then 101 else if j = 1 then 104 else 110
def parentSourceReg (j : Nat) : Reg := if j = 2 then .x9 else .x21
def parentTargetReg (j : Nat) : Reg := if j = 2 then .x9 else .x22
def parentSourceOffset (j : Nat) : Nat := if j = 1 then 0 else 96
def parentTargetOffset (j : Nat) : Nat := if j = 1 then 0 else 32

def parentCallInstructions (j : Nat) : List Instr :=
  [.ADDI .x10 (parentSourceReg j) (BitVec.ofNat 12 (parentSourceOffset j)),
   .ADDI .x12 (parentTargetReg j) (BitVec.ofNat 12 (parentTargetOffset j))]

private def parentCallPrefix (state : MachineState) (j count : Nat) : MachineState :=
  ((parentCallInstructions j).take count).foldl execInstrBr state

def parentSetupState (state : MachineState) (j : Nat) : MachineState := parentCallPrefix state j 2

/-- Input address of parent call `j`. -/
def parentSource (state : MachineState) (j : Nat) : Word :=
  state.getReg (parentSourceReg j) + BitVec.ofNat 64 (parentSourceOffset j)

/-- Output address of parent call `j`. -/
def parentOutput (state : MachineState) (j : Nat) : Word :=
  state.getReg (parentTargetReg j) + BitVec.ofNat 64 (parentTargetOffset j)

abbrev parentQuery (state : MachineState) (j : Nat) : PublicSpec.Domain :=
  .inl (readBuffer state (parentSource state j).toNat 96)

/-- State after parent call `j`: the reply is written at the call's output address. -/
def parentCallState (state : MachineState) (j : Nat) (answer : BitVec 256) : MachineState :=
  writeBits (parentSetupState state j) (parentOutput state j) answer

theorem parent_call_index_bound (j : Nat) : parentCallIndex j ≤ 110 := by
  unfold parentCallIndex; split <;> (try split) <;> omega

theorem parent_setup_memory (state : MachineState) (j : Nat) :
    (parentSetupState state j).mem = state.mem := by
  unfold parentSetupState parentCallPrefix parentCallInstructions
  rfl

theorem parent_setup_registers (state : MachineState) (j : Nat) (hj : j < 3) :
    (parentSetupState state j).getReg .x10 = parentSource state j ∧
    (parentSetupState state j).getReg .x12 = parentOutput state j ∧
    (parentSetupState state j).pc = state.pc + 8 ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → (parentSetupState state j).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · interval_cases j <;>
      simp [parentSetupState, parentCallPrefix, parentCallInstructions, parentSource, parentSourceReg,
        parentSourceOffset, execInstrBr, signExtend12, MachineState.getReg_setPC, MachineState.setPC] <;>
      rfl
  · interval_cases j <;>
      simp [parentSetupState, parentCallPrefix, parentCallInstructions, parentOutput, parentTargetReg,
        parentTargetOffset, parentSourceReg, execInstrBr, signExtend12, MachineState.getReg_setPC,
        MachineState.setPC, MachineState.getReg_setReg_ne] <;>
      rfl
  · interval_cases j <;>
      simp [parentSetupState, parentCallPrefix, parentCallInstructions, execInstrBr,
        MachineState.setPC, BitVec.add_assoc] <;>
      rfl
  · intro reg n10 n12
    unfold parentSetupState parentCallPrefix parentCallInstructions
    simp only [List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12)]

theorem parent_call_memory (state : MachineState) (j : Nat) (answer : BitVec 256) :
    (parentCallState state j answer).mem = (writeBits state (parentOutput state j) answer).mem :=
  write_bits_memory_congr _ _ _ answer (parent_setup_memory state j)

theorem parent_call_register (state : MachineState) (j : Nat) (hj : j < 3)
    (answer : BitVec 256) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentCallState state j answer).getReg reg = state.getReg reg := by
  rw [parentCallState, writeBits_register]
  exact (parent_setup_registers state j hj).2.2.2 reg n10 n12

theorem parent_call_pc (state : MachineState) (j : Nat) (hj : j < 3) (answer : BitVec 256) :
    (parentCallState state j answer).pc = state.pc + 12 := by
  simp only [parentCallState, writeBits, MachineState.setPC]
  rw [(parent_setup_registers state j hj).2.2.1, BitVec.add_assoc]
  rfl

/-- The call's addresses only depend on the pointer registers x9, x21 and x22. -/
theorem parent_source_congr (left right : MachineState) (j : Nat)
    (r9 : left.getReg .x9 = right.getReg .x9) (r21 : left.getReg .x21 = right.getReg .x21) :
    parentSource left j = parentSource right j := by
  unfold parentSource parentSourceReg
  split <;> simp [r9, r21]

theorem parent_output_congr (left right : MachineState) (j : Nat)
    (r9 : left.getReg .x9 = right.getReg .x9) (r22 : left.getReg .x22 = right.getReg .x22) :
    parentOutput left j = parentOutput right j := by
  unfold parentOutput parentTargetReg
  split <;> simp [r9, r22]

/-- Address side conditions of parent call `j`. -/
def ParentCallValid (state : MachineState) (j : Nat) : Prop :=
  rangeValid (parentSource state j) 96 = true ∧ (parentSource state j).toNat % 8 = 0 ∧
    rangeValid (parentOutput state j) 32 = true ∧ (parentOutput state j).toNat % 8 = 0

set_option maxHeartbeats 3200000 in
/-- Direct parent call `j`: two pointer instructions and one 96-byte compression
query. Ten cycles and one query. -/
theorem commit_parent_call (state : MachineState) (j : Nat) (hj : j < 3)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex j))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ParentCallValid state j) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (parentQuery state j))
          let result ← execute (submission.image .commit) fuel (parentCallState state j answer) true
          return result.charge 10 1) := by
  have idx := parent_call_index_bound j
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentCallPrefix state j 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := parentCallPrefix state j)
    intro i hi
    refine ⟨.base (((parentCallInstructions j)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (parentCallIndex j + i) _ (by omega)
      · interval_cases j <;> interval_cases i <;>
          simp [parentCallPrefix, parentCallInstructions, parentCallIndex, execInstrBr, pc,
            MachineState.setPC]
      · interval_cases j <;> interval_cases i <;> rfl
    · interval_cases j <;> interval_cases i <;> rfl
    · interval_cases j <;> interval_cases i <;> rfl
  let ready := parentCallPrefix state j 2
  have regs := parent_setup_registers state j hj
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (parentCallIndex j + 2)) := by
    change (parentSetupState state j).pc = _
    rw [regs.2.2.1, pc]
    interval_cases j <;> rfl
  have fetched : fetch (submission.image .commit) ready = some (.base .ECALL) := by
    apply commit_fetch _ (parentCallIndex j + 2) _ (by omega) readyPC
    interval_cases j <;> rfl
  have r5' : ready.getReg .x5 = 0 := (regs.2.2.2 .x5 (by decide) (by decide)).trans r5
  have r11' : ready.getReg .x11 = 96 := (regs.2.2.2 .x11 (by decide) (by decide)).trans r11
  have r13' : ready.getReg .x13 = 0 := (regs.2.2.2 .x13 (by decide) (by decide)).trans r13
  have r10' : ready.getReg .x10 = parentSource state j := regs.1
  have r12' : ready.getReg .x12 = parentOutput state j := regs.2.1
  have sv : rangeValid (ready.getReg .x10) 96 = true := by rw [r10']; exact valid.1
  have sa : (ready.getReg .x10).toNat % 8 = 0 := by rw [r10']; exact valid.2.1
  have dv : rangeValid (ready.getReg .x12) 32 = true := by rw [r12']; exact valid.2.2.1
  have da : (ready.getReg .x12).toNat % 8 = 0 := by rw [r12']; exact valid.2.2.2
  have memory : readBuffer ready (ready.getReg .x10).toNat 96 =
      readBuffer state (ready.getReg .x10).toNat 96 := by
    have sameMem : ready.mem = state.mem := parent_setup_memory state j
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have input' : oracleInput ready = some (.inl (readBuffer state (ready.getReg .x10).toNat 96)) := by
    simp [oracleInput, r11', r13', sv, sa, dv, da, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, memory]
    try rw [r13']
    try simp [memory]
    try rfl
  have input : oracleInput ready = some (.inl (readBuffer state (parentSource state j).toNat 96)) := by
    rw [input', r10']
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup, execute, fetched, if_pos r5', input]
  simp only [writeOracleAnswer, r12', bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state (parentSource state j).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, parentCallState, parentSetupState,
    ← Nat.add_assoc]
  congr

/-- Move both pointers down by one parent pair; loop while parents remain, else go to
the root call. -/
def parentNextState (state : MachineState) : MachineState :=
  ((state.setReg .x21 (state.getReg .x21 - 192)).setReg .x22 (state.getReg .x22 - 96)).setPC
    (if state.getReg .x22 - 96 = state.getReg .x9 then 4536 else 4500)

private def parentNextInstructions : List Instr :=
  [.ADDI .x21 .x21 3904, .ADDI .x22 .x22 4000]

private def parentNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentNextInstructions.take count).foldl execInstrBr state

theorem commit_parent_next (state : MachineState) (pc : state.pc = 4524) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (parentNextState state) true
          return result.charge 3 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentNextPrefix state 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := parentNextPrefix state)
    intro i hi
    refine ⟨.base ((parentNextInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (107 + i) _ (by omega)
      · interval_cases i <;> simp [parentNextPrefix, parentNextInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentNextPrefix state 2) =
      some (.base (.BNE .x22 .x9 8160)) := by
    apply commit_fetch _ 109 _ (by decide)
    · simp [parentNextPrefix, parentNextInstructions, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (parentNextPrefix state 2) (.base (.BNE .x22 .x9 8160)) =
      some (parentNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      parentNextPrefix, parentNextInstructions, parentNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc, BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- One loop iteration: the odd parent, the even parent, then advance. -/
def parentIterationRun (state : MachineState) : OracleComp World MachineState := do
  let a ← World.query (.inr (parentQuery state 0))
  let b ← World.query (.inr (parentQuery (parentCallState state 0 a) 1))
  return parentNextState (parentCallState (parentCallState state 0 a) 1 b)

theorem parent_iteration_support (state finished : MachineState)
    (reachable : finished ∈ support (parentIterationRun state)) :
    ∃ a b, finished = parentNextState (parentCallState (parentCallState state 0 a) 1 b) := by
  simp only [parentIterationRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨a, _, b, _, rfl⟩ := reachable
  exact ⟨a, b, rfl⟩

set_option maxHeartbeats 1600000 in
/-- One parent loop iteration: nine instructions, 23 cycles and two queries. The
address conditions of the second call are stated on the iteration's start state; the
first call does not move the pointer registers. -/
theorem commit_parent_iteration (state : MachineState) (pc : state.pc = 4500)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (first : ParentCallValid state 0) (second : ParentCallValid state 1) (fuel : Nat) :
    execute (submission.image .commit) (9 + fuel) state true =
      (do let finished ← parentIterationRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 23 2) := by
  rw [show 9 + fuel = 3 + (3 + (3 + fuel)) by omega,
    commit_parent_call state 0 (by decide) (by rw [pc]; rfl) r5 r11 r13 first]
  simp only [parentIterationRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change BitVec 256 at a
  let s1 := parentCallState state 0 a
  have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) : s1.getReg reg = state.getReg reg :=
    parent_call_register state 0 (by decide) a reg n10 n12
  have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex 1) := by
    rw [parent_call_pc state 0 (by decide), pc]; rfl
  have valid1 : ParentCallValid s1 1 := by
    have src := parent_source_congr s1 state 1 (keep .x9 (by decide) (by decide))
      (keep .x21 (by decide) (by decide))
    have out := parent_output_congr s1 state 1 (keep .x9 (by decide) (by decide))
      (keep .x22 (by decide) (by decide))
    unfold ParentCallValid
    rw [src, out]
    exact second
  rw [commit_parent_call s1 1 (by decide) s1pc ((keep .x5 (by decide) (by decide)).trans r5)
    ((keep .x11 (by decide) (by decide)).trans r11) ((keep .x13 (by decide) (by decide)).trans r13)
    valid1]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro b _
  change BitVec 256 at b
  have s2pc : (parentCallState s1 1 b).pc = 4524 := by
    rw [parent_call_pc s1 1 (by decide), s1pc]; rfl
  rw [commit_parent_next _ s2pc]
  simp [Execution.charge, ← Nat.add_assoc]
  rfl

private def parentStartInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 383, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 2047, .SLLI .x6 .x6 11, .ADDI .x6 .x6 1856, .ADD .x21 .x9 .x6,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 191, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 2047, .SLLI .x6 .x6 11, .ADDI .x6 .x6 1952, .ADD .x22 .x9 .x6]

private def parentStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentStartInstructions.take count).foldl execInstrBr state

/-- Pointer initialization before the parent loop (instructions 84-100):
x21 = x9 + 96n - 192 and x22 = x9 + 48n - 96, then branch to the loop. -/
def commitParentsStartState (state : MachineState) : MachineState :=
  execInstrBr (parentStartPrefix state 16) (.BEQ .x22 .x9 40)

set_option maxRecDepth 20000 in
private theorem parent_start_prefix_pc (state : MachineState) (pc : state.pc = 4432) :
    (parentStartPrefix state 16).pc = 4496 := by
  simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem commit_parents_start (state : MachineState) (pc : state.pc = 4432) (fuel : Nat) :
    execute (submission.image .commit) (17 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 17 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (16 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentStartPrefix state 16) true
            return result.charge 16 0) := by
    apply execute_unit_steps (states := parentStartPrefix state)
    intro i hi
    refine ⟨.base ((parentStartInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (84 + i) _ (by omega)
      · interval_cases i <;>
          simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentStartPrefix state 16) =
      some (.base (.BEQ .x22 .x9 40)) := by
    apply commit_fetch _ 100 _ (by decide)
    · rw [parent_start_prefix_pc state pc]; rfl
    · rfl
  have stepped : ordinaryStep (parentStartPrefix state 16) (.base (.BEQ .x22 .x9 40)) =
      some (commitParentsStartState state) := rfl
  rw [show 17 + fuel = 16 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem parent_start_prefix_memory (state : MachineState) :
    (parentStartPrefix state 16).mem = state.mem := rfl

private theorem parent_start_prefix_register (state : MachineState) (reg : Reg)
    (n6 : reg ≠ .x6) (n21 : reg ≠ .x21) (n22 : reg ≠ .x22) :
    (parentStartPrefix state 16).getReg reg = state.getReg reg := by
  simp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n6),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n22)]

set_option maxRecDepth 20000 in
private theorem parent_start_prefix_pointers (state : MachineState) :
    (parentStartPrefix state 16).getReg .x21 = state.getReg .x9 + 1610612544 ∧
    (parentStartPrefix state 16).getReg .x22 = state.getReg .x9 + 805306272 := by
  dsimp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- The start leaves memory and all other registers alone, sets both pointers, and
always enters the loop (the pointer offset is nonzero). -/
theorem commit_parents_start_state (state : MachineState) (pc : state.pc = 4432) :
    (commitParentsStartState state).getReg .x21 = state.getReg .x9 + 1610612544 ∧
    (commitParentsStartState state).getReg .x22 = state.getReg .x9 + 805306272 ∧
    (commitParentsStartState state).pc = 4500 ∧
    (commitParentsStartState state).mem = state.mem ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x21 → reg ≠ .x22 →
      (commitParentsStartState state).getReg reg = state.getReg reg := by
  have pointers := parent_start_prefix_pointers state
  have x9 := parent_start_prefix_register state .x9 (by decide) (by decide) (by decide)
  have different : (parentStartPrefix state 16).getReg .x22 ≠ (parentStartPrefix state 16).getReg .x9 := by
    rw [pointers.2, x9]
    intro same
    have zero := BitVec.add_right_eq_self.mp same
    exact absurd zero (by decide)
  have branch : commitParentsStartState state =
      (parentStartPrefix state 16).setPC ((parentStartPrefix state 16).pc + 4) := by
    unfold commitParentsStartState
    simp only [execInstrBr]
    rw [ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) different)]
  rw [branch]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [MachineState.getReg_setPC]; exact pointers.1
  · rw [MachineState.getReg_setPC]; exact pointers.2
  · simp only [MachineState.setPC]; rw [parent_start_prefix_pc state pc]; rfl
  · exact parent_start_prefix_memory state
  · intro reg n6 n21 n22
    rw [MachineState.getReg_setPC]
    exact parent_start_prefix_register state reg n6 n21 n22

def commitExitState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 4588

theorem commit_exit (state : MachineState) (pc : state.pc = 4580) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 4584
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply commit_fetch _ 121 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply commit_fetch _ 122 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply commit_fetch _ 123 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, MachineState.getReg]
  have s1 : ordinaryStep next (.base (.ADDI .x10 .x0 0)) = some (commitExitState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, commitExitState, MachineState.getReg, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, instructionCycles, bind_assoc, pure_bind]
  simp [commitExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC, Execution.charge]

end CommitGolfCandidate
