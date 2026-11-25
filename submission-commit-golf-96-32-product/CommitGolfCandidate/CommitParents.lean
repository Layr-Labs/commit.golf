import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! Parent construction on the gap heap. Every parent is one direct 96-byte
compression of the contiguous pair `[left | right | zero gap]`; sixteen parents
per loop iteration in descending order, then the fifteen-node straight-line tail
down to the root, the root copy, and the successful return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Instruction index of parent call `j` in the loop (`isTail = false`, `j < 16`)
or in the root tail (`isTail = true`, `j < 15`). -/
def parentCallIndex (isTail : Bool) (j : Nat) : Nat :=
  (if isTail then 755 else 704) + 3 * j

def parentSourceReg (isTail : Bool) : Reg := if isTail then .x9 else .x21
def parentTargetReg (isTail : Bool) : Reg := if isTail then .x9 else .x22
def parentSourceOffset (j : Nat) : Nat := 96 * (15 - j)
def parentTargetOffset (j : Nat) : Nat := heapOffset (15 - j)

private def parentCallPrefix (state : MachineState) (isTail : Bool) (j count : Nat) : MachineState :=
  ((parentCallInstructions isTail j).take count).foldl execInstrBr state

def parentSetupState (state : MachineState) (isTail : Bool) (j : Nat) : MachineState :=
  parentCallPrefix state isTail j 2

/-- Input address of parent call `j`. -/
def parentSource (state : MachineState) (isTail : Bool) (j : Nat) : Word :=
  state.getReg (parentSourceReg isTail) + BitVec.ofNat 64 (parentSourceOffset j)

/-- Output address of parent call `j`. -/
def parentOutput (state : MachineState) (isTail : Bool) (j : Nat) : Word :=
  state.getReg (parentTargetReg isTail) + BitVec.ofNat 64 (parentTargetOffset j)

abbrev parentQuery (state : MachineState) (isTail : Bool) (j : Nat) : PublicSpec.Domain :=
  .inl (readBuffer state (parentSource state isTail j).toNat 96)

/-- State after parent call `j`: the reply is written at the call's output address. -/
def parentCallState (state : MachineState) (isTail : Bool) (j : Nat)
    (answer : BitVec 256) : MachineState :=
  writeBits (parentSetupState state isTail j) (parentOutput state isTail j) answer

theorem parent_setup_memory (state : MachineState) (isTail : Bool) (j : Nat) :
    (parentSetupState state isTail j).mem = state.mem := by
  unfold parentSetupState parentCallPrefix parentCallInstructions
  cases isTail <;> rfl

theorem parent_setup_register (state : MachineState) (isTail : Bool) (j : Nat)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentSetupState state isTail j).getReg reg = state.getReg reg := by
  unfold parentSetupState parentCallPrefix parentCallInstructions
  simp only [List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12)]

theorem parent_setup_registers (state : MachineState) (isTail : Bool) (j : Nat) (hj : j < 16) :
    (parentSetupState state isTail j).getReg .x10 = parentSource state isTail j ∧
    (parentSetupState state isTail j).getReg .x12 = parentOutput state isTail j ∧
    (parentSetupState state isTail j).pc = state.pc + 8 ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 →
      (parentSetupState state isTail j).getReg reg = state.getReg reg := by
  have hsrc : signExtend12 (BitVec.ofNat 12 (96 * (15 - j))) =
      BitVec.ofNat 64 (96 * (15 - j)) :=
    signExtend12_ofNat_mul8 _ (by omega) (by omega)
  have hdst : signExtend12 (BitVec.ofNat 12 (heapOffset (15 - j))) =
      BitVec.ofNat 64 (heapOffset (15 - j)) :=
    signExtend12_ofNat_mul8 _ (by unfold heapOffset; omega) (by unfold heapOffset; omega)
  refine ⟨?_, ?_, ?_, fun reg n10 n12 => parent_setup_register state isTail j reg n10 n12⟩
  · cases isTail <;>
      simp only [parentSetupState, parentCallPrefix, parentCallInstructions, parentSource,
        parentSourceReg, parentSourceOffset, Bool.false_eq_true, ↓reduceIte, List.take,
        List.foldl, execInstrBr, hsrc, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
  · cases isTail
    · simp only [parentSetupState, parentCallPrefix, parentCallInstructions, parentOutput,
        parentTargetReg, parentTargetOffset, Bool.false_eq_true, ↓reduceIte, List.take,
        List.foldl, execInstrBr, hdst, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x22)]
    · simp only [parentSetupState, parentCallPrefix, parentCallInstructions, parentOutput,
        parentTargetReg, parentTargetOffset, ↓reduceIte, List.take,
        List.foldl, execInstrBr, hdst, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x9)]
  · cases isTail <;>
      simp only [parentSetupState, parentCallPrefix, parentCallInstructions,
        List.take, List.foldl, execInstrBr, MachineState.pc_setReg, MachineState.setPC,
        BitVec.add_assoc] <;>
      rfl

theorem parent_call_memory (state : MachineState) (isTail : Bool) (j : Nat) (answer : BitVec 256) :
    (parentCallState state isTail j answer).mem =
      (writeBits state (parentOutput state isTail j) answer).mem :=
  write_bits_memory_congr _ _ _ answer (parent_setup_memory state isTail j)

theorem parent_call_register (state : MachineState) (isTail : Bool) (j : Nat)
    (answer : BitVec 256) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentCallState state isTail j answer).getReg reg = state.getReg reg := by
  rw [parentCallState, writeBits_register]
  exact parent_setup_register state isTail j reg n10 n12

theorem parent_call_pc (state : MachineState) (isTail : Bool) (j : Nat) (hj : j < 16)
    (answer : BitVec 256) :
    (parentCallState state isTail j answer).pc = state.pc + 12 := by
  simp only [parentCallState, writeBits, MachineState.setPC]
  rw [(parent_setup_registers state isTail j hj).2.2.1, BitVec.add_assoc]
  rfl

/-- The call's addresses only depend on the pointer registers x9, x21 and x22. -/
theorem parent_source_congr (left right : MachineState) (isTail : Bool) (j : Nat)
    (r9 : left.getReg .x9 = right.getReg .x9) (r21 : left.getReg .x21 = right.getReg .x21) :
    parentSource left isTail j = parentSource right isTail j := by
  unfold parentSource parentSourceReg
  cases isTail <;> simp [r9, r21]

theorem parent_output_congr (left right : MachineState) (isTail : Bool) (j : Nat)
    (r9 : left.getReg .x9 = right.getReg .x9) (r22 : left.getReg .x22 = right.getReg .x22) :
    parentOutput left isTail j = parentOutput right isTail j := by
  unfold parentOutput parentTargetReg
  cases isTail <;> simp [r9, r22]

/-- Address side conditions of parent call `j`. -/
def ParentCallValid (state : MachineState) (isTail : Bool) (j : Nat) : Prop :=
  rangeValid (parentSource state isTail j) 96 = true ∧ (parentSource state isTail j).toNat % 8 = 0 ∧
    rangeValid (parentOutput state isTail j) 32 = true ∧ (parentOutput state isTail j).toNat % 8 = 0

theorem parent_call_valid_congr (left right : MachineState) (isTail : Bool) (j : Nat)
    (r9 : left.getReg .x9 = right.getReg .x9)
    (r21 : left.getReg .x21 = right.getReg .x21)
    (r22 : left.getReg .x22 = right.getReg .x22)
    (valid : ParentCallValid right isTail j) :
    ParentCallValid left isTail j := by
  unfold ParentCallValid
  rw [parent_source_congr left right isTail j r9 r21,
    parent_output_congr left right isTail j r9 r22]
  exact valid

set_option maxHeartbeats 1600000 in
/-- Direct parent call `j`: two pointer instructions and one 96-byte compression
query. Ten cycles and one query, proved symbolically for all loop and tail calls. -/
theorem commit_parent_call (state : MachineState) (isTail : Bool) (j : Nat)
    (hj : j < if isTail then 15 else 16)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex isTail j))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ParentCallValid state isTail j) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (parentQuery state isTail j))
          let result ← execute (submission.image .commit) fuel
            (parentCallState state isTail j answer) true
          return result.charge 10 1) := by
  have hj16 : j < 16 := by cases isTail <;> simp at hj <;> omega
  have hidxBound : parentCallIndex isTail j + 2 < 811 := by
    unfold parentCallIndex; cases isTail <;> simp at hj ⊢ <;> omega
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining
              (parentCallPrefix state isTail j 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := parentCallPrefix state isTail j)
    intro i hi
    refine ⟨.base (((parentCallInstructions isTail j)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (parentCallIndex isTail j + i) _ (by omega)
      · interval_cases i
        · simpa [parentCallPrefix] using pc
        · simp only [parentCallPrefix, parentCallInstructions, List.take, List.foldl, execInstrBr,
            MachineState.pc_setReg, MachineState.setPC, pc]
          exact pc_add_steps _ 1 _ (by omega)
      · have hcode := commit_instr_parent_setup isTail j i hj hi
        unfold parentCallIndex
        interval_cases i <;> simpa [parentCallInstructions] using hcode
    · interval_cases i <;> cases isTail <;> rfl
    · interval_cases i <;> cases isTail <;> rfl
  let ready := parentCallPrefix state isTail j 2
  have regs := parent_setup_registers state isTail j hj16
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (parentCallIndex isTail j + 2)) := by
    change (parentSetupState state isTail j).pc = _
    rw [regs.2.2.1, pc]
    exact pc_add_steps _ 2 _ (by omega)
  have fetched : fetch (submission.image .commit) ready = some (.base .ECALL) := by
    apply commit_fetch _ (parentCallIndex isTail j + 2) _ hidxBound readyPC
    exact commit_instr_parent_ecall isTail j hj
  have r5' : ready.getReg .x5 = 0 := (regs.2.2.2 .x5 (by decide) (by decide)).trans r5
  have r11' : ready.getReg .x11 = 96 := (regs.2.2.2 .x11 (by decide) (by decide)).trans r11
  have r13' : ready.getReg .x13 = 0 := (regs.2.2.2 .x13 (by decide) (by decide)).trans r13
  have r10' : ready.getReg .x10 = parentSource state isTail j := regs.1
  have r12' : ready.getReg .x12 = parentOutput state isTail j := regs.2.1
  have sv : rangeValid (ready.getReg .x10) 96 = true := by rw [r10']; exact valid.1
  have sa : (ready.getReg .x10).toNat % 8 = 0 := by rw [r10']; exact valid.2.1
  have dv : rangeValid (ready.getReg .x12) 32 = true := by rw [r12']; exact valid.2.2.1
  have da : (ready.getReg .x12).toNat % 8 = 0 := by rw [r12']; exact valid.2.2.2
  have memory : readBuffer ready (ready.getReg .x10).toNat 96 =
      readBuffer state (ready.getReg .x10).toNat 96 := by
    have sameMem : ready.mem = state.mem := parent_setup_memory state isTail j
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have input' : oracleInput ready = some (.inl (readBuffer state (ready.getReg .x10).toNat 96)) := by
    simp [oracleInput, r11', r13', sv, sa, dv, da, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, memory]
    try rw [r13']
    try simp [memory]
    try rfl
  have input : oracleInput ready = some (.inl
      (readBuffer state (parentSource state isTail j).toNat 96)) := by
    rw [input', r10']
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup, execute, fetched, if_pos r5', input]
  simp only [writeOracleAnswer, r12', bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state (parentSource state isTail j).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, parentCallState, parentSetupState,
    ← Nat.add_assoc]
  congr

/-- Run `remaining` consecutive parent calls starting at index `start`. -/
def parentCallsFrom (state : MachineState) (isTail : Bool) (start : Nat) :
    Nat → OracleComp World MachineState
  | 0 => pure state
  | remaining + 1 => do
      let answer ← World.query (.inr (parentQuery state isTail start))
      parentCallsFrom (parentCallState state isTail start answer) isTail (start + 1) remaining

theorem parent_calls_from_register (state finished : MachineState) (isTail : Bool)
    (start remaining : Nat)
    (reachable : finished ∈ support (parentCallsFrom state isTail start remaining))
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state start with
  | zero =>
    simp only [parentCallsFrom, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ remaining ih =>
    simp only [parentCallsFrom, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, rest⟩ := reachable
    exact (ih _ (start + 1) rest).trans
      (parent_call_register state isTail start answer reg n10 n12)

theorem parent_calls_from_pc (state finished : MachineState) (isTail : Bool)
    (start remaining : Nat) (hbound : start + remaining ≤ 16)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex isTail start))
    (reachable : finished ∈ support (parentCallsFrom state isTail start remaining)) :
    finished.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex isTail (start + remaining)) := by
  induction remaining generalizing state start with
  | zero =>
    simp only [parentCallsFrom, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simpa using pc
  | succ remaining ih =>
    simp only [parentCallsFrom, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, rest⟩ := reachable
    have nextPC : (parentCallState state isTail start answer).pc =
        BitVec.ofNat 64 (4096 + 4 * parentCallIndex isTail (start + 1)) := by
      rw [parent_call_pc state isTail start (by omega) answer, pc]
      unfold parentCallIndex
      cases isTail <;> exact pc_add_steps _ 3 _ (by omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih _ (start + 1) (by omega) nextPC rest

section
attribute [local irreducible] execute

theorem commit_parent_calls_from (state : MachineState) (isTail : Bool)
    (start remaining : Nat) (hbound : start + remaining ≤ if isTail then 15 else 16)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex isTail start))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ∀ k, start ≤ k → k < start + remaining → ParentCallValid state isTail k)
    (fuel : Nat) :
    execute (submission.image .commit) (3 * remaining + fuel) state true =
      (do let finished ← parentCallsFrom state isTail start remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (10 * remaining) remaining) := by
  induction remaining generalizing state start with
  | zero => simp [parentCallsFrom, Execution.charge]
  | succ remaining ih =>
    have hstart : start < if isTail then 15 else 16 := by
      cases isTail <;> simp at hbound ⊢ <;> omega
    have hstart16 : start < 16 := by cases isTail <;> simp at hstart <;> omega
    have hboundNext : start + 1 + remaining ≤ if isTail then 15 else 16 := by
      cases isTail <;> simp at hbound ⊢ <;> omega
    rw [show 3 * (remaining + 1) + fuel = 3 + (3 * remaining + fuel) by omega,
      commit_parent_call state isTail start hstart pc r5 r11 r13 (valid start (by omega) (by omega))]
    simp only [parentCallsFrom, bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro answer _
    change BitVec 256 at answer
    let s1 := parentCallState state isTail start answer
    have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
        s1.getReg reg = state.getReg reg :=
      parent_call_register state isTail start answer reg n10 n12
    have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex isTail (start + 1)) := by
      rw [parent_call_pc state isTail start hstart16 answer, pc]
      unfold parentCallIndex
      cases isTail <;> exact pc_add_steps _ 3 _ (by omega)
    rw [ih s1 (start + 1) hboundNext s1pc
      ((keep .x5 (by decide) (by decide)).trans r5)
      ((keep .x11 (by decide) (by decide)).trans r11)
      ((keep .x13 (by decide) (by decide)).trans r13)
      (fun k hk1 hk2 => parent_call_valid_congr s1 state isTail k
        (keep .x9 (by decide) (by decide)) (keep .x21 (by decide) (by decide))
        (keep .x22 (by decide) (by decide)) (valid k (by omega) (by omega)))]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply bind_congr_of_forall_mem_support
    intro result _
    simp only [Execution.charge, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Move both pointers down by 16 parents (8 pairs); loop while parents remain, else go to
the 15-node straight-line tail. -/
def parentNextState (state : MachineState) : MachineState :=
  ((state.setReg .x21 (state.getReg .x21 - 1536)).setReg .x22 (state.getReg .x22 - 768)).setPC
    (if state.getReg .x22 - 768 = state.getReg .x9 then 7116 else 6912)

private def parentNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentNextInstructions.take count).foldl execInstrBr state

theorem commit_parent_next (state : MachineState) (pc : state.pc = 7104) (fuel : Nat) :
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
    · apply commit_fetch _ (752 + i) _ (by omega)
      · interval_cases i <;>
          simp [parentNextPrefix, parentNextInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentNextPrefix state 2) =
      some (.base (.BNE .x22 .x9 7992)) := by
    apply commit_fetch _ 754 _ (by decide)
    · simp [parentNextPrefix, parentNextInstructions, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (parentNextPrefix state 2) (.base (.BNE .x22 .x9 7992)) =
      some (parentNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      parentNextPrefix, parentNextInstructions, parentNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc, BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- One loop iteration: 16 descending parent calls, then advance pointers. -/
def parentIterationRun (state : MachineState) : OracleComp World MachineState := do
  let hashed ← parentCallsFrom state false 0 16
  return parentNextState hashed

/-- The 15-node straight-line tail from node 15 down to root node 1. -/
def parentTailRun (state : MachineState) : OracleComp World MachineState :=
  parentCallsFrom state true 0 15

theorem parent_iteration_support (state finished : MachineState)
    (reachable : finished ∈ support (parentIterationRun state)) :
    ∃ hashed, hashed ∈ support (parentCallsFrom state false 0 16) ∧
      finished = parentNextState hashed := by
  simp only [parentIterationRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨hashed, hh, rfl⟩ := reachable
  exact ⟨hashed, hh, rfl⟩

/-- One 16-parent loop iteration: 51 instructions, 163 cycles, and 16 queries. -/
theorem commit_parent_iteration (state : MachineState) (pc : state.pc = 6912)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ∀ k < 16, ParentCallValid state false k) (fuel : Nat) :
    execute (submission.image .commit) (51 + fuel) state true =
      (do let finished ← parentIterationRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 163 16) := by
  rw [show 51 + fuel = 3 * 16 + (3 + fuel) by omega,
    commit_parent_calls_from state false 0 16 (by decide) (by rw [pc]; rfl) r5 r11 r13
      (fun k _ hk => valid k (by omega))]
  simp only [parentIterationRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have hashedPC : hashed.pc = 7104 := by
    have h := parent_calls_from_pc state hashed false 0 16 (by decide) (by rw [pc]; rfl) reached
    simpa [parentCallIndex] using h
  rw [commit_parent_next hashed hashedPC]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro result _
  simp only [Execution.charge, ← Nat.add_assoc]

/-- The 15-node root tail: 45 instructions, 150 cycles, and 15 queries. -/
theorem commit_parent_tail (state : MachineState) (pc : state.pc = 7116)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ∀ k < 15, ParentCallValid state true k) (fuel : Nat) :
    execute (submission.image .commit) (45 + fuel) state true =
      (do let finished ← parentTailRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 150 15) := by
  simpa [parentTailRun] using
    commit_parent_calls_from state true 0 15 (by decide) (by rw [pc]; rfl) r5 r11 r13
      (fun k _ hk => valid k (by omega)) fuel

private def parentStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentStartInstructions.take count).foldl execInstrBr state

/-- Pointer initialization before the parent loop (instructions 687-703):
`x21 = x9 + 96n - 1536` and `x22 = x9 + 48n - 768`, then branch to the loop. -/
def commitParentsStartState (state : MachineState) : MachineState :=
  execInstrBr (parentStartPrefix state 16) (.BEQ .x22 .x9 208)

set_option maxRecDepth 20000 in
private theorem parent_start_prefix_pc (state : MachineState) (pc : state.pc = 6844) :
    (parentStartPrefix state 16).pc = 6908 := by
  simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem commit_parents_start (state : MachineState) (pc : state.pc = 6844) (fuel : Nat) :
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
    · apply commit_fetch _ (687 + i) _ (by omega)
      · interval_cases i <;>
          simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentStartPrefix state 16) =
      some (.base (.BEQ .x22 .x9 208)) := by
    apply commit_fetch _ 703 _ (by decide)
    · rw [parent_start_prefix_pc state pc]; rfl
    · rfl
  have stepped : ordinaryStep (parentStartPrefix state 16) (.base (.BEQ .x22 .x9 208)) =
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
    (parentStartPrefix state 16).getReg .x21 = state.getReg .x9 + 1610611200 ∧
    (parentStartPrefix state 16).getReg .x22 = state.getReg .x9 + 805305600 := by
  dsimp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- The start leaves memory and all other registers alone, sets both pointers, and
always enters the loop (the pointer offset is nonzero). -/
theorem commit_parents_start_state (state : MachineState) (pc : state.pc = 6844) :
    (commitParentsStartState state).getReg .x21 = state.getReg .x9 + 1610611200 ∧
    (commitParentsStartState state).getReg .x22 = state.getReg .x9 + 805305600 ∧
    (commitParentsStartState state).pc = 6912 ∧
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

end

def commitExitState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 7336

theorem commit_exit (state : MachineState) (pc : state.pc = 7328) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 7332
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply commit_fetch _ 808 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply commit_fetch _ 809 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply commit_fetch _ 810 _ (by decide) rfl; rfl
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
