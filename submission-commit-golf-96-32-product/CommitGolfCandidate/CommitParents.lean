import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! 32-parent unrolled loop and 31-parent tail on the gap heap, plus parent setup and HALT.
Every parent call compresses `[x21 + 96*u - 1536, +96)` into `x22 + heapOffset u`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ### Exact 32-offset decode and sign-extension helpers -/

theorem signExtend12_parentSrc (u : Fin 32) :
    BitVec.ofNat 64 1536 + signExtend12 (BitVec.ofNat 12 (imm ((96 * u.val : Int) - 1536) 12)) =
      BitVec.ofNat 64 (96 * u.val) := by
  fin_cases u <;> rfl

private theorem decode_parent_src (u : Nat) (hu : u < 32) :
    decodeInstruction (BitVec.ofNat 32 (imm ((96 * u : Int) - 1536) 12 * 2^20 + 21 * 2^15 + 10 * 2^7 + 0x13)) =
      some (.base (.ADDI .x10 .x21 (BitVec.ofNat 12 (imm ((96 * u : Int) - 1536) 12)))) := by
  interval_cases u <;> rfl

private theorem decode_parent_dst (u : Nat) (hu : u < 32) :
    decodeInstruction (BitVec.ofNat 32 (imm (heapOffset u) 12 * 2^20 + 22 * 2^15 + 12 * 2^7 + 0x13)) =
      some (.base (.ADDI .x12 .x22 (BitVec.ofNat 12 (heapOffset u)))) := by
  interval_cases u <;> rfl

def parentLaneInstr (u : Nat) : Nat → Instr
  | 0 => .ADDI .x10 .x21 (BitVec.ofNat 12 (imm ((96 * u : Int) - 1536) 12))
  | 1 => .ADDI .x12 .x22 (BitVec.ofNat 12 (heapOffset u))
  | _ => .ECALL

theorem commit_parent_decode (isTail : Bool) (j m : Nat)
    (hj : j < if isTail then 31 else 32) (hm : m < 3) :
    ((submission.image .commit).code[(if isTail then 692 else 593) + 3 * j + m]?).bind decodeInstruction =
      some (.base (parentLaneInstr (31 - j) m)) := by
  cases isTail
  · simp only [Bool.false_eq_true, ↓reduceIte] at hj ⊢
    have hfilt := commit_filtered_parentLoop j m hj hm
    interval_cases m
    · simp only [parentChunk, addi, insn, List.getElem?_cons_zero] at hfilt
      rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_parent_src (31 - j) (by omega)]; rfl
    · simp only [parentChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
      rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_parent_dst (31 - j) (by omega)]; rfl
    · simp only [parentChunk, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
      rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ecall_word]; rfl
  · simp only [↓reduceIte] at hj ⊢
    have hfilt := commit_filtered_parentTail j m hj hm
    interval_cases m
    · simp only [parentChunk, addi, insn, List.getElem?_cons_zero] at hfilt
      rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_parent_src (31 - j) (by omega)]; rfl
    · simp only [parentChunk, addi, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
      rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_parent_dst (31 - j) (by omega)]; rfl
    · simp only [parentChunk, insn, List.getElem?_cons_zero, List.getElem?_cons_succ] at hfilt
      rw [commit_code_word_at _ _ hfilt, Option.bind_some, decode_ecall_word]; rfl

/-! ### Single parent call state transition -/

/-- Source address of parent offset `u < 32`. -/
def parentSource (state : MachineState) (u : Nat) : Word :=
  state.getReg .x21 + signExtend12 (BitVec.ofNat 12 (imm ((96 * u : Int) - 1536) 12))

/-- Output address of parent offset `u < 32`. -/
def parentOutput (state : MachineState) (u : Nat) : Word :=
  state.getReg .x22 + BitVec.ofNat 64 (heapOffset u)

abbrev parentQuery (state : MachineState) (u : Nat) : PublicSpec.Domain :=
  .inl (readBuffer state (parentSource state u).toNat 96)

def parentSetupState (state : MachineState) (u : Nat) : MachineState :=
  ((state.setReg .x10 (parentSource state u)).setReg .x12 (parentOutput state u)).setPC (state.pc + 8)

def parentCallState (state : MachineState) (u : Nat) (answer : BitVec 256) : MachineState :=
  writeBits (parentSetupState state u) (parentOutput state u) answer

theorem parent_call_memory (state : MachineState) (u : Nat) (answer : BitVec 256) :
    (parentCallState state u answer).mem = (writeBits state (parentOutput state u) answer).mem :=
  write_bits_memory_congr _ _ _ answer rfl

theorem parent_call_register (state : MachineState) (u : Nat) (answer : BitVec 256)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentCallState state u answer).getReg reg = state.getReg reg := by
  rw [parentCallState, writeBits_register, parentSetupState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10)]

theorem parent_call_pc (state : MachineState) (u : Nat) (answer : BitVec 256) :
    (parentCallState state u answer).pc = state.pc + 12 := by
  simp only [parentCallState, parentSetupState, writeBits_pc, MachineState.setPC, BitVec.add_assoc]
  rfl

theorem parent_source_congr (left right : MachineState) (u : Nat)
    (r21 : left.getReg .x21 = right.getReg .x21) :
    parentSource left u = parentSource right u := by
  unfold parentSource; rw [r21]

theorem parent_output_congr (left right : MachineState) (u : Nat)
    (r22 : left.getReg .x22 = right.getReg .x22) :
    parentOutput left u = parentOutput right u := by
  unfold parentOutput; rw [r22]

def ParentCallValid (state : MachineState) (u : Nat) : Prop :=
  rangeValid (parentSource state u) 96 = true ∧ (parentSource state u).toNat % 8 = 0 ∧
    rangeValid (parentOutput state u) 32 = true ∧ (parentOutput state u).toNat % 8 = 0

/-- Execute one direct 3-instruction parent call (`j`-th call in loop or tail, `u = 31 - j`). -/
theorem commit_parent_call (state : MachineState) (isTail : Bool) (j : Nat)
    (hj : j < if isTail then 31 else 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * ((if isTail then 692 else 593) + 3 * j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ParentCallValid state (31 - j)) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (parentQuery state (31 - j)))
          let result ← execute (submission.image .commit) fuel (parentCallState state (31 - j) answer) true
          return result.charge 10 1) := by
  let baseIdx := if isTail then 692 else 593
  let u := 31 - j
  have hu : u < 32 := by cases isTail <;> simp at hj <;> omega
  have hbound : baseIdx + 3 * j + 2 < 796 := by
    cases isTail <;> simp [baseIdx] at hj ⊢ <;> omega
  let mid := (state.setReg .x10 (parentSource state u)).setPC (state.pc + 4)
  let ready := parentSetupState state u
  have midPC : mid.pc = BitVec.ofNat 64 (4096 + 4 * (baseIdx + 3 * j + 1)) := by
    change state.pc + 4 = _
    rw [pc]
    apply ofNat64_add_eq _ 4 _; omega
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (baseIdx + 3 * j + 2)) := by
    change state.pc + 8 = _
    rw [pc]
    apply ofNat64_add_eq _ 8 _; omega
  have f0 : fetch (submission.image .commit) state = some (.base (parentLaneInstr u 0)) :=
    commit_fetch state (baseIdx + 3 * j + 0) _ (by omega) pc
      (commit_parent_decode isTail j 0 hj (by decide))
  have f1 : fetch (submission.image .commit) mid = some (.base (parentLaneInstr u 1)) :=
    commit_fetch mid (baseIdx + 3 * j + 1) _ (by omega) midPC
      (commit_parent_decode isTail j 1 hj (by decide))
  have f2 : fetch (submission.image .commit) ready = some (.base .ECALL) :=
    commit_fetch ready (baseIdx + 3 * j + 2) .ECALL (by omega) readyPC
      (commit_parent_decode isTail j 2 hj (by decide))
  have s0 : ordinaryStep state (.base (parentLaneInstr u 0)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, parentLaneInstr,
      parentSource, mid]
  have s1 : ordinaryStep mid (.base (parentLaneInstr u 1)) = some ready := by
    have sheap := signExtend12_heapOffset ⟨u, hu⟩
    have h44 : (4 : Word) + 4 = 8 := by decide
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, parentLaneInstr,
      parentOutput, mid, ready, parentSetupState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, BitVec.add_assoc, sheap, h44]
  have rr5 : ready.getReg .x5 = 0 := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r5]
  have rr11 : ready.getReg .x11 = 96 := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r11]
  have rr13 : ready.getReg .x13 = 0 := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r13]
  have rr10 : ready.getReg .x10 = parentSource state u := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have rr12 : ready.getReg .x12 = parentOutput state u := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
  have sameMem : ready.mem = state.mem := rfl
  have rmem : readBuffer ready (parentSource state u).toNat 96 =
      readBuffer state (parentSource state u).toNat 96 := by
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have hinput : oracleInput ready = some (.inl (readBuffer state (parentSource state u).toNat 96)) := by
    have h := oracleInput_compression ready rr11 rr13
      (by rw [rr10]; exact valid.1) (by rw [rr10]; exact valid.2.1)
      (by rw [rr12]; exact valid.2.2.1) (by rw [rr12]; exact valid.2.2.2)
    rwa [rr10, rmem] at h
  rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0,
    execute_ordinary_step _ _ _ _ _ _ f1 s1,
    execute, f2, if_pos rr5, hinput]
  simp only [writeOracleAnswer, rr12, bind_assoc, pure_bind]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (parentQuery state u))) : OracleComp World (BitVec 256)) >>= k)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, instructionCycles, charge_charge]
  rfl

/-! ### Sequences of parent calls (32-parent block and 31-parent tail) -/

/-- Run `count` consecutive parent calls starting at index `start` (offsets `31 - start` down). -/
def parentCallsRun (state : MachineState) (start : Nat) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (parentQuery state (31 - start)))
      parentCallsRun (parentCallState state (31 - start) answer) (start + 1) count

theorem parent_calls_registers (state finished : MachineState) (start count : Nat)
    (reachable : finished ∈ support (parentCallsRun state start count)) :
    finished.pc = state.pc + BitVec.ofNat 64 (12 * count) ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → finished.getReg reg = state.getReg reg := by
  induction count generalizing state start with
  | zero =>
    simp only [parentCallsRun, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by simp, fun _ _ _ => rfl⟩
  | succ count ih =>
    simp only [parentCallsRun, mem_support_bind_iff] at reachable
    obtain ⟨a, _, hrest⟩ := reachable
    change BitVec 256 at a
    have r2 := ih _ (start + 1) hrest
    refine ⟨?_, ?_⟩
    · rw [r2.1, parent_call_pc, BitVec.add_assoc]
      change state.pc + (BitVec.ofNat 64 12 + BitVec.ofNat 64 (12 * count)) = _
      rw [← BitVec.ofNat_add]
      exact congrArg (fun n => state.pc + BitVec.ofNat 64 n) (by clear * -; omega)
    · intro reg n10 n12
      exact (r2.2 reg n10 n12).trans (parent_call_register state _ a reg n10 n12)

section
attribute [local irreducible] execute

theorem commit_parent_calls (state : MachineState) (isTail : Bool) (start count : Nat)
    (bounded : start + count ≤ if isTail then 31 else 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * ((if isTail then 692 else 593) + 3 * start)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ∀ j, start ≤ j → j < start + count → ParentCallValid state (31 - j))
    (fuel : Nat) :
    execute (submission.image .commit) (3 * count + fuel) state true =
      (do let finished ← parentCallsRun state start count
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (10 * count) count) := by
  induction count generalizing state start with
  | zero => simp [parentCallsRun, Execution.charge]
  | succ count ih =>
    have hj : start < if isTail then 31 else 32 := by clear * - bounded; omega
    have hstep := commit_parent_call state isTail start hj pc r5 r11 r13
      (valid start (by clear * -; omega) (by clear * -; omega)) (3 * count + fuel)
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by clear * -; omega, hstep]
    simp only [parentCallsRun, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro a _
    change BitVec 256 at a
    let s1 := parentCallState state (31 - start) a
    have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) : s1.getReg reg = state.getReg reg :=
      parent_call_register state (31 - start) a reg n10 n12
    have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * ((if isTail then 692 else 593) + 3 * (start + 1))) := by
      dsimp only [s1]
      rw [parent_call_pc, pc]
      apply ofNat64_add_eq _ 12 _; clear * -; omega
    have s1valid : ∀ j, start + 1 ≤ j → j < start + 1 + count → ParentCallValid s1 (31 - j) := by
      intro j hlo hhi
      have hsrc := parent_source_congr s1 state (31 - j) (keep .x21 (by decide) (by decide))
      have hout := parent_output_congr s1 state (31 - j) (keep .x22 (by decide) (by decide))
      unfold ParentCallValid
      rw [hsrc, hout]
      exact valid j (by clear * - hlo; omega) (by clear * - hhi; omega)
    rw [ih s1 (start + 1) (by clear * - bounded; omega) s1pc
      ((keep .x5 (by decide) (by decide)).trans r5)
      ((keep .x11 (by decide) (by decide)).trans r11)
      ((keep .x13 (by decide) (by decide)).trans r13) s1valid]
    simp only [bind_assoc, pure_bind, charge_charge,
      show 10 + 10 * count = 10 * (count + 1) by clear * -; omega,
      show 1 + count = count + 1 by clear * -; omega]
    rfl

end

/-! ### Parent loop latch (indices 689..691) and one 32-parent iteration -/

/-- Decrement `x21 -= x24` (3072) and `x22 -= 1536`; loop to `6468` while `x22 ≠ x9`, else `6864`. -/
def parentNextState (state : MachineState) : MachineState :=
  ((state.setReg .x21 (state.getReg .x21 - state.getReg .x24)).setReg
    .x22 (state.getReg .x22 - 1536)).setPC
    (if state.getReg .x22 - 1536 = state.getReg .x9 then 6864 else 6468)

private def parentNextInstructions : List Instr :=
  [.SUB .x21 .x21 .x24, .ADDI .x22 .x22 2560]

private def parentNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentNextInstructions.take count).foldl execInstrBr state

theorem commit_parent_next (state : MachineState) (pc : state.pc = 6852) (fuel : Nat) :
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
    · apply commit_fetch _ (689 + i) _ (by omega)
      · interval_cases i <;> simp [parentNextPrefix, parentNextInstructions, execInstrBr, pc, MachineState.setPC]
      · have hf := commit_filtered_parentLatch i (by omega)
        interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentNextPrefix state 2) =
      some (.base (.BNE .x22 .x9 7800)) := by
    apply commit_fetch _ 691 _ (by decide)
    · simp [parentNextPrefix, parentNextInstructions, execInstrBr, pc, MachineState.setPC]
    · have hb := commit_code_branch_at 691 1 22 9 "commit-parent" 593
        (commit_filtered_parentLatch 2 (by decide)) (by rw [commit_labelPositions]; rfl)
      rw [hb]; rfl
  have stepped : ordinaryStep (parentNextPrefix state 2) (.base (.BNE .x22 .x9 7800)) =
      some (parentNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      parentNextPrefix, parentNextInstructions, parentNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc, BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, charge_charge]

/-- One 32-parent loop iteration: 32 descending parent calls, then advance. -/
def parentIterationRun (state : MachineState) : OracleComp World MachineState := do
  let done ← parentCallsRun state 0 32
  return parentNextState done

/-- One 32-parent iteration: 99 instructions, 323 cycles, 32 queries. -/
theorem commit_parent_iteration (state : MachineState) (pc : state.pc = 6468)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ∀ u < 32, ParentCallValid state u) (fuel : Nat) :
    execute (submission.image .commit) (99 + fuel) state true =
      (do let finished ← parentIterationRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 323 32) := by
  have hpc : state.pc = BitVec.ofNat 64 (4096 + 4 * (593 + 3 * 0)) := by rw [pc]; rfl
  have hcalls := commit_parent_calls state false 0 32 (by decide) hpc r5 r11 r13
    (fun j _ hj => valid (31 - j) (by omega)) (3 + fuel)
  rw [show 99 + fuel = 3 * 32 + (3 + fuel) by omega, hcalls]
  simp only [parentIterationRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro done hdone
  have hregs := parent_calls_registers state done 0 32 hdone
  have latchPC : done.pc = 6852 := by rw [hregs.1, pc]; rfl
  rw [commit_parent_next done latchPC]
  simp [charge_charge]

/-! ### Parent setup (indices 581..592) and exit (indices 793..795) -/

private def parentStartInstructions : List Instr :=
  [.ADDI .x21 .x23 2560, .ADDI .x24 .x0 1536, .ADDI .x24 .x24 1536,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 191, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 2047, .SLLI .x6 .x6 11, .ADDI .x6 .x6 512, .ADD .x22 .x9 .x6]

private def parentStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentStartInstructions.take count).foldl execInstrBr state

/-- Pointer initialization before the parent loop (indices 581..592):
`x21 := x23 - 1536`, `x24 := 3072`, `x22 := x9 + 48*n - 1536`, then `BEQ x22 x9 400`. -/
def commitParentsStartState (state : MachineState) : MachineState :=
  execInstrBr (parentStartPrefix state 11) (.BEQ .x22 .x9 400)

set_option maxRecDepth 20000 in
private theorem parent_start_prefix_pc (state : MachineState) (pc : state.pc = 6420) :
    (parentStartPrefix state 11).pc = 6464 := by
  simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem commit_parents_start (state : MachineState) (pc : state.pc = 6420) (fuel : Nat) :
    execute (submission.image .commit) (12 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 12 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (11 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentStartPrefix state 11) true
            return result.charge 11 0) := by
    apply execute_unit_steps (states := parentStartPrefix state)
    intro i hi
    refine ⟨.base ((parentStartInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (581 + i) _ (by omega)
      · interval_cases i <;>
          simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]
      · have hf := commit_filtered_parentSetup i (by omega)
        interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentStartPrefix state 11) =
      some (.base (.BEQ .x22 .x9 400)) := by
    apply commit_fetch _ 592 _ (by decide)
    · rw [parent_start_prefix_pc state pc]; rfl
    · have hb := commit_code_branch_at 592 0 22 9 "commit-tail" 692
        (commit_filtered_parentSetup 11 (by decide)) (by rw [commit_labelPositions]; rfl)
      rw [hb]; rfl
  have stepped : ordinaryStep (parentStartPrefix state 11) (.base (.BEQ .x22 .x9 400)) =
      some (commitParentsStartState state) := rfl
  rw [show 12 + fuel = 11 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, charge_charge]

private theorem parent_start_prefix_memory (state : MachineState) :
    (parentStartPrefix state 11).mem = state.mem := rfl

private theorem parent_start_prefix_register (state : MachineState) (reg : Reg)
    (n6 : reg ≠ .x6) (n21 : reg ≠ .x21) (n22 : reg ≠ .x22) (n24 : reg ≠ .x24) :
    (parentStartPrefix state 11).getReg reg = state.getReg reg := by
  simp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n6),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n22),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n24)]

set_option maxRecDepth 20000 in
private theorem parent_start_prefix_pointers (state : MachineState) :
    (parentStartPrefix state 11).getReg .x21 = state.getReg .x23 + 18446744073709550080 ∧
    (parentStartPrefix state 11).getReg .x24 = 3072 ∧
    (parentStartPrefix state 11).getReg .x22 = state.getReg .x9 + 805304832 := by
  dsimp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- Parent setup sets `x21 := x23 - 1536`, `x24 := 3072`, `x22 := x9 + 805304832`,
leaves memory untouched, and enters the parent loop at `pc = 6468`. -/
theorem commit_parents_start_state (state : MachineState) (pc : state.pc = 6420) :
    (commitParentsStartState state).getReg .x21 = state.getReg .x23 - 1536 ∧
    (commitParentsStartState state).getReg .x24 = 3072 ∧
    (commitParentsStartState state).getReg .x22 = state.getReg .x9 + 805304832 ∧
    (commitParentsStartState state).pc = 6468 ∧
    (commitParentsStartState state).mem = state.mem ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x21 → reg ≠ .x22 → reg ≠ .x24 →
      (commitParentsStartState state).getReg reg = state.getReg reg := by
  have pointers := parent_start_prefix_pointers state
  have x9 := parent_start_prefix_register state .x9 (by decide) (by decide) (by decide) (by decide)
  have different : (parentStartPrefix state 11).getReg .x22 ≠ (parentStartPrefix state 11).getReg .x9 := by
    rw [pointers.2.2, x9]
    intro same
    have zero := BitVec.add_right_eq_self.mp same
    exact absurd zero (by decide)
  have branch : commitParentsStartState state =
      (parentStartPrefix state 11).setPC ((parentStartPrefix state 11).pc + 4) := by
    unfold commitParentsStartState
    simp only [execInstrBr]
    rw [ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) different)]
  rw [branch]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hneg : -(1536 : Word) = 18446744073709550080 := by decide
    rw [MachineState.getReg_setPC, pointers.1, BitVec.sub_eq_add_neg, hneg]
  · rw [MachineState.getReg_setPC]; exact pointers.2.1
  · rw [MachineState.getReg_setPC]; exact pointers.2.2
  · simp only [MachineState.setPC]; rw [parent_start_prefix_pc state pc]; rfl
  · exact parent_start_prefix_memory state
  · intro reg n6 n21 n22 n24
    rw [MachineState.getReg_setPC]
    exact parent_start_prefix_register state reg n6 n21 n22 n24

def commitExitState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 7276

theorem commit_exit (state : MachineState) (pc : state.pc = 7268) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 7272
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply commit_fetch _ 793 _ (by decide) pc
    rw [commit_code_word_at _ _ (commit_filtered_epilogue 8 (by decide))]; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply commit_fetch _ 794 _ (by decide) rfl
    rw [commit_code_word_at _ _ (commit_filtered_epilogue 9 (by decide))]; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply commit_fetch _ 795 _ (by decide) rfl
    rw [commit_code_word_at _ _ (commit_filtered_epilogue 10 (by decide))]; rfl
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
