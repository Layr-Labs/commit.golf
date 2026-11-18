import CommitGolfCandidate.CapOpenRecordPrepare
import CommitGolfCandidate.S6OpenStub

/-! Actual instructions between the salt-field block and lower-path entry. The
output cursor advances past the salt field, the group stub (called with link
4264) copies the three other leaf digests of the group and leaves the group's
heap node in x20, and the fixed fourteen-step path counter makes the zero-path
branch fall through. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenRecordCallInstructions : List Instr :=
  [.ADDI .x25 .x25 32, .JAL .x1 388]

def capOpenRecordCallState (state : MachineState) : MachineState :=
  capOpenRecordCallInstructions.foldl execInstrBr state

def capOpenRecordLatchInstructions : List Instr :=
  [.ADDI .x28 .x0 0, .SLLI .x28 .x28 11, .ADDI .x28 .x28 14, .BEQ .x28 .x0 64]

def capOpenRecordLatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenRecordLatchInstructions.take count).foldl execInstrBr state

/-- The whole tail: call, stub, latch. -/
def capOpenRecordTailState (state : MachineState) : MachineState :=
  capOpenRecordLatchPrefix (capOpenStubState (capOpenRecordCallState state)) 4

private theorem fold_take_next {A S : Type} (step : S → A → S)
    (code : List A) (state : S) (fallback : A) (i : Nat) (hi : i < code.length) :
    (code.take (i+1)).foldl step state =
      step ((code.take i).foldl step state) ((code[i]?).getD fallback) := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos code i hi, Option.getD_some]

theorem cap_open_record_latch_succ (state : MachineState) (count : Nat)
    (bounded : count < 4) :
    capOpenRecordLatchPrefix state (count+1) =
      execInstrBr (capOpenRecordLatchPrefix state count)
        ((capOpenRecordLatchInstructions[count]?).getD .EBREAK) :=
  fold_take_next execInstrBr capOpenRecordLatchInstructions state .EBREAK count
    (by simpa only [capOpenRecordLatchInstructions, List.length_cons, List.length_nil] using bounded)

theorem cap_open_record_latch_counter (state : MachineState) :
    (capOpenRecordLatchPrefix state 3).getReg .x28 = 14 := by
  simp (disch := decide) only [capOpenRecordLatchPrefix, capOpenRecordLatchInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rfl

theorem cap_open_record_latch_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 4) :
    (capOpenRecordLatchPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  by_cases final : count = 4
  · subst count
    rw [cap_open_record_latch_succ state 3 (by decide)]
    change (execInstrBr (capOpenRecordLatchPrefix state 3) (.BEQ .x28 .x0 64)).pc = _
    simp only [execInstrBr, cap_open_record_latch_counter,
      show (capOpenRecordLatchPrefix state 3).getReg .x0 = 0 from rfl,
      show ((14 : Word) == (0 : Word)) = false by decide, Bool.false_eq_true, ite_false,
      MachineState.setPC]
    simp only [capOpenRecordLatchPrefix, capOpenRecordLatchInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
    rfl
  · have small : count ≤ 3 := by omega
    interval_cases count <;>
      simp only [capOpenRecordLatchPrefix, capOpenRecordLatchInstructions,
        List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
    · simp
    all_goals rfl

theorem cap_open_record_latch_execute (state : MachineState) (pc : state.pc = 4264)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (4+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordLatchPrefix state 4) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := capOpenRecordLatchPrefix state)
  intro i bounded
  refine ⟨.base ((capOpenRecordLatchInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (42+i) _ (by omega)
    · rw [cap_open_record_latch_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [cap_open_record_latch_succ state i bounded]
    interval_cases i <;>
      simp only [capOpenRecordLatchInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, ↓reduceIte]
  · interval_cases i <;> rfl

private theorem latch_branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

private theorem latch_branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem cap_open_record_latch_memory (state : MachineState) :
    (capOpenRecordLatchPrefix state 4).mem = state.mem := by
  rw [cap_open_record_latch_succ state 3 (by decide)]
  change (execInstrBr (capOpenRecordLatchPrefix state 3) (.BEQ .x28 .x0 64)).mem = _
  rw [latch_branch_memory]
  rfl

theorem cap_open_record_latch_register (state : MachineState) (reg : Reg) (outside : reg ≠ .x28) :
    (capOpenRecordLatchPrefix state 4).getReg reg = state.getReg reg := by
  rw [cap_open_record_latch_succ state 3 (by decide)]
  change (execInstrBr (capOpenRecordLatchPrefix state 3) (.BEQ .x28 .x0 64)).getReg reg = _
  rw [latch_branch_register]
  simp only [capOpenRecordLatchPrefix, capOpenRecordLatchInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_open_record_latch_count (state : MachineState) :
    (capOpenRecordLatchPrefix state 4).getReg .x28 = 14 := by
  rw [cap_open_record_latch_succ state 3 (by decide)]
  change (execInstrBr (capOpenRecordLatchPrefix state 3) (.BEQ .x28 .x0 64)).getReg .x28 = _
  rw [latch_branch_register]
  exact cap_open_record_latch_counter state

/-! ### Call -/

theorem cap_open_record_call_facts (state : MachineState) (pc : state.pc = 4256) :
    (capOpenRecordCallState state).pc = 4648 ∧
    (capOpenRecordCallState state).getReg .x1 = 4264 ∧
    (capOpenRecordCallState state).getReg .x25 = state.getReg .x25 + 32 ∧
    (capOpenRecordCallState state).mem = state.mem ∧
    ∀ reg, reg ≠ .x1 → reg ≠ .x25 → (capOpenRecordCallState state).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp only [capOpenRecordCallState, capOpenRecordCallInstructions, List.foldl, execInstrBr,
      MachineState.setPC, MachineState.setReg, pc]
    rfl
  · simp (disch := decide) only [capOpenRecordCallState, capOpenRecordCallInstructions, List.foldl,
      execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, pc]
    rfl
  · simp (disch := decide) only [capOpenRecordCallState, capOpenRecordCallInstructions, List.foldl,
      execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    rfl
  · intro reg a b
    simp only [capOpenRecordCallState, capOpenRecordCallInstructions, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]

theorem cap_open_record_call_execute (state : MachineState) (pc : state.pc = 4256)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (2+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordCallState state) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := fun i => (capOpenRecordCallInstructions.take i).foldl execInstrBr state)
  intro i bounded
  refine ⟨.base ((capOpenRecordCallInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (40+i) _ (by omega)
    · interval_cases i
      · simpa using pc
      · simp only [capOpenRecordCallInstructions, List.take, List.foldl, execInstrBr,
          MachineState.setPC, MachineState.setReg, pc]
        rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-! ### The whole tail -/

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

/-- From the salt-field exit (pc 4256) to the lower-path entry: 51 instructions, 54 cycles. -/
theorem cap_open_record_tail_execute (state : MachineState) (position rootBase cursor : Nat)
    (pc : state.pc = 4256) (index : state.getReg .x20 = BitVec.ofNat 64 position)
    (positionBound : position < 2^24) (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (groups : state.getReg .x19 = BitVec.ofNat 64 4194304)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (rootAligned : rootBase % 8 = 0) (cursorAligned : cursor % 8 = 0)
    (separate : rootBase + 2^31 ≤ cursor) (bound : cursor + 160 ≤ MEMORY_BYTES)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (51+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordTailState state) allowCoins
          return result.charge 54 0) := by
  have call := cap_open_record_call_facts state pc
  have stub := cap_open_stub_execute (capOpenRecordCallState state) position rootBase (cursor+32)
    call.1 ((call.2.2.2.2 .x20 (by decide) (by decide)).trans index) positionBound
    ((call.2.2.2.2 .x9 (by decide) (by decide)).trans roots)
    (by rw [call.2.2.1, pointer, show (32 : Word) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add])
    call.2.1 rootAligned (by omega) (by omega) (by omega)
  have memory : MEMORY_BYTES ≤ 2^64 := by simp only [MEMORY_BYTES]; omega
  have stubFacts := cap_open_stub_facts (capOpenRecordCallState state) position rootBase (cursor+32)
    call.2.1 ((call.2.2.2.2 .x20 (by decide) (by decide)).trans index) positionBound
    ((call.2.2.2.2 .x9 (by decide) (by decide)).trans roots)
    ((call.2.2.2.2 .x19 (by decide) (by decide)).trans groups)
    (by rw [call.2.2.1, pointer, show (32 : Word) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add])
    (by omega) (by omega)
  rw [show 51+fuel = 2+(45+(4+fuel)) by omega, cap_open_record_call_execute state pc, stub,
    cap_open_record_latch_execute _ stubFacts.1]
  simp only [capOpenRecordTailState, bind_assoc, pure_bind, charge_pair, Nat.reduceAdd]

end CommitGolfCandidate
