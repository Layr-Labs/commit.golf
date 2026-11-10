import CommitGolfCandidate.CapOpenRecordPrepare

/-! Actual instructions between the salt copy and lower-path entry. The output
cursor advances by one salt digest, the index becomes the full heap leaf index,
and the fixed seventeen-step path counter makes the zero-path branch fall
through. This does not identify the salt contents with a commitment yet. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenRecordTailInstructions : List Instr :=
  [.ADDI .x25 .x25 32, .ADD .x20 .x20 .x19,
   .ADDI .x28 .x0 0, .SLLI .x28 .x28 11, .ADDI .x28 .x28 17,
   .BEQ .x28 .x0 64]

def capOpenRecordTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenRecordTailInstructions.take count).foldl execInstrBr state

private theorem fold_take_next {A S : Type} (step : S → A → S)
    (code : List A) (state : S) (fallback : A) (i : Nat) (hi : i < code.length) :
    (code.take (i+1)).foldl step state =
      step ((code.take i).foldl step state) ((code[i]?).getD fallback) := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos code i hi, Option.getD_some]

theorem cap_open_record_tail_succ (state : MachineState) (count : Nat)
    (bounded : count < 6) :
    capOpenRecordTailPrefix state (count+1) =
      execInstrBr (capOpenRecordTailPrefix state count)
        ((capOpenRecordTailInstructions[count]?).getD .EBREAK) := by
  exact fold_take_next execInstrBr capOpenRecordTailInstructions state .EBREAK count
    (by simpa only [capOpenRecordTailInstructions, List.length_cons, List.length_nil]
      using bounded)

theorem cap_open_record_tail_counter (state : MachineState) :
    (capOpenRecordTailPrefix state 5).getReg .x28 = 17 := by
  simp (disch := decide) only [capOpenRecordTailPrefix, capOpenRecordTailInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rfl

theorem cap_open_record_tail_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 6) :
    (capOpenRecordTailPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  by_cases final : count = 6
  · subst count
    rw [cap_open_record_tail_succ state 5 (by decide)]
    change (execInstrBr (capOpenRecordTailPrefix state 5) (.BEQ .x28 .x0 64)).pc = _
    simp only [execInstrBr, cap_open_record_tail_counter,
      show (capOpenRecordTailPrefix state 5).getReg .x0 = 0 from rfl,
      show ((17 : Word) == (0 : Word)) = false by decide, Bool.false_eq_true, ite_false,
      MachineState.setPC]
    simp only [capOpenRecordTailPrefix, capOpenRecordTailInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
    rfl
  · have small : count ≤ 5 := by omega
    interval_cases count <;>
      simp only [capOpenRecordTailPrefix, capOpenRecordTailInstructions,
        List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
    · simp
    all_goals rfl

theorem cap_open_record_tail_execute (state : MachineState) (pc : state.pc = 4256)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (6+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordTailPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := capOpenRecordTailPrefix state)
  intro i bounded
  refine ⟨.base ((capOpenRecordTailInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (40+i) _ (by omega)
    · rw [cap_open_record_tail_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [cap_open_record_tail_succ state i bounded]
    interval_cases i <;>
      simp only [capOpenRecordTailInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, ↓reduceIte]
  · interval_cases i <;> rfl

end CommitGolfCandidate
