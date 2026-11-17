import CommitGolfCandidate.CapCheckConstants

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckConstantsPrefix

theorem cap_check_constants_register (state : MachineState) (count : Nat)
    (reg : Reg) (outside : reg ∉ [Reg.x21, .x9, .x18, .x19, .x31]) :
    (capCheckConstantsPrefix state count).getReg reg = state.getReg reg := by
  have step : ∀ instruction ∈ capCheckConstantsInstructions,
      ∀ current : MachineState,
        (execInstrBr current instruction).getReg reg = current.getReg reg := by
    intro instruction member current
    simp only [capCheckConstantsInstructions, List.mem_cons, List.not_mem_nil,
      or_false] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [execInstrBr, MachineState.getReg_setPC]
      apply MachineState.getReg_setReg_ne
      intro equal
      subst reg
      tauto
  have fold : ∀ instructions : List Instr,
      (∀ instruction ∈ instructions, ∀ current : MachineState,
        (execInstrBr current instruction).getReg reg = current.getReg reg) →
      ∀ current : MachineState,
        (instructions.foldl execInstrBr current).getReg reg = current.getReg reg := by
    intro instructions
    induction instructions with
    | nil => intro _ current; rfl
    | cons instruction rest ih =>
      intro preserved current
      rw [List.foldl_cons, ih (fun i member => preserved i (List.mem_cons_of_mem _ member)),
        preserved instruction List.mem_cons_self]
  unfold capCheckConstantsPrefix
  exact fold _ (fun instruction member => step instruction (List.mem_of_mem_take member)) state

theorem cap_check_constants_finished_pc (state : MachineState)
    (pc : state.pc = 4144) :
    (capCheckConstantsPrefix state 17).pc = 4212 := by
  rw [cap_check_constants_pc state 17 (by decide), pc]
  rfl

end CommitGolfCandidate
