import CommitGolfCandidate.ChainedCursor

/-! Abstract-state BNE execution and PCs at each delivered parent back edge. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
attribute [local irreducible] execute

def branchState (s : MachineState) : MachineState := execInstrBr s (.BNE .x7 .x15 8140)

theorem branch_execution (image : Image) (s : MachineState) (fuel : Nat) (coins : Bool)
    (fetched : fetch image s = some (.base (.BNE .x7 .x15 8140))) :
    execute image (fuel+1) s coins =
      (do let result ← execute image fuel (branchState s) coins
          return result.charge 1 0) := by
  exact execute_ordinary_step image _ _ _ fuel coins fetched rfl

theorem parent_branch_execution (s : MachineState) (h : Height) (pc : s.pc = branchPC h)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (fuel+1) s coins =
      (do let result ← execute chainedCommitImage fuel (branchState s) coins
          return result.charge 1 0) := by
  apply branch_execution
  have opEq : chainedParentOp (23+20*h.val) = .BNE .x7 .x15 8140 := by fin_cases h <;> rfl
  simpa only [opEq] using chained_parent_at ⟨23+20*h.val,by have := h.isLt; omega⟩ s pc

theorem branch_pc_formula (s : MachineState) : (branchState s).pc =
    if s.getReg .x7 != s.getReg .x15 then s.pc+signExtend13 8140 else s.pc+4 := by
  change (if s.getReg .x7 != s.getReg .x15 then s.setPC (s.pc+signExtend13 8140)
    else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem branch_register (s : MachineState) (reg : Reg) : (branchState s).getReg reg = s.getReg reg := by
  by_cases taken : s.getReg .x7 != s.getReg .x15
  · have step : branchState s = s.setPC (s.pc+signExtend13 8140) := by exact ite_eq_left taken
    exact (congrArg (fun st : MachineState => st.getReg reg) step).trans MachineState.getReg_setPC
  · have step : branchState s = s.setPC (s.pc+4) := by exact ite_eq_right taken
    exact (congrArg (fun st : MachineState => st.getReg reg) step).trans MachineState.getReg_setPC

theorem branch_memory (s : MachineState) (query : Word) : (branchState s).getMem query = s.getMem query := by
  by_cases taken : s.getReg .x7 != s.getReg .x15
  · have step : branchState s = s.setPC (s.pc+signExtend13 8140) := by exact ite_eq_left taken
    exact (congrArg (fun st : MachineState => st.getMem query) step).trans MachineState.getMem_setPC
  · have step : branchState s = s.setPC (s.pc+4) := by exact ite_eq_right taken
    exact (congrArg (fun st : MachineState => st.getMem query) step).trans MachineState.getMem_setPC

theorem parent_branch_pc (s : MachineState) (h : Height) (pc : s.pc = branchPC h) :
    (branchState s).pc = if s.getReg .x7 != s.getReg .x15 then bodyPC h else shiftPC h := by
  have back : branchPC h+signExtend13 8140 = bodyPC h := by fin_cases h <;> decide
  have exit : branchPC h+4 = shiftPC h := by fin_cases h <;> rfl
  rw [branch_pc_formula,pc,back,exit]

end CommitGolfCandidate.Chained.Native
