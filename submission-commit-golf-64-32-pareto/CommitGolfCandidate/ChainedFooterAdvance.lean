import CommitGolfCandidate.ChainedFooterInit

/-! Actual footer DFS return edges, factored before the sibling/parent jump. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem advance_set_zero (s : MachineState) (value : Word) : s.setReg .x0 value=s := rfl
@[local simp] private theorem advance_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem advance_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem advance_sign_one : signExtend12 1#12=1#64 := rfl

def footerDecisionOps : List Instr :=
  [.ADDI .x31 .x0 1,.BEQ .x30 .x31 28,.ANDI .x31 .x30 1,.BEQ .x31 .x0 12]
def footerParentOps : List Instr := [.SRLI .x30 .x30 1,.JAL .x0 2097132]
def footerSiblingOps : List Instr := [.ADDI .x30 .x30 1,.JAL .x0 2096592]
def footerAdvanceOps : List Instr := footerDecisionOps++(footerParentOps++footerSiblingOps)
def footerDecisionPrefix (s : MachineState) (count : Nat) : MachineState := (footerDecisionOps.take count).foldl execInstrBr s
def footerParentPrefix (s : MachineState) (count : Nat) : MachineState := (footerParentOps.take count).foldl execInstrBr s
def footerSiblingPrefix (s : MachineState) (count : Nat) : MachineState := (footerSiblingOps.take count).foldl execInstrBr s

theorem opening_footer_advance_layout : openingControllerOps=openingControllerOps.take 2211++
    footerAdvanceOps++openingControllerOps.drop 2219 := by decide
theorem controller_footer_advance_at : OpsAt openingControllerImage 12940 footerAdvanceOps := by
  have code := opening_controller_ops_at
  rw [opening_footer_advance_layout,List.append_assoc] at code
  have body := ops_at_right openingControllerImage 4096 (openingControllerOps.take 2211) _ code
  rw [List.length_take,opening_controller_ops_length] at body
  exact ops_at_left openingControllerImage _ _ _ body
theorem controller_footer_parent_at : OpsAt openingControllerImage 12956 footerParentOps := by
  have code := ops_at_right openingControllerImage 12940 footerDecisionOps _ controller_footer_advance_at
  exact ops_at_left openingControllerImage _ _ _ code
theorem controller_footer_sibling_at : OpsAt openingControllerImage 12964 footerSiblingOps := by
  have code := ops_at_right openingControllerImage 12940 footerDecisionOps _ controller_footer_advance_at
  exact ops_at_right openingControllerImage _ footerParentOps _ code

theorem footer_decision_pc (s : MachineState) (pc : s.pc=12940) (notRoot : s.getReg .x30≠1#64) :
    (footerDecisionPrefix s 4).pc=if s.getReg .x30&&&1#64=0#64 then 12964 else 12956 := by
  by_cases even : s.getReg .x30&&&1#64=0#64 <;>
    simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,pc,notRoot,even,signExtend12,signExtend13]
theorem footer_decision_register (s : MachineState) (reg : Reg) (different : reg≠.x31) :
    (footerDecisionPrefix s 4).getReg reg=s.getReg reg := by
  by_cases root : s.getReg .x30=1#64 <;> by_cases even : s.getReg .x30&&&1#64=0#64 <;>
    simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,root,even,signExtend12,Ne.symm different]
theorem footer_decision_memory (s : MachineState) (query : Word) :
    (footerDecisionPrefix s 4).getMem query=s.getMem query := by
  by_cases root : s.getReg .x30=1#64 <;> by_cases even : s.getReg .x30&&&1#64=0#64 <;>
    simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,root,even,signExtend12]
theorem footer_decision_byte (s : MachineState) (query : Word) : (footerDecisionPrefix s 4).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_decision_memory]

private theorem decision_succ (s : MachineState) (index : Nat) (inside : index<4) :
    footerDecisionPrefix s (index+1)=execInstrBr (footerDecisionPrefix s index) (footerDecisionOps.getD index .EBREAK) := by
  interval_cases index <;> rfl
theorem footer_decision_execution (s : MachineState) (pc : s.pc=12940) (notRoot : s.getReg .x30≠1#64)
    (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (4+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerDecisionPrefix s 4) coins
          return result.charge 4 0) := by
  have code := ops_at_left openingControllerImage 12940 footerDecisionOps _ controller_footer_advance_at
  apply execute_unit_steps (states := footerDecisionPrefix s)
  intro index inside
  refine ⟨.base (footerDecisionOps.getD index .EBREAK),?_,?_,?_⟩
  · apply code index (by simpa [footerDecisionOps] using inside)
    interval_cases index <;> simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,pc,notRoot]
  · rw [decision_succ s index inside]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl

theorem footer_parent_pc (s : MachineState) (pc : s.pc=12956) : (footerParentPrefix s 2).pc=12940 := by
  simp [footerParentPrefix,footerParentOps,execInstrBr,pc,signExtend21]
theorem footer_parent_node (s : MachineState) : (footerParentPrefix s 2).getReg .x30=s.getReg .x30>>>1 := by
  simp [footerParentPrefix,footerParentOps,execInstrBr]
theorem footer_parent_register (s : MachineState) (reg : Reg) (different : reg≠.x30) :
    (footerParentPrefix s 2).getReg reg=s.getReg reg := by
  simp [footerParentPrefix,footerParentOps,execInstrBr,Ne.symm different]
theorem footer_parent_memory (s : MachineState) (query : Word) : (footerParentPrefix s 2).getMem query=s.getMem query := by
  simp [footerParentPrefix,footerParentOps,execInstrBr]
theorem footer_parent_byte (s : MachineState) (query : Word) : (footerParentPrefix s 2).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_parent_memory]
theorem footer_sibling_pc (s : MachineState) (pc : s.pc=12964) : (footerSiblingPrefix s 2).pc=12408 := by
  simp [footerSiblingPrefix,footerSiblingOps,execInstrBr,pc,signExtend21]
theorem footer_sibling_node (s : MachineState) : (footerSiblingPrefix s 2).getReg .x30=s.getReg .x30+1 := by
  simp [footerSiblingPrefix,footerSiblingOps,execInstrBr]
theorem footer_sibling_register (s : MachineState) (reg : Reg) (different : reg≠.x30) :
    (footerSiblingPrefix s 2).getReg reg=s.getReg reg := by
  simp [footerSiblingPrefix,footerSiblingOps,execInstrBr,Ne.symm different]
theorem footer_sibling_memory (s : MachineState) (query : Word) : (footerSiblingPrefix s 2).getMem query=s.getMem query := by
  simp [footerSiblingPrefix,footerSiblingOps,execInstrBr]
theorem footer_sibling_byte (s : MachineState) (query : Word) : (footerSiblingPrefix s 2).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_sibling_memory]

theorem footer_parent_execution (s : MachineState) (pc : s.pc=12956) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (2+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerParentPrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := footerParentPrefix s)
  intro index inside
  refine ⟨.base (footerParentOps.getD index .EBREAK),?_,?_,?_⟩
  · apply controller_footer_parent_at index (by simpa [footerParentOps] using inside)
    interval_cases index <;> simp [footerParentPrefix,footerParentOps,execInstrBr,pc]
  · have next : footerParentPrefix s (index+1)=execInstrBr (footerParentPrefix s index) (footerParentOps.getD index .EBREAK) := by
      interval_cases index <;> rfl
    rw [next]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl
theorem footer_sibling_execution (s : MachineState) (pc : s.pc=12964) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (2+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerSiblingPrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := footerSiblingPrefix s)
  intro index inside
  refine ⟨.base (footerSiblingOps.getD index .EBREAK),?_,?_,?_⟩
  · apply controller_footer_sibling_at index (by simpa [footerSiblingOps] using inside)
    interval_cases index <;> simp [footerSiblingPrefix,footerSiblingOps,execInstrBr,pc]
  · have next : footerSiblingPrefix s (index+1)=execInstrBr (footerSiblingPrefix s index) (footerSiblingOps.getD index .EBREAK) := by
      interval_cases index <;> rfl
    rw [next]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl

theorem footer_root_execution (s : MachineState) (pc : s.pc=12940) (_root : s.getReg .x30=1#64)
    (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (2+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerDecisionPrefix s 2) coins
          return result.charge 2 0) := by
  have code := ops_at_left openingControllerImage 12940 footerDecisionOps _ controller_footer_advance_at
  apply execute_unit_steps (states := footerDecisionPrefix s)
  intro index inside
  refine ⟨.base (footerDecisionOps.getD index .EBREAK),?_,?_,?_⟩
  · apply code index (by simp only [footerDecisionOps,List.length_cons,List.length_nil]; omega)
    interval_cases index <;> simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,pc]
  · rw [decision_succ s index (by omega)]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl
theorem footer_root_pc (s : MachineState) (pc : s.pc=12940) (root : s.getReg .x30=1#64) :
    (footerDecisionPrefix s 2).pc=12972 := by
  simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,pc,root,signExtend13]
theorem footer_root_register (s : MachineState) (root : s.getReg .x30=1#64) (reg : Reg) (different : reg≠.x31) :
    (footerDecisionPrefix s 2).getReg reg=s.getReg reg := by
  simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,root,Ne.symm different]
theorem footer_root_memory (s : MachineState) (root : s.getReg .x30=1#64) (query : Word) :
    (footerDecisionPrefix s 2).getMem query=s.getMem query := by
  simp [footerDecisionPrefix,footerDecisionOps,execInstrBr,root]
theorem footer_root_byte (s : MachineState) (root : s.getReg .x30=1#64) (query : Word) :
    (footerDecisionPrefix s 2).getByte query=s.getByte query := by simp only [MachineState.getByte,footer_root_memory _ root]

end CommitGolfCandidate.Chained.Native
