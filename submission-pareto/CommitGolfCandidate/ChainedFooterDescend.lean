import CommitGolfCandidate.ChainedFooterLookup

/-! Occupied native footer nodes descend internally and prune at cap leaves. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne

@[local simp] private theorem descend_set_zero (s : MachineState) (value : Word) : s.setReg .x0 value=s := rfl

@[local simp] private theorem descend_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def footerKnownOps : List Instr := [.BGEU .x30 .x29 516,.SLLI .x30 .x30 1,.JAL .x0 2097128]
def footerKnownPrefix (s : MachineState) (count : Nat) : MachineState := (footerKnownOps.take count).foldl execInstrBr s

theorem opening_footer_known_layout : openingControllerOps=openingControllerOps.take 2082++
    footerKnownOps++openingControllerOps.drop 2085 := by decide
theorem controller_footer_known_at : OpsAt openingControllerImage 12424 footerKnownOps := by
  have code := opening_controller_ops_at
  rw [opening_footer_known_layout,List.append_assoc] at code
  have body := ops_at_right openingControllerImage 4096 (openingControllerOps.take 2082) _ code
  rw [List.length_take,opening_controller_ops_length] at body
  exact ops_at_left openingControllerImage _ _ _ body

private theorem known_succ (s : MachineState) (index : Nat) (inside : index<3) :
    footerKnownPrefix s (index+1)=execInstrBr (footerKnownPrefix s index) (footerKnownOps.getD index .EBREAK) := by
  interval_cases index <;> rfl

theorem footer_descend_execution (s : MachineState) (pc : s.pc=12424) (internal : footerWide s)
    (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (3+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerKnownPrefix s 3) coins
          return result.charge 3 0) := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  apply execute_unit_steps (states := footerKnownPrefix s)
  intro index inside
  refine ⟨.base (footerKnownOps.getD index .EBREAK),?_,?_,?_⟩
  · apply controller_footer_known_at index (by simpa [footerKnownOps] using inside)
    interval_cases index <;> simp [footerKnownPrefix,footerKnownOps,execInstrBr,pc,internal]
  · rw [known_succ s index inside]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl

theorem footer_descend_pc (s : MachineState) (pc : s.pc=12424) (internal : footerWide s) :
    (footerKnownPrefix s 3).pc=12408 := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [footerKnownPrefix,footerKnownOps,execInstrBr,pc,internal,signExtend21]
theorem footer_descend_node (s : MachineState) (internal : footerWide s) :
    (footerKnownPrefix s 3).getReg .x30=s.getReg .x30<<<1 := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [footerKnownPrefix,footerKnownOps,execInstrBr,internal]
theorem footer_descend_register (s : MachineState) (internal : footerWide s) (reg : Reg) (different : reg≠.x30) :
    (footerKnownPrefix s 3).getReg reg=s.getReg reg := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [footerKnownPrefix,footerKnownOps,execInstrBr,internal,Ne.symm different]
theorem footer_descend_memory (s : MachineState) (internal : footerWide s) (query : Word) :
    (footerKnownPrefix s 3).getMem query=s.getMem query := by
  change BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at internal
  simp [footerKnownPrefix,footerKnownOps,execInstrBr,internal]
theorem footer_descend_byte (s : MachineState) (internal : footerWide s) (query : Word) :
    (footerKnownPrefix s 3).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_descend_memory _ internal]

theorem footer_prune_execution (s : MachineState) (pc : s.pc=12424) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (1+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerKnownPrefix s 1) coins
          return result.charge 1 0) := by
  have fetched : fetch openingControllerImage s=some (.base (.BGEU .x30 .x29 516)) :=
    controller_footer_known_at 0 (by decide) _ (by simpa using pc)
  simpa only [Nat.add_comm,instructionCycles] using
    execute_ordinary_step openingControllerImage _ s (footerKnownPrefix s 1) fuel coins fetched rfl
theorem footer_prune_pc (s : MachineState) (pc : s.pc=12424) (leaf : ¬footerWide s) :
    (footerKnownPrefix s 1).pc=12940 := by
  change ¬BitVec.ult (s.getReg .x30) (s.getReg .x29)=true at leaf
  simp [footerKnownPrefix,footerKnownOps,execInstrBr,pc,leaf,signExtend13]
theorem footer_prune_register (s : MachineState) (reg : Reg) : (footerKnownPrefix s 1).getReg reg=s.getReg reg := by
  by_cases internal : footerWide s
  · have same : footerKnownPrefix s 1=s.setPC (s.pc+4) := ite_eq_right (by simpa [footerWide] using internal)
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : footerKnownPrefix s 1=s.setPC (s.pc+516) := ite_eq_left internal
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
theorem footer_prune_memory (s : MachineState) (query : Word) : (footerKnownPrefix s 1).getMem query=s.getMem query := by
  by_cases internal : footerWide s
  · have same : footerKnownPrefix s 1=s.setPC (s.pc+4) := ite_eq_right (by simpa [footerWide] using internal)
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : footerKnownPrefix s 1=s.setPC (s.pc+516) := ite_eq_left internal
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
theorem footer_prune_byte (s : MachineState) (query : Word) : (footerKnownPrefix s 1).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_prune_memory]

end CommitGolfCandidate.Chained.Native
