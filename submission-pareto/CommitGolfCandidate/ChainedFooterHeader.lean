import CommitGolfCandidate.ChainedRecordLoop

/-! Actual footer header chooses six high bits internally and two at cap leaves. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def footerHeaderOps : List Instr :=
  [.ADDI .x10 .x0 2,.BGEU .x30 .x29 8,.ADDI .x10 .x0 6,.ADDI .x9 .x0 1]
def footerWide (s : MachineState) : Bool := BitVec.ult (s.getReg .x30) (s.getReg .x29)
def footerSetWidth (s : MachineState) (value : BitVec 12) : MachineState := execInstrBr s (.ADDI .x10 .x0 value)
def footerGuard (s : MachineState) : MachineState := execInstrBr s (.BGEU .x30 .x29 8)
def footerSetSkip (s : MachineState) : MachineState := execInstrBr s (.ADDI .x9 .x0 1)
def footerHeaderState (s : MachineState) : MachineState :=
  footerSetSkip (if footerWide s then footerSetWidth (footerGuard (footerSetWidth s 2)) 6
    else footerGuard (footerSetWidth s 2))
def footerHeaderCycles (s : MachineState) : Nat := if footerWide s then 4 else 3

theorem footer_set_width_pc (s : MachineState) (value : BitVec 12) : (footerSetWidth s value).pc=s.pc+4 := rfl
theorem footer_set_width_register (s : MachineState) (value : BitVec 12) (reg : Reg) (different : reg≠.x10) :
    (footerSetWidth s value).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem footer_set_skip_register (s : MachineState) (reg : Reg) (different : reg≠.x9) :
    (footerSetSkip s).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem footer_set_skip_pc (s : MachineState) : (footerSetSkip s).pc=s.pc+4 := rfl
theorem footer_set_width_byte (s : MachineState) (value : BitVec 12) (query : Word) :
    (footerSetWidth s value).getByte query=s.getByte query := rfl
theorem footer_set_skip_byte (s : MachineState) (query : Word) : (footerSetSkip s).getByte query=s.getByte query := rfl
theorem footer_width_set_test (s : MachineState) (value : BitVec 12) : footerWide (footerSetWidth s value)=footerWide s := rfl

theorem footer_guard_pc (s : MachineState) : (footerGuard s).pc=if footerWide s then s.pc+4 else s.pc+8 := by
  change (if ¬footerWide s then s.setPC (s.pc+8) else s.setPC (s.pc+4)).pc=_
  cases test : footerWide s <;> simp only [test,Bool.false_eq_true,not_false_eq_true,not_true_eq_false,↓reduceIte] <;> rfl
theorem footer_guard_register (s : MachineState) (reg : Reg) : (footerGuard s).getReg reg=s.getReg reg := by
  by_cases wide : footerWide s
  · have same : footerGuard s=s.setPC (s.pc+4) := ite_eq_right (by simpa [footerWide] using wide)
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : footerGuard s=s.setPC (s.pc+8) := ite_eq_left wide
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
theorem footer_guard_memory (s : MachineState) (query : Word) : (footerGuard s).getMem query=s.getMem query := by
  by_cases wide : footerWide s
  · have same : footerGuard s=s.setPC (s.pc+4) := ite_eq_right (by simpa [footerWide] using wide)
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : footerGuard s=s.setPC (s.pc+8) := ite_eq_left wide
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
theorem footer_guard_byte (s : MachineState) (query : Word) : (footerGuard s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_guard_memory]

theorem footer_header_skip (s : MachineState) : (footerHeaderState s).getReg .x9=1 := rfl
theorem footer_header_width_value (s : MachineState) :
    (footerHeaderState s).getReg .x10=if footerWide s then 6 else 2 := by
  rw [footerHeaderState,footer_set_skip_register _ .x10 (by decide)]
  split
  · rfl
  · rw [footer_guard_register]
    rfl
theorem footer_header_register (s : MachineState) (reg : Reg) (a : reg≠.x9) (b : reg≠.x10) :
    (footerHeaderState s).getReg reg=s.getReg reg := by
  rw [footerHeaderState,footer_set_skip_register _ reg a]
  split <;> simp only [footer_set_width_register _ _ reg b,footer_guard_register]
theorem footer_header_byte (s : MachineState) (query : Word) : (footerHeaderState s).getByte query=s.getByte query := by
  rw [footerHeaderState,footer_set_skip_byte]
  split <;> simp only [footer_set_width_byte,footer_guard_byte]
theorem footer_header_pc (s : MachineState) : (footerHeaderState s).pc=s.pc+16 := by
  rw [footerHeaderState,footer_set_skip_pc]
  split <;> rename_i wide
  · rw [footer_set_width_pc,footer_guard_pc,footer_width_set_test,ite_eq_left wide,footer_set_width_pc]
    rw [BitVec.add_assoc,BitVec.add_assoc,BitVec.add_assoc]
    rfl
  · rw [footer_guard_pc,footer_width_set_test,ite_eq_right wide,footer_set_width_pc]
    rw [BitVec.add_assoc,BitVec.add_assoc]
    rfl

theorem footer_header_width (s : MachineState) (node : Nat) (fit : node<2^64)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) :
    (footerHeaderState s).getReg .x10=BitVec.ofNat 64 (InteriorCodec.footerWidth node-232) := by
  rw [footer_header_width_value,footerWide,cursor,limit,BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  by_cases leaf : 256≤node
  · have large : ¬node<256 := by omega
    simp [large,InteriorCodec.footerWidth,leaf]
  · have small : node<256 := by omega
    simp [small,InteriorCodec.footerWidth,leaf]

theorem opening_footer_header_layout : openingControllerOps=
    openingControllerOps.take 2085++footerHeaderOps++openingControllerOps.drop 2089 := by decide
theorem controller_footer_header_at (image : Image) (base : Word) (code : OpsAt image base openingControllerOps) :
    OpsAt image (base+8340) footerHeaderOps := by
  rw [opening_footer_header_layout,List.append_assoc] at code
  have afterPrefix := ops_at_right image base (openingControllerOps.take 2085) _ code
  rw [List.length_take,opening_controller_ops_length] at afterPrefix
  exact ops_at_left image _ _ _ afterPrefix

theorem footer_header_execution (image : Image) (base : Word) (code : OpsAt image base footerHeaderOps)
    (s : MachineState) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (footerHeaderCycles s+fuel) s coins=
      (do let result ← execute image fuel (footerHeaderState s) coins
          return result.charge (footerHeaderCycles s) 0) := by
  have first : fetch image s=some (.base (.ADDI .x10 .x0 2)) := code 0 (by decide) _ (by simpa using pc)
  have guardFetch : fetch image (footerSetWidth s 2)=some (.base (.BGEU .x30 .x29 8)) := by
    apply code 1 (by decide)
    rw [footer_set_width_pc,pc]
    rfl
  have firstStep : ordinaryStep s (.base (.ADDI .x10 .x0 2))=some (footerSetWidth s 2) := rfl
  have guardStep : ordinaryStep (footerSetWidth s 2) (.base (.BGEU .x30 .x29 8))=
      some (footerGuard (footerSetWidth s 2)) := rfl
  by_cases wide : footerWide s
  · have middlePC : (footerGuard (footerSetWidth s 2)).pc=base+8 := by
      rw [footer_guard_pc,footer_width_set_test,ite_eq_left wide,footer_set_width_pc,pc,BitVec.add_assoc]; rfl
    have middle : fetch image (footerGuard (footerSetWidth s 2))=some (.base (.ADDI .x10 .x0 6)) :=
      code 2 (by decide) _ middlePC
    have middleStep : ordinaryStep (footerGuard (footerSetWidth s 2)) (.base (.ADDI .x10 .x0 6))=
        some (footerSetWidth (footerGuard (footerSetWidth s 2)) 6) := rfl
    have last : fetch image (footerSetWidth (footerGuard (footerSetWidth s 2)) 6)=some (.base (.ADDI .x9 .x0 1)) := by
      apply code 3 (by decide)
      rw [footer_set_width_pc,middlePC,BitVec.add_assoc]; rfl
    have lastStep : ordinaryStep (footerSetWidth (footerGuard (footerSetWidth s 2)) 6) (.base (.ADDI .x9 .x0 1))=
        some (footerSetSkip (footerSetWidth (footerGuard (footerSetWidth s 2)) 6)) := rfl
    rw [footerHeaderCycles,ite_eq_left wide,show 4+fuel=((fuel+1)+1)+1+1 by omega,
      execute_ordinary_step image _ _ _ _ coins first firstStep,
      execute_ordinary_step image _ _ _ _ coins guardFetch guardStep,
      execute_ordinary_step image _ _ _ _ coins middle middleStep,
      execute_ordinary_step image _ _ _ _ coins last lastStep]
    simp [footerHeaderState,wide,Execution.charge,instructionCycles,←Nat.add_assoc]
  · have last : fetch image (footerGuard (footerSetWidth s 2))=some (.base (.ADDI .x9 .x0 1)) := by
      apply code 3 (by decide)
      rw [footer_guard_pc,footer_width_set_test,ite_eq_right wide,footer_set_width_pc,pc,BitVec.add_assoc]; rfl
    have lastStep : ordinaryStep (footerGuard (footerSetWidth s 2)) (.base (.ADDI .x9 .x0 1))=
        some (footerSetSkip (footerGuard (footerSetWidth s 2))) := rfl
    rw [footerHeaderCycles,ite_eq_right wide,show 3+fuel=(fuel+1)+1+1 by omega,
      execute_ordinary_step image _ _ _ _ coins first firstStep,
      execute_ordinary_step image _ _ _ _ coins guardFetch guardStep,
      execute_ordinary_step image _ _ _ _ coins last lastStep]
    simp [footerHeaderState,wide,Execution.charge,instructionCycles,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
