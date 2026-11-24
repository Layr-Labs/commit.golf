import CommitGolfCandidate.ChainedFooterAdvance

/-! Actual variable-row footer-tail setup and traversal fetches, including zero rows. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[local simp] private theorem footer_setup_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def footerTailSetupOps : List Instr :=
  [.ADDI .x20 .x6 0,.SLLI .x21 .x19 1,.SUB .x21 .x7 .x21,.ADDI .x22 .x19 0,
   .ADDI .x23 .x0 0,.ADDI .x25 .x0 0,.ADDI .x27 .x0 8]
def footerTailSetupPrefix (s : MachineState) (count : Nat) : MachineState :=
  (footerTailSetupOps.take count).foldl execInstrBr s

theorem footer_tail_setup_cursor (s : MachineState) : (footerTailSetupPrefix s 7).getReg .x20=s.getReg .x6 := by
  change s.getReg .x6+0=s.getReg .x6
  exact BitVec.add_zero _
theorem footer_tail_setup_source (s : MachineState) :
    (footerTailSetupPrefix s 7).getReg .x21=s.getReg .x7-(s.getReg .x19<<<1) := rfl
theorem footer_tail_setup_count (s : MachineState) : (footerTailSetupPrefix s 7).getReg .x22=s.getReg .x19 := by
  change s.getReg .x19+0=s.getReg .x19
  exact BitVec.add_zero _
theorem footer_tail_setup_buffer (s : MachineState) : TailBuffer (footerTailSetupPrefix s 7) [] :=
  ⟨rfl,rfl,rfl,by decide⟩
theorem footer_tail_setup_byte (s : MachineState) (query : Word) :
    (footerTailSetupPrefix s 7).getByte query=s.getByte query := rfl
theorem footer_tail_setup_frame (s : MachineState) (reg : Reg)
    (a : reg≠.x20) (b : reg≠.x21) (c : reg≠.x22) (d : reg≠.x23) (e : reg≠.x25) (f : reg≠.x27) :
    (footerTailSetupPrefix s 7).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem footer_tail_setup_pc (s : MachineState) (count : Nat) (small : count≤7) :
    (footerTailSetupPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [footerTailSetupPrefix,footerTailSetupOps,execInstrBr,BitVec.add_assoc]

theorem footer_tail_setup_table (s : MachineState) (metadata count : Nat)
    (table : s.getReg .x7=BitVec.ofNat 64 (metadata+2*count)) (rows : s.getReg .x19=BitVec.ofNat 64 count) :
    (footerTailSetupPrefix s 7).getReg .x21=BitVec.ofNat 64 metadata := by
  rw [footer_tail_setup_source,table,rows,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 (metadata+2*count)-BitVec.ofNat 64 count*BitVec.ofNat 64 2=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm count 2,BitVec.ofNat_add,BitVec.add_sub_cancel]

theorem footer_tail_setup_execution (image : Image) (base : Word) (code : OpsAt image base footerTailSetupOps)
    (s : MachineState) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (7+fuel) s coins=
      (do let result ← execute image fuel (footerTailSetupPrefix s 7) coins
          return result.charge 7 0) := by
  apply execute_unit_steps (states := footerTailSetupPrefix s)
  intro index inside
  refine ⟨.base (footerTailSetupOps.getD index .EBREAK),?_,?_,?_⟩
  · apply code index (by simpa [footerTailSetupOps] using inside)
    rw [footer_tail_setup_pc s index (by omega),pc]
  · interval_cases index <;> rfl
  · interval_cases index <;> rfl

theorem opening_footer_tail_layout : openingControllerOps=openingControllerOps.take 2219++
    (footerTailSetupOps++tailTraverseOps)++openingControllerOps.drop 2243 := by decide
theorem controller_footer_tail_at : OpsAt openingControllerImage 12972 footerTailSetupOps ∧
    TailTraverseAt openingControllerImage 13000 := by
  have code := opening_controller_ops_at
  rw [opening_footer_tail_layout,List.append_assoc] at code
  have body := ops_at_right openingControllerImage 4096 (openingControllerOps.take 2219) _ code
  rw [List.length_take,opening_controller_ops_length] at body
  have both := ops_at_left openingControllerImage _ _ _ body
  have setup := ops_at_left openingControllerImage _ _ _ both
  have traverse := ops_at_right openingControllerImage _ _ _ both
  refine ⟨setup,?_⟩
  intro index s pc
  exact traverse index.val index.isLt s pc

end CommitGolfCandidate.Chained.Native
