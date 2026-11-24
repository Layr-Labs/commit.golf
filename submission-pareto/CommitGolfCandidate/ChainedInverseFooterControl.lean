import CommitGolfCandidate.ChainedInverseFooterCode

/-! Projected footer-loop counter, branch and field-step frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] execute

def inverseFooterDecrease (s : MachineState) : MachineState := execInstrBr s (.ADDI .x22 .x22 4095)
def inverseFooterMore (s : MachineState) : Bool := !(s.getReg .x22==0#64)
def inverseFooterGuard (s : MachineState) : MachineState := execInstrBr s (.BNE .x22 .x0 7708)
def inverseFooterFieldState (s : MachineState) : MachineState :=
  inverseFooterGuard (inverseFooterDecrease (inverseFieldState 29 s))
def inverseFooterControlOps : List Instr := [.ADDI .x22 .x22 4095,.BNE .x22 .x0 7708]
@[irreducible] def inverseFooterControlStates (s decreased guarded : MachineState) : Nat → MachineState
  | 0 => s
  | 1 => decreased
  | _ => guarded

theorem inverse_footer_states_zero (s decreased guarded : MachineState) :
    inverseFooterControlStates s decreased guarded 0=s := by delta inverseFooterControlStates; rfl
theorem inverse_footer_states_one (s decreased guarded : MachineState) :
    inverseFooterControlStates s decreased guarded 1=decreased := by delta inverseFooterControlStates; rfl
theorem inverse_footer_states_two (s decreased guarded : MachineState) :
    inverseFooterControlStates s decreased guarded 2=guarded := by delta inverseFooterControlStates; rfl

@[irreducible] def inverseFooterControlPrefix (s : MachineState) (count : Nat) : MachineState :=
  inverseFooterControlStates s (inverseFooterDecrease s) (inverseFooterGuard (inverseFooterDecrease s)) count

theorem inverse_footer_control_zero (s : MachineState) : inverseFooterControlPrefix s 0=s := by
  rw [inverseFooterControlPrefix,inverse_footer_states_zero]
theorem inverse_footer_control_one (s : MachineState) : inverseFooterControlPrefix s 1=inverseFooterDecrease s := by
  rw [inverseFooterControlPrefix,inverse_footer_states_one]
theorem inverse_footer_control_two (s : MachineState) :
    inverseFooterControlPrefix s 2=inverseFooterGuard (inverseFooterDecrease s) := by
  rw [inverseFooterControlPrefix,inverse_footer_states_two]

theorem inverse_footer_decrease_count (s : MachineState) :
    (inverseFooterDecrease s).getReg .x22=s.getReg .x22-1#64 := by
  change s.getReg .x22+signExtend12 4095=_
  rw [BitVec.sub_eq_add_neg]
  rfl
theorem inverse_footer_decrease_register (s : MachineState) (reg : Reg) (apart : reg≠.x22) :
    (inverseFooterDecrease s).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem inverse_footer_decrease_pc (s : MachineState) : (inverseFooterDecrease s).pc=s.pc+4 := rfl

theorem inverse_footer_guard_register (s : MachineState) (reg : Reg) :
    (inverseFooterGuard s).getReg reg=s.getReg reg := by
  by_cases more : inverseFooterMore s
  · have same : inverseFooterGuard s=s.setPC (s.pc+signExtend13 7708) := ite_eq_left more
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : inverseFooterGuard s=s.setPC (s.pc+4) := ite_eq_right more
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC

theorem inverse_footer_guard_memory (s : MachineState) (query : Word) :
    (inverseFooterGuard s).getMem query=s.getMem query := by
  by_cases more : inverseFooterMore s
  · have same : inverseFooterGuard s=s.setPC (s.pc+signExtend13 7708) := ite_eq_left more
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : inverseFooterGuard s=s.setPC (s.pc+4) := ite_eq_right more
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC

theorem inverse_footer_project_pc (before after : MachineState) (target : Word)
    (same : after=before.setPC target) : after.pc=target := congrArg MachineState.pc same

theorem inverse_footer_bne_pc (s : MachineState) (offset : BitVec 13) :
    (execInstrBr s (.BNE .x22 .x0 offset)).pc=
      if inverseFooterMore s then s.pc+signExtend13 offset else s.pc+4 := by
  by_cases more : inverseFooterMore s
  · have same : execInstrBr s (.BNE .x22 .x0 offset)=s.setPC (s.pc+signExtend13 offset) := ite_eq_left more
    have projected := inverse_footer_project_pc s _ _ same
    exact projected.trans (ite_eq_left more).symm
  · have same : execInstrBr s (.BNE .x22 .x0 offset)=s.setPC (s.pc+4) := ite_eq_right more
    have projected := inverse_footer_project_pc s _ _ same
    exact projected.trans (ite_eq_right more).symm

theorem inverse_footer_guard_pc (s : MachineState) :
    (inverseFooterGuard s).pc=if inverseFooterMore s then s.pc+signExtend13 7708 else s.pc+4 :=
  inverse_footer_bne_pc s 7708

theorem inverse_footer_guard_byte (s : MachineState) (query : Word) :
    (inverseFooterGuard s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,inverse_footer_guard_memory]
theorem inverse_footer_decrease_byte (s : MachineState) (query : Word) :
    (inverseFooterDecrease s).getByte query=s.getByte query := rfl

theorem inverse_footer_field_byte (s : MachineState) (query : Word) :
    (inverseFooterFieldState s).getByte query=(inverseFieldState 29 s).getByte query := by
  rw [inverseFooterFieldState,inverse_footer_guard_byte,inverse_footer_decrease_byte]

theorem inverse_footer_field_count (s : MachineState) :
    (inverseFooterFieldState s).getReg .x22=s.getReg .x22-1#64 := by
  rw [inverseFooterFieldState,inverse_footer_guard_register,inverse_footer_decrease_count,
    inverse_field_frame _ _ .x22 (by decide) (by decide) (by decide) (by decide)]

theorem inverse_footer_field_register (s : MachineState) (reg : Reg) (apart : reg≠.x22) :
    (inverseFooterFieldState s).getReg reg=(inverseFieldState 29 s).getReg reg := by
  rw [inverseFooterFieldState,inverse_footer_guard_register,inverse_footer_decrease_register _ reg apart]

theorem inverse_footer_field_pc (s : MachineState) (base : Word) (remaining : Nat)
    (pc : s.pc=base+4) (count : s.getReg .x22=BitVec.ofNat 64 (remaining+1))
    (fit : remaining+1<2^64) :
    (inverseFooterFieldState s).pc=if remaining=0 then base+492 else base+4 := by
  have bodyPC : (inverseFieldState 29 s).pc=base+484 := by
    rw [inverseFieldState,inverse_field_tail_pc _ 4 (by decide),low_copy_pc,pc,
      BitVec.add_assoc,BitVec.add_assoc]
    rfl
  have decreased : (inverseFooterDecrease (inverseFieldState 29 s)).getReg .x22=BitVec.ofNat 64 remaining := by
    rw [inverse_footer_decrease_count,inverse_field_frame _ _ .x22 (by decide) (by decide) (by decide) (by decide),count]
    have result := BitVec.ofNat_sub_ofNat_of_le (remaining+1) 1 (by decide : 1<2^64) (by omega)
    simpa only [Nat.add_sub_cancel] using result
  have more : inverseFooterMore (inverseFooterDecrease (inverseFieldState 29 s))=decide (remaining≠0) := by
    rw [inverseFooterMore,decreased]
    change (!(remaining%2^64==0))=decide (remaining≠0)
    rw [Nat.mod_eq_of_lt (by omega)]
    cases remaining <;> rfl
  rw [inverseFooterFieldState,inverse_footer_guard_pc,more,inverse_footer_decrease_pc,bodyPC]
  by_cases empty : remaining=0 <;> simp [empty,BitVec.add_assoc]; rfl

theorem inverse_footer_control_at (image : Image) (base : Word) (code : OpsAt image base inverseFooterOps) :
    OpsAt image (base+484) inverseFooterControlOps := by
  have start : OpsAt image (base+4) (inverseFieldOps 29++inverseFooterControlOps) :=
    ops_at_right image base ([.BEQ .x22 .x0 492] : List Instr) _ code
  have tail := ops_at_right image (base+4) (inverseFieldOps 29) inverseFooterControlOps start
  simp only [inverseFieldOps,List.length_ofFn,BitVec.add_assoc] at tail
  have offset : (4 : Word)+BitVec.ofNat 64 (4*(4*29+4))=(484 : Word) := by rfl
  rw [offset] at tail
  exact tail

theorem inverse_footer_control_execution (image : Image) (base : Word)
    (code : OpsAt image base inverseFooterControlOps) (s : MachineState) (pc : s.pc=base)
    (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins=
      (do let result ← execute image fuel (inverseFooterControlPrefix s 2) coins
          return result.charge 2 0) := by
  conv_lhs => rw [←inverse_footer_control_zero s]
  apply execute_unit_steps (states := inverseFooterControlPrefix s)
  intro index inside
  refine ⟨.base (inverseFooterControlOps.getD index .EBREAK),?_,?_,?_⟩
  · apply code index inside
    have bounded : index<2 := inside
    interval_cases index
    · rw [inverse_footer_control_zero]
      change s.pc=base+0#64
      rw [BitVec.add_zero]
      exact pc
    · rw [inverse_footer_control_one,inverse_footer_decrease_pc]
      rw [pc]
      rfl
  · interval_cases index
    · rw [inverse_footer_control_zero,inverse_footer_control_one]; rfl
    · rw [inverse_footer_control_one,inverse_footer_control_two]; rfl
  · interval_cases index <;> rfl

end CommitGolfCandidate.Chained.Native
