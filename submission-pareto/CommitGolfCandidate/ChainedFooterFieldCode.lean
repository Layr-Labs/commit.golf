import CommitGolfCandidate.ChainedFooterHeader

/-! The actual footer field-copy and descriptor instructions, with no generic-header assumption. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem field_build_at_of_ops (image : Image) (base : Word) (n : Nat)
    (code : OpsAt image base (fieldBuildOps n)) :
    LowCopyAt image base n ∧ FieldDescriptorAt image (base+BitVec.ofNat 64 (16*n)) := by
  constructor
  · intro index inside i s pc
    have bound : 4*index+i.val<4*n := by have := i.isLt; omega
    have location : s.pc=base+BitVec.ofNat 64 (4*(4*index+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := code (4*index+i.val) (by simp only [fieldBuildOps,List.length_ofFn]; omega) s location
    have same : fieldBuildOp n (4*index+i.val)=byteCopyOp i.val := by
      have remainder : (4*index+i.val)%4=i.val := by have := i.isLt; omega
      simp only [fieldBuildOp,ite_eq_left bound,remainder]
    simpa only [field_build_ops_get n (4*index+i.val) (by omega),same] using result
  · intro i s pc
    have location : s.pc=base+BitVec.ofNat 64 (4*(4*n+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := code (4*n+i.val) (by simp only [fieldBuildOps,List.length_ofFn]; have := i.isLt; omega) s location
    have same : fieldBuildOp n (4*n+i.val)=fieldDescriptorOp i.val := by simp [fieldBuildOp]
    simpa only [field_build_ops_get n (4*n+i.val) (by have := i.isLt; omega),same] using result

theorem opening_footer_field_layout : openingControllerOps=openingControllerOps.take 2089++
    (fieldBuildOps 29++[.ADDI .x19 .x19 1])++openingControllerOps.drop 2211 := by decide

theorem controller_footer_field_at (image : Image) (base : Word) (code : OpsAt image base openingControllerOps) :
    LowCopyAt image (base+8356) 29 ∧ FieldDescriptorAt image ((base+8356)+464) ∧
    OpsAt image (base+8840) [.ADDI .x19 .x19 1] := by
  rw [opening_footer_field_layout,List.append_assoc] at code
  have afterPrefix := ops_at_right image base (openingControllerOps.take 2089) _ code
  rw [List.length_take,opening_controller_ops_length] at afterPrefix
  have both := ops_at_left image _ _ _ afterPrefix
  have body := ops_at_left image _ _ _ both
  have counter := ops_at_right image _ _ _ both
  change OpsAt image (base+8356) (fieldBuildOps 29) at body
  have parts := field_build_at_of_ops image _ 29 body
  have address : (base+8356)+484=base+8840 := by rw [BitVec.add_assoc]; rfl
  change OpsAt image ((base+8356)+484) [.ADDI .x19 .x19 1] at counter
  rw [address] at counter
  exact ⟨parts.1,parts.2,counter⟩

end CommitGolfCandidate.Chained.Native
