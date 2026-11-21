import CommitGolfCandidate.ChainedFooterFrame
import CommitGolfCandidate.TwoPermutationPackedOpeningFinish
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

/-! The unused zero mark stays zero during the cached opener's unrolled parent sweep. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open TwoPermutationPrototype.PackedOpening (capPreparation unrollEnter)
set_option maxRecDepth 8192

theorem cached_group_lower (positions : Positions) (ordinal group : Nat)
    (member : group∈groupsBefore positions ordinal) : 256≤group := by
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  exact (lower_cap_range index).1

theorem cached_group_zero_absent (positions : Positions) (ordinal : Nat) :
    0∉groupsBefore positions ordinal := by
  intro member
  have := cached_group_lower positions ordinal 0 member
  omega

theorem cached_mark_zero (positions : Positions) (ordinal : Nat) :
    markWord (groupsBefore positions ordinal) 0=0#64 := by
  have unmarked : capIsMarked (groupsBefore positions ordinal) 0 8=false := by
    apply Bool.eq_false_iff.mpr
    intro occupied
    obtain ⟨group,member,equal⟩ := List.any_eq_true.mp occupied
    have lower := cached_group_lower positions ordinal group member
    have zero : group/256=0 := by simpa using equal
    omega
  change BitVec.ofNat 64 (capIsMarked (groupsBefore positions ordinal) 0 8).toNat=0#64
  rw [unmarked]
  rfl

@[local simp] private theorem marks_mem_setReg (s : MachineState) (reg : Reg) (value : Word) :
    (s.setReg reg value).mem=s.mem := by cases reg <;> rfl

private theorem mark_finish_zero (s : MachineState) (node d : Nat) (positive : 0<node) (small : node<512) :
    (Postorder.finish s node d).getMem (Postorder.addr 0)=s.getMem (Postorder.addr 0) := by
  have different : Postorder.addr 0≠Postorder.addr node := by
    intro equal
    have values := nat_address_injective (by decide : markBase+8*0<2^64)
      (by unfold markBase; omega : markBase+8*node<2^64) equal
    omega
  simp [Postorder.finish,MachineState.getMem,MachineState.setMem,MachineState.setPC,different]

theorem cached_postorder_zero (s : MachineState) (node height d : Nat) (span : CapSpan node height) :
    (Postorder.eval s node height d).getMem (Postorder.addr 0)=s.getMem (Postorder.addr 0) := by
  induction height generalizing s node d with
  | zero => simp [Postorder.eval,MachineState.getMem,MachineState.setPC]
  | succ height ih =>
    obtain ⟨left,right⟩ := cap_span_children node height span
    rw [Postorder.eval,mark_finish_zero _ node d (cap_span_node node _ span).1 (cap_span_node node _ span).2,
      ih _ _ _ right,ih _ _ _ left]

attribute [local irreducible] Postorder.eval

theorem cached_preparation_zero (s : MachineState) :
    (PackedOpening.capPreparation s).getMem (BitVec.ofNat 64 4096)=s.getMem (BitVec.ofNat 64 4096) := by
  change (Postorder.eval (unrollEnter s) 1 8 0).getMem (Postorder.addr 0)=_
  rw [cached_postorder_zero _ _ _ _ cap_span_root]
  rfl

end CommitGolfCandidate.Chained.Native
