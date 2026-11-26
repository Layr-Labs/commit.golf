import CommitGolfCandidate.ReconstructedCheckCapLevelRead

namespace CommitGolfCandidate.Reconstruction.CheckCapLevelNodes
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckCapLevel
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open HonestCapPlan (pairs)
open HonestSizeSchedule (row)
open CheckCapMembership (child)
set_option maxRecDepth 17000
set_option maxHeartbeats 1400000

theorem live (f : Nat→Bool) (d p : Nat) (side : Bool) (pos : 0<d) (lo : pairs d≤p) :
    Live f d (2*p+side.toNat)=child f d p side := by
  unfold Live child
  rw [(HonestCapState.powers d pos).1]
  congr 1
  omega

theorem used_parent (f : Nat→Bool) (d p : Nat) (pos : 0<d) (bound : d≤9) :
    Live f (d-1) p=CheckCapMembership.used f d p := by
  unfold Live CheckCapMembership.used child
  rw [show 9-(d-1)=(9-d)+1 by omega]
  simp only [row,Bool.toNat_false,Bool.toNat_true,Nat.add_zero,pairs]

theorem bounds (d p : Nat) (pos : 0<d) (lo : pairs d≤p) (hi : p<2^d) (side : Bool) :
    2^d≤2*p+side.toNat ∧ 2*p+side.toNat<2^(d+1) := by
  obtain ⟨wd,ht⟩:=HonestCapState.powers d pos
  have val : side.toNat≤1:=by cases side <;> decide
  omega

theorem known (f : Nat→Bool) (d p : Nat) (pos : 0<d) (lo : pairs d≤p) (hi : p<2^d)
    (side : Bool) (on : Live f d (2*p+side.toNat)=true) :
    CheckCapMembership.used f d p=true ∧ 2*p+side.toNat∉CapSchedule.pending f d := by
  rw [live _ _ _ _ pos lo] at on
  have membership := CheckCapMembership.decision f d p pos lo ((HonestCapState.powers d pos).1 ▸ hi) side
  refine ⟨?_,fun h=>by have bad:=(membership.mp h).2;rw [on] at bad;cases bad⟩
  cases side <;> simp_all [CheckCapMembership.used]

theorem flags (f : Nat→Bool) (d : Nat) (s : MachineState) (pos : 0<d) (bound : d≤9)
    (rows : HonestSizeRows.Rows f d (pairs d) s) : CheckParentLoop.flags s (CheckCapMembership.used f d) (pairs d) (2^d) := by
  intro p low high
  have top:=(HonestCapState.powers d pos).1
  have diff : p-pairs d<pairs d:=by omega
  have bit:=rows.parent (p-pairs d) diff
  rw [ite_eq_left diff,show pairs d+(p-pairs d)=p by omega] at bit
  exact bit

theorem source (o : Oracle) (f : Nat→Bool) (d stream c p : Nat) (s u : MachineState) (m : Memory)
    (pos : 0<d) (max : d≤9) (lo : pairs d≤p) (hi : p<2^d) (side : Bool)
    (start : Boundary f stream d c s) (out : CheckCapLevelRead.Post f stream d c s u m)
    (ok : (parsed f d stream c m).valid=true) (selected : CheckCapMembership.used f d p=true) :
    Canonical d (view (parsed f d stream c m).data (2*p+side.toNat)) := by
  let id:=2*p+side.toNat
  obtain ⟨l,h⟩:=bounds d p pos lo hi side
  have hiId : id<1024:=lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide : 0<2) (by omega : d+1≤10))
  by_cases found : id∈CapSchedule.pending f d
  · exact CheckCapPhysical.canonical d m _ stream c id pos max found (CheckCapMembership.nodup ..) ok
  · have yes : Live f d id=true := by
      rw [live _ _ _ _ pos lo]
      have iff:=CheckCapMembership.decision f d p pos lo ((HonestCapState.powers d pos).1 ▸ hi) side
      cases hh : child f d p side with
      | false=>exact False.elim (found (iff.mpr ⟨selected,hh⟩))
      | true=>rfl
    have same:=CheckCapPhysical.untouched d (Encoding.lows d) m (CapSchedule.pending f d) stream c id found
    have u : view (parsed f d stream c m).data id=node s id:=same.trans (out.base.same id hiId)
    rw [show view (parsed f d stream c m).data (2*p+side.toNat)=node s id from u]
    exact start.canonical id l h yes

theorem unchanged (f : Nat→Bool) (d stream c p : Nat) (s u : MachineState) (m : Memory) (side : Bool)
    (pos : 0<d) (max : d≤9) (lo : pairs d≤p) (hi : p<2^d) (input : CheckCapLevelRead.Post f stream d c s u m)
    (on : Live f d (2*p+side.toNat)=true) : view (parsed f d stream c m).data (2*p+side.toNat)=node s (2*p+side.toNat) := by
  have found:=known f d p pos lo hi side on
  have ib:=(bounds d p pos lo hi side).2
  have sm : 2*p+side.toNat<1024:=lt_of_lt_of_le ib (Nat.pow_le_pow_right (by decide : 0<2) (by omega : d+1≤10))
  exact (CheckCapPhysical.untouched _ _ _ _ _ _ _ found.2).trans (input.base.same _ sm)

end CommitGolfCandidate.Reconstruction.CheckCapLevelNodes
