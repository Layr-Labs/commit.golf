import CommitGolfCandidate.ReconstructedBindingWeight

namespace CommitGolfCandidate.Reconstruction.Binding
open Finset
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
attribute [local irreducible] Finset.univ
attribute [local instance] Classical.propDecidable
noncomputable section

def Reject (m : Table) (k : Key) (y : Digest) : Prop :=
  (∃ j, m j = some y) ∨ m (unary y) ≠ none ∨ unary y = k ∨ EndpointCollision (put m k y)

/-- The 256-bit exceptions count prior full answers and prior unary inputs.
The remaining possible bad answers form the exact fibers of earlier endpoints
of the depth identified by the ready key. -/
theorem fresh_answer_count (m : Table) (keys : Finset Key) (k : Key)
    (safe : DistinctAnswers m) (covers : Covers keys m) (noPaid : ¬ EndpointCollision m) :
    1000000 * (Finset.univ.filter (Reject m k)).card ≤ 1000000*(2*keys.card+1) +
      1221263*2^18 * (mass m) * (weight m k) := by
  classical
  let exceptions := (keys.image (extendTable m) ∪ keys.image Prod.fst) ∪ {k.1}
  have base : exceptions.card ≤ 2*keys.card+1 := by
    have e := Finset.card_union_le (keys.image (extendTable m) ∪ keys.image Prod.fst) {k.1}
    have f := Finset.card_union_le (keys.image (extendTable m)) (keys.image Prod.fst)
    have a : (keys.image (extendTable m)).card ≤ keys.card := Finset.card_image_le
    have b : (keys.image Prod.fst).card ≤ keys.card := Finset.card_image_le
    simp only [Finset.card_singleton] at e
    dsimp [exceptions]; omega
  have outside {y : Digest} (bad : Reject m k y) (ex : y ∉ exceptions) :
      ∃ s, readySeed m k = some s ∧ y ∈ dangerous m s.depth := by
    have nz : ∀ j, m j ≠ some y := by
      intro j hj
      apply ex
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2
        ⟨j,covers _ _ hj,by simp [extendTable,hj]⟩))
    have nu : m (unary y) = none := by
      cases h : m (unary y) with
      | none => rfl
      | some v => exact False.elim (ex (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.2 ⟨unary y,covers _ _ h,rfl⟩))))
    have ns : unary y ≠ k := fun eq => ex (Finset.mem_union_right _
      (Finset.mem_singleton.2 (congrArg Prod.fst eq)))
    rcases bad with ⟨j,hj⟩ | h | h | hit
    · exact False.elim (nz j hj)
    · exact False.elim (h nu)
    · exact False.elim (ns h)
    · obtain ⟨s,t,v,r,d,seen,eq⟩ := endpoint_collision_after_put _ _ _ safe noPaid nu ns hit
      refine ⟨s,ready_chosen _ safe _ _ r,Finset.mem_biUnion.2 ⟨t,?_,?_⟩⟩
      · exact Finset.mem_filter.2 ⟨(mem_completed (m := m) (s := t)).2 ⟨v,seen⟩,d.symm⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,by simp [seen,eq]⟩
  cases chosen : readySeed m k with
  | none =>
    have subset : Finset.univ.filter (Reject m k) ⊆ exceptions := by
      intro y hy
      by_contra no
      obtain ⟨s,hs,_⟩ := outside (Finset.mem_filter.mp hy).2 no
      simp [chosen] at hs
    have bound := (Finset.card_le_card subset).trans base
    simp [weight,chosen]; omega
  | some s =>
    have subset : Finset.univ.filter (Reject m k) ⊆ exceptions ∪ dangerous m s.depth := by
      intro y hy
      by_cases ex : y ∈ exceptions
      · exact Finset.mem_union_left _ ex
      · obtain ⟨t,ht,mem⟩ := outside (Finset.mem_filter.mp hy).2 ex
        exact Finset.mem_union_right _ (Option.some.inj (ht.symm.trans chosen) ▸ mem)
    have add := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
    have c := danger_card m s.depth
    have f := Nat.mul_le_mul_left (atDepth m s.depth).card (normalized_fiber s.depth)
    have mass' := Nat.mul_le_mul_right (1221263 * 2^18 * work s.depth) (paid_mass_per_depth m s.depth)
    simp only [weight,chosen,Option.map_some,Option.getD_some]
    calc
      _ ≤ 1000000 * ((2*keys.card+1) + (atDepth m s.depth).card * fiberSize s.depth) :=
        Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := by nlinarith only [f,mass']

end
end CommitGolfCandidate.Reconstruction.Binding
