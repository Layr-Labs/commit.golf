import CommitGolfCandidate.S3PermPinCall

/-! Conditional answer fibers of an abstract pinned two-call hash. Forward
queries have no unary bad answers. -/

namespace CommitGolfCandidate.Permutation.PinCall
open Finset
variable {S X1 R C P M2 D : Type} [Fintype S] [DecidableEq S]

theorem answer_fibers (H : PinCall S X1 R C P M2 D)
    [Fintype R] [Fintype P] [Fintype M2] [DecidableEq C] [DecidableEq P] [DecidableEq D]
    (Kd Kc Kp K2 k : Nat)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hKp : ∀ p : P, (univ.filter fun s => H.pin s = p).card ≤ Kp)
    (hK2 : Fintype.card R * Fintype.card P * Fintype.card M2 ≤ K2)
    (hkf : Kd + 2*Kc ≤ k) (hki : K2 + 2*Kp ≤ k) :
    (∀ x old, ∃ F : Finset S, F.card ≤ k ∧
      ∀ y, H.badSpec.pair ⟨.fwd,x,y⟩ old → y ∈ F) ∧
    (∀ x y, ¬ H.badSpec.single ⟨.fwd,x,y⟩) ∧
    (∀ y old, ∃ F : Finset S, F.card ≤ k ∧
      ∀ x, H.badSpec.pair ⟨.inv,x,y⟩ old → x ∈ F) ∧
    (∀ y, ∃ F : Finset S, F.card ≤ K2 ∧
      ∀ x, H.badSpec.single ⟨.inv,x,y⟩ → x ∈ F) := by
  classical
  have hslot : ∀ c : C, (univ.image fun p : R × P × M2 => H.enc2 (p.1, c, p.2.1, p.2.2)).card ≤
      K2 := by
    intro c
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ← mul_assoc]
    exact hK2
  refine ⟨?_,?_,?_,?_⟩
  · intro x old
    refine ⟨(univ.filter fun s => H.trunc s = H.trunc old.out) ∪
      (univ.filter fun s => H.chop s = H.chop old.out) ∪
      (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m)), ?_, ?_⟩
    · have h3 : (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m)).card ≤
          Kc := by
        rcases (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m)
          ).eq_empty_or_nonempty with h0 | ⟨y0, hy0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨r0, p0, m0, h0⟩ := (Finset.mem_filter.1 hy0).2
          refine (Finset.card_le_card fun y hy => ?_).trans (hKc (H.chop y0))
          obtain ⟨r, p, m, h⟩ := (Finset.mem_filter.1 hy).2
          have hinj := H.enc2_inj (h.symm.trans h0)
          simp only [Prod.mk.injEq] at hinj
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hinj.2.1⟩
      have := hKd (H.trunc old.out)
      have := hKc (H.chop old.out)
      have h12 := Finset.card_union_le (univ.filter fun s => H.trunc s = H.trunc old.out)
        (univ.filter fun s => H.chop s = H.chop old.out)
      have h123 := Finset.card_union_le
        ((univ.filter fun s => H.trunc s = H.trunc old.out) ∪
          (univ.filter fun s => H.chop s = H.chop old.out))
        (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m))
      omega
    · intro y hy
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with h | h | h | h | h | h
      · exact Or.inl (Or.inl h.2)
      · exact Or.inl (Or.inr h.2)
      · exact Or.inr h.2
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
  · intro x y hs
    exact absurd hs.1 (by simp)
  · intro y old
    refine ⟨(univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop old.out, p.2.1, p.2.2)) ∪
      (univ.filter fun s => H.pin s = H.pin old.inp) ∪
      (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m)), ?_, ?_⟩
    · have h6 : (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m)).card ≤
          Kp := by
        rcases (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m)
          ).eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨r0, m0, h0⟩ := (Finset.mem_filter.1 hx0).2
          refine (Finset.card_le_card fun x hx => ?_).trans (hKp (H.pin x0))
          obtain ⟨r, m, h⟩ := (Finset.mem_filter.1 hx).2
          have hinj := H.enc2_inj (h.symm.trans h0)
          simp only [Prod.mk.injEq] at hinj
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hinj.2.2.1⟩
      have := hslot (H.chop old.out)
      have := hKp (H.pin old.inp)
      have h45 := Finset.card_union_le
        (univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop old.out, p.2.1, p.2.2))
        (univ.filter fun s => H.pin s = H.pin old.inp)
      have h456 := Finset.card_union_le
        ((univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop old.out, p.2.1, p.2.2)) ∪
          (univ.filter fun s => H.pin s = H.pin old.inp))
        (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m))
      omega
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with h | h | h | h | h | h
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · obtain ⟨r, p, m, h⟩ := h.2
        exact Or.inl (Or.inl (Finset.mem_image.2 ⟨(r, p, m), Finset.mem_univ _, h.symm⟩))
      · exact Or.inl (Or.inr h.2.1)
      · exact Or.inr h.2
  · intro y
    refine ⟨univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop y, p.2.1, p.2.2), hslot _,
      fun x hx => ?_⟩
    obtain ⟨r, m, h⟩ := hx.2
    exact Finset.mem_image.2 ⟨(r, H.pin x, m), Finset.mem_univ _, h.symm⟩

end CommitGolfCandidate.Permutation.PinCall
