import CommitGolfCandidate.S3PermTwoCall

/-!
# The two-call leaf hash without a fixed prefix: collision resistance from an overlap

The same two calls as in S3PermTwoCall.lean,

    o1 = π (enc1 x1)
    o2 = π (enc2 (r, chop o1, m2))
    digest = trunc o2

but `enc1` need not have a sparse range (for the design it is the identity on the state). In its
place a leaf input `(x1, r, m2)` is *valid* when `ovA x1 = ovM m2`: a part of the first-call input
is read again by the second call. For the design `ovA` is leaf bytes 136..200 as they sit in the
first window and `ovM` the same bytes as they sit in the second window.

Seven bad events, named after the fresh answer that causes them. `new` is the entry created by
the query, `old` any older entry:

* forward, `trunc new.out = trunc old.out` (digest collision);
* forward, `chop new.out = chop old.out` (chain collision);
* inverse, `new.inp` is a second-call input whose chaining slot is `chop old.out`;
* forward, `chop new.out` is the chaining slot of the second-call input `old.inp`;
* inverse, `new.inp = enc1 x` and `old.inp = enc2 (r, c, m)` with `ovA x = ovM m`
  (a first-call input created backwards matches the overlap of an older second-call input);
* inverse, `new.inp = enc1 x` and `old.inp = enc1 x'` with `ovA x = ovA x'`
  (a first-call input created backwards has the overlap of an older first-call input);
* inverse, alone: `new.inp` is a second-call input whose chaining slot is `chop new.out`.

`overlap_collision_imp_bad` is the deterministic extraction: a table that evaluates two different
valid leaf inputs to one digest is not good. `overlap_prob_not_good_le` is the probability bound,
`overlap_probe_collision_bound` the bound for an adversary followed by a replay of leaves.

Why the events suffice. Write an evaluation as entries `e1` (first call) and `e2` (second call).
If the two second-call entries differ, their digests agree; the newer one, if created forwards,
is a digest collision. If it was created backwards, its own first-call entry `e1` is either the
same entry (the lone event), older (third event), newer and forward (fourth event) or newer and
backward (fifth event, by validity). If the two second-call entries are the same entry, the nonce,
the chaining value and `m2` agree, so the first-call inputs differ, have one chaining value and,
by validity, one overlap: the newer first-call entry is a chain collision if created forwards and
the sixth event if created backwards.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

namespace TwoCall

variable {X1 R C M2 D O : Type} (H : TwoCall S X1 R C M2 D) (ovA : X1 → O) (ovM : M2 → O)

/-- The bad events of the overlap proof, see the file header. -/
def overlapSpec : BadSpec S where
  pair new old :=
    (new.dir = .fwd ∧ H.trunc new.out = H.trunc old.out) ∨
    (new.dir = .fwd ∧ H.chop new.out = H.chop old.out) ∨
    (new.dir = .inv ∧ ∃ r m, new.inp = H.enc2 (r, H.chop old.out, m)) ∨
    (new.dir = .fwd ∧ ∃ r m, old.inp = H.enc2 (r, H.chop new.out, m)) ∨
    (new.dir = .inv ∧ ∃ x r c m, new.inp = H.enc1 x ∧ old.inp = H.enc2 (r, c, m) ∧
      ovA x = ovM m) ∨
    (new.dir = .inv ∧ ∃ x x', new.inp = H.enc1 x ∧ old.inp = H.enc1 x' ∧ ovA x = ovA x')
  single e := e.dir = .inv ∧ ∃ r m, e.inp = H.enc2 (r, H.chop e.out, m)

/-- **Extraction (deterministic).** If a table holds the calls of two different valid leaf inputs
with the same digest, it is not good. No probability and no well-formedness of the table is
needed. -/
theorem overlap_collision_imp_bad {t : Trace S} {i i' : X1 × R × M2} {d : D} (hne : i ≠ i')
    (hv : ovA i.1 = ovM i.2.2) (hv' : ovA i'.1 = ovM i'.2.2)
    (h : H.Evaluates t i d) (h' : H.Evaluates t i' d) : ¬ (H.overlapSpec ovA ovM).Good t := by
  intro hg
  obtain ⟨e1, he1, e2, he2, hx1, hx2, hd⟩ := h
  obtain ⟨e1', he1', e2', he2', hx1', hx2', hd'⟩ := h'
  -- a second-call entry `a2` whose digest part equals that of another entry `b2`, in the case
  -- where `a2` is the newer of the two
  have keyA : ∀ (a1 a2 b2 : Entry S) (j : X1 × R × M2), a1 ∈ t → a2 ∈ t →
      ovA j.1 = ovM j.2.2 → a1.inp = H.enc1 j.1 →
      a2.inp = H.enc2 (j.2.1, H.chop a1.out, j.2.2) →
      H.trunc a2.out = H.trunc b2.out → ¬ (H.overlapSpec ovA ovM).pair a2 b2 → False := by
    intro a1 a2 b2 j ha1 ha2 hjv hj1 hj2 htr hnp
    cases hdir : a2.dir with
    | fwd => exact hnp (Or.inl ⟨hdir, htr⟩)
    | inv =>
      by_cases heq : a1 = a2
      · subst heq
        exact hg.not_single ha1 ⟨hdir, j.2.1, j.2.2, hj2⟩
      · rcases hg.not_pair ha2 ha1 (Ne.symm heq) with h | h
        · exact h (Or.inr (Or.inr (Or.inl ⟨hdir, j.2.1, j.2.2, hj2⟩)))
        · cases hdir1 : a1.dir with
          | fwd => exact h (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdir1, j.2.1, j.2.2, hj2⟩))))
          | inv =>
            exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hdir1, j.1, j.2.1, H.chop a1.out, j.2.2, hj1, hj2, hjv⟩)))))
  -- a first-call entry `a1` with the chaining part and the overlap of another first-call entry
  -- `b1`, in the case where `a1` is the newer of the two
  have keyB : ∀ (a1 b1 : Entry S) (x x' : X1), a1.inp = H.enc1 x → b1.inp = H.enc1 x' →
      ovA x = ovA x' → H.chop a1.out = H.chop b1.out →
      ¬ (H.overlapSpec ovA ovM).pair a1 b1 → False := by
    intro a1 b1 x x' hx hx' hov hch hnp
    cases hdir : a1.dir with
    | fwd => exact hnp (Or.inr (Or.inl ⟨hdir, hch⟩))
    | inv =>
      exact hnp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hdir, x, x', hx, hx', hov⟩)))))
  by_cases h2 : e2 = e2'
  · have hinp : H.enc2 (i.2.1, H.chop e1.out, i.2.2) =
        H.enc2 (i'.2.1, H.chop e1'.out, i'.2.2) := by rw [← hx2, ← hx2', h2]
    have hinj := H.enc2_inj hinp
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hr, hc, hm⟩ := hinj
    have hx : i.1 ≠ i'.1 := fun hx => hne (Prod.ext hx (Prod.ext hr hm))
    have he : e1 ≠ e1' := by
      rintro rfl
      exact hx (H.enc1_inj (hx1.symm.trans hx1'))
    have hov : ovA i.1 = ovA i'.1 := by rw [hv, hv', hm]
    rcases hg.not_pair he1 he1' he with h | h
    · exact keyB e1 e1' i.1 i'.1 hx1 hx1' hov hc h
    · exact keyB e1' e1 i'.1 i.1 hx1' hx1 hov.symm hc.symm h
  · rcases hg.not_pair he2 he2' h2 with h | h
    · exact keyA e1 e2 e2' i he1 he2 hv hx1 hx2 (hd.trans hd'.symm) h
    · exact keyA e1' e2' e2 i' he1' he2' hv' hx1' hx2' (hd'.trans hd.symm) h

/-- The probability that the table is not good, for any strategy. `Kd` and `Kc` bound the number
of states with a given digest part and a given chaining part, `K2` the number of second-call
inputs with a given chaining slot, `Ko` the number of first-call inputs with a given overlap. -/
theorem overlap_prob_not_good_le [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C]
    [DecidableEq D] [DecidableEq O] {α : Type} (Kd Kc K2 Ko Q : ℕ) (hQ : Q < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hKo : ∀ o : O, (univ.filter fun x : X1 => ovA x = o).card ≤ Ko) (st : Strat S α) :
    st.prob PState.init (fun _ s' => ¬ (H.overlapSpec ovA ovM).Good s'.trace ∧ s'.count ≤ Q) ≤
      unionBound (Fintype.card S) (Kd + 2 * Kc + K2 + 2 * Ko) K2 Q := by
  classical
  refine prob_not_good_le (H.overlapSpec ovA ovM) (Kd + 2 * Kc + K2 + 2 * Ko) K2 Q hQ
    ?_ ?_ ?_ ?_ st
  · intro x old
    refine ⟨(univ.filter fun s => H.trunc s = H.trunc old.out) ∪
      (univ.filter fun s => H.chop s = H.chop old.out) ∪
      (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m)), ?_, ?_⟩
    · have h3 : (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m)).card ≤ Kc := by
        rcases (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m)).eq_empty_or_nonempty
          with h0 | ⟨y0, hy0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨r0, m0, h0⟩ := (Finset.mem_filter.1 hy0).2
          refine (Finset.card_le_card fun y hy => ?_).trans (hKc (H.chop y0))
          obtain ⟨r, m, h⟩ := (Finset.mem_filter.1 hy).2
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
        (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m))
      omega
    · intro y hy
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with h | h | h | h | h | h
      · exact Or.inl (Or.inl h.2)
      · exact Or.inl (Or.inr h.2)
      · exact absurd h.1 (by simp)
      · exact Or.inr h.2
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
  · intro x
    exact ⟨∅, Nat.zero_le _, fun y hy => by simp [overlapSpec] at hy⟩
  · intro y old
    refine ⟨(univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2)) ∪
      (univ.filter fun s => ∃ x r c m, s = H.enc1 x ∧ old.inp = H.enc2 (r, c, m) ∧
        ovA x = ovM m) ∪
      (univ.filter fun s => ∃ x x', s = H.enc1 x ∧ old.inp = H.enc1 x' ∧ ovA x = ovA x'),
      ?_, ?_⟩
    · have h1 : (univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2)).card ≤ K2 := by
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, Fintype.card_prod]
        exact hK2
      have h2 : (univ.filter fun s => ∃ x r c m, s = H.enc1 x ∧ old.inp = H.enc2 (r, c, m) ∧
          ovA x = ovM m).card ≤ Ko := by
        rcases (univ.filter fun s => ∃ x r c m, s = H.enc1 x ∧ old.inp = H.enc2 (r, c, m) ∧
          ovA x = ovM m).eq_empty_or_nonempty with h0 | ⟨s0, hs0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨x0, r0, c0, m0, -, hold0, -⟩ := (Finset.mem_filter.1 hs0).2
          refine (Finset.card_le_card (t := (univ.filter fun x : X1 => ovA x = ovM m0).image
            H.enc1) fun s hs => ?_).trans (Finset.card_image_le.trans (hKo (ovM m0)))
          obtain ⟨x, r, c, m, hsx, hold, hov⟩ := (Finset.mem_filter.1 hs).2
          have hinj := H.enc2_inj (hold.symm.trans hold0)
          simp only [Prod.mk.injEq] at hinj
          refine Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hsx.symm⟩
          rw [hov, hinj.2.2]
      have h3 : (univ.filter fun s => ∃ x x', s = H.enc1 x ∧ old.inp = H.enc1 x' ∧
          ovA x = ovA x').card ≤ Ko := by
        rcases (univ.filter fun s => ∃ x x', s = H.enc1 x ∧ old.inp = H.enc1 x' ∧
          ovA x = ovA x').eq_empty_or_nonempty with h0 | ⟨s0, hs0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨x0, x0', -, hold0, -⟩ := (Finset.mem_filter.1 hs0).2
          refine (Finset.card_le_card (t := (univ.filter fun x : X1 => ovA x = ovA x0').image
            H.enc1) fun s hs => ?_).trans (Finset.card_image_le.trans (hKo (ovA x0')))
          obtain ⟨x, x', hsx, hold, hov⟩ := (Finset.mem_filter.1 hs).2
          have hx' : x' = x0' := H.enc1_inj (hold.symm.trans hold0)
          refine Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hsx.symm⟩
          rw [hov, hx']
      have h12 := Finset.card_union_le
        (univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2))
        (univ.filter fun s => ∃ x r c m, s = H.enc1 x ∧ old.inp = H.enc2 (r, c, m) ∧
          ovA x = ovM m)
      have h123 := Finset.card_union_le
        ((univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2)) ∪
          (univ.filter fun s => ∃ x r c m, s = H.enc1 x ∧ old.inp = H.enc2 (r, c, m) ∧
            ovA x = ovM m))
        (univ.filter fun s => ∃ x x', s = H.enc1 x ∧ old.inp = H.enc1 x' ∧ ovA x = ovA x')
      omega
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      rcases hx with h | h | h | h | h | h
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · obtain ⟨r, m, h⟩ := h.2
        exact Or.inl (Or.inl ⟨(r, m), h.symm⟩)
      · exact absurd h.1 (by simp)
      · exact Or.inl (Or.inr h.2)
      · exact Or.inr h.2
  · intro y
    refine ⟨univ.image fun p : R × M2 => H.enc2 (p.1, H.chop y, p.2), ?_, fun x hx => ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_prod]
      exact hK2
    · obtain ⟨r, m, h⟩ := hx.2
      exact Finset.mem_image.2 ⟨(r, m), Finset.mem_univ _, h.symm⟩

end TwoCall

end CommitGolfCandidate.Permutation
