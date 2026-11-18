import CommitGolfCandidate.S3PermTwoCall

/-!
# The two-call leaf hash without a fixed capacity: collision resistance from an overlap

The earlier entry made the first call safe against inverse queries with a fixed prefix (`InverseHitsPrefix`).
Here every state is a valid first-call input. Instead, a field of the first-call input is repeated
in the second-call input (leaf bytes 144..200 enter both calls):

    o1 = π (enc1 x1)
    o2 = π (enc2 (r, chop o1, m2))        with  ovB (enc2 (r, c, m2)) = ovA (enc1 x1)
    digest = trunc o2

`ovA` reads the repeated field of a state used as a first-call input, `ovB` reads it from a state
used as a second-call input. A leaf input is `Consistent` when the two agree.

Bad events (fresh answer `new` against an older entry `old`): the four pair events of
S3PermTwoCall (digest collision, chain collision, inverse hits chain, forward hits slot), two
overlap events (a fresh inverse answer repeats the overlap field of an older entry, read at
first-call or at second-call position), and one event of a single entry (a fresh inverse answer is
a second-call input whose chaining slot is the chaining part of its own reply).

`collision_imp_bad` is the deterministic extraction lemma; `prob_bad_le` the probability bound.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]
variable {X1 R C M2 D O : Type}

/-- Overlap fields of a two-call hash: `ovA` reads the repeated field of a state used as a
first-call input, `ovB` the same field of a state used as a second-call input. -/
structure Overlap (H : TwoCall S X1 R C M2 D) (O : Type) where
  ovA : S → O
  ovB : S → O

namespace Overlap

variable {H : TwoCall S X1 R C M2 D} (V : Overlap H O)

/-- The second message part repeats the overlap field of the first-call input. -/
def Consistent (i : X1 × R × M2) : Prop :=
  ∀ c : C, V.ovB (H.enc2 (i.2.1, c, i.2.2)) = V.ovA (H.enc1 i.1)

/-- The bad events of the overlap proof, see the file header. -/
def badSpec : BadSpec S where
  pair new old :=
    (new.dir = .fwd ∧ H.trunc new.out = H.trunc old.out) ∨
    (new.dir = .fwd ∧ H.chop new.out = H.chop old.out) ∨
    (new.dir = .inv ∧ ∃ r m, new.inp = H.enc2 (r, H.chop old.out, m)) ∨
    (new.dir = .fwd ∧ ∃ r m, old.inp = H.enc2 (r, H.chop new.out, m)) ∨
    (new.dir = .inv ∧ V.ovA new.inp = V.ovA old.inp) ∨
    (new.dir = .inv ∧ V.ovA new.inp = V.ovB old.inp)
  single e := e.dir = .inv ∧ ∃ r m, e.inp = H.enc2 (r, H.chop e.out, m)

/-- **Extraction (deterministic).** If a table holds the four calls of two different consistent
leaf inputs with the same digest, it contains a bad event. -/
theorem collision_imp_bad {t : Trace S} {i i' : X1 × R × M2} {d : D} (hne : i ≠ i')
    (hc : V.Consistent i) (hc' : V.Consistent i')
    (h : H.Evaluates t i d) (h' : H.Evaluates t i' d) : ¬ V.badSpec.Good t := by
  intro hg
  obtain ⟨e1, he1, e2, he2, hx1, hx2, hd⟩ := h
  obtain ⟨e1', he1', e2', he2', hx1', hx2', hd'⟩ := h'
  -- a second-call entry `a2` whose digest part equals that of another entry `b2`
  have keyA : ∀ (a1 a2 b2 : Entry S) (j : X1 × R × M2), V.Consistent j → a1 ∈ t → a2 ∈ t →
      a1.inp = H.enc1 j.1 → a2.inp = H.enc2 (j.2.1, H.chop a1.out, j.2.2) →
      H.trunc a2.out = H.trunc b2.out → ¬ V.badSpec.pair a2 b2 → False := by
    intro a1 a2 b2 j hj ha1 ha2 hj1 hj2 htr hnp
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
            refine h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hdir1, ?_⟩)))))
            rw [hj2, hj1]
            exact (hj (H.chop a1.out)).symm
  -- first-call entries `a1`, `b1` with equal chaining parts and equal overlap fields
  have keyB : ∀ (a1 b1 : Entry S), H.chop a1.out = H.chop b1.out →
      V.ovA a1.inp = V.ovA b1.inp → ¬ V.badSpec.pair a1 b1 → False := by
    intro a1 b1 hch hov hnp
    cases hdir : a1.dir with
    | fwd => exact hnp (Or.inr (Or.inl ⟨hdir, hch⟩))
    | inv => exact hnp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdir, hov⟩)))))
  by_cases h2 : e2 = e2'
  · have hinp : H.enc2 (i.2.1, H.chop e1.out, i.2.2) =
        H.enc2 (i'.2.1, H.chop e1'.out, i'.2.2) := by rw [← hx2, ← hx2', h2]
    have hinj := H.enc2_inj hinp
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hr, hch, hm⟩ := hinj
    have hx : i.1 ≠ i'.1 := fun hx => hne (Prod.ext hx (Prod.ext hr hm))
    have he : e1 ≠ e1' := by
      rintro rfl
      exact hx (H.enc1_inj (hx1.symm.trans hx1'))
    have hov : V.ovA e1.inp = V.ovA e1'.inp := by
      rw [hx1, hx1', ← hc (H.chop e1.out), ← hc' (H.chop e1'.out), hinp]
    rcases hg.not_pair he1 he1' he with h | h
    · exact keyB e1 e1' hch hov h
    · exact keyB e1' e1 hch.symm hov.symm h
  · rcases hg.not_pair he2 he2' h2 with h | h
    · exact keyA e1 e2 e2' i hc he1 he2 hx1 hx2 (hd.trans hd'.symm) h
    · exact keyA e1' e2' e2 i' hc' he1' he2' hx1' hx2' (hd'.trans hd.symm) h

/-- The probability of a bad event, for any strategy. `Kd` and `Kc` bound the number of states
with a given digest part and a given chaining part, `K2` the number of second-call inputs with a
given chaining slot, `Ko` the number of states with a given overlap field (first-call position). -/
theorem prob_bad_le [Fintype R] [Fintype M2] [DecidableEq C] [DecidableEq D] [DecidableEq O]
    {α : Type} (Kd Kc K2 Ko Q : ℕ) (hQ : Q < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hKo : ∀ o : O, (univ.filter fun s => V.ovA s = o).card ≤ Ko) (st : Strat S α) :
    st.prob PState.init (fun _ s' => ¬ V.badSpec.Good s'.trace ∧ s'.count ≤ Q) ≤
      unionBound (Fintype.card S) (Kd + 2 * Kc + K2 + 2 * Ko) K2 Q := by
  classical
  refine prob_not_good_le V.badSpec (Kd + 2 * Kc + K2 + 2 * Ko) K2 Q hQ ?_ ?_ ?_ ?_ st
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
    exact ⟨∅, Nat.zero_le _, fun y hy => by simp [badSpec] at hy⟩
  · intro y old
    refine ⟨(univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2)) ∪
      (univ.filter fun s => V.ovA s = V.ovA old.inp) ∪
      (univ.filter fun s => V.ovA s = V.ovB old.inp), ?_, ?_⟩
    · have h1 : (univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2)).card ≤ K2 := by
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, Fintype.card_prod]
        exact hK2
      have := hKo (V.ovA old.inp)
      have := hKo (V.ovB old.inp)
      have h12 := Finset.card_union_le
        (univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2))
        (univ.filter fun s => V.ovA s = V.ovA old.inp)
      have h123 := Finset.card_union_le
        ((univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2)) ∪
          (univ.filter fun s => V.ovA s = V.ovA old.inp))
        (univ.filter fun s => V.ovA s = V.ovB old.inp)
      omega
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
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

end Overlap

end CommitGolfCandidate.Permutation
