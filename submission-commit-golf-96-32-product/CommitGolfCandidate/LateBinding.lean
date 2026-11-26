import CommitGolfCandidate.LateModel

namespace CommitGolfCandidate.Late
open CommitGolf

/-- The four actual queries in program order, including the input of each branch. -/
def inputs (h : Compression) (odd : Bool) (s : Salt) (v : Entry) : List Block :=
  let x := firstBlock v
  let y := middleBlock v (h x)
  let z := lastBlock v
  [x, y, z, finalBlock odd s (h y) (h z)]

private theorem append_eq {m n : Nat} {a c : BitVec m} {b d : BitVec n} :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  constructor
  · intro e
    constructor
    · simpa only [BitVec.extractLsb'_append_eq_left] using
        congrArg (fun x : BitVec (m+n) => x.extractLsb' n m) e
    · simpa only [BitVec.extractLsb'_append_eq_right] using
        congrArg (fun x : BitVec (m+n) => x.extractLsb' 0 n) e
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem final_injective (odd : Bool) {s t : Salt} {a b c d : Digest}
    (eq : finalBlock odd s a b = finalBlock odd t c d) : s = t ∧ a = c ∧ b = d := by
  cases odd
  · obtain ⟨s0b, ac⟩ := append_eq.mp eq
    obtain ⟨s0, bd⟩ := append_eq.mp s0b
    exact ⟨(append_eq.mp s0).1, ac, bd⟩
  · obtain ⟨ba0, st⟩ := append_eq.mp eq
    obtain ⟨ba, _⟩ := append_eq.mp ba0
    exact ⟨st, (append_eq.mp ba).2, (append_eq.mp ba).1⟩

private theorem middle_injective {v w : Entry} {u u' : Digest}
    (eq : middleBlock v u = middleBlock w u') :
    u = u' ∧ v.extractLsb' 768 512 = w.extractLsb' 768 512 :=
  (append_eq.mp eq).symm

private theorem chunks_determine_entry {v w : Entry} (x : firstBlock v = firstBlock w)
    (y : v.extractLsb' 768 512 = w.extractLsb' 768 512) (z : lastBlock v = lastBlock w) :
    v = w := by
  have rebuild (e : Entry) :
      lastBlock e ++ (e.extractLsb' 768 512 ++ firstBlock e) = e := by
    unfold lastBlock firstBlock
    have lower := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
      (x := e) (len₂ := 512) (show 768 = 0 + 768 by rfl)
    exact (congrArg (fun x : BitVec 1280 => e.extractLsb' 1280 768 ++ x) lower).trans
      (BitVec.extractLsb'_append_extractLsb' (x := e) (w := 768) (len := 1280))
  calc v = _ := (rebuild v).symm
       _ = _ := by rw [x, y, z]
       _ = w := rebuild w

/-- Different entries at the same index with the same leaf digest yield a collision
between queries actually made by the respective four-call replays. -/
theorem leaf_collision (h : Compression) (odd : Bool) (s t : Salt) (v w : Entry)
    (different : v ≠ w) (same : leaf h odd s v = leaf h odd t w) :
    ∃ x ∈ inputs h odd s v, ∃ y ∈ inputs h odd t w, x ≠ y ∧ h x = h y := by
  let a := middleBlock v (h (firstBlock v))
  let b := lastBlock v
  let c := middleBlock w (h (firstBlock w))
  let d := lastBlock w
  let f := finalBlock odd s (h a) (h b)
  let g := finalBlock odd t (h c) (h d)
  change h f = h g at same
  change ∃ x ∈ [firstBlock v, a, b, f], ∃ y ∈ [firstBlock w, c, d, g], _
  by_cases fg : f = g
  · obtain ⟨_, ac, bd⟩ := final_injective odd fg
    by_cases xy : a = c
    · obtain ⟨uv, mid⟩ := middle_injective xy
      by_cases last : b = d
      · have first : firstBlock v ≠ firstBlock w := fun e =>
          different (chunks_determine_entry e mid last)
        exact ⟨_, by simp, _, by simp, first, uv⟩
      · exact ⟨b, by simp, d, by simp, last, bd⟩
    · exact ⟨a, by simp, c, by simp, xy, ac⟩
  · exact ⟨f, by simp, g, by simp, fg, same⟩

end CommitGolfCandidate.Late
