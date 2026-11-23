import CommitGolfCandidate.TwoPermutationPackedCapFinish
import CommitGolfCandidate.TwoPermutationPackedNearCap

/-! # One-byte search: 128 frontier nodes

A subtree with `h+1` levels has at most `2^h` frontier nodes. With 128 = 2^7 for the whole cap, every node on the
right spine down to 127 is marked, the subtree at 255 contributes exactly one node, and that node, the last of the
frontier, is the two-load pick (`groupPick`). -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling RiscvZkvm.Rv64

theorem marked_child (groups : List Nat) (node h : Nat) (marked : capIsMarked groups node (h+1) = true) :
    capIsMarked groups (2*node) h = true ∨ capIsMarked groups (2*node+1) h = true := by
  simp only [capIsMarked, List.any_eq_true, beq_iff_eq] at marked ⊢
  obtain ⟨g, member, at_⟩ := marked
  have split : g/2^h = 2*node ∨ g/2^h = 2*node+1 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul] at at_
    omega
  rcases split with e | e
  · exact Or.inl ⟨g, member, e⟩
  · exact Or.inr ⟨g, member, e⟩

theorem frontier_bound (groups : List Nat) : ∀ h node, (capFrontierNodes groups node (h+1)).length ≤ 2^h := by
  intro h
  induction h with
  | zero =>
    intro node
    simp only [capFrontierNodes]
    split
    · next marked =>
      rcases marked_child groups node 0 marked with a | b
      · simp [a]; split <;> simp
      · simp [b]; split <;> simp
    · simp
  | succ h ih =>
    intro node
    rw [capFrontierNodes]
    split
    · rw [List.length_append, Nat.pow_succ]
      have := ih (2*node)
      have := ih (2*node+1)
      omega
    · simp only [List.length_singleton]
      exact Nat.one_le_two_pow

/-- A full subtree (`2^h` frontier nodes, h ≥ 1) has its root marked and both halves full. -/
theorem frontier_full (groups : List Nat) (h node : Nat) (one : 1 ≤ h)
    (full : (capFrontierNodes groups node (h+1)).length = 2^h) :
    capIsMarked groups node (h+1) = true ∧
      (capFrontierNodes groups (2*node) h).length = 2^(h-1) ∧
      (capFrontierNodes groups (2*node+1) h).length = 2^(h-1) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h'+1 := ⟨h-1, by omega⟩
  rw [capFrontierNodes] at full
  split at full
  · next marked =>
    rw [List.length_append] at full
    have a := frontier_bound groups h' (2*node)
    have b := frontier_bound groups h' (2*node+1)
    rw [Nat.pow_succ] at full
    exact ⟨marked, by simp only [Nat.add_sub_cancel]; omega, by simp only [Nat.add_sub_cancel]; omega⟩
  · simp only [List.length_singleton] at full
    have : 2 ≤ 2^(h'+1) := by rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := h'); omega
    omega

/-- With 128 frontier nodes the right spine down to 127 is marked, and the last frontier node is the pick. -/
theorem full_frontier_pick (groups : List Nat) (full : (capFrontierNodes groups 1 8).length = 128) :
    capIsMarked groups 127 2 = true ∧
      groupPick groups = some ((capFrontierNodes groups 1 8).getLast?.getD 0) := by
  -- walk down the right spine: 1, 3, 7, 15, 31, 63, 127
  obtain ⟨m1, _, r1⟩ := frontier_full groups 7 1 (by decide) full
  obtain ⟨m3, _, r3⟩ := frontier_full groups 6 3 (by decide) (by simpa using r1)
  obtain ⟨m7, _, r7⟩ := frontier_full groups 5 7 (by decide) (by simpa using r3)
  obtain ⟨m15, _, r15⟩ := frontier_full groups 4 15 (by decide) (by simpa using r7)
  obtain ⟨m31, _, r31⟩ := frontier_full groups 3 31 (by decide) (by simpa using r15)
  obtain ⟨m63, _, r63⟩ := frontier_full groups 2 63 (by decide) (by simpa using r31)
  obtain ⟨m127, _, r127⟩ := frontier_full groups 1 127 (by decide) (by simpa using r63)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow] at r127
  have last (node h : Nat) (marked : capIsMarked groups node (h+1) = true)
      (some : (capFrontierNodes groups (2*node+1) h) ≠ []) :
      (capFrontierNodes groups node (h+1)).getLast? = (capFrontierNodes groups (2*node+1) h).getLast? := by
    rw [capFrontierNodes, if_pos marked, List.getLast?_append]
    cases e : (capFrontierNodes groups (2*node+1) h).getLast? with
    | none => simp [List.getLast?_eq_none_iff] at e; exact absurd e some
    | some x => simp
  have nonempty (node h : Nat) (n : Nat) (len : (capFrontierNodes groups node h).length = n) (pos : 0 < n) :
      capFrontierNodes groups node h ≠ [] := by
    intro e; rw [e] at len; simp at len; omega
  have chain : (capFrontierNodes groups 1 8).getLast? = (capFrontierNodes groups 255 1).getLast? := by
    rw [last 1 7 m1 (nonempty _ _ _ r1 (by decide)), last 3 6 m3 (nonempty _ _ _ r3 (by decide)),
      last 7 5 m7 (nonempty _ _ _ r7 (by decide)), last 15 4 m15 (nonempty _ _ _ r15 (by decide)),
      last 31 3 m31 (nonempty _ _ _ r31 (by decide)), last 63 2 m63 (nonempty _ _ _ r63 (by decide)),
      last 127 1 m127 (nonempty _ _ _ r127 (by decide))]
  refine ⟨m127, ?_⟩
  rw [chain]
  -- the subtree at 255 has exactly one frontier node
  simp only [capFrontierNodes] at r127 ⊢
  unfold groupPick
  by_cases m255 : capIsMarked groups 255 (0+1) = true
  · rw [if_pos m255] at r127 ⊢
    by_cases a : capIsMarked groups 511 0 = true <;> by_cases b : capIsMarked groups 510 0 = true <;>
      simp_all
  · rw [if_neg m255] at ⊢
    have a : capIsMarked groups 511 0 = false := by
      by_contra x
      have := marked_child groups 255 0
      simp only [capIsMarked, List.any_eq_true, beq_iff_eq, Bool.not_eq_false] at x m255
      obtain ⟨g, member, at_⟩ := x
      exact m255 ⟨g, member, by simp at at_ ⊢; omega⟩
    have b : capIsMarked groups 510 0 = false := by
      by_contra x
      simp only [capIsMarked, List.any_eq_true, beq_iff_eq, Bool.not_eq_false] at x m255
      obtain ⟨g, member, at_⟩ := x
      exact m255 ⟨g, member, by simp at at_ ⊢; omega⟩
    simp [a, b]

/-! ### Distinct frontier nodes -/

theorem frontier_below (groups : List Nat) :
    ∀ h node x, x ∈ capFrontierNodes groups node h → ∃ t, t ≤ h ∧ x/2^t = node := by
  intro h
  induction h with
  | zero =>
    intro node x member
    simp only [capFrontierNodes] at member
    split at member
    · simp at member
    · simp at member; exact ⟨0, le_refl _, by simp [member]⟩
  | succ h ih =>
    intro node x member
    rw [capFrontierNodes] at member
    split at member
    · rcases List.mem_append.mp member with a | b
      · obtain ⟨t, th, at_⟩ := ih _ _ a
        refine ⟨t+1, by omega, ?_⟩
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, at_]; omega
      · obtain ⟨t, th, at_⟩ := ih _ _ b
        refine ⟨t+1, by omega, ?_⟩
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, at_]; omega
    · simp at member; exact ⟨0, by omega, by simp [member]⟩

theorem apart (n x t s : Nat) (pos : 0 < n) (left : x/2^t = 2*n) (right : x/2^s = 2*n+1) : False := by
  rcases Nat.lt_trichotomy t s with lt | eq | gt
  · have e : x/2^s = (x/2^t)/2^(s-t) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show t+(s-t) = s by omega]
    rw [e, left] at right
    have : 2*n/2^(s-t) ≤ 2*n/2 := Nat.div_le_div_left (Nat.le_self_pow (by omega) 2) (by decide)
    omega
  · subst eq; omega
  · have e : x/2^t = (x/2^s)/2^(t-s) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show s+(t-s) = t by omega]
    rw [e, right] at left
    have : (2*n+1)/2^(t-s) ≤ (2*n+1)/2 := Nat.div_le_div_left (Nat.le_self_pow (by omega) 2) (by decide)
    omega

theorem frontier_nodup (groups : List Nat) : ∀ h node, 0 < node → (capFrontierNodes groups node h).Nodup := by
  intro h
  induction h with
  | zero => intro node _; simp only [capFrontierNodes]; split <;> simp
  | succ h ih =>
    intro node pos
    rw [capFrontierNodes]
    split
    · rw [List.nodup_append]
      refine ⟨ih _ (by omega), ih _ (by omega), ?_⟩
      intro x a y b same
      subst same
      obtain ⟨t, _, at_⟩ := frontier_below groups h _ _ a
      obtain ⟨s, _, bt⟩ := frontier_below groups h _ _ b
      exact apart node x t s pos at_ bt
    · simp

/-! ### The honest patch -/

theorem wbit (H : BitVec 256) (i : Nat) (hi : i < 256) :
    (pad238 (clearTop H)).getLsbD i = (decide (i < 230) && H.getLsbD i) := by
  simp only [pad238, clearTop, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases a : i < 230
  · simp [a, show i < 238 by omega, hi]
  · by_cases b : i < 238
    · simp [a, b]; omega
    · simp [a, b]

theorem rh_bit (x : BitVec 64) (h : BitVec 16) (j : Nat) (hj : j < 64) :
    (replaceHalfword x 2 h).getLsbD j = if 32 ≤ j ∧ j < 48 then h.getLsbD (j-32) else x.getLsbD j := by
  interval_cases j <;> simp [replaceHalfword]

theorem eh_bit (x : BitVec 64) (t : Nat) (ht : t < 16) : (extractHalfword x 2).getLsbD t = x.getLsbD (32+t) := by
  interval_cases t <;> simp [extractHalfword]

theorem ph_bit (h : BitVec 16) (g : BitVec 64) (t : Nat) (ht : t < 16) :
    (patchHalf h g).getLsbD t = if t < 6 then h.getLsbD t else g.getLsbD (t-6) := by
  interval_cases t <;> simp [patchHalf, signExtend12]

/-- The honest patch: for an honest digest `H` (bits 238.. zero), trial `g = H[230..237]` turns the cleared
`pad238 (clearTop H)` back into `H`. -/
theorem honest_patch (H : BitVec 256) (high : ∀ i, 238 ≤ i → i < 256 → H.getLsbD i = false) :
    let w := pad238 (clearTop H)
    let g := (H.extractLsb' 230 8).toNat
    (∀ k < 3, w.extractLsb' (64*k) 64 = H.extractLsb' (64*k) 64) ∧
      replaceHalfword (w.extractLsb' 192 64) 2
        (patchHalf (extractHalfword (w.extractLsb' 192 64) 2) (BitVec.ofNat 64 g)) = H.extractLsb' 192 64 := by
  intro w g
  have wb (i : Nat) (hi : i < 256) : w.getLsbD i = (decide (i < 230) && H.getLsbD i) := wbit H i hi
  constructor
  · intro k hk
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', wb _ (by omega)]
    simp [hj, show 64*k+j < 230 by omega]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have gbit (t : Nat) : (BitVec.ofNat 64 g).getLsbD t = (decide (t < 8) && H.getLsbD (230+t)) := by
      simp only [g, BitVec.getLsbD_ofNat, BitVec.testBit_toNat, BitVec.getLsbD_extractLsb']
      by_cases a : t < 8 <;> by_cases b : t < 64 <;> simp [a, b] <;> omega
    rw [rh_bit _ _ j hj, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    by_cases mid : 32 ≤ j ∧ j < 48
    · rw [if_pos mid, ph_bit _ _ _ (by omega)]
      by_cases low : j-32 < 6
      · rw [if_pos low, eh_bit _ _ (by omega), BitVec.getLsbD_extractLsb', wb _ (by omega)]
        simp [show 32+(j-32) < 64 by omega, show 192+(32+(j-32)) = 192+j by omega,
          show 192+j < 230 by omega, hj]
      · rw [if_neg low, gbit]
        by_cases top : j-32-6 < 8
        · simp [top, show 230+(j-32-6) = 192+j by omega, hj]
        · simp [top, high (192+j) (by omega) (by omega)]
    · rw [if_neg mid, BitVec.getLsbD_extractLsb', wb _ (by omega)]
      simp only [hj, decide_true, Bool.true_and]
      by_cases a : j < 32
      · simp [show 192+j < 230 by omega]
      · simp [show ¬ 192+j < 230 by omega, high (192+j) (by omega) (by omega)]

theorem clear_zero (H : BitVec 256) (high : ∀ i, 238 ≤ i → i < 256 → H.getLsbD i = false)
    (zero : (H.extractLsb' 230 8).toNat = 0) : pad238 (clearTop H) = H := by
  have z : H.extractLsb' 230 8 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using zero)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [wbit H i hi]
  by_cases a : i < 230
  · simp [a]
  · by_cases b : i < 238
    · have := congrArg (fun x : BitVec 8 => x.getLsbD (i-230)) z
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, show i-230 < 8 by omega, decide_true,
        Bool.true_and, show 230+(i-230) = i by omega] at this
      simp [a, this]
    · simp [a, high i (by omega) hi]

end TwoPermutationPrototype.Packed.Checker
