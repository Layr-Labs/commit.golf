import CommitGolfCandidate.PermLean.Hazard
import ToMathlib.Data.BitVec

/-! # Spec v1 (PL-A) permutation leaf hash: first-occurrence analysis, counting, arithmetic

Spec v1 (PL-A): for a 256-byte value `v` (little-endian bytes,
byte `j` = bits `[8j, 8j+8)`, as in the contract's `readBuffer`)

* `x₁ = v[0..200)`, `y₁ = P x₁`,
* `x₂ = y₁[88..200) ‖ v[168..256)` (112-byte link, then 88 value bytes; `v[168..200)` is read by
  both calls),
* `h = (P x₂)[0..32)`; the leaf digest is `C(nonce ‖ 0^8 ‖ h)` (not used here).

This file proves that two different values with equal `h`, whose four permutation evaluations are
all in a log, force a *hazard* in that log (`leaf_hash_unclean`), defines the hazard sets
`leafHazard` with their size bounds, and bounds their total probability by `q / 2^121`.

The case analysis is stated for an abstract `Layout` (`Layout.chain_collision`), so the salted
variant (spec v0) is the same theorem with other slices. -/

namespace PermLean
open CommitGolf OracleComp
open scoped ENNReal

/-! ## Order of two log entries -/

/-- Two different entries of a log: one of them occurs before an occurrence of the other. -/
theorem order_of_ne {α : Type} {log : Log α} {e e' : Entry α} (he : e ∈ log) (he' : e' ∈ log)
    (ne : e ≠ e') :
    (∃ pre post, log = pre ++ e' :: post ∧ e ∈ pre) ∨
      (∃ pre post, log = pre ++ e :: post ∧ e' ∈ pre) := by
  induction log with
  | nil => simp at he
  | cons a rest ih =>
    rcases List.mem_cons.mp he with first | inRest
    · subst first
      have later : e' ∈ rest := (List.mem_cons.mp he').resolve_left (Ne.symm ne)
      obtain ⟨s, t, rfl⟩ := List.append_of_mem later
      exact Or.inl ⟨e :: s, t, by simp, by simp⟩
    · rcases List.mem_cons.mp he' with first' | inRest'
      · subst first'
        obtain ⟨s, t, rfl⟩ := List.append_of_mem inRest
        exact Or.inr ⟨e' :: s, t, by simp, by simp⟩
      · rcases ih inRest inRest' with ⟨pre, post, eq, mem⟩ | ⟨pre, post, eq, mem⟩
        · exact Or.inl ⟨a :: pre, post, by simp [eq], List.mem_cons_of_mem _ mem⟩
        · exact Or.inr ⟨a :: pre, post, by simp [eq], List.mem_cons_of_mem _ mem⟩

/-! ## Clean logs -/

/-- Every entry of the log avoided its hazard set at the moment it was appended. -/
def Clean (H : Hazard) (log : Log Word) : Prop :=
  ∀ pre e post, log = pre ++ e :: post →
    (e.inverse = false → e.output ∉ H.forward pre e.input) ∧
    (e.inverse = true → e.input ∉ H.inverse pre e.output)

/-! ## The two-call chain, abstractly -/

/-- The slices of a two-call chain `x₁ ↦ y₁`, `x₂ ↦ y₂`: the digest slice of `y₂`, the link
(`link₁ y₁ = link₂ x₂`) and the overlap (`overlap₁ x₁ = overlap₂ x₂`). -/
structure Layout (L : ℕ) where
  digest : Word → BitVec 256
  link₁ : Word → BitVec L
  link₂ : Word → BitVec L
  overlap₁ : Word → BitVec 256
  overlap₂ : Word → BitVec 256

variable {L : ℕ}

/-- A fresh forward answer `y` is bad after `pre` if its digest slice repeats an earlier digest
slice, or its link slice repeats an earlier input link or an earlier output link. -/
def Layout.forwardBad (lay : Layout L) (pre : Log Word) (y : Word) : Prop :=
  lay.digest y ∈ pre.map (fun e => lay.digest e.output) ∨
  lay.link₁ y ∈ pre.map (fun e => lay.link₂ e.input) ∨
  lay.link₁ y ∈ pre.map (fun e => lay.link₁ e.output)

/-- A fresh inverse answer `x` to the query `y` is bad after `pre` if it links to `y` itself or to
an earlier output, or its first-call overlap repeats an earlier second-call or first-call overlap. -/
def Layout.inverseBad (lay : Layout L) (pre : Log Word) (y x : Word) : Prop :=
  lay.link₂ x = lay.link₁ y ∨
  lay.link₂ x ∈ pre.map (fun e => lay.link₁ e.output) ∨
  lay.overlap₁ x ∈ pre.map (fun e => lay.overlap₂ e.input) ∨
  lay.overlap₁ x ∈ pre.map (fun e => lay.overlap₁ e.input)

/-- Clean with respect to the chain predicates. -/
def Layout.Clean (lay : Layout L) (log : Log Word) : Prop :=
  ∀ pre e post, log = pre ++ e :: post →
    (e.inverse = false → ¬ lay.forwardBad pre e.output) ∧
    (e.inverse = true → ¬ lay.inverseBad pre e.output e.input)

/-- The second call of the later chain. -/
theorem Layout.later_second (lay : Layout L) {log : Log Word} (clean : lay.Clean log)
    {pre post : Log Word} {e₂ e₁' e₂' : Entry Word}
    (split : log = pre ++ e₂' :: post) (earlier : e₂ ∈ pre) (m₁' : e₁' ∈ log)
    (link' : lay.link₂ e₂'.input = lay.link₁ e₁'.output)
    (overlap' : lay.overlap₂ e₂'.input = lay.overlap₁ e₁'.input)
    (same : lay.digest e₂.output = lay.digest e₂'.output) : False := by
  have here := clean pre e₂' post split
  cases dir : e₂'.inverse
  · exact (here.1 dir) (Or.inl (List.mem_map.mpr ⟨e₂, earlier, same⟩))
  · by_cases self : e₁' = e₂'
    · subst self
      exact (here.2 dir) (Or.inl link')
    · have place : e₁' ∈ pre ∨ e₁' ∈ post := by
        rw [split] at m₁'
        simp only [List.mem_append, List.mem_cons] at m₁'
        rcases m₁' with h | h | h
        · exact Or.inl h
        · exact absurd h self
        · exact Or.inr h
      rcases place with before | after
      · exact (here.2 dir) (Or.inr (Or.inl (List.mem_map.mpr ⟨e₁', before, link'.symm⟩)))
      · obtain ⟨s, t, rfl⟩ := List.append_of_mem after
        have there := clean (pre ++ e₂' :: s) e₁' t (by rw [split]; simp)
        have mem : e₂' ∈ pre ++ e₂' :: s := by simp
        cases dir' : e₁'.inverse
        · exact (there.1 dir') (Or.inr (Or.inl (List.mem_map.mpr ⟨e₂', mem, link'⟩)))
        · exact (there.2 dir')
            (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e₂', mem, overlap'⟩))))

/-- The first call of the later chain, when both chains share their second input. -/
theorem Layout.later_first (lay : Layout L) {log : Log Word} (clean : lay.Clean log)
    {pre post : Log Word} {e₁ e₁' : Entry Word}
    (split : log = pre ++ e₁' :: post) (earlier : e₁ ∈ pre)
    (link : lay.link₁ e₁.output = lay.link₁ e₁'.output)
    (overlap : lay.overlap₁ e₁.input = lay.overlap₁ e₁'.input) : False := by
  have here := clean pre e₁' post split
  cases dir : e₁'.inverse
  · exact (here.1 dir) (Or.inr (Or.inr (List.mem_map.mpr ⟨e₁, earlier, link⟩)))
  · exact (here.2 dir) (Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨e₁, earlier, overlap⟩))))

/-- **(C') First-occurrence analysis.** Two chains whose four evaluations are in a clean log,
with different inputs and equal digest slices, are impossible. -/
theorem Layout.chain_collision (lay : Layout L) {log : Log Word} (clean : lay.Clean log)
    {e₁ e₂ e₁' e₂' : Entry Word} (m₁ : e₁ ∈ log) (m₂ : e₂ ∈ log) (m₁' : e₁' ∈ log)
    (m₂' : e₂' ∈ log)
    (link : lay.link₂ e₂.input = lay.link₁ e₁.output)
    (link' : lay.link₂ e₂'.input = lay.link₁ e₁'.output)
    (overlap : lay.overlap₂ e₂.input = lay.overlap₁ e₁.input)
    (overlap' : lay.overlap₂ e₂'.input = lay.overlap₁ e₁'.input)
    (different : e₁.input ≠ e₁'.input ∨ e₂.input ≠ e₂'.input)
    (same : lay.digest e₂.output = lay.digest e₂'.output) : False := by
  by_cases inputs : e₂.input = e₂'.input
  · have first : e₁.input ≠ e₁'.input := different.resolve_right (not_not.mpr inputs)
    have ne : e₁ ≠ e₁' := fun h => first (congrArg Entry.input h)
    have links : lay.link₁ e₁.output = lay.link₁ e₁'.output := by
      rw [← link, ← link', inputs]
    have overlaps : lay.overlap₁ e₁.input = lay.overlap₁ e₁'.input := by
      rw [← overlap, ← overlap', inputs]
    rcases order_of_ne m₁ m₁' ne with ⟨pre, post, split, earlier⟩ | ⟨pre, post, split, earlier⟩
    · exact lay.later_first clean split earlier links overlaps
    · exact lay.later_first clean split earlier links.symm overlaps.symm
  · have ne : e₂ ≠ e₂' := fun h => inputs (congrArg Entry.input h)
    rcases order_of_ne m₂ m₂' ne with ⟨pre, post, split, earlier⟩ | ⟨pre, post, split, earlier⟩
    · exact lay.later_second clean split earlier m₁' link' overlap' same
    · exact lay.later_second clean split earlier m₁ link overlap same.symm

/-! ## Spec v1 -/

/-- Spec v1 slices: `y[0..32)`, `y₁[88..200)`, `x₂[0..112)`, `x₁[168..200)`, `x₂[112..144)`. -/
def v1 : Layout 896 where
  digest y := y.extractLsb' 0 256
  link₁ y := y.extractLsb' 704 896
  link₂ x := x.extractLsb' 0 896
  overlap₁ x := x.extractLsb' 1344 256
  overlap₂ x := x.extractLsb' 896 256

/-- First permutation input: the first 200 bytes of the value. -/
def leafX1 (v : BitVec 2048) : Word := v.extractLsb' 0 1600

/-- Second permutation input: `y₁[88..200)` in bytes `[0..112)`, `v[168..256)` in `[112..200)`. -/
def leafX2 (v : BitVec 2048) (y₁ : Word) : Word := v.extractLsb' 1344 704 ++ y₁.extractLsb' 704 896

/-- The permutation part of the leaf hash: `h = (P x₂)[0..32)`. -/
def leafHash (σ : Perm) (v : BitVec 2048) : BitVec 256 :=
  v1.digest (σ (leafX2 v (σ (leafX1 v))))

theorem v1_link (v : BitVec 2048) (y₁ : Word) : v1.link₂ (leafX2 v y₁) = v1.link₁ y₁ :=
  BitVec.extractLsb'_append_eq_right

theorem v1_overlap (v : BitVec 2048) (y₁ : Word) :
    v1.overlap₂ (leafX2 v y₁) = v1.overlap₁ (leafX1 v) := by
  show (v.extractLsb' 1344 704 ++ y₁.extractLsb' 704 896 : BitVec (704 + 896)).extractLsb' 896 256 =
    (v.extractLsb' 0 1600 : BitVec 1600).extractLsb' 1344 256
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have a : ¬ (896 + i < 896) := by omega
  have b : decide (896 + i - 896 < 704) = true := decide_eq_true (by omega)
  have c : decide (1344 + i < 1600) = true := decide_eq_true (by omega)
  have d : 1344 + (896 + i - 896) = 0 + (1344 + i) := by omega
  have h₀ : decide (i < 256) = true := decide_eq_true hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, a, ite_false, b, c, d, h₀,
    Bool.true_and]

/-- The two permutation inputs determine the value. -/
theorem leaf_inputs_injective {v v' : BitVec 2048} {y y' : Word}
    (first : leafX1 v = leafX1 v') (second : leafX2 v y = leafX2 v' y') : v = v' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases low : i < 1600
  · have bit : (v.extractLsb' 0 1600 : BitVec 1600).getLsbD i =
        (v'.extractLsb' 0 1600 : BitVec 1600).getLsbD i :=
      congrArg (fun w : BitVec 1600 => w.getLsbD i) first
    have l : decide (i < 1600) = true := decide_eq_true low
    simp only [BitVec.getLsbD_extractLsb', l, Bool.true_and, Nat.zero_add] at bit
    exact bit
  · have bit : (v.extractLsb' 1344 704 ++ y.extractLsb' 704 896 : BitVec (704 + 896)).getLsbD
          (i - 448) =
        (v'.extractLsb' 1344 704 ++ y'.extractLsb' 704 896 : BitVec (704 + 896)).getLsbD
          (i - 448) :=
      congrArg (fun w : BitVec (704 + 896) => w.getLsbD (i - 448)) second
    have a : ¬ (i - 448 < 896) := by omega
    have b : decide (i - 448 - 896 < 704) = true := decide_eq_true (by omega)
    have c : 1344 + (i - 448 - 896) = i := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, a, ite_false, b, c,
      Bool.true_and] at bit
    exact bit

/-- **Leaf lemma (log form).** Different values with equal `h`, whose four permutation evaluations
are logged, make the log unclean. -/
theorem leaf_hash_unclean {log : Log Word} (clean : v1.Clean log) {v v' : BitVec 2048}
    (different : v ≠ v') {e₁ e₂ e₁' e₂' : Entry Word}
    (m₁ : e₁ ∈ log) (m₂ : e₂ ∈ log) (m₁' : e₁' ∈ log) (m₂' : e₂' ∈ log)
    (in₁ : e₁.input = leafX1 v) (in₂ : e₂.input = leafX2 v e₁.output)
    (in₁' : e₁'.input = leafX1 v') (in₂' : e₂'.input = leafX2 v' e₁'.output)
    (same : v1.digest e₂.output = v1.digest e₂'.output) : False := by
  refine v1.chain_collision clean m₁ m₂ m₁' m₂' (by rw [in₂, v1_link]) (by rw [in₂', v1_link])
    (by rw [in₂, in₁, v1_overlap]) (by rw [in₂', in₁', v1_overlap]) ?_ same
  by_contra both
  rw [not_or, not_not, not_not] at both
  exact different (leaf_inputs_injective (in₁.symm.trans (both.1.trans in₁'))
    (in₂.symm.trans (both.2.trans in₂')))

/-- **Leaf lemma (oracle form).** For a log consistent with `σ`, `h` is injective on values whose
four evaluations are logged, unless the log is unclean. This is the permutation half of a mixed
detector "compression collision ∨ permutation hazard". -/
theorem leafHash_injective_of_clean {σ : Perm} {log : Log Word} (clean : v1.Clean log)
    (consistent : ∀ e ∈ log, σ e.input = e.output) {v v' : BitVec 2048}
    (logged : ∀ u ∈ [v, v'], leafX1 u ∈ log.inputs ∧ leafX2 u (σ (leafX1 u)) ∈ log.inputs)
    (same : leafHash σ v = leafHash σ v') : v = v' := by
  by_contra different
  have entry : ∀ x ∈ log.inputs, ∃ e ∈ log, e.input = x ∧ e.output = σ x := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact ⟨e, he, rfl, (consistent e he).symm⟩
  obtain ⟨l₁, l₂⟩ := logged v (by simp)
  obtain ⟨l₁', l₂'⟩ := logged v' (by simp)
  obtain ⟨e₁, m₁, i₁, o₁⟩ := entry _ l₁
  obtain ⟨e₂, m₂, i₂, o₂⟩ := entry _ l₂
  obtain ⟨e₁', m₁', i₁', o₁'⟩ := entry _ l₁'
  obtain ⟨e₂', m₂', i₂', o₂'⟩ := entry _ l₂'
  exact leaf_hash_unclean clean different m₁ m₂ m₁' m₂' i₁ (by rw [i₂, o₁]) i₁'
    (by rw [i₂', o₁']) (by rw [o₂, o₂']; exact same)

/-! ## Counting words with a fixed slice -/

/-- Exactly `2^(n-w)` words of width `n` have a given `w`-bit slice at offset `off`. -/
theorem card_extract_fiber (n off w : ℕ) (fits : off + w ≤ n) (t : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = t).card = 2 ^ (n - w) := by
  classical
  let mask : BitVec w → BitVec n := fun u => (u.setWidth n) <<< off
  have slice_xor : ∀ (x : BitVec n) (u : BitVec w),
      (x ^^^ mask u).extractLsb' off w = x.extractLsb' off w ^^^ u := by
    intro x u
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h₀ : decide (i < w) = true := decide_eq_true hi
    have a : decide (off + i < n) = true := decide_eq_true (by omega)
    have b : decide (off + i < off) = false := decide_eq_false (by omega)
    have c : decide (i < n) = true := decide_eq_true (by omega)
    simp only [mask, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, Nat.add_sub_cancel_left, h₀, a, b, c, Bool.true_and, Bool.not_false]
  have equal : ∀ t t' : BitVec w,
      (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = t).card =
        (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = t').card := by
    intro t t'
    apply Finset.card_nbij' (fun x => x ^^^ mask (t ^^^ t')) (fun x => x ^^^ mask (t ^^^ t'))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [slice_xor, hx, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [slice_xor, hx, BitVec.xor_comm t t', ← BitVec.xor_assoc, BitVec.xor_self,
        BitVec.zero_xor]
    · intro x _
      show x ^^^ mask (t ^^^ t') ^^^ mask (t ^^^ t') = x
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · intro x _
      show x ^^^ mask (t ^^^ t') ^^^ mask (t ^^^ t') = x
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have total : (Finset.univ : Finset (BitVec n)).card =
      ∑ u ∈ (Finset.univ : Finset (BitVec w)),
        (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = u).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.sum_congr rfl (fun u _ => equal u t), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_bitVec, Fintype.card_bitVec, smul_eq_mul] at total
  have split : 2 ^ n = 2 ^ w * 2 ^ (n - w) := by
    rw [← pow_add]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (total.symm.trans split)

/-- At most `#l · 2^(n-w)` words have their slice in a list `l`. -/
theorem card_filter_slice_mem (n off w : ℕ) (fits : off + w ≤ n) (l : List (BitVec w)) :
    (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w ∈ l).card ≤
      l.length * 2 ^ (n - w) := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    have sub : (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w ∈ a :: l) ⊆
        (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = a) ∪
          (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w ∈ l) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        List.mem_cons] at hx ⊢
      exact hx
    calc _ ≤ _ := Finset.card_le_card sub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 ^ (n - w) + l.length * 2 ^ (n - w) :=
          Nat.add_le_add (card_extract_fiber n off w fits a).le ih
      _ = (a :: l).length * 2 ^ (n - w) := by
          rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-! ## The hazard sets of spec v1 and their sizes -/

/-- Words per value of a 256-bit slice: `2^1344` (kept opaque so that no tactic evaluates it). -/
@[irreducible] def wide : ℕ := 2 ^ (PERMUTATION_WIDTH - 256)

theorem wide_eq : wide = 2 ^ (PERMUTATION_WIDTH - 256) := by unfold wide; rfl

theorem three_slices (k W : ℕ) : k * W + k * W + k * W ≤ (3 * k + 1) * W := by nlinarith

theorem four_slices (k W : ℕ) : W + k * W + k * W + k * W ≤ (3 * k + 1) * W := by nlinarith

theorem fits_digest : 0 + 256 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
theorem fits_link₁ : 704 + 896 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
theorem fits_link₂ : 0 + 896 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
theorem fits_overlap₁ : 1344 + 256 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
theorem narrow_le_wide : 2 ^ (PERMUTATION_WIDTH - 896) ≤ wide := by
  rw [wide_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by unfold PERMUTATION_WIDTH; omega)

open Classical in
theorem forward_card_le (log : Log Word) :
    (Finset.univ.filter fun y => v1.forwardBad log y).card ≤ (3 * log.length + 1) * wide := by
  classical
  have hA := card_filter_slice_mem PERMUTATION_WIDTH 0 256 fits_digest
    (log.map fun e => v1.digest e.output)
  have hB := card_filter_slice_mem PERMUTATION_WIDTH 704 896 fits_link₁
    (log.map fun e => v1.link₂ e.input)
  have hC := card_filter_slice_mem PERMUTATION_WIDTH 704 896 fits_link₁
    (log.map fun e => v1.link₁ e.output)
  rw [List.length_map, ← wide_eq] at hA
  rw [List.length_map] at hB hC
  have sub : (Finset.univ.filter fun y => v1.forwardBad log y) ⊆
      ((Finset.univ.filter fun x : Word => x.extractLsb' 0 256 ∈
          log.map fun e => v1.digest e.output) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 704 896 ∈
          log.map fun e => v1.link₂ e.input)) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 704 896 ∈
          log.map fun e => v1.link₁ e.output) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have narrow := narrow_le_wide
  calc _ ≤ _ := Finset.card_le_card sub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ log.length * wide + log.length * wide + log.length * wide :=
        Nat.add_le_add (Nat.add_le_add hA (hB.trans (Nat.mul_le_mul_left _ narrow)))
          (hC.trans (Nat.mul_le_mul_left _ narrow))
    _ ≤ (3 * log.length + 1) * wide := three_slices _ _

open Classical in
theorem inverse_card_le (log : Log Word) (y : Word) :
    (Finset.univ.filter fun x => v1.inverseBad log y x).card ≤ (3 * log.length + 1) * wide := by
  classical
  have hA := card_extract_fiber PERMUTATION_WIDTH 0 896 fits_link₂ (v1.link₁ y)
  have hB := card_filter_slice_mem PERMUTATION_WIDTH 0 896 fits_link₂
    (log.map fun e => v1.link₁ e.output)
  have hC := card_filter_slice_mem PERMUTATION_WIDTH 1344 256 fits_overlap₁
    (log.map fun e => v1.overlap₂ e.input)
  have hD := card_filter_slice_mem PERMUTATION_WIDTH 1344 256 fits_overlap₁
    (log.map fun e => v1.overlap₁ e.input)
  rw [List.length_map] at hB
  rw [List.length_map, ← wide_eq] at hC hD
  have sub : (Finset.univ.filter fun x => v1.inverseBad log y x) ⊆
      (((Finset.univ.filter fun x : Word => x.extractLsb' 0 896 = v1.link₁ y) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 0 896 ∈
          log.map fun e => v1.link₁ e.output)) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 1344 256 ∈
          log.map fun e => v1.overlap₂ e.input)) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 1344 256 ∈
          log.map fun e => v1.overlap₁ e.input) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    rcases hx with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have narrow := narrow_le_wide
  calc _ ≤ _ := Finset.card_le_card sub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ wide + log.length * wide + log.length * wide + log.length * wide :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hA.le.trans narrow)
          (hB.trans (Nat.mul_le_mul_left _ narrow))) hC) hD
    _ ≤ (3 * log.length + 1) * wide := four_slices _ _

open Classical in
/-- **The spec v1 hazard.** -/
noncomputable def leafHazard : Hazard where
  forward log _ := Finset.univ.filter fun y => v1.forwardBad log y
  inverse log y := Finset.univ.filter fun x => v1.inverseBad log y x
  bound k := (3 * k + 1) * wide
  forward_card log _ := forward_card_le log
  inverse_card log y := inverse_card_le log y

/-- A clean log for `leafHazard` is clean for the chain predicates. -/
theorem clean_leaf {log : Log Word} (clean : Clean leafHazard log) : v1.Clean log := by
  intro pre e post split
  obtain ⟨fwd, inv⟩ := clean pre e post split
  refine ⟨fun dir bad => fwd dir ?_, fun dir bad => inv dir ?_⟩
  · simp only [leafHazard, Finset.mem_filter, Finset.mem_univ, true_and]
    exact bad
  · simp only [leafHazard, Finset.mem_filter, Finset.mem_univ, true_and]
    exact bad

/-! ## (E) The permutation part of the binding bound -/

/-- With at most `2^64` extra queries for the reduction, the spec v1 hazard has probability at
most `q / 2^121` for every `1 ≤ q ≤ 2^120` (larger `q` make the binding bound trivial). -/
theorem leaf_budget (q extra : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (overhead : extra ≤ 2 ^ 64) :
    hazardBudget leafHazard 0 (q + extra) ≤ (q : ℝ≥0∞) / 2 ^ 121 := by
  set Q := q + extra with hQdef
  have card : Fintype.card Word = 2 ^ PERMUTATION_WIDTH := Fintype.card_bitVec _
  have width : 256 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
  have each : ∀ j < Q, leafHazard.bound (0 + j) ≤ (3 * Q + 1) * wide := by
    intro j hj
    show (3 * (0 + j) + 1) * wide ≤ (3 * Q + 1) * wide
    exact Nat.mul_le_mul_right _ (by omega)
  have room : 2 * (0 + Q) ≤ Fintype.card Word := by
    rw [card]
    calc 2 * (0 + Q) ≤ 2 ^ 122 := by
          have : (2 : ℕ) ^ 122 = 2 * (2 ^ 120 + 2 ^ 120) := by norm_num
          rw [this]
          have : extra ≤ 2 ^ 120 := overhead.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
          omega
      _ ≤ 2 ^ PERMUTATION_WIDTH := Nat.pow_le_pow_right (by norm_num) (by unfold PERMUTATION_WIDTH; omega)
  have budget := hazardBudget_le leafHazard 0 Q ((3 * Q + 1) * wide) each room
  -- the integer inequality
  have square : Q * Q ≤ q * 2 ^ 129 := by
    have t1 : q * q ≤ q * 2 ^ 120 := Nat.mul_le_mul_left q small
    have t2 : q * extra ≤ q * 2 ^ 64 := Nat.mul_le_mul_left q overhead
    have t3 : extra * extra ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul overhead overhead
    have t4 : 2 ^ 64 * 2 ^ 64 ≤ q * 2 ^ 128 := by
      rw [← pow_add]
      exact Nat.le_mul_of_pos_left _ positive
    rw [hQdef]
    nlinarith
  have small_part : Q * (2 * (3 * Q + 1)) ≤ q * 2 ^ 135 := by
    have one : 1 ≤ Q := by omega
    nlinarith
  have integer : Q * (2 * ((3 * Q + 1) * wide)) ≤ q * 2 ^ (PERMUTATION_WIDTH - 121) := by
    have reshape : ∀ Q W : ℕ, Q * (2 * ((3 * Q + 1) * W)) = (Q * (2 * (3 * Q + 1))) * W := by
      intro Q W
      ring
    have shape := reshape Q wide
    have power : 2 ^ (PERMUTATION_WIDTH - 121) = 2 ^ 135 * wide := by
      rw [wide_eq, ← pow_add, show 135 + (PERMUTATION_WIDTH - 256) = PERMUTATION_WIDTH - 121 by
        omega]
    rw [shape, power]
    calc Q * (2 * (3 * Q + 1)) * wide ≤ q * 2 ^ 135 * wide := Nat.mul_le_mul_right _ small_part
      _ = q * (2 ^ 135 * wide) := Nat.mul_assoc _ _ _
  refine budget.trans ?_
  rw [card, ← mul_div_assoc, ← Nat.cast_mul]
  calc ((Q * (2 * ((3 * Q + 1) * wide)) : ℕ) : ℝ≥0∞) / ((2 ^ PERMUTATION_WIDTH : ℕ) : ℝ≥0∞)
      ≤ ((q * 2 ^ (PERMUTATION_WIDTH - 121) : ℕ) : ℝ≥0∞) / ((2 ^ PERMUTATION_WIDTH : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast integer) _
    _ = (q : ℝ≥0∞) / 2 ^ 121 := by
        have split : PERMUTATION_WIDTH = 121 + (PERMUTATION_WIDTH - 121) := by omega
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
        conv_lhs => rw [show (2 : ℝ≥0∞) ^ PERMUTATION_WIDTH =
          2 ^ 121 * 2 ^ (PERMUTATION_WIDTH - 121) by rw [← pow_add, ← split]]
        exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

end PermLean
