import CommitGolf.Oracle
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.ProbabilityNotation
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType.Basic
import ToMathlib.Probability.UniformOn

/-! # Ideal-permutation hazard bound

For a uniformly sampled `Perm = Equiv.Perm (BitVec 1600)` and any adaptive adversary
`OracleComp World β` (private coins, compression with a fixed table, forward and inverse
permutation queries), we bound the probability that some *fresh* permutation answer lands in a
history-dependent hazard set.

* The adversary is run against a fixed `σ` by `run`, which keeps a log of fresh evaluations and
  a sticky flag: a fresh forward query `x ↦ σ x` raises it when `σ x ∈ H.forward log x`, a fresh
  inverse query `y ↦ σ⁻¹ y` raises it when `σ⁻¹ y ∈ H.inverse log y`.
* `hazard_sum_bound`: summed over the permutations consistent with a starting log,
  the flag probability is at most `#ext log * ∑_{j<q} bound(k+j) / (2^1600 - (k+j))`.
* `hazard_bound`: the same for `σ ← $ᵗ Perm`, starting from the empty log.

No lazy-sampling equivalence is needed: the proof partitions the consistent permutations by the
fresh answer, and a transposition shows that all fibres have equal size.
-/

namespace PermLean
open CommitGolf OracleComp OracleSpec
open scoped ENNReal

/-! ## Generic combinatorics of partial permutations

Everything in this section is generic over a finite type `α`; nothing unfolds `2 ^ 1600`. -/

section Generic
variable {α : Type} [Fintype α] [DecidableEq α]

/-- One fresh permutation evaluation `σ input = output`; `inverse` records its direction. -/
structure Entry (α : Type) where
  input : α
  output : α
  inverse : Bool

abbrev Log (α : Type) := List (Entry α)

abbrev Log.inputs (log : Log α) : List α := log.map Entry.input
abbrev Log.outputs (log : Log α) : List α := log.map Entry.output

/-- Permutations consistent with every logged evaluation. -/
@[irreducible] noncomputable def ext (log : Log α) : Finset (Equiv.Perm α) := by
  classical
  exact Finset.univ.filter fun σ => ∀ e ∈ log, σ e.input = e.output

theorem mem_ext {log : Log α} {σ : Equiv.Perm α} :
    σ ∈ ext log ↔ ∀ e ∈ log, σ e.input = e.output := by
  classical
  unfold ext
  simp

theorem mem_ext_append {log : Log α} {e : Entry α} {σ : Equiv.Perm α} :
    σ ∈ ext (log ++ [e]) ↔ σ ∈ ext log ∧ σ e.input = e.output := by
  simp only [mem_ext, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]

theorem ext_nil : ext ([] : Log α) = Finset.univ := by
  ext σ
  simp [mem_ext]

/-- A fresh input of a consistent permutation lands outside the logged outputs. -/
theorem apply_not_mem_outputs {log : Log α} {σ : Equiv.Perm α} (hσ : σ ∈ ext log) {x : α}
    (fresh : x ∉ log.inputs) : σ x ∉ log.outputs := by
  intro h
  obtain ⟨e, he, hy⟩ := List.mem_map.mp h
  apply fresh
  have same : σ x = σ e.input := by rw [mem_ext.mp hσ e he]; exact hy.symm
  exact List.mem_map.mpr ⟨e, he, (σ.injective same).symm⟩

/-- A fresh output of a consistent permutation has its preimage outside the logged inputs. -/
theorem symm_not_mem_inputs {log : Log α} {σ : Equiv.Perm α} (hσ : σ ∈ ext log) {y : α}
    (fresh : y ∉ log.outputs) : σ.symm y ∉ log.inputs := by
  intro h
  obtain ⟨e, he, hx⟩ := List.mem_map.mp h
  apply fresh
  have same : y = e.output := by
    rw [← mem_ext.mp hσ e he, hx, Equiv.apply_symm_apply]
  exact List.mem_map.mpr ⟨e, he, same.symm⟩

/-- A logged input has its logged answer under every consistent permutation. -/
theorem apply_of_mem_inputs {log : Log α} {x : α} (known : x ∈ log.inputs) :
    ∃ y, ∀ σ ∈ ext log, σ x = y := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp known
  exact ⟨e.output, fun σ hσ => mem_ext.mp hσ e he⟩

/-- A logged output has its logged preimage under every consistent permutation. -/
theorem symm_of_mem_outputs {log : Log α} {y : α} (known : y ∈ log.outputs) :
    ∃ x, ∀ σ ∈ ext log, σ.symm y = x := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp known
  refine ⟨e.input, fun σ hσ => ?_⟩
  rw [Equiv.symm_apply_eq, mem_ext.mp hσ e he]

theorem filter_apply_eq (log : Log α) (x y : α) (b : Bool) :
    (ext log).filter (fun σ => σ x = y) = ext (log ++ [⟨x, y, b⟩]) := by
  ext σ
  rw [Finset.mem_filter, mem_ext_append]

theorem filter_symm_eq (log : Log α) (x y : α) (b : Bool) :
    (ext log).filter (fun σ => σ.symm y = x) = ext (log ++ [⟨x, y, b⟩]) := by
  ext σ
  rw [Finset.mem_filter, mem_ext_append, Equiv.symm_apply_eq]
  exact and_congr Iff.rfl eq_comm

/-- Fibres over two fresh outputs have equal size: compose with a transposition. -/
theorem card_ext_output (log : Log α) (x y y' : α) (b : Bool)
    (hy : y ∉ log.outputs) (hy' : y' ∉ log.outputs) :
    (ext (log ++ [⟨x, y, b⟩])).card = (ext (log ++ [⟨x, y', b⟩])).card := by
  have fixes : ∀ σ ∈ ext log, ∀ e ∈ log, (Equiv.swap y y' * σ) e.input = e.output := by
    intro σ hσ e he
    have member : e.output ∈ log.outputs := List.mem_map_of_mem he
    rw [Equiv.Perm.mul_apply, mem_ext.mp hσ e he]
    exact Equiv.swap_apply_of_ne_of_ne (fun (h : e.output = y) => hy (h ▸ member))
      (fun (h : e.output = y') => hy' (h ▸ member))
  apply Finset.card_nbij' (fun σ => Equiv.swap y y' * σ) (fun σ => Equiv.swap y y' * σ)
  · intro σ hσ
    rw [Finset.mem_coe, mem_ext_append] at hσ ⊢
    refine ⟨mem_ext.mpr (fixes σ hσ.1), ?_⟩
    simp only [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]
  · intro σ hσ
    rw [Finset.mem_coe, mem_ext_append] at hσ ⊢
    refine ⟨mem_ext.mpr (fixes σ hσ.1), ?_⟩
    simp only [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_right]
  · intro σ _
    exact Equiv.swap_mul_self_mul y y' σ
  · intro σ _
    exact Equiv.swap_mul_self_mul y y' σ

/-- Fibres over two fresh inputs have equal size: precompose with a transposition. -/
theorem card_ext_input (log : Log α) (x x' y : α) (b : Bool)
    (hx : x ∉ log.inputs) (hx' : x' ∉ log.inputs) :
    (ext (log ++ [⟨x, y, b⟩])).card = (ext (log ++ [⟨x', y, b⟩])).card := by
  have fixes : ∀ σ ∈ ext log, ∀ e ∈ log, (σ * Equiv.swap x x') e.input = e.output := by
    intro σ hσ e he
    have member : e.input ∈ log.inputs := List.mem_map_of_mem he
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
      (fun (h : e.input = x) => hx (h ▸ member)) (fun (h : e.input = x') => hx' (h ▸ member)),
      mem_ext.mp hσ e he]
  apply Finset.card_nbij' (fun σ => σ * Equiv.swap x x') (fun σ => σ * Equiv.swap x x')
  · intro σ hσ
    rw [Finset.mem_coe, mem_ext_append] at hσ ⊢
    refine ⟨mem_ext.mpr (fixes σ hσ.1), ?_⟩
    simp only [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_right]
  · intro σ hσ
    rw [Finset.mem_coe, mem_ext_append] at hσ ⊢
    refine ⟨mem_ext.mpr (fixes σ hσ.1), ?_⟩
    simp only [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]
  · intro σ _
    exact Equiv.mul_swap_mul_self x x' σ
  · intro σ _
    exact Equiv.mul_swap_mul_self x x' σ

/-- At least `|α| - #l` elements avoid a list `l`. -/
theorem card_avoid (l : List α) :
    Fintype.card α - l.length ≤ (Finset.univ.filter fun w : α => w ∉ l).card := by
  have whole := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (fun w : α => w ∈ l)
  have listed : (Finset.univ.filter fun w : α => w ∈ l).card ≤ l.length :=
    (Finset.card_le_card (fun w hw => List.mem_toFinset.mpr (Finset.mem_filter.mp hw).2)).trans
      (List.toFinset_card_le l)
  rw [Finset.card_univ] at whole
  omega

end Generic

/-! ## The counting step -/

theorem nat_le_div (a d s : ℕ) (scaled : a * d ≤ s) (plain : a ≤ s) :
    (a : ℝ≥0∞) ≤ (s : ℝ≥0∞) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | positive
  · rcases Nat.eq_zero_or_pos s with rfl | positive'
    · have : a = 0 := by omega
      simp [this]
    · rw [Nat.cast_zero, ENNReal.div_zero (by exact_mod_cast positive'.ne')]
      exact le_top
  · rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast positive.ne'))
      (Or.inl (ENNReal.natCast_ne_top d))]
    exact_mod_cast scaled

/-- Partition `S` by `g`; when all fibres have equal size and at most `b` of the at least `D`
possible values are bad, the bad values carry at most `b / D` of the mass. -/
theorem fiber_sum_bound {α ι : Type} [DecidableEq α] (S : Finset ι) (g : ι → α) (T : Finset α)
    (E : α → Finset ι)
    (maps : ∀ σ ∈ S, g σ ∈ T) (fiber : ∀ y ∈ T, S.filter (fun σ => g σ = y) = E y)
    (equal : ∀ y ∈ T, ∀ y' ∈ T, (E y).card = (E y').card)
    (D : ℕ) (large : D ≤ T.card) (bad : Finset α) (b : ℕ) (badCard : bad.card ≤ b)
    (F : α → ι → ℝ≥0∞) (atMostOne : ∀ y σ, F y σ ≤ 1) (ε : ℝ≥0∞)
    (good : ∀ y ∈ T, y ∉ bad → ∑ σ ∈ E y, F y σ ≤ (E y).card * ε) :
    ∑ σ ∈ S, F (g σ) σ ≤ S.card * ((b : ℝ≥0∞) / D + ε) := by
  classical
  have split : ∑ σ ∈ S, F (g σ) σ = ∑ y ∈ T, ∑ σ ∈ E y, F y σ := by
    rw [← Finset.sum_fiberwise_of_maps_to maps]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← fiber y hy]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [(Finset.mem_filter.mp hσ).2]
  have count : S.card = ∑ y ∈ T, (E y).card := by
    rw [Finset.card_eq_sum_card_fiberwise maps]
    exact Finset.sum_congr rfl fun y hy => by rw [fiber y hy]
  have small : ∀ y ∈ T, ((E y).card : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) / D := by
    intro y hy
    have total : T.card * (E y).card = S.card := by
      rw [count, Finset.sum_congr rfl fun y' hy' => equal y' hy' y hy, Finset.sum_const,
        smul_eq_mul]
    have nonempty : 1 ≤ T.card := Finset.card_pos.mpr ⟨y, hy⟩
    apply nat_le_div
    · calc (E y).card * D ≤ (E y).card * T.card := Nat.mul_le_mul_left _ large
        _ = S.card := by rw [Nat.mul_comm]; exact total
    · calc (E y).card = 1 * (E y).card := (Nat.one_mul _).symm
        _ ≤ T.card * (E y).card := Nat.mul_le_mul_right _ nonempty
        _ = S.card := total
  calc ∑ σ ∈ S, F (g σ) σ = ∑ y ∈ T, ∑ σ ∈ E y, F y σ := split
    _ ≤ ∑ y ∈ T, ((if y ∈ bad then ((E y).card : ℝ≥0∞) else 0) + (E y).card * ε) := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hb : y ∈ bad
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
          calc ∑ σ ∈ E y, F y σ ≤ ∑ σ ∈ E y, (1 : ℝ≥0∞) :=
                Finset.sum_le_sum fun σ _ => atMostOne y σ
            _ = (E y).card := by simp
            _ ≤ _ := le_self_add
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), zero_add]
          exact good y hy hb
    _ = ∑ y ∈ T with y ∈ bad, ((E y).card : ℝ≥0∞) + S.card * ε := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_mul, count, Nat.cast_sum]
    _ ≤ b * ((S.card : ℝ≥0∞) / D) + S.card * ε := by
        gcongr
        calc ∑ y ∈ T with y ∈ bad, ((E y).card : ℝ≥0∞)
            ≤ ∑ y ∈ T with y ∈ bad, ((S.card : ℝ≥0∞) / D) :=
              Finset.sum_le_sum fun y hy => small y (Finset.mem_filter.mp hy).1
          _ = (T.filter (· ∈ bad)).card * ((S.card : ℝ≥0∞) / D) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ b * ((S.card : ℝ≥0∞) / D) := by
              gcongr
              exact_mod_cast (Finset.card_le_card
                (fun y hy => (Finset.mem_filter.mp hy).2)).trans badCard
    _ = S.card * ((b : ℝ≥0∞) / D + ε) := by
        rw [mul_add, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← mul_assoc,
          mul_comm (b : ℝ≥0∞)]

/-! ## The adversary against a fixed permutation, with a hazard log -/

/-- A permutation word of the contract. -/
abbrev Word := BitVec PERMUTATION_WIDTH

/-- History-dependent hazard sets for fresh answers, of size at most `bound` of the log length. -/
structure Hazard where
  forward : Log Word → Word → Finset Word
  inverse : Log Word → Word → Finset Word
  bound : ℕ → ℕ
  forward_card : ∀ log x, (forward log x).card ≤ bound log.length
  inverse_card : ∀ log y, (inverse log y).card ≤ bound log.length

/-- Membership test kept opaque, so that no decidability instance over `BitVec 1600` is ever
unfolded during unification. -/
@[irreducible] def hit (S : Finset Word) (w : Word) : Bool := decide (w ∈ S)

theorem hit_eq_false {S : Finset Word} {w : Word} (h : w ∉ S) : hit S w = false := by
  unfold hit
  exact decide_eq_false h

/-- The log of fresh evaluations and the sticky hazard flag. -/
abbrev State := Log Word × Bool

/-- Answer one query against the fixed compression table `C` and permutation `σ`. -/
def step (H : Hazard) (C : Compression) (σ : Perm) (s : State) :
    (t : World.Domain) → ProbComp (World.Range t × State)
  | .inl coins => (fun a => (a, s)) <$>
      (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins))
  | .inr (.inl x) => pure (C x, s)
  | .inr (.inr (.inl x)) => pure (σ x,
      if x ∈ s.1.inputs then s
      else (s.1 ++ [⟨x, σ x, false⟩], s.2 || hit (H.forward s.1 x) (σ x)))
  | .inr (.inr (.inr y)) => pure (σ.symm y,
      if y ∈ s.1.outputs then s
      else (s.1 ++ [⟨σ.symm y, y, true⟩], s.2 || hit (H.inverse s.1 y) (σ.symm y)))

/-- Run an adversary against fixed `C, σ`, threading the hazard state. -/
def run (H : Hazard) (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    State → ProbComp (β × State) :=
  OracleComp.recOn comp (fun value s => pure (value, s))
    (fun t _ next s => step H C σ s t >>= fun r => next r.1 r.2)

theorem run_pure (H : Hazard) (C : Compression) (σ : Perm) {β : Type} (value : β) (s : State) :
    run H C σ (pure value : OracleComp World β) s = pure (value, s) := rfl

theorem run_query_bind (H : Hazard) (C : Compression) (σ : Perm) {β : Type} (t : World.Domain)
    (next : World.Range t → OracleComp World β) (s : State) :
    run H C σ ((liftM (World.query t) : OracleComp World _) >>= next) s =
      step H C σ s t >>= fun r => run H C σ (next r.1) r.2 := rfl

/-- The contract's public-query budget: compression and both permutation directions cost one,
private coins are free. -/
def PublicQueryBound {β : Type} (comp : OracleComp World β) (budget : ℕ) : Prop :=
  IsQueryBound comp budget (fun t left => Oracle.callCost t ≤ left)
    (fun t left => left - Oracle.callCost t)

/-- Per-query hazard rate once `k` evaluations are logged. -/
noncomputable def rate (H : Hazard) (k : ℕ) : ℝ≥0∞ :=
  (H.bound k : ℝ≥0∞) / ((Fintype.card Word - k : ℕ) : ℝ≥0∞)

/-- Hazard budget of `q` further public queries from a log of length `k`. -/
noncomputable def hazardBudget (H : Hazard) (k q : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range q, rate H (k + j)

theorem hazardBudget_mono (H : Hazard) (k : ℕ) {q q' : ℕ} (le : q' ≤ q) :
    hazardBudget H k q' ≤ hazardBudget H k q :=
  Finset.sum_le_sum_of_subset (Finset.range_mono le)

theorem hazardBudget_succ (H : Hazard) (k q : ℕ) (positive : 1 ≤ q) :
    rate H k + hazardBudget H (k + 1) (q - 1) = hazardBudget H k q := by
  unfold hazardBudget
  conv_rhs => rw [show q = (q - 1) + 1 from by omega, Finset.sum_range_succ']
  rw [add_comm, Nat.add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show k + 1 + j = k + (j + 1) from by omega]

/-- Point masses of a finite draw sum to at most one. -/
theorem sum_point_le_one {γ : Type} [Fintype γ] (mx : ProbComp γ) :
    ∑ a, Pr{let x ← mx}[x = a] ≤ 1 := by
  have total := prEvent_bind_eq_sum_fintype mx (fun a => (pure a : ProbComp γ)) (fun _ => True)
  simp only [bind_pure] at total
  calc ∑ a, Pr{let x ← mx}[x = a]
      = ∑ a, Pr{let x ← mx}[x = a] * Pr{let y ← (pure a : ProbComp γ)}[True] := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [prEvent_pure]
        simp
    _ = Pr{let y ← mx}[True] := total.symm
    _ ≤ 1 := prEvent_le_one _

/-- One fresh forward query: the answer is spread evenly over the unlogged words. -/
theorem fresh_forward_step (H : Hazard) (log : Log Word) (x : Word) (fresh : x ∉ log.inputs)
    (G : Perm → ℝ≥0∞) (F : Word → Perm → ℝ≥0∞) (same : ∀ σ, G σ = F (σ x) σ)
    (atMostOne : ∀ y σ, F y σ ≤ 1) (ε : ℝ≥0∞)
    (good : ∀ y, y ∉ H.forward log x →
      ∑ σ ∈ ext (log ++ [⟨x, y, false⟩]), F y σ ≤ (ext (log ++ [⟨x, y, false⟩])).card * ε) :
    ∑ σ ∈ ext log, G σ ≤ (ext log).card * (rate H log.length + ε) := by
  simp only [same]
  have avoid := card_avoid log.outputs
  rw [List.length_map] at avoid
  exact fiber_sum_bound (ext log) (fun σ => σ x)
    (Finset.univ.filter fun w => w ∉ log.outputs)
    (fun y => ext (log ++ [⟨x, y, false⟩]))
    (fun σ hσ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, apply_not_mem_outputs hσ fresh⟩)
    (fun y _ => filter_apply_eq log x y false)
    (fun y hy y' hy' => card_ext_output log x y y' false
      (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hy').2)
    (Fintype.card Word - log.length) avoid
    (H.forward log x) (H.bound log.length) (H.forward_card log x) F atMostOne ε
    (fun y _ notBad => good y notBad)

/-- One fresh inverse query: the preimage is spread evenly over the unlogged words. -/
theorem fresh_inverse_step (H : Hazard) (log : Log Word) (y : Word) (fresh : y ∉ log.outputs)
    (G : Perm → ℝ≥0∞) (F : Word → Perm → ℝ≥0∞) (same : ∀ σ, G σ = F (σ.symm y) σ)
    (atMostOne : ∀ x σ, F x σ ≤ 1) (ε : ℝ≥0∞)
    (good : ∀ x, x ∉ H.inverse log y →
      ∑ σ ∈ ext (log ++ [⟨x, y, true⟩]), F x σ ≤ (ext (log ++ [⟨x, y, true⟩])).card * ε) :
    ∑ σ ∈ ext log, G σ ≤ (ext log).card * (rate H log.length + ε) := by
  simp only [same]
  have avoid := card_avoid log.inputs
  rw [List.length_map] at avoid
  exact fiber_sum_bound (ext log) (fun σ => σ.symm y)
    (Finset.univ.filter fun w => w ∉ log.inputs)
    (fun x => ext (log ++ [⟨x, y, true⟩]))
    (fun σ hσ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, symm_not_mem_inputs hσ fresh⟩)
    (fun x _ => filter_symm_eq log x y true)
    (fun x hx x' hx' => card_ext_input log x x' y true
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2)
    (Fintype.card Word - log.length) avoid
    (H.inverse log y) (H.bound log.length) (H.inverse_card log y) F atMostOne ε
    (fun x _ notBad => good x notBad)

/-- **Hazard bound, counting form.** Summed over the permutations consistent with a log of
length `k`, the probability that a `q`-query adversary raises the flag is at most
`#ext log * ∑_{j<q} bound(k+j)/(2^1600-(k+j))`. -/
theorem hazard_sum_bound (H : Hazard) (C : Compression) {β : Type} (comp : OracleComp World β) :
    ∀ (q : ℕ), PublicQueryBound comp q → ∀ (log : Log Word),
      ∑ σ ∈ ext log, Pr{let r ← run H C σ comp (log, false)}[r.2.2 = true] ≤
        (ext log).card * hazardBudget H log.length q := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro q _ log
    simp [run_pure]
  | query_bind t next ih =>
    intro q bounded log
    change Oracle.callCost t ≤ q ∧
      (∀ answer, PublicQueryBound (next answer) (q - Oracle.callCost t)) at bounded
    rcases t with coins | publicQuery
    · -- private coins: free, and independent of the permutation
      have tails : ∀ a, PublicQueryBound (next a) q := bounded.2
      let coin : ProbComp (unifSpec.Range coins) := liftM (unifSpec.query coins)
      have unfold : ∀ σ, run H C σ ((liftM (World.query (.inl coins)) : OracleComp World _) >>= next)
          (log, false) = coin >>= fun a => run H C σ (next a) (log, false) := by
        intro σ
        rw [run_query_bind]
        simp only [step, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, coin]
        rfl
      simp only [unfold]
      calc ∑ σ ∈ ext log, Pr{let r ← coin >>= fun a => run H C σ (next a) (log, false)}[r.2.2 = true]
          = ∑ σ ∈ ext log, ∑ a, Pr{let x ← coin}[x = a] *
              Pr{let r ← run H C σ (next a) (log, false)}[r.2.2 = true] :=
            Finset.sum_congr rfl fun σ _ => prEvent_bind_eq_sum_fintype _ _ _
        _ = ∑ a, Pr{let x ← coin}[x = a] *
              ∑ σ ∈ ext log, Pr{let r ← run H C σ (next a) (log, false)}[r.2.2 = true] := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
        _ ≤ ∑ a, Pr{let x ← coin}[x = a] * ((ext log).card * hazardBudget H log.length q) := by
            gcongr with a
            exact ih a q (tails a) log
        _ = (∑ a, Pr{let x ← coin}[x = a]) * ((ext log).card * hazardBudget H log.length q) := by
            rw [Finset.sum_mul]
        _ ≤ 1 * ((ext log).card * hazardBudget H log.length q) := by
            gcongr
            exact sum_point_le_one coin
        _ = _ := one_mul _
    · have positive : 1 ≤ q := bounded.1
      have tails : ∀ a, PublicQueryBound (next a) (q - 1) := bounded.2
      have smaller : (ext log).card * hazardBudget H log.length (q - 1) ≤
          (ext log).card * hazardBudget H log.length q := by
        gcongr
        exact hazardBudget_mono H _ (Nat.sub_le q 1)
      rcases publicQuery with x | permQuery
      · -- compression: a fixed table, nothing logged
        have unfold : ∀ σ, run H C σ
            ((liftM (World.query (.inr (.inl x))) : OracleComp World _) >>= next) (log, false) =
            run H C σ (next (C x)) (log, false) := by
          intro σ
          rw [run_query_bind]
          simp only [step, pure_bind]
        simp only [unfold]
        exact (ih (C x) (q - 1) (tails _) log).trans smaller
      · rcases permQuery with x | y
        · -- forward permutation query
          have unfold : ∀ σ, run H C σ
              ((liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World _) >>= next)
              (log, false) = run H C σ (next (σ x)) (if x ∈ log.inputs then (log, false)
                else (log ++ [⟨x, σ x, false⟩], hit (H.forward log x) (σ x))) := by
            intro σ
            rw [run_query_bind]
            simp only [step, pure_bind, Bool.false_or]
          by_cases known : x ∈ log.inputs
          · simp only [unfold, known, ite_true]
            obtain ⟨answer, fixed⟩ := apply_of_mem_inputs known
            calc ∑ σ ∈ ext log, Pr{let r ← run H C σ (next (σ x)) (log, false)}[r.2.2 = true]
                = ∑ σ ∈ ext log, Pr{let r ← run H C σ (next answer) (log, false)}[r.2.2 = true] :=
                  Finset.sum_congr rfl fun σ hσ => by rw [fixed σ hσ]
              _ ≤ _ := (ih answer (q - 1) (tails _) log).trans smaller
          · refine (fresh_forward_step H log x known _
              (fun y σ => Pr{let r ← (run H C σ (next y)
                (log ++ [⟨x, y, false⟩], hit (H.forward log x) y))}[r.2.2 = true])
              (fun σ => ?_) (fun _ _ => prEvent_le_one _) (hazardBudget H (log.length + 1) (q - 1))
              (fun y notBad => ?_)).trans (le_of_eq ?_)
            · simp only [unfold, known, ite_false]
            · have cleared : hit (H.forward log x) y = false := hit_eq_false notBad
              have step := ih y (q - 1) (tails y) (log ++ [⟨x, y, false⟩])
              rw [List.length_append, List.length_singleton] at step
              simpa only [cleared] using step
            · rw [← hazardBudget_succ H _ q positive]
        · -- inverse permutation query
          have unfold : ∀ σ, run H C σ
              ((liftM (World.query (.inr (.inr (.inr y)))) : OracleComp World _) >>= next)
              (log, false) = run H C σ (next (σ.symm y)) (if y ∈ log.outputs then (log, false)
                else (log ++ [⟨σ.symm y, y, true⟩], hit (H.inverse log y) (σ.symm y))) := by
            intro σ
            rw [run_query_bind]
            simp only [step, pure_bind, Bool.false_or]
          by_cases known : y ∈ log.outputs
          · simp only [unfold, known, ite_true]
            obtain ⟨answer, fixed⟩ := symm_of_mem_outputs known
            calc ∑ σ ∈ ext log, Pr{let r ← run H C σ (next (σ.symm y)) (log, false)}[r.2.2 = true]
                = ∑ σ ∈ ext log, Pr{let r ← run H C σ (next answer) (log, false)}[r.2.2 = true] :=
                  Finset.sum_congr rfl fun σ hσ => by rw [fixed σ hσ]
              _ ≤ _ := (ih answer (q - 1) (tails _) log).trans smaller
          · refine (fresh_inverse_step H log y known _
              (fun x σ => Pr{let r ← (run H C σ (next x)
                (log ++ [⟨x, y, true⟩], hit (H.inverse log y) x))}[r.2.2 = true])
              (fun σ => ?_) (fun _ _ => prEvent_le_one _) (hazardBudget H (log.length + 1) (q - 1))
              (fun x notBad => ?_)).trans (le_of_eq ?_)
            · simp only [unfold, known, ite_false]
            · have cleared : hit (H.inverse log y) x = false := hit_eq_false notBad
              have step := ih x (q - 1) (tails x) (log ++ [⟨x, y, true⟩])
              rw [List.length_append, List.length_singleton] at step
              simpa only [cleared] using step
            · rw [← hazardBudget_succ H _ q positive]


/-! ## The contract's uniform permutation -/

/-- A uniform sample puts the same mass on every point (generic, so no cardinality of
`Perm` is ever computed). -/
theorem uniform_point_eq {γ : Type} [SampleableType γ] (a b : γ) :
    Pr{let τ ← ($ᵗ γ : ProbComp γ)}[τ = a] = Pr{let τ ← ($ᵗ γ : ProbComp γ)}[τ = b] := by
  let : MeasurableSpace γ := ⊤
  let : Fintype γ := Fintype.ofFinite γ
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton,
    SampleableType.evalDist_uniformSample, ProbabilityTheory.uniformOn_univ_apply_singleton,
    ProbabilityTheory.uniformOn_univ_apply_singleton]

/-- **Hazard bound.** For the contract's uniform permutation, any fixed compression table, and
any adversary making at most `q` public queries (private coins free), some fresh forward answer
lands in `H.forward` or some fresh inverse answer lands in `H.inverse` with probability at most
`∑_{j<q} H.bound j / (2^1600 - j)`. -/
theorem hazard_bound (H : Hazard) (C : Compression) {β : Type} (comp : OracleComp World β)
    (q : ℕ) (bounded : PublicQueryBound comp q) :
    Pr{let r ← ($ᵗ Perm >>= fun σ => run H C σ comp ([], false))}[r.2.2 = true] ≤
      hazardBudget H 0 q := by
  rw [prEvent_bind_eq_sum_fintype]
  set c := Pr{let τ ← ($ᵗ Perm : ProbComp Perm)}[τ = 1] with hc
  have point : ∀ σ : Perm, Pr{let τ ← ($ᵗ Perm : ProbComp Perm)}[τ = σ] = c :=
    fun σ => uniform_point_eq σ 1
  simp only [point]
  rw [← Finset.mul_sum]
  have whole : ext ([] : Log Word) = (Finset.univ : Finset Perm) :=
    Finset.eq_univ_iff_forall.mpr fun σ => by simp [mem_ext]
  have total := hazard_sum_bound H C comp q bounded []
  rw [whole, List.length_nil] at total
  have mass : c * ((Finset.univ : Finset Perm).card : ℝ≥0∞) ≤ 1 := by
    calc c * ((Finset.univ : Finset Perm).card : ℝ≥0∞)
        = ∑ σ : Perm, Pr{let τ ← ($ᵗ Perm : ProbComp Perm)}[τ = σ] := by
          rw [Finset.sum_congr rfl fun σ _ => point σ, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 1 := sum_point_le_one _
  calc c * ∑ σ, Pr{let r ← run H C σ comp ([], false)}[r.2.2 = true]
      ≤ c * (((Finset.univ : Finset Perm).card : ℝ≥0∞) * hazardBudget H 0 q) := by
        gcongr
    _ = (c * ((Finset.univ : Finset Perm).card : ℝ≥0∞)) * hazardBudget H 0 q := by
        rw [mul_assoc]
    _ ≤ 1 * hazardBudget H 0 q := by gcongr
    _ = hazardBudget H 0 q := one_mul _

/-! ## Numeric form of the budget -/

/-- While at most half of the domain is logged, a step costs at most `2b / 2^1600`. -/
theorem rate_le (H : Hazard) (m b : ℕ) (hb : H.bound m ≤ b) (room : 2 * m ≤ Fintype.card Word) :
    rate H m ≤ ((2 * b : ℕ) : ℝ≥0∞) / (Fintype.card Word : ℝ≥0∞) := by
  unfold rate
  have hN : (Fintype.card Word : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have nonempty : 0 < Fintype.card Word := Fintype.card_pos
  have hpos : 0 < Fintype.card Word - m := by omega
  have twice : Fintype.card Word ≤ 2 * (Fintype.card Word - m) := by omega
  rw [ENNReal.le_div_iff_mul_le (Or.inl hN) (Or.inl (ENNReal.natCast_ne_top _))]
  calc (H.bound m : ℝ≥0∞) / ((Fintype.card Word - m : ℕ) : ℝ≥0∞) * Fintype.card Word
      ≤ (H.bound m : ℝ≥0∞) / ((Fintype.card Word - m : ℕ) : ℝ≥0∞) *
          (((Fintype.card Word - m : ℕ) : ℝ≥0∞) * 2) := by
        gcongr
        exact_mod_cast (by omega : Fintype.card Word ≤ (Fintype.card Word - m) * 2)
    _ = (H.bound m : ℝ≥0∞) * 2 := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by exact_mod_cast hpos.ne')
          (ENNReal.natCast_ne_top _)]
    _ ≤ ((2 * b : ℕ) : ℝ≥0∞) := by
        rw [mul_comm]
        exact_mod_cast Nat.mul_le_mul_left 2 hb

/-- A per-step size bound `b` and a half-full domain give `hazardBudget ≤ q · 2b / 2^1600`. -/
theorem hazardBudget_le (H : Hazard) (k q b : ℕ) (each : ∀ j < q, H.bound (k + j) ≤ b)
    (room : 2 * (k + q) ≤ Fintype.card Word) :
    hazardBudget H k q ≤ q * (((2 * b : ℕ) : ℝ≥0∞) / (Fintype.card Word : ℝ≥0∞)) := by
  unfold hazardBudget
  calc ∑ j ∈ Finset.range q, rate H (k + j)
      ≤ ∑ _j ∈ Finset.range q, ((2 * b : ℕ) : ℝ≥0∞) / (Fintype.card Word : ℝ≥0∞) :=
        Finset.sum_le_sum fun j hj => rate_le H (k + j) b (each j (Finset.mem_range.mp hj))
          (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end PermLean
