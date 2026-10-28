import CommitGolf.Binding
import CommitGolfBaseline.MerkleProof.Honest
import CommitGolfBaseline.MerkleProof.Lazy

/-! # The Merkle baseline: binding

**Reduction.** Run the adversary, then re-climb both of its accepted paths at a conflicting
position (`recheck`, `2 × LOG_LENGTH = 48` calls). If the adversary wins, the two paths start
from different leaves and end at the same root, so some level compresses two different states
to the same digest (`collision_of_pClimb_eq`). Both states were just queried, so the recorded
table is not `Good`.

**Bound.** By `probEvent_not_good_le`, this happens within `q + 48` calls with probability at
most `∑_{j < q + 48} (j · 2^1344 + 2^512) / (2^1600 - j)`, roughly `(q + 48)² / 2^257`, which is
below `q / 2^128` for `1 ≤ q < 2^128`. For `q ≥ 2^128` the bound is at least `1`. -/

namespace CommitGolf.Baseline
open OracleComp OracleSpec Scheme

/-! ### The reduction -/

open Classical in
/-- Re-climb both openings at a conflicting position, if there is one. -/
noncomputable def recheck (claim : Claim) : OracleComp World Unit :=
  if h : claim.Conflicting then
    let i := h.choose
    let h₀ := h.choose_spec.choose
    let h₁ := h.choose_spec.choose_spec.choose
    do
      let _ ← (liftM (climb i.1 (claim.values₀ ⟨i, h₀⟩)
        (pathOf claim.positions₀ claim.proof₀ ⟨i, h₀⟩)) : OracleComp World Digest)
      let _ ← (liftM (climb i.1 (claim.values₁ ⟨i, h₁⟩)
        (pathOf claim.positions₁ claim.proof₁ ⟨i, h₁⟩)) : OracleComp World Digest)
      return ()
  else return ()

theorem length_climbInputs (π : Perm) (index : Nat) (leaf : Digest) (siblings : List Digest) :
    (climbInputs π index leaf siblings).length = siblings.length := by
  induction siblings generalizing index leaf with
  | nil => rfl
  | cons s rest ih => simp [climbInputs, ih]

/-- When the claim wins against `π`, re-checking it from any table records at most
`2 × LOG_LENGTH` new pairs and leaves a table that is not `Good`. -/
theorem logRun_recheck (π : Perm) (claim : Claim) (hbreak : merkle.Breaks π claim)
    (table : Table) :
    ∃ table', logRun π (recheck claim) table = pure ((), table') ∧ ¬ Good table' ∧
      table'.length ≤ table.length + 2 * LOG_LENGTH := by
  obtain ⟨hconf, hacc₀, hacc₁⟩ := hbreak
  simp only [Perm.family_eval] at hacc₀ hacc₁
  set i := hconf.choose
  set h₀ := hconf.choose_spec.choose
  set h₁ := hconf.choose_spec.choose_spec.choose
  have hne : claim.values₀ ⟨i, h₀⟩ ≠ claim.values₁ ⟨i, h₁⟩ :=
    hconf.choose_spec.choose_spec.choose_spec
  obtain ⟨hlen₀, hroot₀⟩ := check_accepts π _ _ _ _ hacc₀ ⟨i, h₀⟩
  obtain ⟨hlen₁, hroot₁⟩ := check_accepts π _ _ _ _ hacc₁ ⟨i, h₁⟩
  obtain ⟨x, hx, x', hx', hxx', hzx, hzx', htrunc⟩ :=
    collision_of_pClimb_eq π i.1 _ _ _ _ (hlen₀.trans hlen₁.symm) hne (hroot₀.trans hroot₁.symm)
  refine ⟨((climbInputs π i.1 (claim.values₁ ⟨i, h₁⟩)
      (pathOf claim.positions₁ claim.proof₁ ⟨i, h₁⟩)).map fun x => (x, π x)).reverse ++
    (((climbInputs π i.1 (claim.values₀ ⟨i, h₀⟩)
      (pathOf claim.positions₀ claim.proof₀ ⟨i, h₀⟩)).map fun x => (x, π x)).reverse ++ table),
    ?_, ?_, ?_⟩
  · simp only [recheck, dif_pos hconf]
    rw [logRun_bind, logRun_liftM_climb, pure_bind, logRun_bind, logRun_liftM_climb, pure_bind]
    rfl
  · intro hgood
    refine hxx' (hgood (x, π x) ?_ (x', π x') ?_ hzx hzx' htrunc)
    · simp only [List.mem_append, List.mem_reverse, List.mem_map]
      exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
    · simp only [List.mem_append, List.mem_reverse, List.mem_map]
      exact Or.inl ⟨x', hx', rfl⟩
  · simp [length_climbInputs, hlen₀, hlen₁]
    omega

/-! ### Arithmetic

The numbers involved have hundreds of digits; Lean's `norm_num` handles them once the
exponentiation threshold is raised. -/

set_option exponentiation.threshold 2000

theorem sum_closed (n : Nat) :
    2 * (∑ j ∈ Finset.range n, (j * 2 ^ 1344 + 2 ^ 512)) =
      2 ^ 1344 * (n * (n - 1)) + 2 * n * 2 ^ 512 := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_add, ← Finset.sum_range_id_mul_two]
  ring

theorem binding_arith (q : Nat) (h1 : 1 ≤ q) (h2 : q < 2 ^ 128) :
    2 ^ 128 * (∑ j ∈ Finset.range (q + 48), (j * 2 ^ 1344 + 2 ^ 512)) ≤
      q * (2 ^ 1600 - (q + 48)) := by
  have hs := sum_closed (q + 48)
  set S := ∑ j ∈ Finset.range (q + 48), (j * 2 ^ 1344 + 2 ^ 512)
  have hn : q + 48 ≤ 2 ^ 1600 := by
    have : (2:ℕ) ^ 128 + 48 ≤ 2 ^ 1600 := by norm_num
    omega
  have hsub : q + 48 - 1 = q + 47 := by omega
  rw [hsub] at hs
  suffices h : 2 * (2 ^ 128 * S) ≤ 2 * (q * (2 ^ 1600 - (q + 48))) by omega
  zify [hn] at hs ⊢
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast h1
  have hq2 : (q : ℤ) ≤ 2 ^ 128 - 1 := by
    have : (q : ℤ) < 2 ^ 128 := by exact_mod_cast h2
    omega
  have hqq : (q : ℤ) * q ≤ q * (2 ^ 128 - 1) := mul_le_mul_of_nonneg_left hq2 hq0
  nlinarith [hqq, hq1, hs]

theorem sum_le (q : Nat) (h1 : 1 ≤ q) (h2 : q < 2 ^ 128) :
    ∑ j ∈ Finset.range (q + 48),
        ((j * 2 ^ 1344 + 2 ^ 512 : Nat) : ENNReal) / ((2 ^ 1600 - j : Nat) : ENNReal) ≤
      (q : ENNReal) / 2 ^ 128 := by
  set n := q + 48
  set D : ℕ := 2 ^ 1600 - n
  have hD : 0 < D := by
    have : (2:ℕ) ^ 128 + 48 < 2 ^ 1600 := by norm_num
    omega
  calc ∑ j ∈ Finset.range n,
        ((j * 2 ^ 1344 + 2 ^ 512 : Nat) : ENNReal) / ((2 ^ 1600 - j : Nat) : ENNReal)
      ≤ ∑ j ∈ Finset.range n, ((j * 2 ^ 1344 + 2 ^ 512 : Nat) : ENNReal) / (D : ENNReal) := by
        refine Finset.sum_le_sum fun j hj => ENNReal.div_le_div_left ?_ _
        have := Finset.mem_range.mp hj
        exact_mod_cast (by omega : D ≤ 2 ^ 1600 - j)
    _ = ((∑ j ∈ Finset.range n, (j * 2 ^ 1344 + 2 ^ 512) : Nat) : ENNReal) / (D : ENNReal) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]
    _ = ((2 ^ 128 * ∑ j ∈ Finset.range n, (j * 2 ^ 1344 + 2 ^ 512) : Nat) : ENNReal) /
          ((2 ^ 128 * D : Nat) : ENNReal) := by
        push_cast
        rw [ENNReal.mul_div_mul_left] <;> simp
    _ ≤ ((q * D : Nat) : ENNReal) / ((2 ^ 128 * D : Nat) : ENNReal) := by
        exact ENNReal.div_le_div_right (Nat.cast_le.mpr (binding_arith q h1 h2)) _
    _ = (q : ENNReal) / 2 ^ 128 := by
        rw [Nat.cast_mul, Nat.cast_mul,
          ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hD.ne') (ENNReal.natCast_ne_top D)]
        norm_cast

/-! ### Binding -/

/-- The adversary's win, followed by `recheck`, leaves a table that is not `Good`. -/
theorem probEvent_breaks_le (adversary : Adversary merkle.oracles) (q : Nat) :
    Pr[fun (π, claim, calls) => merkle.Breaks π claim ∧ calls ≤ q | bindingGame adversary] ≤
      Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ q + 2 * LOG_LENGTH | do
        let π ← $ᵗ Perm
        logRun π (adversary >>= recheck) []] := by
  classical
  simp only [bindingGame, OracleFamily.sample, IdealPermutation.sample, Perm.family_run]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun π => mul_le_mul' le_rfl ?_
  rw [run_eq_logRun, logRun_bind, bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
  rw [probEvent_pure]
  split_ifs with h
  · obtain ⟨hbreak, hcalls⟩ := h
    obtain ⟨table', hrun, hbad, hlen⟩ := logRun_recheck π p.1 hbreak p.2
    have hcalls : p.2.length ≤ q := hcalls
    rw [hrun, probEvent_pure, if_pos ⟨hbad, by dsimp only; omega⟩]
  · exact zero_le

theorem merkle_binding : merkle.Binding := by
  intro adversary q hq
  by_cases hbig : 2 ^ 128 ≤ q
  · refine probEvent_le_one.trans ?_
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
    exact_mod_cast hbig
  · push Not at hbig
    calc _ ≤ _ := probEvent_breaks_le adversary q
      _ ≤ _ := probEvent_not_good_le _ _
      _ ≤ _ := sum_le q hq hbig

end CommitGolf.Baseline
