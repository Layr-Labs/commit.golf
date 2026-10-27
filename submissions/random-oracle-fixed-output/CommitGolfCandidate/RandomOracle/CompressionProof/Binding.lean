import CommitGolf.BindingFinite
import CommitGolfCandidate.RandomOracle.CompressionProof.Honest
import CommitGolfCandidate.RandomOracle.CompressionProof.Lazy

/-! # Position binding for the compression Merkle baseline

Rechecking the two conflicting paths uses 48 calls and exposes a compression collision.
The adaptive collision bound is below `q / 2^128` for `1 ≤ q < 2^128`; for larger `q` the
required bound is at least one. Only the adversary's original calls count toward `q`. -/

namespace CommitGolf.CompressionBaseline
open OracleComp OracleSpec Scheme

/-! ### The reduction -/

open Classical in
/-- Re-climb both openings at a conflicting position, if there is one. -/
noncomputable def recheck (claim : Claim) : OracleComp HashWorld Unit :=
  if h : claim.Conflicting then
    let i := h.choose
    let h₀ := h.choose_spec.choose
    let h₁ := h.choose_spec.choose_spec.choose
    do
      let _ ← (liftM (climb i.1 (claim.values₀ ⟨i, h₀⟩)
        (pathOf claim.positions₀ claim.proof₀ ⟨i, h₀⟩)) : OracleComp HashWorld Digest)
      let _ ← (liftM (climb i.1 (claim.values₁ ⟨i, h₁⟩)
        (pathOf claim.positions₁ claim.proof₁ ⟨i, h₁⟩)) : OracleComp HashWorld Digest)
      return ()
  else return ()

theorem length_climbInputs (π : Hash) (index : Nat) (leaf : Digest) (siblings : List Digest) :
    (climbInputs π index leaf siblings).length = siblings.length := by
  induction siblings generalizing index leaf with
  | nil => rfl
  | cons s rest ih => simp [climbInputs, ih]

/-- When the claim wins against `π`, re-checking it from any table records at most
`2 × LOG_LENGTH` new pairs and leaves a table that is not `Good`. -/
theorem logRun_recheck (π : Hash) (claim : Claim) (hbreak : merkle.Breaks π claim)
    (table : Table) :
    ∃ table', logRun π (recheck claim) table = pure ((), table') ∧ ¬ Good table' ∧
      table'.length ≤ table.length + 2 * LOG_LENGTH := by
  obtain ⟨hconf, hacc₀, hacc₁⟩ := hbreak
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
    2 * (∑ j ∈ Finset.range n, (j + 1)) = n * (n + 1) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_add, mul_comm 2 (∑ j ∈ Finset.range n, j), Finset.sum_range_id_mul_two]
  cases n with
  | zero => simp
  | succ n => simp; ring

theorem binding_arith (q : Nat) (h1 : 1 ≤ q) (h2 : q < 2 ^ 128) :
    2 ^ 128 * (∑ j ∈ Finset.range (q + 48), (j + 1)) ≤ q * 2 ^ 256 := by
  have hs := sum_closed (q + 48)
  set S := ∑ j ∈ Finset.range (q + 48), (j + 1)
  zify at hs ⊢
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast h1
  have hq2 : (q : ℤ) ≤ 2 ^ 128 - 1 := by
    have : (q : ℤ) < 2 ^ 128 := by exact_mod_cast h2
    omega
  have hqq : (q : ℤ) * q ≤ q * (2 ^ 128 - 1) := mul_le_mul_of_nonneg_left hq2 hq0
  nlinarith [hqq, hq1, hs]

theorem sum_le (q : Nat) (h1 : 1 ≤ q) (h2 : q < 2 ^ 128) :
    ∑ j ∈ Finset.range (q + 48), ((j + 1 : Nat) : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) ≤
      (q : ENNReal) / 2 ^ 128 := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have h := binding_arith q h1 h2
  have h' : (2 : ENNReal) ^ 128 * ∑ j ∈ Finset.range (q + 48), ((j + 1 : Nat) : ENNReal) ≤
      (q : ENNReal) * 2 ^ 256 := by exact_mod_cast h
  calc _ = ((2 : ENNReal) ^ 128 * ∑ j ∈ Finset.range (q + 48), ((j + 1 : Nat) : ENNReal)) /
        (2 ^ 128 * 2 ^ 256) := by
          rw [ENNReal.mul_div_mul_left] <;> norm_num [div_eq_mul_inv]
    _ ≤ ((q : ENNReal) * 2 ^ 256) / (2 ^ 128 * 2 ^ 256) :=
      ENNReal.div_le_div_right h' _
    _ = _ := by
      rw [ENNReal.mul_div_mul_right] <;> norm_num [div_eq_mul_inv]

/-! ### Binding -/

/-- The adversary's win, followed by `recheck`, leaves a table that is not `Good`. -/
theorem probEvent_breaks_le (adversary : Adversary family) (q : Nat) :
    Pr[fun (π, claim, calls) => merkle.Breaks π claim ∧ calls ≤ q | finiteBindingGame adversary] ≤
      Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ q + 2 * LOG_LENGTH | do
        let π ← $ᵗ Hash
        logRun π (adversary >>= recheck) []] := by
  classical
  simp only [finiteBindingGame, OracleFamily.sample, IdealCompression.sample, Hash.family_run]
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
  rw [Scheme.bindingProbability_eq_finite _ (by trivial)]
  by_cases hbig : 2 ^ 128 ≤ q
  · refine probEvent_le_one.trans ?_
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
    exact_mod_cast hbig
  · push Not at hbig
    calc _ ≤ _ := probEvent_breaks_le adversary q
      _ ≤ _ := probEvent_not_good_le _ _
      _ ≤ _ := sum_le q hq hbig

end CommitGolf.CompressionBaseline
