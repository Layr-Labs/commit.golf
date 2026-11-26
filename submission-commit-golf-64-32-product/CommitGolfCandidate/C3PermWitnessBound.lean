import CommitGolfCandidate.C3XTable
import CommitGolfCandidate.C3XFlag

/-! # The cross-oracle binding event of the 3c1p leaf

`C3PermWitness`: two recorded permutation rows with different inputs and equal 256-bit output
prefixes, where the `t3` field of each input is the reply of a recorded compression row.

Neither oracle alone bounds this event (C3XLog.lean). The proof splits it on the marked run of
the program, which records the same rows for every fixed oracle (`marked_rows_erase`):

* the witness holds and the flag of `scan` is not raised: then the lazily sampled permutation
  table of the marked run is bad (`witness_bad_or_flag`), for every fixed compression function
  (`marked_table_probability`, at most `Q (Q - 1) / 2 · 2^1344 / (2^1600 - Q)`);
* the flag is raised: a fresh compression reply is the `t3` field of an input that an earlier
  inverse call returned, for every fixed permutation (`flag_bound`, at most
  `Q (Q - 1) / (2 · 2^256)`).

With `Q ≤ q + 2^31` public calls and `1 ≤ q ≤ 2^120` each part is at most `q / 2^134`, so the
event has probability at most `q / 2^133` (`c3_perm_witness_bound_sharp`).
`c3_perm_witness_bound` is the same statement at the share `q / 2^122` that the leader's tree
gives its leaf event. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp
  OracleComp.DeferredSampling

set_option autoImplicit false
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

/-! ### Arithmetic -/

/-- `Q^2 ≤ q · 2^122` for `Q ≤ q + 2^31` and `1 ≤ q ≤ 2^120`. -/
theorem c3_square_bound (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (count : calls ≤ q + 2 ^ 31) : calls * calls ≤ q * 2 ^ 122 := by
  have quadratic := Nat.mul_le_mul_left q small
  have floor := Nat.mul_le_mul_right (2 ^ 31 * 2 ^ 31) positive
  have reserve := Nat.mul_le_mul_left q (by decide : 2 * (2 ^ 31 * 2 ^ 31 + 2 * 2 ^ 31) ≤ 2 ^ 120)
  have bound := Nat.mul_le_mul count count
  nlinarith

/-- The union bound of the permutation table at the sizes of the leaf. -/
theorem c3_table_margin (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (count : calls ≤ q + 2 ^ 31) :
    ((calls : ℝ) * ((calls : ℝ) - 1) / 2 * ((2 ^ 1344 : ℕ) : ℝ) + (calls : ℝ) * ((0 : ℕ) : ℝ)) /
        (((2 ^ 1600 : ℕ) : ℝ) - calls) ≤ (q : ℝ) / 2 ^ 134 := by
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have qUpper : (q : ℝ) ≤ 2 ^ 120 := by exact_mod_cast small
  have nonneg : (0 : ℝ) ≤ calls := by positivity
  have terms : (calls : ℝ) ≤ (q : ℝ) + 2 ^ 31 := by exact_mod_cast count
  have callsUpper : (calls : ℝ) ≤ 2 ^ 121 := by
    have threshold : (2 : ℝ) ^ 120 + 2 ^ 31 ≤ 2 ^ 121 := by norm_num
    linarith
  have denominator : (2 : ℝ) ^ 1599 ≤ 2 ^ 1600 - (calls : ℝ) := by
    have threshold : (2 : ℝ) ^ 1599 + 2 ^ 121 ≤ 2 ^ 1600 := by norm_num
    linarith
  have denominatorPos : (0 : ℝ) < 2 ^ 1600 - (calls : ℝ) :=
    lt_of_lt_of_le (by positivity) denominator
  have squareBound : (calls : ℝ) * calls ≤ (q : ℝ) * 2 ^ 122 := by
    exact_mod_cast c3_square_bound q calls positive small count
  have factor : (calls : ℝ) * ((calls : ℝ) - 1) ≤ (calls : ℝ) * calls := by nlinarith
  have half : (calls : ℝ) * ((calls : ℝ) - 1) / 2 * 2 ^ 1344 =
      (calls : ℝ) * ((calls : ℝ) - 1) * 2 ^ 1343 := by
    rw [show (2 : ℝ) ^ 1344 = 2 * 2 ^ 1343 by norm_num]
    ring
  have unified : (2 : ℝ) ^ 122 * 2 ^ 1343 * 2 ^ 134 = 2 ^ 1599 := by norm_num
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero]
  rw [div_le_div_iff₀ denominatorPos (by positivity), half]
  calc (calls : ℝ) * ((calls : ℝ) - 1) * 2 ^ 1343 * 2 ^ 134
      ≤ (calls : ℝ) * calls * 2 ^ 1343 * 2 ^ 134 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right factor (by positivity))
          (by positivity)
    _ ≤ (q : ℝ) * 2 ^ 122 * 2 ^ 1343 * 2 ^ 134 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right squareBound (by positivity))
          (by positivity)
    _ = (q : ℝ) * 2 ^ 1599 := by rw [← unified]; ring
    _ ≤ (q : ℝ) * (2 ^ 1600 - (calls : ℝ)) := mul_le_mul_of_nonneg_left denominator qNonneg

/-- The flag term at the sizes of the leaf. -/
theorem c3_flag_margin (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (count : calls ≤ q + 2 ^ 31) :
    ((calls * (calls - 1) : ℕ) : ENNReal) / (2 * 2 ^ 256) ≤ (q : ENNReal) / 2 ^ 134 := by
  have natural : calls * (calls - 1) ≤ q * 2 ^ 123 := by
    have square := c3_square_bound q calls positive small count
    have shrink := Nat.mul_le_mul_left calls (Nat.sub_le calls 1)
    have double : q * 2 ^ 122 ≤ q * 2 ^ 123 := Nat.mul_le_mul_left q (by decide)
    omega
  have base : ((calls * (calls - 1) : ℕ) : ENNReal) ≤ (q : ENNReal) * 2 ^ 123 := by
    exact_mod_cast natural
  calc ((calls * (calls - 1) : ℕ) : ENNReal) / (2 * 2 ^ 256)
      ≤ ((q : ENNReal) * 2 ^ 123) / (2 * 2 ^ 256) := ENNReal.div_le_div_right base _
    _ = (q : ENNReal) / 2 ^ 134 := by
      rw [show (2 : ENNReal) * 2 ^ 256 = 2 ^ 134 * 2 ^ 123 by ring]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

theorem c3_budget_sum (q : ℕ) :
    (q : ENNReal) / 2 ^ 134 + (q : ENNReal) / 2 ^ 134 = (q : ENNReal) / 2 ^ 133 := by
  have same : (2 : ENNReal) ^ 134 = 2 ^ 133 * 2 := by
    rw [show (134 : ℕ) = 133 + 1 by decide, pow_succ]
  rw [same, ← ENNReal.add_div]
  have scaled : (q : ENNReal) + (q : ENNReal) = (q : ENNReal) * 2 := by ring
  rw [scaled]
  exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-! ### The two parts in the contract's model -/

/-- A witness without a raised flag, for every fixed compression function. -/
theorem c3_table_term {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound program calls) :
    Pr{let result ← (do let p ← $ᵗ Perm
                        fixedOracleRun ⟨compress, p⟩ (markedRows program))}[
      C3PermWitness (scan ScanState.init result.2).rows ∧
        ¬ (scan ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 := by
  have fits : calls < 2 ^ 1600 := by omega
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal
    ((marked_table_probability compress program calls fits bounded).trans
      (c3_table_margin q calls positive small withReplay))).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- A raised flag, for every fixed permutation. -/
theorem c3_flag_term {α : Type} (p : Perm) (program : OracleComp World α)
    (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound program calls) :
    Pr{let result ← (do let compress ← $ᵗ Compression
                        fixedOracleRun ⟨compress, p⟩ (markedRows program))}[
      (scan ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 :=
  (fixed_permutation_flag_bound p program calls bounded).trans
    (c3_flag_margin q calls positive small withReplay)

/-! ### The bound -/

/-- **The cross-oracle event of the 3c1p leaf.** For every program whose recorded public calls
number at most `calls ≤ q + 2^31`, with both oracles sampled uniformly, the recorded rows contain
a `C3PermWitness` with probability at most `q / 2^133`. -/
theorem c3_perm_witness_bound_sharp {α : Type} (program : OracleComp World α) (q calls : ℕ)
    (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3PermWitness result.2] ≤ (q : ENNReal) / 2 ^ 133 := by
  have plain : PublicQueryBound program calls := public_bound_of_record_rows bounded
  have rewritten : (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program)) =
      (fun result : α × List MarkedRow => (result.1, result.2.map MarkedRow.erase)) <$>
        (Oracle.sample >>= fun oracle => fixedOracleRun oracle (markedRows program)) := by
    rw [map_bind]
    exact bind_congr fun oracle => (marked_rows_erase oracle program).symm
  have coupled :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (recordRows program))}[C3PermWitness result.2] =
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        C3PermWitness (result.2.map MarkedRow.erase)] := by
    rw [rewritten, prEvent_map]
  have split :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        C3PermWitness (result.2.map MarkedRow.erase)] ≤
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        (C3PermWitness (scan ScanState.init result.2).rows ∧
          ¬ (scan ScanState.init result.2).flag) ∨ (scan ScanState.init result.2).flag] := by
    refine prEvent_mono _ _ _ fun result witness => ?_
    by_cases raised : (scan ScanState.init result.2).flag
    · exact Or.inr raised
    · exact Or.inl ⟨scan_witness result.2 witness, raised⟩
  have table :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        C3PermWitness (scan ScanState.init result.2).rows ∧
          ¬ (scan ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 := by
    simp only [Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      c3_table_term compress program q calls positive small withReplay plain
  have flag :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        (scan ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 := by
    have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (markedRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => (scan ScanState.init result.2).flag)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      c3_flag_term p program q calls positive small withReplay plain
  rw [coupled]
  exact (split.trans (prEvent_or_le _ _ _)).trans
    ((add_le_add table flag).trans_eq (c3_budget_sum q))

/-- The statement consumed by `C3ReplayBound`: the share `q / 2^122` of the leader's leaf event. -/
theorem c3_perm_witness_bound (program : OracleComp World Unit) (q calls : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3PermWitness result.2] ≤ (q : ENNReal) / 2 ^ 122 :=
  (c3_perm_witness_bound_sharp program q calls positive small withReplay bounded).trans
    (ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _)

end TwoPermutationPrototype.Sampling
