import CommitGolfCandidate.C3PBindingWitness
import CommitGolfCandidate.C3PermWitnessBound
import CommitGolfCandidate.C3PXTable
import CommitGolfCandidate.C3PXFlag

/-! # The cross-oracle binding event of the paired 3c1p leaf

`C3PPermWitness` is the event of `C3PermWitness` in two window shapes (`C3PBindingWitness`): even
leaves read `z` at input bits 1088..1344 and their digest at reply bits 1344..1600, odd leaves
read `z` at input bits 256..512 and their digest at reply bits 0..256.

`shape_witness_bound_sharp` is the proof of `c3_perm_witness_bound_sharp` with the two windows as
parameters (`C3PXScan`, `C3PXTable`, `C3PXFlag`). It asks only that each window value has at most
`2^1344` states, and gives `q / 2^133` per shape. The four fibre counts are below, and the two
shapes together cost `q / 2^132` (`c3p_perm_witness_bound_sharp`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp
  OracleComp.DeferredSampling

set_option autoImplicit false
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

/-! ### The two parts in the contract's model -/

/-- A witness without a raised flag, for every fixed compression function. -/
theorem shape_table_term (zField digest : Block → BitVec 256)
    (zFibre : ∀ c : BitVec 256, (Finset.univ.filter fun s : PermState => zField s = c).card ≤ 2 ^ 1344)
    (digestFibre : ∀ d : BitVec 256, (Finset.univ.filter fun s : PermState => digest s = d).card ≤ 2 ^ 1344)
    {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound program calls) :
    Pr{let result ← (do let p ← $ᵗ Perm
                        fixedOracleRun ⟨compress, p⟩ (markedRows program))}[
      C3PShapeWitness zField digest (shapeScan zField ScanState.init result.2).rows ∧
        ¬ (shapeScan zField ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 := by
  have fits : calls < 2 ^ 1600 := by omega
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal
    ((shape_table_probability zField digest zFibre digestFibre compress program calls fits bounded).trans
      (c3_table_margin q calls positive small withReplay))).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- A raised flag, for every fixed permutation. -/
theorem shape_flag_term (zField : Block → BitVec 256) {α : Type} (p : Perm) (program : OracleComp World α)
    (q calls : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound program calls) :
    Pr{let result ← (do let compress ← $ᵗ Compression
                        fixedOracleRun ⟨compress, p⟩ (markedRows program))}[
      (shapeScan zField ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 :=
  (shape_fixed_permutation_flag_bound zField p program calls bounded).trans
    (c3_flag_margin q calls positive small withReplay)

/-! ### The bound -/

/-- **The cross-oracle event of one window shape.** For every program whose recorded public calls
number at most `calls ≤ q + 2^31`, with both oracles sampled uniformly, the recorded rows contain
a `C3PShapeWitness zField digest` with probability at most `q / 2^133`. -/
theorem shape_witness_bound_sharp (zField digest : Block → BitVec 256)
    (zFibre : ∀ c : BitVec 256, (Finset.univ.filter fun s : PermState => zField s = c).card ≤ 2 ^ 1344)
    (digestFibre : ∀ d : BitVec 256, (Finset.univ.filter fun s : PermState => digest s = d).card ≤ 2 ^ 1344)
    {α : Type} (program : OracleComp World α) (q calls : ℕ)
    (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3PShapeWitness zField digest result.2] ≤ (q : ENNReal) / 2 ^ 133 := by
  have plain : PublicQueryBound program calls := public_bound_of_record_rows bounded
  have rewritten : (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program)) =
      (fun result : α × List MarkedRow => (result.1, result.2.map MarkedRow.erase)) <$>
        (Oracle.sample >>= fun oracle => fixedOracleRun oracle (markedRows program)) := by
    rw [map_bind]
    exact bind_congr fun oracle => (marked_rows_erase oracle program).symm
  have coupled :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (recordRows program))}[C3PShapeWitness zField digest result.2] =
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        C3PShapeWitness zField digest (result.2.map MarkedRow.erase)] := by
    rw [rewritten, prEvent_map]
  have split :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        C3PShapeWitness zField digest (result.2.map MarkedRow.erase)] ≤
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        (C3PShapeWitness zField digest (shapeScan zField ScanState.init result.2).rows ∧
          ¬ (shapeScan zField ScanState.init result.2).flag) ∨ (shapeScan zField ScanState.init result.2).flag] := by
    refine prEvent_mono _ _ _ fun result witness => ?_
    by_cases raised : (shapeScan zField ScanState.init result.2).flag
    · exact Or.inr raised
    · exact Or.inl ⟨shape_scan_witness zField digest result.2 witness, raised⟩
  have table :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        C3PShapeWitness zField digest (shapeScan zField ScanState.init result.2).rows ∧
          ¬ (shapeScan zField ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 := by
    simp only [Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      shape_table_term zField digest zFibre digestFibre compress program q calls positive small withReplay plain
  have flag :
      Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (markedRows program))}[
        (shapeScan zField ScanState.init result.2).flag] ≤ (q : ENNReal) / 2 ^ 134 := by
    have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (markedRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => (shapeScan zField ScanState.init result.2).flag)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      shape_flag_term zField p program q calls positive small withReplay plain
  rw [coupled]
  exact (split.trans (prEvent_or_le _ _ _)).trans
    ((add_le_add table flag).trans_eq (c3_budget_sum q))

/-! ### The windows of the paired leaf -/

/-- The even digest window is the window of `c3T3Field`: bits 1344..1600. -/
theorem c3p_even_digest_fibre (d : BitVec 256) :
    (Finset.univ.filter fun s : PermState => c3pEvenDigest s = d).card ≤ 2 ^ 1344 :=
  c3_field_fiber d

/-- At most `2^1344` states share bits 1088..1344. -/
theorem c3p_even_z_fibre (c : BitVec 256) :
    (Finset.univ.filter fun s : PermState => c3pEvenZField s = c).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun s : PermState => c3pEvenZField s = c)
    (t := (Finset.univ : Finset (BitVec 1344)))
    (fun s => BitVec.ofNat 1344 (s.toNat % 2 ^ 1088 + (s.toNat / 2 ^ 1344) * 2 ^ 1088))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [c3pEvenZField, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_ofNat] at e1 e2
      have hA := c3_state_lt a
      have hB := c3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-- At most `2^1344` states share bits 256..512. -/
theorem c3p_odd_z_fibre (c : BitVec 256) :
    (Finset.univ.filter fun s : PermState => c3pOddZField s = c).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun s : PermState => c3pOddZField s = c)
    (t := (Finset.univ : Finset (BitVec 1344)))
    (fun s => BitVec.ofNat 1344 (s.toNat % 2 ^ 256 + (s.toNat / 2 ^ 512) * 2 ^ 256))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [c3pOddZField, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_ofNat] at e1 e2
      have hA := c3_state_lt a
      have hB := c3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

theorem c3p_budget_sum (q : ℕ) :
    (q : ENNReal) / 2 ^ 133 + (q : ENNReal) / 2 ^ 133 = (q : ENNReal) / 2 ^ 132 := by
  have same : (2 : ENNReal) ^ 133 = 2 ^ 132 * 2 := by
    rw [show (133 : ℕ) = 132 + 1 by decide, pow_succ]
  rw [same, ← ENNReal.add_div]
  have scaled : (q : ENNReal) + (q : ENNReal) = (q : ENNReal) * 2 := by ring
  rw [scaled]
  exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-- **The cross-oracle event of the paired 3c1p leaf**: `q / 2^133` for each of its two shapes. -/
theorem c3p_perm_witness_bound_sharp {α : Type} (program : OracleComp World α) (q calls : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3PPermWitness result.2] ≤ (q : ENNReal) / 2 ^ 132 := by
  unfold C3PPermWitness
  exact (prEvent_or_le _ _ _).trans ((add_le_add
    (shape_witness_bound_sharp c3pEvenZField c3pEvenDigest c3p_even_z_fibre c3p_even_digest_fibre
      program q calls positive small withReplay bounded)
    (shape_witness_bound_sharp c3pOddZField outputDigest c3p_odd_z_fibre c3_digest_fiber
      program q calls positive small withReplay bounded)).trans_eq (c3p_budget_sum q))

end TwoPermutationPrototype.Sampling
