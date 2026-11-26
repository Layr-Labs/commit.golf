import CommitGolfCandidate.C3PermWitnessBound
import CommitGolfCandidate.K3T238Witness
import CommitGolfCandidate.K3T238Birthday
import CommitGolfCandidate.K3T238Budget

/-! # The replay bound of the 3c1p leaf over a 238-bit tree

For an entry whose internal nodes keep 238 bits (and whose leaf digest and `t3` stay at 256), the
evidence of a binding break is a compression collision on the low 238 bits of two replies
(`CompressionWitness238`, K3T238Witness) or the cross-oracle event `C3PermWitness`.

* tree: `255·q/2^128`, the product-form birthday bound at 238 bits for every fixed permutation
  (`projected238_collision_exp`, `t238_tree_budget`);
* leaf: `q/2^133` (`c3_perm_witness_bound_sharp`).

Together at most `q/2^120` (`c3_replay_bound_238`), which is what
`scheme_binding_of_replay_with` asks for. A 240-bit collision is a 238-bit one, so the evidence of
the 240-bit tree (`C3ReplayEvidence`) is covered as well (`C3ReplayEvidence.to238`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp OracleComp.DeferredSampling

set_option autoImplicit false
set_option maxRecDepth 8192

private theorem c3_projected238_witness_stored (rows : List PublicRow) (cache : CompressionCache)
    (stores : ∀ row ∈ rows, compressionStored cache row) (hit : CompressionWitness238 rows) :
    ProjectedCollision238 cache := by
  obtain ⟨x, y, a, b, left, right, different, equal⟩ := hit
  have query₀ : cache x = some a := stores _ left
  have query₁ : cache y = some b := stores _ right
  refine ⟨x, y, low238 a, low238 b, different, ?_, ?_, heq_of_eq equal⟩
  · change Option.map low238 (cache x) = some (low238 a)
    rw [query₀]
    rfl
  · change Option.map low238 (cache y) = some (low238 b)
    rw [query₁]
    rfl

/-- The 238-bit tree term for every fixed permutation (the statement of
`fixed_permutation_projected238_bound` in our product tree). -/
theorem c3_tree238_bound {α : Type} (p : Perm) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let compress ← $ᵗ Compression
                        fixedOracleRun ⟨compress, p⟩ (recordRows program))}[
      CompressionWitness238 result.2] ≤ 255 * (q : ENNReal) / 2 ^ 128 := by
  have room : calls ≤ 2 ^ 237 := by
    have top : q + 2 ^ 31 ≤ 2 ^ 120 + 2 ^ 31 := Nat.add_le_add_right small _
    have fits : (2 : Nat) ^ 120 + 2 ^ 31 ≤ 2 ^ 237 := by norm_num
    exact withReplay.trans (top.trans fits)
  have equivalent := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty p (recordRows program))).prEvent_eq
      (fun result => CompressionWitness238 result.2)
  rw [← equivalent, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ (fun result reached hit => ?_)).trans
    ((projected238_collision_exp p (recordRows program) calls bounded room).trans
      (t238_tree_budget q calls positive small withReplay))
  exact c3_projected238_witness_stored result.1.2 result.2
    (compression_replay_stored p program ∅ result reached) hit

/-- Evidence of a binding break over a 238-bit tree with 3c1p leaves. -/
def C3ReplayEvidence238 (rows : List PublicRow) : Prop :=
  CompressionWitness238 rows ∨ C3PermWitness rows

theorem C3ReplayEvidence.to238 {rows : List PublicRow} (hit : C3ReplayEvidence rows) :
    C3ReplayEvidence238 rows := by
  rcases hit with tree | leaf
  · exact Or.inl tree.to238
  · exact Or.inr leaf

theorem C3ReplayEvidence238.mono {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later) (evidence : C3ReplayEvidence238 earlier) :
    C3ReplayEvidence238 later := by
  rcases evidence with tree | leaf
  · exact Or.inl (tree.mono contained)
  · exact Or.inr (leaf.mono contained)

theorem c3_budget_sum_238 (q : Nat) :
    255 * (q : ENNReal) / 2 ^ 128 + (q : ENNReal) / 2 ^ 133 ≤ (q : ENNReal) / 2 ^ 120 := by
  have leaf : (q : ENNReal) / 2 ^ 133 ≤ (q : ENNReal) / 2 ^ 128 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  refine (add_le_add le_rfl leaf).trans_eq ?_
  rw [← ENNReal.add_div, show 255 * (q : ENNReal) + q = 2 ^ 8 * q by ring,
    show (2 : ENNReal) ^ 128 = 2 ^ 8 * 2 ^ 120 by
      rw [show (128 : Nat) = 8 + 120 by decide, pow_add]]
  exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

/-- **Binding replay bound, 238-bit tree and 3c1p leaves**: tree `255·q/2^128`, leaf `q/2^133`. -/
theorem c3_replay_bound_238 {α : Type} (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3ReplayEvidence238 result.2] ≤ (q : ENNReal) / 2 ^ 120 := by
  unfold C3ReplayEvidence238
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans (c3_budget_sum_238 q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (recordRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness238 result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      c3_tree238_bound p program q calls positive small withReplay bounded
  · exact c3_perm_witness_bound_sharp program q calls positive small withReplay bounded

/-- Binding of any scheme whose two-check replay exposes `C3ReplayEvidence238`. -/
theorem scheme_binding_of_c3_replay_238 (scheme : Scheme)
    (spec : BindingReplayEvidence scheme C3ReplayEvidence238) : scheme.Binding :=
  scheme_binding_of_replay_with scheme spec (fun included evidence => evidence.mono included)
    fun program q calls positive small replayed bounded =>
      c3_replay_bound_238 program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
