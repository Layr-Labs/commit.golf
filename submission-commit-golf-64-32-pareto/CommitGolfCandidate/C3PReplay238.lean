import CommitGolfCandidate.C3PPermWitnessBound
import CommitGolfCandidate.C3XReplay238

/-! # The replay bound of the paired 3c1p leaf over a 238-bit tree

tree `255·q/2^128` (`c3_tree238_bound`), leaf `q/2^132` (`c3p_perm_witness_bound_sharp`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp OracleComp.DeferredSampling

set_option autoImplicit false

def C3PReplayEvidence238 (rows : List PublicRow) : Prop :=
  CompressionWitness238 rows ∨ C3PPermWitness rows

theorem C3PReplayEvidence.to238 {rows : List PublicRow} (hit : C3PReplayEvidence rows) :
    C3PReplayEvidence238 rows := by
  rcases hit with tree | leaf
  · exact Or.inl tree.to238
  · exact Or.inr leaf

theorem C3PReplayEvidence238.mono {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later) (evidence : C3PReplayEvidence238 earlier) :
    C3PReplayEvidence238 later := by
  rcases evidence with tree | leaf
  · exact Or.inl (tree.mono contained)
  · exact Or.inr (leaf.mono contained)

theorem c3p_budget_sum_238 (q : Nat) :
    255 * (q : ENNReal) / 2 ^ 128 + (q : ENNReal) / 2 ^ 132 ≤ (q : ENNReal) / 2 ^ 120 := by
  have leaf : (q : ENNReal) / 2 ^ 132 ≤ (q : ENNReal) / 2 ^ 128 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  refine (add_le_add le_rfl leaf).trans_eq ?_
  rw [← ENNReal.add_div, show 255 * (q : ENNReal) + q = 2 ^ 8 * q by ring,
    show (2 : ENNReal) ^ 128 = 2 ^ 8 * 2 ^ 120 by
      rw [show (128 : Nat) = 8 + 120 by decide, pow_add]]
  exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

theorem c3p_replay_bound_238 {α : Type} (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3PReplayEvidence238 result.2] ≤ (q : ENNReal) / 2 ^ 120 := by
  unfold C3PReplayEvidence238
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans (c3p_budget_sum_238 q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (recordRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness238 result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      c3_tree238_bound p program q calls positive small withReplay bounded
  · exact c3p_perm_witness_bound_sharp program q calls positive small withReplay bounded

theorem scheme_binding_of_c3p_replay_238 (scheme : Scheme)
    (spec : BindingReplayEvidence scheme C3PReplayEvidence238) : scheme.Binding :=
  scheme_binding_of_replay_with scheme spec (fun included evidence => evidence.mono included)
    fun program q calls positive small replayed bounded =>
      c3p_replay_bound_238 program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
