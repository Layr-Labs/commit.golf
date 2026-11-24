import CommitGolfCandidate.JointOracle241Recorded
import CommitGolfCandidate.JointOracle241Sampling

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp JointOracle241
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2100

theorem joint241_witnesses_bad (layout : PeerLeafLayout) (rows : List PublicRow) (s : State)
    (stored : ∀ row ∈ rows, Stores s row)
    (hit : CompressionWitness rows ∨ PinnedLeafWitnessW 241 rows) : bad s := by
  rcases hit with collision | leaf
  · apply Or.inl
    apply projected_collision_width
    obtain ⟨x,y,a,b,left,right,different,equal⟩ := collision
    have query₀ : s.cache x = some a := stored _ left
    have query₁ : s.cache y = some b := stored _ right
    refine ⟨x,y,low240 a,low240 b,different,?_,?_,heq_of_eq equal⟩
    · change Option.map low240 (s.cache x) = some (low240 a)
      rw [query₀]
      rfl
    · change Option.map low240 (s.cache y) = some (low240 b)
      rw [query₁]
      rfl
  · exact Or.inr (pinned_witness_bad_width 241 (by decide) layout s.trace rows
      (fun x y present => stored (.permutation x y) present) leaf)

theorem joint_replay_bound_241_of_layout (layout : PeerLeafLayout) {α : Type}
    (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (replayed : calls ≤ q+2^31) (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      CompressionWitness result.2 ∨ PinnedLeafWitnessW 241 result.2] ≤ (q : ENNReal)/2^120 := by
  simp only [Oracle.sample,bind_assoc,pure_bind]
  rw [joint_sampling_probability]
  unfold lazyOut
  rw [prEvent_map]
  change Pr{let result ← model.run (recordRows program) State.empty}[
    CompressionWitness result.1.2 ∨ PinnedLeafWitnessW 241 result.1.2] ≤ _
  refine (prEvent_mono_of_support _ _ _ (fun result reached hit =>
    joint241_witnesses_bad layout result.1.2 result.2
      (recorded_stores program State.empty result reached).2 hit)).trans ?_
  exact lazy_bad_target (recordRows program) q calls positive replayed bounded

end TwoPermutationPrototype.Sampling
