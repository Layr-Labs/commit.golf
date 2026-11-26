import CommitGolfCandidate.TwoPermutationBindingBridge
import CommitGolfCandidate.ChainedSchedule

/-! The chained checker uses the general replay interface with 32-bit overhead. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp
open TwoPermutationPrototype.Sampling

abbrev BindingReplay (scheme : Scheme) (witness : List PublicRow → Prop) :=
  BindingReplayEvidence scheme witness (2^32)

theorem replay_program_bound (scheme : Scheme) {witness : List PublicRow → Prop}
    (spec : BindingReplay scheme witness) (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (recordRows (boundedReplay spec.replay adversary budget)) (budget+2^32) :=
  bounded_replay_queries scheme spec adversary budget

theorem checker_replay_room (left right : Nat) (leftBound : left ≤ checkerBound (2^24))
    (rightBound : right ≤ checkerBound (2^24)) : left+right ≤ 2^32 := by
  have := replay_room
  omega

theorem binding_of_replay (scheme : Scheme) {witness : List PublicRow → Prop}
    (spec : BindingReplay scheme witness)
    (preserves : ∀ {earlier later}, (∀ row ∈ earlier, row ∈ later) → witness earlier → witness later)
    (collisionBound : ∀ (program : OracleComp World Unit) (q calls : Nat),
      1 ≤ q → q ≤ 2^120 → calls ≤ q+2^32 → PublicQueryBound (recordRows program) calls →
      Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
        witness result.2] ≤ (q : ENNReal)/2^120) : scheme.Binding :=
  scheme_binding_of_replay_with scheme spec preserves collisionBound

end CommitGolfCandidate.Chained
