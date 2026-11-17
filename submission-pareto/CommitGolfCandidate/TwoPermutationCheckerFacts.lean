import CommitGolfCandidate.TwoPermutationCheckerContract
import CommitGolfCandidate.TwoPermutationCheckObservation

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling

structure CheckerObservationFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 26*input.positions.card
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    Nonempty (RecordedOpening oracle index.val (input.values index) input.commitment observed.1.2)
  honest : ∀ message salts, input = honestCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success

/-- Package the checker observations into exactly the quantified facts consumed by the certificate. -/
theorem checker_facts_of_observations
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      CheckerObservationFacts oracle input (checkObservation Assembly.submission oracle input)) :
    Assembly.CheckerFacts := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries, ?_, ?_⟩
  · intro oracle input
    dsimp only
    intro success
    have count := (checked oracle input).queries
    have cardinal : input.positions.card ≤ 16777216 := by
      have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
      exact h
    exact ⟨by omega, (checked oracle input).paths success⟩
  · intro oracle message positions salts
    exact (checked oracle (honestCheckInput oracle message positions salts)).honest message salts rfl

theorem checker_oversized_observation (oracle : Oracle) (input : CheckInput)
    (oversized : Assembly.submission.sizes.proof < input.proof.length) :
    CheckerObservationFacts oracle input (checkObservation Assembly.submission oracle input) := by
  rw [check_observation_oversized oracle input oversized]
  refine ⟨by decide,Nat.zero_le _,?_ ,?_⟩
  · intro impossible
    cases impossible
  · intro message salts canonical
    have valid : input.proof.length ≤ Assembly.submission.sizes.proof :=
      canonical.symm ▸ honest_input_admitted oracle message input.positions salts
    omega

end TwoPermutationPrototype.Checker
