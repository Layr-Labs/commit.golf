import CommitGolfCandidate.QuadCertificate
import CommitGolfCandidate.HybWrapHonest

/-! Checker-side facts for the hybrid compact proofs: the same four facts as
`QuadCertificate.CheckerFacts`, with honest acceptance stated for the compact honest input, and
the bridge from that input to the donor's honest input (the wrapper's expansion of an honest
compact proof is the honest donor proof, `HybWrap.expand_honest`). -/
namespace TwoPermutationPrototype.QuadCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

set_option autoImplicit false

/-- An honest checker input in the submitted compact format. -/
abbrev capCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  HybWrap.capCheckInput oracle message positions salts

structure CapCheckerFacts (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100*input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts,
    (Checker.checkObservation s oracle (capCheckInput oracle message positions salts)).1.1.exit = .success

theorem cap_check_input_length (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (capCheckInput oracle message positions salts).proof.length = HybWrap.compactLength positions := by
  unfold capCheckInput HybWrap.capCheckInput pentaHonestView
  exact cap_proof_length _ _ _ _

/-- The wrapper's expansion of an honest compact input is the donor's honest input. -/
theorem expand_cap_check_input (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    HybWrap.expandInput oracle (capCheckInput oracle message positions salts) =
      Quad.Checker.honestCheckInput oracle message positions salts :=
  HybWrap.expand_honest oracle message positions salts

end TwoPermutationPrototype.QuadCertificate
