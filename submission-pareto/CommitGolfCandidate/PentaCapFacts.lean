import CommitGolfCandidate.QuadCertificate
import CommitGolfCandidate.PentaCapRoundtrip

/-! Checker-side facts for level-7 cap proofs: the same four facts as
`QuadCertificate.CheckerFacts`, with honest acceptance stated for the cap honest input, and the
bridge from that input to the donor's honest input (the wrapper's expansion of an honest cap
proof is the honest penta proof). -/
namespace TwoPermutationPrototype.QuadCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

set_option autoImplicit false

/-- An honest checker input in the cap format. -/
def capCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := pentaHonestView capTranscriptBuilder
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

structure CapCheckerFacts (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100*input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts,
    (Checker.checkObservation s oracle (capCheckInput oracle message positions salts)).1.1.exit = .success

theorem cap_check_input_length (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (capCheckInput oracle message positions salts).proof.length = PentaWrap.capLength positions := by
  unfold capCheckInput pentaHonestView
  exact cap_proof_length _ _ _ _

/-- The wrapper's expansion of an honest cap input is the donor's honest input. -/
theorem expand_cap_check_input (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    PentaWrap.expandInput (capCheckInput oracle message positions salts) =
      honestCheckInput oracle message positions salts := by
  have h := PentaWrap.expand_cap_proof (pentaFunction (BiPermutation.equiv Block oracle.permutation).forward)
    positions (fun index => salts index.val)
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
  unfold capCheckInput honestCheckInput PentaWrap.expandInput pentaHonestView
  dsimp only
  rw [h]
  rfl

end TwoPermutationPrototype.QuadCertificate
