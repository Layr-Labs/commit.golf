import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.Layout2Abstract

namespace CommitGolf.K1Check
open CommitGolfCandidate TwoPermutationPrototype
open TwoPermutationPrototype.QuartetCertificate (CheckerFactsDec honestCheckInput)

/-- A certified checker on an encoded external input. Its trace, query budget and binding
depend only on the converted record bytes. No inverse table is required here. -/
theorem checker_facts_dec_for (τ : Layout2.Tables) (wf : Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → GroupedOpening.pget K1Artifact.checkData k=Layout2.tableByte τ k) :
    CheckerFactsDec (fun p proof=>Layout2.convert τ p.card proof) K1Artifact.submission := by
  have checked:=Packed.Checker.executable_converted_observation τ wf physical
  refine ⟨fun o i=>(checked o i).terminates,?_,Packed.Checker.binding_of_decoder τ wf physical,?_⟩
  · intro oracle i
    have calls:=(checked oracle i).queries
    change _≤26*i.positions.card at calls
    omega
  · intro oracle msg ps salts i _ canonical
    have same : i.positions=ps := congrArg CheckInput.positions canonical
    subst ps
    exact (checked oracle i).honest msg salts canonical

end CommitGolf.K1Check
