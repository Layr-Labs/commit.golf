import CommitGolfCandidate.K1CheckFacts
import CommitGolfCandidate.Layout2V1DeliveredData

/-! The one-byte checker's facts with the delivered V1 tables (`decTables`); `Cap.decoder` is their conversion. -/
namespace CommitGolf.K1Check
open TwoPermutationPrototype CommitGolfCandidate.Layout2

theorem onebyte_checker_facts :
    QuartetCertificate.CheckerFactsEnc CommitGolfCandidate.Layout2.Cap.obEnc K1Artifact.submission :=
  checker_facts_onebyte_for decTables v1_delivered_wellFormed v1_physical (fun _ _ => rfl)

end CommitGolf.K1Check
