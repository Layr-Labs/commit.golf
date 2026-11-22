import CommitGolfCandidate.K1CheckFacts
import CommitGolfCandidate.Layout2V1DeliveredData

namespace CommitGolf.K1Check
open TwoPermutationPrototype CommitGolfCandidate.Layout2
theorem v2a_checker_facts : QuartetCertificate.CheckerFactsDec
    CommitGolfCandidate.Layout2.Quartet.decoder K1Artifact.submission :=
  checker_facts_dec_for decTables v1_delivered_wellFormed v1_physical

end CommitGolf.K1Check
