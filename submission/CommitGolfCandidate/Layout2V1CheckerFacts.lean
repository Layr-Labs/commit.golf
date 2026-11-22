import CommitGolfCandidate.K1CheckFacts
import CommitGolfCandidate.Layout2V1DeliveredData

namespace CommitGolf.K1Check
open CommitGolfCandidate TwoPermutationPrototype

theorem v1_checker_facts : QuartetCertificate.CheckerFactsDec
    (fun p P=>Layout2.convert Layout2.decTables p.card P) K1Artifact.submission :=
  checker_facts_dec_for Layout2.decTables Layout2.v1_delivered_wellFormed Layout2.v1_physical

end CommitGolf.K1Check
