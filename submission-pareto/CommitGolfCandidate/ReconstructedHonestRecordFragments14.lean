import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt1376 : ∀ i : Fin 128, checked i.val 1376=true := by decide +kernel

theorem receipt1392 : ∀ i : Fin 128, checked i.val 1392=true := by decide +kernel

theorem receipt1408 : ∀ i : Fin 128, checked i.val 1408=true := by decide +kernel

theorem receipt1424 : ∀ i : Fin 128, checked i.val 1424=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
