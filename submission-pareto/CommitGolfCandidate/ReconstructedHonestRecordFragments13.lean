import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt1280 : ∀ i : Fin 128, checked i.val 1280=true := by decide +kernel

theorem receipt1296 : ∀ i : Fin 128, checked i.val 1296=true := by decide +kernel

theorem receipt1312 : ∀ i : Fin 128, checked i.val 1312=true := by decide +kernel

theorem receipt1328 : ∀ i : Fin 128, checked i.val 1328=true := by decide +kernel

theorem receipt1344 : ∀ i : Fin 128, checked i.val 1344=true := by decide +kernel

theorem receipt1360 : ∀ i : Fin 128, checked i.val 1360=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
