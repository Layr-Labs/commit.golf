import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt224 : ∀ i : Fin 128, checked i.val 224=true := by decide +kernel

theorem receipt240 : ∀ i : Fin 128, checked i.val 240=true := by decide +kernel

theorem receipt256 : ∀ i : Fin 128, checked i.val 256=true := by decide +kernel

theorem receipt272 : ∀ i : Fin 128, checked i.val 272=true := by decide +kernel

theorem receipt288 : ∀ i : Fin 128, checked i.val 288=true := by decide +kernel

theorem receipt304 : ∀ i : Fin 128, checked i.val 304=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
