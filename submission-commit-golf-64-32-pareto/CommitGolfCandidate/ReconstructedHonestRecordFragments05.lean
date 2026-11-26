import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt512 : ∀ i : Fin 128, checked i.val 512=true := by decide +kernel

theorem receipt528 : ∀ i : Fin 128, checked i.val 528=true := by decide +kernel

theorem receipt544 : ∀ i : Fin 128, checked i.val 544=true := by decide +kernel

theorem receipt560 : ∀ i : Fin 128, checked i.val 560=true := by decide +kernel

theorem receipt576 : ∀ i : Fin 128, checked i.val 576=true := by decide +kernel

theorem receipt592 : ∀ i : Fin 128, checked i.val 592=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
