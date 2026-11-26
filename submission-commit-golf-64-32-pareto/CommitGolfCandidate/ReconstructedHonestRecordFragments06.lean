import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt608 : ∀ i : Fin 128, checked i.val 608=true := by decide +kernel

theorem receipt624 : ∀ i : Fin 128, checked i.val 624=true := by decide +kernel

theorem receipt640 : ∀ i : Fin 128, checked i.val 640=true := by decide +kernel

theorem receipt656 : ∀ i : Fin 128, checked i.val 656=true := by decide +kernel

theorem receipt672 : ∀ i : Fin 128, checked i.val 672=true := by decide +kernel

theorem receipt688 : ∀ i : Fin 128, checked i.val 688=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
