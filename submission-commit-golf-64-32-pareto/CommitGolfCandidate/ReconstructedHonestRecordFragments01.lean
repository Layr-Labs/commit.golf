import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt111 : ∀ i : Fin 128, checked i.val 111=true := by decide +kernel

theorem receipt112 : ∀ i : Fin 128, checked i.val 112=true := by decide +kernel

theorem receipt128 : ∀ i : Fin 128, checked i.val 128=true := by decide +kernel

theorem receipt160 : ∀ i : Fin 128, checked i.val 160=true := by decide +kernel

theorem receipt176 : ∀ i : Fin 128, checked i.val 176=true := by decide +kernel

theorem receipt192 : ∀ i : Fin 128, checked i.val 192=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
