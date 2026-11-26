import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt320 : ∀ i : Fin 128, checked i.val 320=true := by decide +kernel

theorem receipt336 : ∀ i : Fin 128, checked i.val 336=true := by decide +kernel

theorem receipt352 : ∀ i : Fin 128, checked i.val 352=true := by decide +kernel

theorem receipt368 : ∀ i : Fin 128, checked i.val 368=true := by decide +kernel

theorem receipt384 : ∀ i : Fin 128, checked i.val 384=true := by decide +kernel

theorem receipt400 : ∀ i : Fin 128, checked i.val 400=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
