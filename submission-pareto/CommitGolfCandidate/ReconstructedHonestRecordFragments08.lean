import CommitGolfCandidate.ReconstructedHonestRecordCheck

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem receipt800 : ∀ i : Fin 128, checked i.val 800=true := by decide +kernel

theorem receipt816 : ∀ i : Fin 128, checked i.val 816=true := by decide +kernel

theorem receipt832 : ∀ i : Fin 128, checked i.val 832=true := by decide +kernel

theorem receipt848 : ∀ i : Fin 128, checked i.val 848=true := by decide +kernel

theorem receipt864 : ∀ i : Fin 128, checked i.val 864=true := by decide +kernel

theorem receipt880 : ∀ i : Fin 128, checked i.val 880=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
