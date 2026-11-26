import CommitGolfCandidate.ReconstructedHonestFlagCheck

namespace CommitGolfCandidate.Reconstruction.HonestFlagCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem flags496 : ∀ i : Fin 128, checked i.val 496=true := by decide +kernel

theorem flags512 : ∀ i : Fin 128, checked i.val 512=true := by decide +kernel

theorem flags528 : ∀ i : Fin 128, checked i.val 528=true := by decide +kernel

theorem flags544 : ∀ i : Fin 128, checked i.val 544=true := by decide +kernel

theorem flags560 : ∀ i : Fin 128, checked i.val 560=true := by decide +kernel

theorem flags576 : ∀ i : Fin 128, checked i.val 576=true := by decide +kernel

theorem flags592 : ∀ i : Fin 128, checked i.val 592=true := by decide +kernel

theorem flags608 : ∀ i : Fin 128, checked i.val 608=true := by decide +kernel

theorem flags624 : ∀ i : Fin 128, checked i.val 624=true := by decide +kernel

theorem flags640 : ∀ i : Fin 128, checked i.val 640=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestFlagCheck
