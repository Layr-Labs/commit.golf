import CommitGolfCandidate.ReconstructedHonestFlagCheck

namespace CommitGolfCandidate.Reconstruction.HonestFlagCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem flags130 : ∀ i : Fin 128, checked i.val 130=true := by decide +kernel

theorem flags111 : ∀ i : Fin 128, checked i.val 111=true := by decide +kernel

theorem flags112 : ∀ i : Fin 128, checked i.val 112=true := by decide +kernel

theorem flags128 : ∀ i : Fin 128, checked i.val 128=true := by decide +kernel

theorem flags143 : ∀ i : Fin 128, checked i.val 143=true := by decide +kernel

theorem flags144 : ∀ i : Fin 128, checked i.val 144=true := by decide +kernel

theorem flags149 : ∀ i : Fin 128, checked i.val 149=true := by decide +kernel

theorem flags160 : ∀ i : Fin 128, checked i.val 160=true := by decide +kernel

theorem flags176 : ∀ i : Fin 128, checked i.val 176=true := by decide +kernel

theorem flags184 : ∀ i : Fin 128, checked i.val 184=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestFlagCheck
