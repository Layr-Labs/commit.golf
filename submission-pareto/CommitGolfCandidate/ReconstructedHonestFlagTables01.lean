import CommitGolfCandidate.ReconstructedHonestFlagCheck

namespace CommitGolfCandidate.Reconstruction.HonestFlagCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 40000000

theorem flags192 : ∀ i : Fin 128, checked i.val 192=true := by decide +kernel

theorem flags197 : ∀ i : Fin 128, checked i.val 197=true := by decide +kernel

theorem flags208 : ∀ i : Fin 128, checked i.val 208=true := by decide +kernel

theorem flags224 : ∀ i : Fin 128, checked i.val 224=true := by decide +kernel

theorem flags240 : ∀ i : Fin 128, checked i.val 240=true := by decide +kernel

theorem flags256 : ∀ i : Fin 128, checked i.val 256=true := by decide +kernel

theorem flags272 : ∀ i : Fin 128, checked i.val 272=true := by decide +kernel

theorem flags288 : ∀ i : Fin 128, checked i.val 288=true := by decide +kernel

theorem flags304 : ∀ i : Fin 128, checked i.val 304=true := by decide +kernel

theorem flags320 : ∀ i : Fin 128, checked i.val 320=true := by decide +kernel

end CommitGolfCandidate.Reconstruction.HonestFlagCheck
