import CommitGolfCandidate.ReconstructedCheckLowerLayout

namespace CommitGolfCandidate.Reconstruction.CheckLowerPlan
set_option maxRecDepth 26000
set_option maxHeartbeats 6000000

private theorem g0 : ∀ j : Fin 8, receipt (0+j.val) 222=true := by decide +kernel
private theorem g1 : ∀ j : Fin 8, receipt (8+j.val) 222=true := by decide +kernel
private theorem g2 : ∀ j : Fin 8, receipt (16+j.val) 222=true := by decide +kernel
private theorem g3 : ∀ j : Fin 8, receipt (24+j.val) 222=true := by decide +kernel
private theorem g4 : ∀ j : Fin 8, receipt (32+j.val) 222=true := by decide +kernel
private theorem g5 : ∀ j : Fin 8, receipt (40+j.val) 222=true := by decide +kernel
private theorem g6 : ∀ j : Fin 8, receipt (48+j.val) 222=true := by decide +kernel
private theorem g7 : ∀ j : Fin 8, receipt (56+j.val) 222=true := by decide +kernel

theorem width222 (r : Fin 64) : receipt r.val 222=true := by
  let j : Fin 8:=⟨r.val%8,by omega⟩
  let k : Fin 8:=⟨r.val/8,by have:=r.isLt;omega⟩
  have idx : r.val=8*k.val+j.val:=by change r.val=8*(r.val/8)+r.val%8;omega
  rw [idx]
  generalize k=z
  fin_cases z
  · exact g0 j
  · exact g1 j
  · exact g2 j
  · exact g3 j
  · exact g4 j
  · exact g5 j
  · exact g6 j
  · exact g7 j

end CommitGolfCandidate.Reconstruction.CheckLowerPlan
