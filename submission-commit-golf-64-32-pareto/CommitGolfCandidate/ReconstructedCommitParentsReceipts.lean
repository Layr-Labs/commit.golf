import CommitGolfCandidate.ReconstructedCommitParentsPacking
import CommitGolfCandidate.ReconstructedCommitParentsLine

namespace CommitGolfCandidate.Reconstruction.CommitParents.Image
open CommitGolf
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 5000000

/-- Each receipt compares the whole contiguous encoded level at once. The
packed-slice proof transfers this equality to the trusted per-PC decoder. -/
private theorem level0 : levelMatch 0 := by unfold levelMatch; decide +kernel
private theorem level1 : levelMatch 1 := by unfold levelMatch; decide +kernel
private theorem level2 : levelMatch 2 := by unfold levelMatch; decide +kernel
private theorem level3 : levelMatch 3 := by unfold levelMatch; decide +kernel
private theorem level4 : levelMatch 4 := by unfold levelMatch; decide +kernel
private theorem level5 : levelMatch 5 := by unfold levelMatch; decide +kernel
private theorem level6 : levelMatch 6 := by unfold levelMatch; decide +kernel
private theorem level7 : levelMatch 7 := by unfold levelMatch; decide +kernel
private theorem level8 : levelMatch 8 := by unfold levelMatch; decide +kernel
private theorem level9 : levelMatch 9 := by unfold levelMatch; decide +kernel
private theorem level10 : levelMatch 10 := by unfold levelMatch; decide +kernel
private theorem level11 : levelMatch 11 := by unfold levelMatch; decide +kernel
private theorem level12 : levelMatch 12 := by unfold levelMatch; decide +kernel
private theorem level13 : levelMatch 13 := by unfold levelMatch; decide +kernel
private theorem level14 : levelMatch 14 := by unfold levelMatch; decide +kernel
private theorem level15 : levelMatch 15 := by unfold levelMatch; decide +kernel
private theorem level16 : levelMatch 16 := by unfold levelMatch; decide +kernel
private theorem level17 : levelMatch 17 := by unfold levelMatch; decide +kernel
private theorem level18 : levelMatch 18 := by unfold levelMatch; decide +kernel
private theorem level19 : levelMatch 19 := by unfold levelMatch; decide +kernel
private theorem level20 : levelMatch 20 := by unfold levelMatch; decide +kernel
private theorem level21 : levelMatch 21 := by unfold levelMatch; decide +kernel
private theorem level22 : levelMatch 22 := by unfold levelMatch; decide +kernel
private theorem level23 : levelMatch 23 := by unfold levelMatch; decide +kernel

theorem all_levels (d : Fin 24) : levelMatch d := by
  fin_cases d
  · exact level0
  · exact level1
  · exact level2
  · exact level3
  · exact level4
  · exact level5
  · exact level6
  · exact level7
  · exact level8
  · exact level9
  · exact level10
  · exact level11
  · exact level12
  · exact level13
  · exact level14
  · exact level15
  · exact level16
  · exact level17
  · exact level18
  · exact level19
  · exact level20
  · exact level21
  · exact level22
  · exact level23

private theorem limit : ∀ d : Fin 24, start d (unroll d) ≤ 150132 := by decide

theorem node_loaded (d : Fin 24) (i : Fin (unroll d)) :
    Loaded CommitSetup.im (CommitBlocks.addr (start d i)) (body d i) := by
  intro j s pc
  have mono : start d (i.val+1) ≤ start d (unroll d) := by
    unfold start
    gcongr <;> have := i.isLt <;> omega
  have max := limit d
  rw [next_start] at mono
  have fin : start d i+j.val < 150132 := by have := j.isLt;omega
  apply CommitSetup.fetch_at ⟨_,fin⟩ _ _ s
  · change s.pc = CommitBlocks.addr (start d i+j.val)
    unfold CommitBlocks.addr at pc ⊢
    rw [pc,←BitVec.ofNat_add]
    congr 1;omega
  · rw [receipt_fetch d i i.isLt j (all_levels d)];exact Atom.decoded _

end CommitGolfCandidate.Reconstruction.CommitParents.Image
