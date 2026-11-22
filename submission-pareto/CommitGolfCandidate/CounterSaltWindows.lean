import CommitGolfCandidate.CounterSaltLayout
import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.TaggedPinnedModel

/-!
# Salt slices of the K1 generator reply

The generator reply of a group, as 25 words: rank 0 (the A leaf) takes words 0,1, rank 1 (the C
leaf) words 23,24 and rank `r ≥ 2` words `2 (r-1), 2 (r-1)+1` (`CounterSaltLayout.bitOffset`).
-/

namespace TwoPermutationPrototype.RV64.PackedLeaves.Counter
open CommitGolf TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (parts bitOffset)

/-- First reply word of the salt of rank `j`. -/
def sliceStart (j : Fin 11) : Nat := if j.val=0 then 0 else if j.val=1 then 23 else 2*(j.val-1)

theorem slice_start_bound (j : Fin 11) : sliceStart j+2≤25 := by
  have := j.isLt;unfold sliceStart;split_ifs <;> omega

def slice (z : Words 25) (j : Fin 11) : Words 2 :=
  fun i => z ⟨sliceStart j+i.val, by have := i.isLt;have := slice_start_bound j;omega⟩

theorem slice_eq (z : BitVec 1600) (j : Fin 11) :
    slice (replyWords z) j = saltWords ((parts z).1 j) := by
  funext i
  have hi := i.isLt
  have off : bitOffset j=64*sliceStart j := by unfold bitOffset sliceStart;split_ifs <;> omega
  unfold slice saltWords parts replyWords
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have low : k<64 := hk
  have inner : 64*i.val+k<128 := by omega
  simp only [BitVec.getLsbD_extractLsb',low,inner,decide_true,Bool.true_and,off]
  congr 1
  omega

theorem slice_window (z : Words 25) (j : Fin 11) (m : Memory) (base : Nat)
    (h : window m base=z) : (window m (base+sliceStart j) : Words 2)=slice z j := by
  funext i
  have e := congrFun h ⟨sliceStart j+i.val,by have := i.isLt;have := slice_start_bound j;omega⟩
  simp only [window] at e ⊢
  simp only [slice]
  rw [←e,Nat.add_assoc]

end TwoPermutationPrototype.RV64.PackedLeaves.Counter
