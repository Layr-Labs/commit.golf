import CommitGolfCandidate.CounterSaltLayout
import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.TaggedPinnedModel

namespace TwoPermutationPrototype.RV64.PackedLeaves.Counter
open CommitGolf TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (parts bitOffset)

def slice (z : Words 25) (j : Fin 11) : Words 2 :=
  fun i => z ⟨(if j.val = 0 then 23 else 2*(j.val-1))+i.val, by
    have := i.isLt;have := j.isLt;split <;> omega⟩

theorem slice_eq (z : BitVec 1600) (j : Fin 11) :
    slice (replyWords z) j = saltWords ((parts z).1 j) := by
  funext i
  have hi := i.isLt
  have bound : 64*i.val+64 ≤ 128 := by omega
  unfold slice saltWords parts replyWords bitOffset
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have low : k<64 := hk
  have inner : 64*i.val+k<128 := by omega
  simp only [BitVec.getLsbD_extractLsb',low,inner,decide_true,Bool.true_and]
  congr 1
  split <;> omega

/-- The base here is the first word of the expansion result, 120 bytes before the entry. -/
def directMemory (m : Memory) (base : Nat) (tag : Word) (a z : Words 25) : Memory :=
  writeWord (writeWindow (writeWindow m (base+11) a) base z) (base+22) tag

theorem direct_second (m : Memory) (base : Nat) (tag : Word) (a z : Words 25) :
    window (directMemory m base tag a z) (base+22) =
      pinnedWords tag (slice z 0) a (window m (base+15)) := by
  funext i
  have hi := i.isLt
  by_cases h0 : i.val=0
  · simp [window,directMemory,writeWord,pinnedWords,h0]
  have diff : base+22+i.val ≠ base+22 := by omega
  by_cases h3 : i.val<3
  · have hit : base≤base+22+i.val ∧ base+22+i.val<base+25 := by omega
    simp only [window,directMemory,writeWord,diff,ite_false,writeWindow,hit,dite_true,pinnedWords,h0,h3,slice,true_and,Fin.val_zero,ite_true]
    congr 1
    apply Fin.ext
    dsimp;omega
  have no : ¬(base≤base+22+i.val ∧ base+22+i.val<base+25) := by omega
  simp only [window,directMemory,writeWord,diff,ite_false,writeWindow,no,dite_false,pinnedWords,h0,h3]
  by_cases h : i.val<14
  · have yes : base+11≤base+22+i.val ∧ base+22+i.val<base+11+25 := by omega
    simp only [h,yes,dite_true,true_and]
    congr 1; apply Fin.ext; dsimp; omega
  · have out : ¬(base+11≤base+22+i.val ∧ base+22+i.val<base+11+25) := by omega
    simp only [h,out,dite_false]
    congr 1;omega

theorem retained_slices (m : Memory) (base : Nat) (tag : Word) (a z : Words 25)
    (j : Fin 11) (later : j.val ≠ 0) :
    window (directMemory m base tag a z) (base+2*(j.val-1)) = slice z j := by
  funext i
  have hj := j.isLt
  have hi := i.isLt
  have diff : base+2*(j.val-1)+i.val ≠ base+22 := by omega
  have hit : base≤base+2*(j.val-1)+i.val ∧ base+2*(j.val-1)+i.val<base+25 := by omega
  simp only [window,directMemory,writeWord,diff,ite_false,writeWindow,hit,dite_true,slice,later,true_and,ite_false]
  congr 1;apply Fin.ext;dsimp;omega

theorem write_outside (m : Memory) (base w : Nat) (tag : Word) (a z : Words 25)
    (h : w<base ∨ base+36≤w) : directMemory m base tag a z w=m w := by
  have outside : ¬(base≤w ∧ w<base+25) := by omega
  have outside' : ¬(base+11≤w ∧ w<base+11+25) := by omega
  have outsideTag : w≠base+22 := by omega
  simp [directMemory,writeWord,writeWindow,outside,outside',outsideTag]

end TwoPermutationPrototype.RV64.PackedLeaves.Counter
