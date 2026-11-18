import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import CommitGolfCandidate.OverlapInputs
import CommitGolfCandidate.TwoPermutationMemoryBridge

namespace TwoPermutationPrototype.Overlap
open TwoPermutationPrototype.RV64

/-- r addresses the beginning of the first permutation's reply, thirteen words before the value. -/
def afterFirst (mem : Memory) (r : Nat) (a : Words 25) := writeWindow mem r a

def beforeSecond (mem : Memory) (r index : Nat) (salt : Words 2) (a : Words 25) :=
  writeWord (writeWord (writeWord (afterFirst mem r a) (r+20) (secondTag index))
    (r+25) (salt 0)) (r+26) (salt 1)

def resultMemory (mem : Memory) (r index dst : Nat) (s : Words 2) (a b : Words 25) :=
  writeWindow (beforeSecond mem r index s a) dst b

theorem first_window (mem : Memory) (r : Nat) :
    window (writeWord mem (r+12) 0) (r+12) = firstInput (window mem (r+13)) := by
  funext i
  fin_cases i <;> simp (disch := omega) [window,writeWord,firstInput,Nat.add_assoc]

theorem first_reply_over_zero (mem : Memory) (r : Nat) (a : Words 25) (w : Nat) :
    writeWindow (writeWord mem (r+12) 0) r a w = afterFirst mem r a w := by
  unfold afterFirst writeWindow
  split
  · rfl
  · rename_i h
    simp [writeWord,show w≠r+12 by omega]

theorem second_window (mem : Memory) (r index : Nat) (s : Words 2) (a : Words 25) :
    window (beforeSecond mem r index s a) (r+20) = secondInput index s a (window mem (r+13)) := by
  funext i
  fin_cases i <;> simp (disch := omega) [window,beforeSecond,afterFirst,writeWord,writeWindow,
    secondInput,Nat.add_assoc]

theorem outside (mem : Memory) (r index dst : Nat) (s : Words 2) (a b : Words 25) (w : Nat)
    (input : w<r ∨ r+27≤w) (output : w<dst ∨ dst+25≤w) :
    resultMemory mem r index dst s a b w = mem w := by
  have a0 : w≠r+20 := by omega
  have a1 : w≠r+25 := by omega
  have a2 : w≠r+26 := by omega
  have h1 : ¬ (dst≤w ∧ w<dst+25) := by omega
  have h2 : ¬ (r≤w ∧ w<r+25) := by omega
  simp only [resultMemory,beforeSecond,afterFirst,writeWindow,writeWord,dif_neg h1,dif_neg h2,
    if_neg a0,if_neg a1,if_neg a2]

theorem digest_words (mem : Memory) (r index dst : Nat) (s : Words 2) (a b : Words 25) :
    window (resultMemory mem r index dst s a b) dst = lowDigest b := by
  funext j
  have small := j.isLt
  have h : dst ≤ dst+j.val ∧ dst+j.val < dst+25 := by omega
  simp only [window,resultMemory,writeWindow,lowDigest,dif_pos h,Nat.add_sub_cancel_left]

end TwoPermutationPrototype.Overlap
