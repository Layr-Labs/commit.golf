import CommitGolfCandidate.CounterSaltLayout
import CommitGolfCandidate.TwoPermutationHidingHits

/-! Opening-side view of the K1 counter salts (`CounterSaltLayout`): the generator input words
and the reply words each salt rank takes. Self-contained so the opener proofs do not depend on
the commit-side modules. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input parts bitOffset)
set_option maxRecDepth 8000

/-- Salt-group rank of leaf `n`: 11-leaf groups inside each 4096-leaf tile. -/
def rank (n : Nat) := (n%4096)%11
/-- Word index of the message block of leaf `i` (byte `4096 + 256 i`). -/
def msgWord (i : Nat) := 512+32*i
/-- Generator input word `j` (`1 ≤ j ≤ 3`) holds key word `j-1`; later words are zero. -/
def keyBlock (key : BitVec 192) (j : Nat) : Word := key.extractLsb' (64*(j-1)) 64

theorem reply_pack (v : BitVec 1600) : packBuffer (replyWords v)=v := by
  apply BitVec.eq_of_getLsbD_eq;intro k hk
  let j : Fin 25 := ⟨k/64,by omega⟩
  have h:=congrArg (fun w : BitVec 64 => w.getLsbD (k%64)) (packed_word (replyWords v) j)
  have b : k%64<64 := by omega
  unfold replyWords at h
  dsimp only [j] at h
  change ((packBuffer _).extractLsb' (64*(k/64)) 64).getLsbD (k%64) =
    (v.extractLsb' (64*(k/64)) 64).getLsbD (k%64) at h
  unfold replyWords
  simpa only [BitVec.getLsbD_extractLsb',b,decide_true,Bool.true_and,Nat.div_add_mod] using h

theorem coordinate_first (i : Index) : firstLeaf (coord i).1=i.val-rank i.val := by
  unfold firstLeaf coord rank
  dsimp only
  have small : i.val%4096/11<373 := by omega
  rw [show (373*(i.val/4096)+i.val%4096/11)/373=i.val/4096 by omega,
    show (373*(i.val/4096)+i.val%4096/11)%373=i.val%4096/11 by omega]
  omega

/-- K1 generator input: word 0 is the base address of the group's C leaf (`ctr`), words 1..3 the key. -/
theorem input_word (idx : Index) (key : BitVec 192) (j : Fin 25) :
    replyWords (input (coord idx).1 key) j =
      (if j.val=0 then wordAddress (msgWord (idx.val-rank idx.val+1)) else keyBlock key j.val) := by
  unfold input replyWords
  have h := j.isLt
  by_cases zero : j.val=0
  · simp only [zero,ite_true,Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256),
      BitVec.extractLsb'_append_eq_right]
    unfold Permutation.CounterSalt.ctr
    rw [coordinate_first];unfold wordAddress msgWord;congr 1;omega
  · rw [if_neg zero]
    by_cases low : j.val<4
    · rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64*j.val+64≤256),
          BitVec.extractLsb'_append_eq_of_le (by omega : 64≤64*j.val)]
      unfold keyBlock;congr 1 <;> omega
    · rw [BitVec.extractLsb'_append_eq_of_le (by omega : 256≤64*j.val)]
      unfold keyBlock
      apply BitVec.eq_of_getLsbD_eq;intro k hk
      simp [hk,show 192≤64*(j.val-1)+k by omega]

/-- First reply word of salt slot `j` (K1 `bitOffset / 64`): rank 0 -> 0, rank 1 -> 23, rank r ≥ 2 -> 2(r-1). -/
def saltSlot (j : Fin 11) : Nat := if j.val=0 then 0 else if j.val=1 then 23 else 2*(j.val-1)

theorem salt_slot_bound (j : Fin 11) : saltSlot j+2≤25 := by
  have := j.isLt;unfold saltSlot;split;omega;split <;> omega

def saltSlice (z : Words 25) (j : Fin 11) : Words 2 :=
  fun i => z ⟨saltSlot j+i.val, by have := i.isLt;have := salt_slot_bound j;omega⟩

theorem salt_slice_eq (z : BitVec 1600) (j : Fin 11) :
    saltSlice (replyWords z) j = saltWords ((parts z).1 j) := by
  funext i
  have hi := i.isLt
  have off : bitOffset j=64*saltSlot j := by
    unfold bitOffset saltSlot;split;rfl;split;rfl;omega
  unfold saltSlice saltWords parts replyWords
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have inner : 64*i.val+k<128 := by omega
  simp only [BitVec.getLsbD_extractLsb',hk,inner,decide_true,Bool.true_and,off]
  congr 1
  omega

end TwoPermutationPrototype.GroupedOpening
