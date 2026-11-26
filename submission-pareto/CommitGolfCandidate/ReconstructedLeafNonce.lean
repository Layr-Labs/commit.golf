import CommitGolfCandidate.ReconstructedLeafMemory

namespace CommitGolfCandidate.Reconstruction.LeafNonce
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Words)
open Generator LeafMemory CommitWindows

def firstWord (l : Fin 12) : Fin 25 := ⟨if l.val = 0 then 23 else 2*(l.val-1), by
  have := l.isLt; split <;> omega⟩
def nextWord (l : Fin 12) : Fin 25 := ⟨(firstWord l).val+1,by
  have := l.isLt
  simp only [firstWord]; split <;> omega⟩

def selected (tape : BitVec 1600) (l : Fin 12) := tape.extractLsb' (saltBit l 0) 120

private theorem keep56 (k : Nat) :
    (0x00ffffffffffffff : BitVec 64).getLsbD k = decide (k < 56 ∧ k < 64) := by
  change (BitVec.ofNat 64 (2^56-1)).getLsbD k = _
  rw [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]
  by_cases h : k < 56 <;> by_cases h' : k < 64 <;> simp [h,h']

/-- Two physical words with the final byte cleared are precisely the same widened
120-bit salt used in the binding and hiding games, including the wrap to slot 23. -/
theorem pair (b : BitVec 1600) (l : Fin 12) :
    nonce (replyWords b (firstWord l)) (replyWords b (nextWord l)) =
      saltWords ((selected b l).setWidth 128) := by
  have atBit : saltBit l 0 = 64*(firstWord l).val := by simp [saltBit,firstWord,Nat.mul_comm]
  funext j
  fin_cases j
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp [nonce,replyWords,saltWords,selected,BitVec.getLsbD_extractLsb',atBit,hk,show k<120 by omega,show k<128 by omega]
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have eq : 64*(nextWord l).val+k = 64*(firstWord l).val+(64+k) := by
      change 64*((firstWord l).val+1)+k = _; omega
    change ((replyWords b (nextWord l)) &&& 0x00ffffffffffffff).getLsbD k =
      (((selected b l).setWidth 128).extractLsb' 64 64).getLsbD k
    rw [BitVec.getLsbD_and,keep56,BitVec.getLsbD_extractLsb']
    by_cases included : k < 56 <;>
      simp [replyWords,selected,atBit,hk,show 64+k < 128 by omega,
        show (64+k<120) ↔ k<56 by omega,eq,included]

theorem zero (b : BitVec 1600) :
    zeroNonce b = saltWords ((selected b 0).setWidth 128) := pair b 0

end CommitGolfCandidate.Reconstruction.LeafNonce
