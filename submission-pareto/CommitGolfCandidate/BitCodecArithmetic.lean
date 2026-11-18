import CommitGolfCandidate.ProofCodecBits
import CommitGolfCandidate.TwoPermutationPackedUnpackPrefix

namespace CommitGolfCandidate.ProofCodec.BitPacked
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype.Packed.Checker

theorem source_min (k bit : Nat) :
    sourceBit k bit=bit+min k (bit/3847+if 367≤bit%3847 then 1 else 0) := by
  by_cases within : bit<3847*k <;> by_cases head : 367≤bit%3847 <;>
    simp only [sourceBit,within,head,ite_true,ite_false] <;> omega

theorem less_flag (a b : Nat) (ha : a<2^40) (hb : b<2^40) :
    (2^64-b+a)%2^64/2^63=(if a<b then 1 else 0) := by
  by_cases before : a<b
  · rw [if_pos before,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg before,show (2^64-b+a)%2^64=a-b by omega]
    omega

def minCode : List Instr := [
  .SUB .x31 .x7 .x16,.SRLI .x31 .x31 63,
  .SUB .x30 .x16 .x7,.MUL .x30 .x30 .x31,.SUB .x7 .x16 .x30]

theorem min_code (v : Reg → Nat) (ha : v .x7<2^40) (hb : v .x16<2^40) :
    (minCode.foldl stepV v) .x7=min (v .x16) (v .x7) := by
  unfold minCode
  vsimp
  simp only [show (63 : BitVec 6).toNat=63 from rfl]
  have flag := less_flag _ _ ha hb
  norm_num only [Nat.reducePow] at flag ⊢
  rw [flag]
  by_cases before : v .x7<v .x16
  · rw [if_pos before,Nat.min_eq_right (by omega)]
    simp only [Nat.mul_one]
    omega
  · rw [if_neg before,Nat.min_eq_left (by omega)]
    simp only [Nat.mul_zero,Nat.zero_mod,Nat.sub_zero]
    omega

theorem expand_keep (k bit : Nat) :
    (if omitted k bit then 0 else 1)=
      1-((bit+3480)%3848+1)/3848*(if (bit+3480)/3848<k then 1 else 0) := by
  by_cases head : bit%3848=367
  · have quotient : (bit+3480)/3848=bit/3848 := by omega
    have remainder : (bit+3480)%3848=3847 := by omega
    by_cases within : bit/3848<k <;> simp [omitted,head,quotient,remainder,within]
  · have zero : ((bit+3480)%3848+1)/3848=0 := by omega
    simp [omitted,head,zero]

end CommitGolfCandidate.ProofCodec.BitPacked
