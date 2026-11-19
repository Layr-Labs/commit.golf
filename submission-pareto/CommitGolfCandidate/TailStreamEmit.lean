import CommitGolfCandidate.TailStreamCode
import CommitGolfCandidate.HeadStreamSeven
import CommitGolfCandidate.TwoPermutationPackedOpeningPack

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
set_option maxRecDepth 8192

theorem byte_and127 (x : Byte) :
    x.setWidth 64 &&& 127#64=BitVec.ofNat 64 (x.toNat%128) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  rw [show (127 : Nat)=2^7-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem packed_word (a b : Nat) (m : Nat) (ha : a<128) (hb : b<128) (hm : m<7) :
    ((BitVec.ofNat 64 a >>> m) ||| (BitVec.ofNat 64 b <<< (7-m))).setWidth 8=
      BitVec.ofNat 8 (a/2^m+b*2^(7-m)) := by
  rw [w_shr _ _ (by omega),w_shl]
  have low : a/2^m<2^(7-m) := by
    interval_cases m <;> norm_num at * <;> omega
  have fit : a/2^m+b*2^(7-m)<2^64 := by
    interval_cases m <;> norm_num at * <;> omega
  have lowFit : a/2^m<2^64 := by
    interval_cases m <;> norm_num at * <;> omega
  have highFit : b*2^(7-m)<2^64 := by
    interval_cases m <;> norm_num at * <;> omega
  rw [w_or_mul _ _ _ _ rfl low lowFit highFit fit,truncate_w]

theorem packed_group_byte (k : Nat) (Q : Proof) (g m : Nat) (hm : m<7) :
    ((BitVec.ofNat 64 (ProofCodec.HeadStreamSeven.head k Q (8*g+m)) >>> m) |||
      (BitVec.ofNat 64 (ProofCodec.HeadStreamSeven.head k Q (8*g+m+1)) <<< (7-m))).setWidth 8=
        ProofCodec.HeadStreamSeven.headPackedByte k Q (7*g+m) := by
  rw [packed_word _ _ _ (ProofCodec.HeadStreamSeven.head_lt k Q _)
    (ProofCodec.HeadStreamSeven.head_lt k Q _) hm,
    ProofCodec.HeadStreamSeven.head_group_byte k Q g m hm]
  have div : 8*m/7=m := by omega
  have rem : 8*m%7=m := by omega
  rw [div,rem]

end TwoPermutationPrototype.PackedOpening.TailStream
