import CommitGolfCandidate.HeadStreamExec
import CommitGolfCandidate.HeadStreamZero

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
set_option maxRecDepth 8192

theorem byte_and3 (x : Byte) : x.setWidth 64 &&& 3#64=BitVec.ofNat 64 (x.toNat%4) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  rw [show (3 : Nat)=2^2-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_and63 (x : Byte) : x.setWidth 64 &&& 63#64=BitVec.ofNat 64 (x.toNat%64) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  rw [show (63 : Nat)=2^6-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem merged_word (a b : Byte) :
    ((BitVec.ofNat 64 (b.toNat%4) <<< (6 : Nat)) |||
      BitVec.ofNat 64 (a.toNat%64)).setWidth 8=ProofCodec.HeadStreamZero.merge a b := by
  rw [w_shl _ 6,BitVec.or_comm]
  norm_num only [Nat.reducePow]
  rw [w_or_mul (a.toNat%64) (b.toNat%4) 64 6 rfl (by omega) (by omega) (by omega) (by omega),
    truncate_w]
  unfold ProofCodec.HeadStreamZero.merge
  congr 1
  omega

theorem merged_byte (a b : Byte) :
    (BitVec.ofNat 8 (b.toNat%4) <<< (6 : Nat)) ||| BitVec.ofNat 8 (a.toNat%64)=
      ProofCodec.HeadStreamZero.merge a b := by
  simpa using merged_word a b

end TwoPermutationPrototype.PackedOpening.HeadStream
