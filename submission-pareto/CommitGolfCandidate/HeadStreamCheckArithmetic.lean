import CommitGolfCandidate.HeadStreamCheckWords

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open PackedOpening.Pack (w_add w_sub w_mul w_divu w_shl w_shr toNat_w w_inj w_or_mul)
open ProofCodec.HeadStream

theorem and_mask (x : Word) (n : Nat) (hn : n<64) :
    x &&& BitVec.ofNat 64 (2^n-1)=BitVec.ofNat 64 (x.toNat%2^n) := by
  apply BitVec.eq_of_toNat_eq
  have power : 2^n≤2^64 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2^n-1<2^64),Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem header_word (a b : Byte) (m : Nat) (hm : m<8) :
    ((BitVec.ofNat 64 a.toNat >>> m) |||
      (BitVec.ofNat 64 b.toNat * (256#64 >>> m))) &&& 63#64=
      BitVec.ofNat 64 ((a.toNat/2^m+b.toNat*2^(8-m))%64) := by
  have ab := a.isLt
  have bb := b.isLt
  have pow : 256/2^m=2^(8-m) := by interval_cases m <;> decide
  have low : a.toNat/2^m<2^(8-m) := by interval_cases m <;> norm_num at * <;> omega
  have hi : b.toNat*2^(8-m)<2^64 := by interval_cases m <;> norm_num at * <;> omega
  have sum : a.toNat/2^m+b.toNat*2^(8-m)<2^64 := by interval_cases m <;> norm_num at * <;> omega
  rw [w_shr _ _ (by omega),show 256#64=BitVec.ofNat 64 256 from rfl,
    w_shr _ _ (by decide),pow,w_mul,
    w_or_mul _ _ _ (8-m) rfl low (by have := Nat.div_le_self a.toNat (2^m);omega) hi sum]
  rw [show 63#64=BitVec.ofNat 64 (2^6-1) from rfl,and_mask _ 6 (by decide),toNat_w _ sum]
  rfl

theorem source_kept (k p : Nat) : ¬(compactSource k p<481*k ∧ compactSource k p%481=45) := by
  by_cases inside : p<480*k
  · rw [compact_record_source k p inside]
    by_cases h : 45≤p%480 <;> simp only [h,ite_true,ite_false] <;> omega
  · rw [compact_footer_source k p (by omega)]
    omega

theorem source_strict (k p q : Nat) (hpq : p<q) : compactSource k p<compactSource k q := by
  have div : (p+435)/480≤(q+435)/480 := Nat.div_le_div_right (by omega)
  unfold compactSource
  omega

theorem target_source (k p : Nat) : compactTarget k (compactSource k p)=p := by
  have eq := compact_source_target k (compactSource k p) (source_kept k p)
  by_cases lo : compactTarget k (compactSource k p)<p
  · have := source_strict k _ _ lo
    omega
  by_cases hi : p<compactTarget k (compactSource k p)
  · have := source_strict k _ _ hi
    omega
  omega

end TwoPermutationPrototype.Packed.Checker.HeadRestore
