import CommitGolfCandidate.Stage3cPackedWords
namespace CommitGolfCandidate.Chained.BinaryMachine.Reader
open RiscvZkvm.Rv64
def window (v start n : Nat) := (v/2^start)%2^n

theorem append_window (v start n m : Nat) :
    window v start (n+m)=window v start n+2^n*window v (start+n) m := by
  simp only [window,pow_add,Nat.mod_mul,Nat.div_div_eq_div_mul]

theorem window_low (v start n m : Nat) (hm : m≤n) : window v start n % 2^m = window v start m := by
  apply Nat.mod_mod_of_dvd
  exact pow_dvd_pow _ hm

theorem window_high (v start n m : Nat) (hm : m≤n) : window v start n / 2^m = window v (start+m) (n-m) := by
  unfold window
  rw [show 2^n=2^m*2^(n-m) by rw [←pow_add,show m+(n-m)=n by omega],Nat.mod_mul_right_div_self,Nat.div_div_eq_div_mul,pow_add]

theorem refill_byte (v start bits : Nat) (lo : Word) (byte : BitVec 8)
    (buf : lo.toNat=window v start bits) (next : byte.toNat=window v (start+bits) 8) :
    lo ||| (byte.zeroExtend 64 <<< bits)=BitVec.ofNat 64 (window v start (bits+8)) := by
  rw [Writer.joined_word lo _ bits (buf ▸ Nat.mod_lt _ (Nat.two_pow_pos bits)),buf,append_window]
  have bound : window v (start+bits) 8 < 18446744073709551616 := by rw [←next];have h:=byte.isLt;omega
  simp [next,Nat.mod_eq_of_lt bound]

theorem extract_chunk (x : Word) (n : Nat) (le : n≤64) :
    ((x <<< (64-n)) >>> (64-n)).toNat=x.toNat%2^n := by
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  have eq : 2^64=2^(64-n)*2^n := by rw [←pow_add,show 64-n+n=64 by omega]
  rw [eq,Nat.mod_mul_right_div_self,Nat.mul_div_cancel _ (Nat.two_pow_pos (64-n))]

theorem take_window (x : Word) (v start haveBits chunk : Nat) (small : haveBits≤64) (enough : chunk≤haveBits)
    (buf : x.toNat=window v start haveBits) :
    ((x <<< (64-chunk)) >>> (64-chunk)).toNat=window v start chunk ∧
      (x >>> chunk).toNat=window v (start+chunk) (haveBits-chunk) := by
  rw [extract_chunk _ _ (by omega),BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,buf]
  exact ⟨window_low _ _ _ _ enough,window_high _ _ _ _ enough⟩

theorem packed_byte (t s ix) (i : Nat) (hi : i<Binary.proofBytes) :
    ((Binary.packed t s ix)[i]?.getD 0).toNat=
      window (Binary.encode (ix.flatMap (Binary.recordFields t s)++(List.range 256).map (Binary.slot t ix))) (8*i) 8 := by
  simp only [Binary.packed,List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some,BitVec.toNat_ofNat,window]
end CommitGolfCandidate.Chained.BinaryMachine.Reader
