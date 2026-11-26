import CommitGolfCandidate.ReconstructedCheckRecordSpec
import CommitGolfCandidate.ReconstructedRecordDigits

namespace CommitGolfCandidate.Reconstruction.CheckHonestFields
open CommitGolf RiscvZkvm.Rv64 Wire
open TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000
abbrev W := BitVec.ofNat 64

theorem four (a b : List Field) (f g h k : Field) (hf : f.width≤64) (hg : g.width≤64) (hh : h.width≤64) (hk : k.width≤64) :
    let s := pack (a++f::g::h::k::b)
    HonestStream.get s (bits a) f.width=clipped f ∧
      HonestStream.get s (bits a+f.width) g.width=clipped g ∧
      HonestStream.get s (bits a+(f.width+g.width)) h.width=clipped h ∧
      HonestStream.get s (bits a+(f.width+g.width+h.width)) k.width=clipped k := by
  refine ⟨field_read a _ f hf,?_,?_,?_⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,bits_append,bits,Nat.add_zero]
      using field_read (a++[f]) (h::k::b) g hg
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,bits_append,bits,Nat.add_zero]
      using field_read (a++[f,g]) (k::b) h hh
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,bits_append,bits,Nat.add_zero,
      Nat.add_assoc] using field_read (a++[f,g,h]) b k hk

private theorem low_as_words (x : BitVec 192) :
    ((W ((x.toNat >>> 128)%2^64) ++ W ((x.toNat >>> 64)%2^64)) ++ W (x.toNat%2^64))=x := by
  have lo : W (x.toNat%2^64)=x.extractLsb' 0 64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]
  have mid : W ((x.toNat >>> 64)%2^64)=x.extractLsb' 64 64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]
  have hi : W ((x.toNat >>> 128)%2^64)=x.extractLsb' 128 64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]
  rw [lo,mid,hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  by_cases l : j<64 <;> by_cases m : j-64<64 <;>
    simp only [l,m,show j-64-64<64 by omega,decide_true,decide_false,ite_true,ite_false,
      Bool.true_and,Bool.false_and,Nat.zero_add] <;> congr 1 <;> omega

private theorem high_as_words (x : BitVec 64) (w : Nat) :
    (W (x.toNat >>> w) <<< w) ||| W (x.toNat%2^w)=x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
  have small := x.isLt
  have lower := Nat.mod_le x.toNat (2^w)
  have upper := Nat.div_le_self x.toNat (2^w)
  rw [Nat.mod_eq_of_lt (upper.trans_lt small),Nat.mod_eq_of_lt (lower.trans_lt small),
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self ..) small)]
  rw [←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos w)),Nat.shiftLeft_eq,Nat.mul_comm]
  exact Nat.div_add_mod _ _

theorem sibling (a b : List Field) (x : Binding.Digest) (w : Nat) (hi : w≤256) :
    CheckLowerInput.sibling (pack (a++Encoding.lowFields x w++b)) (bits a) w (Encoding.highDigit x w)=x := by
  rw [List.append_assoc]
  obtain ⟨v0,v1,v2,v3⟩ := four a b ⟨x.1.toNat,64⟩ ⟨x.1.toNat >>> 64,64⟩
    ⟨x.1.toNat >>> 128,64⟩ ⟨x.2.toNat,w-192⟩ (by change 64≤64;decide) (by change 64≤64;decide) (by change 64≤64;decide) (by change w-192≤64;omega)
  let s := pack (a++(Encoding.lowFields x w++b))
  change HonestStream.get s (bits a) 64=x.1.toNat%2^64 at v0
  change HonestStream.get s (bits a+64) 64=(x.1.toNat >>> 64)%2^64 at v1
  change HonestStream.get s (bits a+128) 64=(x.1.toNat >>> 128)%2^64 at v2
  change HonestStream.get s (bits a+192) (w-192)=x.2.toNat%2^(w-192) at v3
  change CheckLowerInput.sibling s (bits a) w (Encoding.highDigit x w)=x
  unfold CheckLowerInput.sibling
  rw [v0,v1,v2,v3]
  exact Prod.ext (low_as_words x.1) (high_as_words x.2 (w-192))

end CommitGolfCandidate.Reconstruction.CheckHonestFields
