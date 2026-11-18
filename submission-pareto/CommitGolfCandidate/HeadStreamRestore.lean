import CommitGolfCandidate.HeadStreamCodec
import Mathlib.Tactic.IntervalCases

namespace CommitGolfCandidate.ProofCodec.HeadStream
open CommitGolf

def expandedLength (k L : Nat) : Nat := L+k/8
def frontLength (k : Nat) (Q : Proof) : Nat := expandedLength k Q.length-k

def restoredHead (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  let p := frontLength k Q+7*r/8
  ((Q.getD p 0).toNat/2^(7*r%8)+(Q.getD (p+1) 0).toNat*2^(8-7*r%8))%128

def compactTarget (k p : Nat) : Nat := p-min k ((p+435)/481)

def expandedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<481*k ∧ p%481=45 then BitVec.ofNat 8 (restoredHead k Q (p/481))
  else Q.getD (compactTarget k p) 0

def restore (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (expandedLength k Q.length) => expandedByte k Q p.val

def unpack (k : Nat) (Q : Proof) : Option Proof := ProofCodec.unpack k (restore k Q)

@[simp] theorem restore_length (k : Nat) (Q : Proof) : (restore k Q).length=expandedLength k Q.length := by
  simp [restore]

theorem restore_convert_length (k : Nat) (Q : Proof) (records : 481*k≤Q.length) :
    expandedLength k (convert k Q).length=Q.length := by
  simp only [expandedLength,convert_length]
  omega

theorem front_convert (k : Nat) (Q : Proof) (records : 481*k≤Q.length) :
    frontLength k (convert k Q)=Q.length-k := by
  rw [frontLength,restore_convert_length k Q records]

theorem compact_source_target (k p : Nat) (kept : ¬(p<481*k ∧ p%481=45)) :
    compactSource k (compactTarget k p)=p := by
  by_cases within : p<481*k
  · by_cases before : p%481<45
    · have quotient : (p+435)/481=p/481 := by omega
      have target : compactTarget k p=480*(p/481)+p%481 := by
        unfold compactTarget
        rw [quotient,Nat.min_eq_right (by omega)]
        omega
      rw [target,compactSource,show (480*(p/481)+p%481+435)/480=p/481 by omega,
        Nat.min_eq_right (by omega)]
      omega
    · have after : 46≤p%481 := by omega
      have quotient : (p+435)/481=p/481+1 := by omega
      have target : compactTarget k p=480*(p/481)+(p%481-1) := by
        unfold compactTarget
        rw [quotient,Nat.min_eq_right (by omega)]
        omega
      rw [target,compactSource,show (480*(p/481)+(p%481-1)+435)/480=p/481+1 by omega,
        Nat.min_eq_right (by omega)]
      omega
  · have target : compactTarget k p=p-k := by
      unfold compactTarget
      rw [Nat.min_eq_left (by omega)]
    rw [target,compact_footer_source k _ (by omega)]
    omega

theorem compact_target_bound (k L p : Nat) (records : 481*k≤L) (inside : p<L)
    (kept : ¬(p<481*k ∧ p%481=45)) : compactTarget k p<L-k := by
  unfold compactTarget
  by_cases within : p<481*k
  · by_cases before : p%481<45
    · have quotient : (p+435)/481=p/481 := by omega
      rw [quotient,Nat.min_eq_right (by omega)]
      omega
    · have after : 46≤p%481 := by omega
      have quotient : (p+435)/481=p/481+1 := by omega
      rw [quotient,Nat.min_eq_right (by omega)]
      omega
  · rw [Nat.min_eq_left (by omega)]
    omega

theorem converted_head_byte (k : Nat) (Q : Proof) (p : Nat) (records : 481*k≤Q.length)
    (inside : Q.length-k+p<Q.length-k/8) :
    (convert k Q).getD (Q.length-k+p) 0=headPackedByte k Q p := by
  rw [getD_convert k Q _ inside,convertedByte,if_neg (by omega)]
  congr 1
  omega

theorem decode_middle (a b c m : Nat) (ha : a<128) (hb : b<128) (hc : c<128)
    (hm : 1≤m) (hm' : m≤6) :
    (((a/2^(m-1)+b*2^(8-m))%256)/2^(8-m)+
      ((b/2^m+c*2^(7-m))%256)*2^m)%128=b := by
  interval_cases m <;> norm_num at * <;> omega

theorem decode_first (a b u : Nat) (ha : a<128) :
    ((a+b*128)%256+u*256)%128=a := by omega

theorem decode_last (a b u : Nat) (ha : a<128) (hb : b<128) :
    (((a/64+b*2)%256)/2+u*128)%128=b := by omega

theorem head_tail_bound (k g m : Nat) (hm : m<7) (hr : 8*g+m<k) :
    7*g+m<k-k/8 := by
  by_cases h : k/8≤g <;> omega

theorem restored_head_group (k : Nat) (Q : Proof) (g m : Nat)
    (records : 481*k≤Q.length) (hm : m<8) (hr : 8*g+m<k) :
    restoredHead k (convert k Q) (8*g+m)=head k Q (8*g+m) := by
  by_cases first : m=0
  · subst m
    have tail := head_tail_bound k g 0 (by omega) hr
    have read := converted_head_byte k Q (7*g) records (by omega)
    rw [show 7*g=7*g+0 by omega,head_group_byte k Q g 0 (by omega)] at read
    simp only [Nat.add_zero] at read
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+0)/8=7*g by omega,
      show 7*(8*g+0)%8=0 by omega,read]
    simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceSub,Nat.div_one,Nat.add_zero]
    exact decode_first _ _ _ (head_lt k Q _)
  by_cases last : m=7
  · subst m
    have tail : 7*g+6<k-k/8 := by
      by_cases h : k/8≤g <;> omega
    have read := converted_head_byte k Q (7*g+6) records (by omega)
    rw [head_group_byte k Q g 6 (by omega)] at read
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+7)/8=7*g+6 by omega,
      show 7*(8*g+7)%8=1 by omega,read]
    simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceSub,Nat.div_one,Nat.add_assoc,Nat.reduceAdd]
    exact decode_last _ _ _ (head_lt k Q _) (head_lt k Q _)
  have mid : 1≤m ∧ m≤6 := by omega
  have tail := head_tail_bound k g m (by omega) hr
  have readA := converted_head_byte k Q (7*g+(m-1)) records (by omega)
  have readB := converted_head_byte k Q (7*g+m) records (by omega)
  rw [head_group_byte k Q g (m-1) (by omega)] at readA
  rw [head_group_byte k Q g m (by omega)] at readB
  dsimp only [restoredHead]
  rw [front_convert k Q records,show 7*(8*g+m)/8=7*g+(m-1) by omega,
    show 7*(8*g+m)%8=8-m by omega,readA,
    show Q.length-k+(7*g+(m-1))+1=Q.length-k+(7*g+m) by omega,readB,
    show 7-(m-1)=8-m by omega,show 8-(8-m)=m by omega,
    show 8*g+(m-1)+1=8*g+m by omega]
  simp only [BitVec.toNat_ofNat,Nat.reducePow]
  exact decode_middle _ _ _ m (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) mid.1 mid.2

theorem restored_head_convert (k : Nat) (Q : Proof) (r : Nat)
    (records : 481*k≤Q.length) (hr : r<k) :
    restoredHead k (convert k Q) r=head k Q r := by
  have eq : r=8*(r/8)+r%8 := by omega
  rw [eq]
  exact restored_head_group k Q _ _ records (by omega) (by omega)

theorem getD_restore (k : Nat) (Q : Proof) (p : Nat) (inside : p<expandedLength k Q.length) :
    (restore k Q).getD p 0=expandedByte k Q p := by
  simp [restore,List.getD_eq_getElem?_getD,inside]

theorem restore_convert (k : Nat) (Q : Proof) (records : 481*k≤Q.length)
    (heads : ∀ r<k, (Q.getD (481*r+45) 0).toNat<128) : restore k (convert k Q)=Q := by
  apply List.ext_getElem
  · rw [restore_length,restore_convert_length k Q records]
  intro p hp hq
  suffices equality : (restore k (convert k Q)).getD p 0=Q.getD p 0 by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hq] at equality
    exact equality
  rw [getD_restore k _ p (by rw [restore_convert_length k Q records];exact hq)]
  unfold expandedByte
  by_cases marked : p<481*k ∧ p%481=45
  · have hr : p/481<k := by omega
    have low := heads (p/481) hr
    have index : 481*(p/481)+45=p := by omega
    rw [index] at low
    rw [if_pos marked,restored_head_convert k Q _ records hr,head,if_pos hr,index,
      Nat.mod_eq_of_lt low]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · have bound := compact_target_bound k Q.length p records hq marked
    rw [if_neg marked,getD_convert k Q _ (by omega),convertedByte,if_pos bound,
      compact_source_target k p marked]

theorem restore_pack (k b : Nat) (P : Proof) (len : P.length=498*k+30*b)
    (leaf : ∀ r<k, (P.getD (498*r+46) 0).toNat<16) :
    restore k (pack k P)=ProofCodec.pack k P := by
  have count : unpackedCount k P.length=15*k+b := by rw [len,unpackedCount];omega
  have records : 481*k≤(ProofCodec.pack k P).length := by
    rw [ProofCodec.pack_length,count]
    unfold ProofCodec.packedLength bodyLength
    omega
  apply restore_convert k (ProofCodec.pack k P) records
  intro r hr
  rw [ProofCodec.getD_pack k P _ (by rw [count];unfold ProofCodec.packedLength bodyLength;omega),
    count,ProofCodec.packedByte,if_pos (by unfold bodyLength;omega),if_pos (by omega),
    show (481*r+45)/481=r by omega,ProofCodec.headByte_toNat]
  have low := leaf r hr
  omega

theorem unpack_pack (k b : Nat) (P : Proof) (len : P.length=498*k+30*b)
    (small : ProofCodec.packedLength k (15*k+b)≤2^33)
    (top : ∀ j<15*k+b, (P.getD (unpackedDigest k j+29) 0).toNat<64)
    (salt : ∀ r<k, (P.getD (498*r+15) 0).toNat<8)
    (leaf : ∀ r<k, (P.getD (498*r+46) 0).toNat<16)
    (leafTop : ∀ r<k, P.getD (498*r+47) 0=0) :
    unpack k (pack k P)=some P := by
  have count : unpackedCount k P.length=15*k+b := by rw [len,unpackedCount];omega
  have records : 481*k≤(ProofCodec.pack k P).length := by
    rw [ProofCodec.pack_length,count]
    unfold ProofCodec.packedLength bodyLength
    omega
  have heads : ∀ r<k, ((ProofCodec.pack k P).getD (481*r+45) 0).toNat<128 := by
    intro r hr
    rw [ProofCodec.getD_pack k P _ (by rw [count];unfold ProofCodec.packedLength bodyLength;omega),
      count,ProofCodec.packedByte,if_pos (by unfold bodyLength;omega),if_pos (by omega),
      show (481*r+45)/481=r by omega,ProofCodec.headByte_toNat]
    have low := leaf r hr
    omega
  unfold unpack pack
  rw [restore_convert k (ProofCodec.pack k P) records heads]
  exact ProofCodec.unpack_pack k b P len small top salt
    (fun r hr => lt_trans (leaf r hr) (by decide)) leafTop

theorem unpack_empty : unpack 0 []=some [] := by decide
theorem unpack_missing_record : unpack 1 []=none := by decide

end CommitGolfCandidate.ProofCodec.HeadStream
