import CommitGolfCandidate.HeadStreamZero

/-! Seven-bit tails, densely packed eight per seven bytes. -/
namespace CommitGolfCandidate.ProofCodec.HeadStreamSeven
open CommitGolf
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def compactSource (k p : Nat) : Nat := p+min k ((p+435)/479)
def compactTarget (k p : Nat) : Nat := p-min k ((p+435)/480)
def head (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  if r<k then (Q.getD (480*r+44) 0).toNat%128 else 0
def headPackedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  let r := 8*(p/7)+8*(p%7)/7
  let shift := 8*(p%7)%7
  BitVec.ofNat 8 (head k Q r/2^shift+head k Q (r+1)*2^(7-shift))
def convertedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<Q.length-k then Q.getD (compactSource k p) 0
  else headPackedByte k Q (p-(Q.length-k))
def convert (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (Q.length-k/8) => convertedByte k Q p.val
def packedLength (k n : Nat) : Nat := HeadStreamZero.packedLength k n-k/8
def pack (k : Nat) (P : Proof) : Proof := convert k (HeadStreamZero.pack k P)

@[simp] theorem convert_length (k : Nat) (Q : Proof) : (convert k Q).length=Q.length-k/8 := by
  simp [convert]
theorem getD_convert (k : Nat) (Q : Proof) (p : Nat) (inside : p<Q.length-k/8) :
    (convert k Q).getD p 0=convertedByte k Q p := by
  simp [convert,List.getD_eq_getElem?_getD,inside]
theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length=packedLength k (unpackedCount k P.length) := by
  simp [pack,packedLength,HeadStreamZero.pack_length]
theorem packed_length_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    packedLength k (15*k+b)≤66672 := by
  have count : (15*k+b+3)/4≤512 := by omega
  unfold packedLength HeadStreamZero.packedLength ProofCodec.packedLength bodyLength
  by_cases full : k=128
  · subst k; omega
  · omega
theorem packed_length_max : packedLength 128 (15*128+128)=66672 := by decide

theorem compact_source_bounds (k L p : Nat) (records : 480*k≤L) (inside : p<L-k) :
    p≤compactSource k p ∧ compactSource k p<L := by
  unfold compactSource
  omega

theorem compact_record_source (k p : Nat) (inside : p<479*k) :
    compactSource k p=480*(p/479)+p%479+(if 44≤p%479 then 1 else 0) := by
  unfold compactSource
  by_cases after : 44≤p%479 <;> simp only [after,ite_true,ite_false] <;> omega

theorem compact_footer_source (k p : Nat) (outside : 479*k≤p) :
    compactSource k p=p+k := by
  unfold compactSource
  rw [Nat.min_eq_left (by omega)]


theorem head_lt (k : Nat) (Q : Proof) (r : Nat) : head k Q r<128 := by
  unfold head
  split_ifs <;> omega
theorem head_group_byte (k : Nat) (Q : Proof) (g m : Nat) (hm : m<7) :
    headPackedByte k Q (7*g+m)=
      BitVec.ofNat 8 (head k Q (8*g+8*m/7)/2^(8*m%7)+
        head k Q (8*g+8*m/7+1)*2^(7-8*m%7)) := by
  simp only [headPackedByte,show (7*g+m)/7=g by omega,show (7*g+m)%7=m by omega]

def expandedLength (k L : Nat) : Nat := L+k/8
def frontLength (k : Nat) (Q : Proof) : Nat := expandedLength k Q.length-k
def restoredHead (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  let p := frontLength k Q+7*r/8
  ((Q.getD p 0).toNat/2^(7*r%8)+(Q.getD (p+1) 0).toNat*2^(8-7*r%8))%128
def expandedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<480*k ∧ p%480=44 then BitVec.ofNat 8 (restoredHead k Q (p/480))
  else Q.getD (compactTarget k p) 0
def restore (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (expandedLength k Q.length) => expandedByte k Q p.val
def unpack (k : Nat) (Q : Proof) : Option Proof := HeadStreamZero.unpack k (restore k Q)

@[simp] theorem restore_length (k : Nat) (Q : Proof) :
    (restore k Q).length=expandedLength k Q.length := by simp [restore]
theorem restore_convert_length (k : Nat) (Q : Proof) (records : 480*k≤Q.length) :
    expandedLength k (convert k Q).length=Q.length := by
  simp only [expandedLength,convert_length]
  omega
theorem front_convert (k : Nat) (Q : Proof) (records : 480*k≤Q.length) :
    frontLength k (convert k Q)=Q.length-k := by
  rw [frontLength,restore_convert_length k Q records]
theorem compact_source_target (k p : Nat) (kept : ¬(p<480*k ∧ p%480=44)) :
    compactSource k (compactTarget k p)=p := by
  by_cases within : p<480*k
  · by_cases before : p%480<44
    · have quotient : (p+435)/480=p/480 := by omega
      have target : compactTarget k p=479*(p/480)+p%480 := by
        unfold compactTarget
        rw [quotient,Nat.min_eq_right (by omega)]
        omega
      rw [target,compactSource,show (479*(p/480)+p%480+435)/479=p/480 by omega,
        Nat.min_eq_right (by omega)]
      omega
    · have after : 45≤p%480 := by omega
      have quotient : (p+435)/480=p/480+1 := by omega
      have target : compactTarget k p=479*(p/480)+(p%480-1) := by
        unfold compactTarget
        rw [quotient,Nat.min_eq_right (by omega)]
        omega
      rw [target,compactSource,show (479*(p/480)+(p%480-1)+435)/479=p/480+1 by omega,
        Nat.min_eq_right (by omega)]
      omega
  · have target : compactTarget k p=p-k := by
      unfold compactTarget
      rw [Nat.min_eq_left (by omega)]
    rw [target,compact_footer_source k _ (by omega)]
    omega

theorem compact_target_bound (k L p : Nat) (records : 480*k≤L) (inside : p<L)
    (kept : ¬(p<480*k ∧ p%480=44)) : compactTarget k p<L-k := by
  unfold compactTarget
  by_cases within : p<480*k
  · by_cases before : p%480<44
    · have quotient : (p+435)/480=p/480 := by omega
      rw [quotient,Nat.min_eq_right (by omega)]
      omega
    · have after : 45≤p%480 := by omega
      have quotient : (p+435)/480=p/480+1 := by omega
      rw [quotient,Nat.min_eq_right (by omega)]
      omega
  · rw [Nat.min_eq_left (by omega)]
    omega


theorem converted_head_byte (k : Nat) (Q : Proof) (p : Nat) (records : 480*k≤Q.length)
    (inside : Q.length-k+p<Q.length-k/8) :
    (convert k Q).getD (Q.length-k+p) 0=headPackedByte k Q p := by
  rw [getD_convert k Q _ inside,convertedByte,if_neg (by omega)]
  congr 1
  omega
theorem decode_first (a b u : Nat) (ha : a<128) :
    ((a+b*128)%256+u*256)%128=a := by omega
theorem decode_last (a b u : Nat) (ha : a<128) (hb : b<128) :
    (((a/64+b*2)%256)/2+u*128)%128=b := by omega
theorem decode_middle (a b c m : Nat) (ha : a<128) (hb : b<128) (hc : c<128)
    (lo : 1≤m) (hi : m≤6) :
    (((a/2^(m-1)+b*2^(8-m))%256)/2^(8-m)+
      ((b/2^m+c*2^(7-m))%256)*2^m)%128=b := by
  interval_cases m <;> norm_num at * <;> omega

theorem restored_head_group (k : Nat) (Q : Proof) (g m : Nat)
    (records : 480*k≤Q.length) (hm : m<8) (hr : 8*g+m<k) :
    restoredHead k (convert k Q) (8*g+m)=head k Q (8*g+m) := by
  interval_cases m
  · have readA := converted_head_byte k Q (7*g+0) records (by omega)
    rw [head_group_byte k Q g 0 (by decide)] at readA
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+0)/8=7*g+0 by omega,
      show 7*(8*g+0)%8=0 by omega,readA]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_first _ _ _ (head_lt k Q _)
  · have readA := converted_head_byte k Q (7*g+0) records (by omega)
    rw [head_group_byte k Q g 0 (by decide)] at readA
    have readB := converted_head_byte k Q (7*g+1) records (by omega)
    rw [head_group_byte k Q g 1 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+1)/8=7*g+0 by omega,
      show 7*(8*g+1)%8=7 by omega,readA,
      show Q.length-k+(7*g+0)+1=Q.length-k+(7*g+1) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    simpa only [Nat.reduceSub,Nat.reducePow,Nat.div_one] using
      decode_middle (head k Q (8*g)) (head k Q (8*g+1)) (head k Q (8*g+2)) 1
        (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) (by decide) (by decide)
  · have readA := converted_head_byte k Q (7*g+1) records (by omega)
    rw [head_group_byte k Q g 1 (by decide)] at readA
    have readB := converted_head_byte k Q (7*g+2) records (by omega)
    rw [head_group_byte k Q g 2 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+2)/8=7*g+1 by omega,
      show 7*(8*g+2)%8=6 by omega,readA,
      show Q.length-k+(7*g+1)+1=Q.length-k+(7*g+2) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_middle _ _ _ 2 (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) (by decide) (by decide)
  · have readA := converted_head_byte k Q (7*g+2) records (by omega)
    rw [head_group_byte k Q g 2 (by decide)] at readA
    have readB := converted_head_byte k Q (7*g+3) records (by omega)
    rw [head_group_byte k Q g 3 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+3)/8=7*g+2 by omega,
      show 7*(8*g+3)%8=5 by omega,readA,
      show Q.length-k+(7*g+2)+1=Q.length-k+(7*g+3) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_middle _ _ _ 3 (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) (by decide) (by decide)
  · have readA := converted_head_byte k Q (7*g+3) records (by omega)
    rw [head_group_byte k Q g 3 (by decide)] at readA
    have readB := converted_head_byte k Q (7*g+4) records (by omega)
    rw [head_group_byte k Q g 4 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+4)/8=7*g+3 by omega,
      show 7*(8*g+4)%8=4 by omega,readA,
      show Q.length-k+(7*g+3)+1=Q.length-k+(7*g+4) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_middle _ _ _ 4 (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) (by decide) (by decide)
  · have readA := converted_head_byte k Q (7*g+4) records (by omega)
    rw [head_group_byte k Q g 4 (by decide)] at readA
    have readB := converted_head_byte k Q (7*g+5) records (by omega)
    rw [head_group_byte k Q g 5 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+5)/8=7*g+4 by omega,
      show 7*(8*g+5)%8=3 by omega,readA,
      show Q.length-k+(7*g+4)+1=Q.length-k+(7*g+5) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_middle _ _ _ 5 (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) (by decide) (by decide)
  · have readA := converted_head_byte k Q (7*g+5) records (by omega)
    rw [head_group_byte k Q g 5 (by decide)] at readA
    have readB := converted_head_byte k Q (7*g+6) records (by omega)
    rw [head_group_byte k Q g 6 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+6)/8=7*g+5 by omega,
      show 7*(8*g+6)%8=2 by omega,readA,
      show Q.length-k+(7*g+5)+1=Q.length-k+(7*g+6) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_middle _ _ _ 6 (head_lt k Q _) (head_lt k Q _) (head_lt k Q _) (by decide) (by decide)
  · have readA := converted_head_byte k Q (7*g+6) records (by omega)
    rw [head_group_byte k Q g 6 (by decide)] at readA
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 7*(8*g+7)/8=7*g+6 by omega,
      show 7*(8*g+7)%8=1 by omega,readA]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_last _ _ _ (head_lt k Q _) (head_lt k Q _)

theorem restored_head_convert (k : Nat) (Q : Proof) (r : Nat)
    (records : 480*k≤Q.length) (hr : r<k) :
    restoredHead k (convert k Q) r=head k Q r := by
  have eq : r=8*(r/8)+r%8 := by omega
  rw [eq]
  exact restored_head_group k Q _ _ records (by omega) (by omega)

theorem getD_restore (k : Nat) (Q : Proof) (p : Nat) (inside : p<expandedLength k Q.length) :
    (restore k Q).getD p 0=expandedByte k Q p := by
  simp [restore,List.getD_eq_getElem?_getD,inside]

theorem restore_convert (k : Nat) (Q : Proof) (records : 480*k≤Q.length)
    (heads : ∀ r<k, (Q.getD (480*r+44) 0).toNat<128) : restore k (convert k Q)=Q := by
  apply List.ext_getElem
  · rw [restore_length,restore_convert_length k Q records]
  intro p hp hq
  suffices equality : (restore k (convert k Q)).getD p 0=Q.getD p 0 by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hq] at equality
    exact equality
  rw [getD_restore k _ p (by rw [restore_convert_length k Q records];exact hq)]
  unfold expandedByte
  by_cases marked : p<480*k ∧ p%480=44
  · have hr : p/480<k := by omega
    have low := heads (p/480) hr
    have index : 480*(p/480)+44=p := by omega
    rw [index] at low
    rw [if_pos marked,restored_head_convert k Q _ records hr,head,if_pos hr,index,
      Nat.mod_eq_of_lt low]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · have bound := compact_target_bound k Q.length p records hq marked
    rw [if_neg marked,getD_convert k Q _ (by omega),convertedByte,if_pos bound,
      compact_source_target k p marked]


theorem merge_seven_lt (low high : Byte) (small : high.toNat<2) :
    (HeadStreamZero.merge low high).toNat<128 := by
  unfold HeadStreamZero.merge
  simp only [BitVec.toNat_ofNat]
  omega


theorem header_nat_lt_two (salt leaf : Nat) (small : salt<2) (zero : leaf=0) :
    salt%4+4*(leaf%32)<2 := by
  rw [zero]
  omega

theorem restore_pack (k b : Nat) (P : Proof) (len : P.length=498*k+30*b)
    (salt : ∀ r<k, (P.getD (498*r+15) 0).toNat<2)
    (leaf : ∀ r<k, P.getD (498*r+46) 0=0) :
    restore k (pack k P)=HeadStreamZero.pack k P := by
  have count : unpackedCount k P.length=15*k+b := by rw [len,unpackedCount];omega
  have records : 481*k≤(ProofCodec.pack k P).length := by
    rw [ProofCodec.pack_length,count]
    unfold ProofCodec.packedLength bodyLength
    omega
  apply restore_convert
  · simp only [HeadStreamZero.pack,HeadStreamZero.convert_length]
    omega
  · intro r hr
    rw [HeadStreamZero.pack,HeadStreamZero.getD_convert k _ _ (by omega),
      HeadStreamZero.converted_tail k _ r hr]
    apply merge_seven_lt
    rw [ProofCodec.getD_pack k P _ (by rw [count];unfold ProofCodec.packedLength bodyLength;omega),
      count,ProofCodec.packedByte,if_pos (by unfold bodyLength;omega),if_pos (by omega),
      show (481*r+45)/481=r by omega,ProofCodec.headByte_toNat,leaf r hr]
    apply header_nat_lt_two _ _ (salt r hr)
    exact BitVec.toNat_zero

theorem unpack_pack (k b : Nat) (P : Proof) (len : P.length=498*k+30*b)
    (small : ProofCodec.packedLength k (15*k+b)≤2^33)
    (top : ∀ j<15*k+b, (P.getD (unpackedDigest k j+29) 0).toNat<64)
    (salt : ∀ r<k, (P.getD (498*r+15) 0).toNat<2)
    (leaf : ∀ r<k, P.getD (498*r+46) 0=0)
    (tail : ∀ r<k, (P.getD (498*r+45) 0).toNat<64)
    (leafTop : ∀ r<k, P.getD (498*r+47) 0=0) :
    unpack k (pack k P)=some P := by
  unfold unpack
  rw [restore_pack k b P len salt leaf]
  exact HeadStreamZero.unpack_pack k b P len small top
    (fun r hr => lt_trans (salt r hr) (by decide)) leaf tail leafTop

theorem packed_empty : convert 0 []=[] := by decide
theorem unpack_empty : unpack 0 []=some [] := by decide
theorem unpack_missing_record : unpack 1 []=none := by decide

end CommitGolfCandidate.ProofCodec.HeadStreamSeven
