import CommitGolfCandidate.HeadStreamRestore

/-! Five-bit record heads, densely packed eight per five bytes. -/
namespace CommitGolfCandidate.ProofCodec.HeadStreamFive
open CommitGolf
set_option maxHeartbeats 1000000
export HeadStream (compactSource compactTarget compact_source_bounds compact_record_source
  compact_footer_source compact_source_target compact_target_bound)

def head (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  if r<k then (Q.getD (481*r+45) 0).toNat%32 else 0

def headPackedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  let r := 8*(p/5)+8*(p%5)/5
  let shift := 8*(p%5)%5
  BitVec.ofNat 8 (head k Q r/2^shift+head k Q (r+1)*2^(5-shift)+head k Q (r+2)*2^(10-shift))

def convertedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<Q.length-k then Q.getD (compactSource k p) 0
  else headPackedByte k Q (p-(Q.length-k))

def convert (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (Q.length-3*k/8) => convertedByte k Q p.val

def packedLength (k n : Nat) : Nat := ProofCodec.packedLength k n-3*k/8
def pack (k : Nat) (P : Proof) : Proof := convert k (ProofCodec.pack k P)

@[simp] theorem convert_length (k : Nat) (Q : Proof) : (convert k Q).length=Q.length-3*k/8 := by
  simp [convert]

theorem getD_convert (k : Nat) (Q : Proof) (p : Nat) (inside : p<Q.length-3*k/8) :
    (convert k Q).getD p 0=convertedByte k Q p := by
  simp [convert,List.getD_eq_getElem?_getD,inside]

theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length=packedLength k (unpackedCount k P.length) := by
  simp [pack,packedLength,ProofCodec.pack_length]

theorem packed_length_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    packedLength k (15*k+b)≤66768 := by
  have count : (15*k+b+3)/4≤512 := by omega
  unfold packedLength ProofCodec.packedLength bodyLength
  by_cases full : k=128
  · subst k; omega
  · omega

theorem packed_length_max : packedLength 128 (15*128+128)=66768 := by decide

theorem head_lt (k : Nat) (Q : Proof) (r : Nat) : head k Q r<32 := by
  unfold head
  split_ifs <;> omega

theorem head_group_byte (k : Nat) (Q : Proof) (g m : Nat) (hm : m<5) :
    headPackedByte k Q (5*g+m)=
      BitVec.ofNat 8 (head k Q (8*g+8*m/5)/2^(8*m%5)+
        head k Q (8*g+8*m/5+1)*2^(5-8*m%5)+
        head k Q (8*g+8*m/5+2)*2^(10-8*m%5)) := by
  simp only [headPackedByte,show (5*g+m)/5=g by omega,show (5*g+m)%5=m by omega]

def expandedLength (k L : Nat) : Nat := L+3*k/8
def frontLength (k : Nat) (Q : Proof) : Nat := expandedLength k Q.length-k

def restoredHead (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  let p := frontLength k Q+5*r/8
  ((Q.getD p 0).toNat/2^(5*r%8)+(Q.getD (p+1) 0).toNat*2^(8-5*r%8))%32

def expandedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<481*k ∧ p%481=45 then BitVec.ofNat 8 (restoredHead k Q (p/481))
  else Q.getD (compactTarget k p) 0

def restore (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (expandedLength k Q.length) => expandedByte k Q p.val

def unpack (k : Nat) (Q : Proof) : Option Proof := ProofCodec.unpack k (restore k Q)

@[simp] theorem restore_length (k : Nat) (Q : Proof) :
    (restore k Q).length=expandedLength k Q.length := by simp [restore]

theorem restore_convert_length (k : Nat) (Q : Proof) (records : 481*k≤Q.length) :
    expandedLength k (convert k Q).length=Q.length := by
  simp only [expandedLength,convert_length]
  omega

theorem front_convert (k : Nat) (Q : Proof) (records : 481*k≤Q.length) :
    frontLength k (convert k Q)=Q.length-k := by
  rw [frontLength,restore_convert_length k Q records]

theorem converted_head_byte (k : Nat) (Q : Proof) (p : Nat) (records : 481*k≤Q.length)
    (inside : Q.length-k+p<Q.length-3*k/8) :
    (convert k Q).getD (Q.length-k+p) 0=headPackedByte k Q p := by
  rw [getD_convert k Q _ inside,convertedByte,if_neg (by omega)]
  congr 1
  omega

theorem decode_0 (a b c u : Nat) (ha : a<32) :
    ((a+(b*32+c*1024))%256+u*256)%32=a := by omega

theorem decode_1 (a b c d : Nat) (ha : a<32) (hb : b<32) :
    (((a+(b*32+c*1024))%256)/32+((b/8+(c*4+d*128))%256)*8)%32=b := by omega

theorem decode_2 (a b c u : Nat) (ha : a<32) (hb : b<32) :
    (((a/8+(b*4+c*128))%256)/4+u*64)%32=b := by omega

theorem decode_3 (a b c d e : Nat) (ha : a<32) (hb : b<32) (hc : c<32) :
    (((a/8+(b*4+c*128))%256)/128+((c/2+(d*16+e*512))%256)*2)%32=c := by omega

theorem decode_4 (a b c d : Nat) (ha : a<32) (hb : b<32) :
    (((a/2+(b*16+c*512))%256)/16+((b/16+(c*2+d*64))%256)*16)%32=b := by omega

theorem decode_5 (a b c u : Nat) (ha : a<32) (hb : b<32) :
    (((a/16+(b*2+c*64))%256)/2+u*128)%32=b := by omega

theorem decode_6 (a b c d e : Nat) (ha : a<32) (hb : b<32) (hc : c<32) :
    (((a/16+(b*2+c*64))%256)/64+((c/4+(d*8+e*256))%256)*4)%32=c := by omega

theorem decode_7 (a b c u : Nat) (ha : a<32) (hb : b<32) :
    (((a/4+(b*8+c*256))%256)/8+u*32)%32=b := by omega

theorem restored_head_group (k : Nat) (Q : Proof) (g m : Nat)
    (records : 481*k≤Q.length) (hm : m<8) (hr : 8*g+m<k) :
    restoredHead k (convert k Q) (8*g+m)=head k Q (8*g+m) := by
  interval_cases m
  · have readA := converted_head_byte k Q (5*g+0) records (by omega)
    rw [head_group_byte k Q g 0 (by decide)] at readA
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+0)/8=5*g+0 by omega,
      show 5*(8*g+0)%8=0 by omega,readA]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_0 _ _ _ _ (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+0) records (by omega)
    rw [head_group_byte k Q g 0 (by decide)] at readA
    have readB := converted_head_byte k Q (5*g+1) records (by omega)
    rw [head_group_byte k Q g 1 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+1)/8=5*g+0 by omega,
      show 5*(8*g+1)%8=5 by omega,readA,
      show Q.length-k+(5*g+0)+1=Q.length-k+(5*g+1) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_1 _ _ _ _ (head_lt k Q _) (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+1) records (by omega)
    rw [head_group_byte k Q g 1 (by decide)] at readA
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+2)/8=5*g+1 by omega,
      show 5*(8*g+2)%8=2 by omega,readA]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_2 _ _ _ _ (head_lt k Q _) (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+1) records (by omega)
    rw [head_group_byte k Q g 1 (by decide)] at readA
    have readB := converted_head_byte k Q (5*g+2) records (by omega)
    rw [head_group_byte k Q g 2 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+3)/8=5*g+1 by omega,
      show 5*(8*g+3)%8=7 by omega,readA,
      show Q.length-k+(5*g+1)+1=Q.length-k+(5*g+2) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_3 _ _ _ _ _ (head_lt k Q _) (head_lt k Q _) (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+2) records (by omega)
    rw [head_group_byte k Q g 2 (by decide)] at readA
    have readB := converted_head_byte k Q (5*g+3) records (by omega)
    rw [head_group_byte k Q g 3 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+4)/8=5*g+2 by omega,
      show 5*(8*g+4)%8=4 by omega,readA,
      show Q.length-k+(5*g+2)+1=Q.length-k+(5*g+3) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_4 _ _ _ _ (head_lt k Q _) (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+3) records (by omega)
    rw [head_group_byte k Q g 3 (by decide)] at readA
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+5)/8=5*g+3 by omega,
      show 5*(8*g+5)%8=1 by omega,readA]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_5 _ _ _ _ (head_lt k Q _) (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+3) records (by omega)
    rw [head_group_byte k Q g 3 (by decide)] at readA
    have readB := converted_head_byte k Q (5*g+4) records (by omega)
    rw [head_group_byte k Q g 4 (by decide)] at readB
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+6)/8=5*g+3 by omega,
      show 5*(8*g+6)%8=6 by omega,readA,
      show Q.length-k+(5*g+3)+1=Q.length-k+(5*g+4) by omega,readB]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_6 _ _ _ _ _ (head_lt k Q _) (head_lt k Q _) (head_lt k Q _)
  · have readA := converted_head_byte k Q (5*g+4) records (by omega)
    rw [head_group_byte k Q g 4 (by decide)] at readA
    dsimp only [restoredHead]
    rw [front_convert k Q records,show 5*(8*g+7)/8=5*g+4 by omega,
      show 5*(8*g+7)%8=3 by omega,readA]
    simp only [BitVec.toNat_ofNat,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reducePow,
      Nat.reduceSub,Nat.reduceAdd,Nat.div_one,Nat.add_zero,Nat.zero_add,Nat.add_assoc]
    exact decode_7 _ _ _ _ (head_lt k Q _) (head_lt k Q _)

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
    (heads : ∀ r<k, (Q.getD (481*r+45) 0).toNat<32) : restore k (convert k Q)=Q := by
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
    (leaf : ∀ r<k, (P.getD (498*r+46) 0).toNat<4) :
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
    (leaf : ∀ r<k, (P.getD (498*r+46) 0).toNat<4)
    (leafTop : ∀ r<k, P.getD (498*r+47) 0=0) :
    unpack k (pack k P)=some P := by
  unfold unpack
  rw [restore_pack k b P len leaf]
  exact ProofCodec.unpack_pack k b P len small top salt
    (fun r hr => lt_trans (leaf r hr) (by decide)) leafTop

theorem packed_empty : convert 0 []=[] := by decide
theorem unpack_empty : unpack 0 []=some [] := by decide
theorem unpack_missing_record : unpack 1 []=none := by decide

end CommitGolfCandidate.ProofCodec.HeadStreamFive
