import CommitGolfCandidate.HeadStreamThree

/-! No head stream: two salt bits share the last six-bit leaf byte. -/
namespace CommitGolfCandidate.ProofCodec.HeadStreamZero
open CommitGolf
set_option maxHeartbeats 1000000
export HeadStream (compactSource compactTarget compact_source_bounds compact_record_source
  compact_footer_source compact_source_target compact_target_bound)

def merge (low head : Byte) : Byte :=
  BitVec.ofNat 8 (low.toNat%64+64*(head.toNat%4))

@[simp] theorem merge_low (low head : Byte) : (merge low head).toNat%64=low.toNat%64 := by
  have a := low.isLt
  have b := head.isLt
  simp only [merge,BitVec.toNat_ofNat]
  omega

@[simp] theorem merge_high (low head : Byte) : (merge low head).toNat/64=head.toNat%4 := by
  have a := low.isLt
  have b := head.isLt
  simp only [merge,BitVec.toNat_ofNat]
  omega

def convertedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<480*k ∧ p%480=44 then
    merge (Q.getD (481*(p/480)+44) 0) (Q.getD (481*(p/480)+45) 0)
  else Q.getD (compactSource k p) 0

def convert (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (Q.length-k) => convertedByte k Q p.val

def packedLength (k n : Nat) : Nat := ProofCodec.packedLength k n-k
def pack (k : Nat) (P : Proof) : Proof := convert k (ProofCodec.pack k P)
def expandedLength (k L : Nat) : Nat := L+k

def restoredHead (_k : Nat) (Q : Proof) (r : Nat) : Nat :=
  (Q.getD (480*r+44) 0).toNat/64

def expandedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<481*k ∧ p%481=45 then BitVec.ofNat 8 (restoredHead k Q (p/481))
  else if p<481*k ∧ p%481=44 then BitVec.ofNat 8 ((Q.getD (compactTarget k p) 0).toNat%64)
  else Q.getD (compactTarget k p) 0

def restore (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (expandedLength k Q.length) => expandedByte k Q p.val

def unpack (k : Nat) (Q : Proof) : Option Proof := ProofCodec.unpack k (restore k Q)

@[simp] theorem convert_length (k : Nat) (Q : Proof) : (convert k Q).length=Q.length-k := by
  simp [convert]

@[simp] theorem restore_length (k : Nat) (Q : Proof) :
    (restore k Q).length=expandedLength k Q.length := by simp [restore]

theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length=packedLength k (unpackedCount k P.length) := by
  simp [pack,packedLength,ProofCodec.pack_length]

theorem packed_length_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    packedLength k (15*k+b)≤66688 := by
  have count : (15*k+b+3)/4≤512 := by omega
  unfold packedLength ProofCodec.packedLength bodyLength
  omega

theorem packed_length_max : packedLength 128 (15*128+128)=66688 := by decide

theorem getD_convert (k : Nat) (Q : Proof) (p : Nat) (inside : p<Q.length-k) :
    (convert k Q).getD p 0=convertedByte k Q p := by
  simp [convert,List.getD_eq_getElem?_getD,inside]

theorem getD_restore (k : Nat) (Q : Proof) (p : Nat) (inside : p<expandedLength k Q.length) :
    (restore k Q).getD p 0=expandedByte k Q p := by
  simp [restore,List.getD_eq_getElem?_getD,inside]

theorem restore_convert_length (k : Nat) (Q : Proof) (records : 481*k≤Q.length) :
    expandedLength k (convert k Q).length=Q.length := by
  simp only [expandedLength,convert_length]
  omega

theorem converted_tail (k : Nat) (Q : Proof) (r : Nat) (hr : r<k) :
    convertedByte k Q (480*r+44)=merge (Q.getD (481*r+44) 0) (Q.getD (481*r+45) 0) := by
  rw [convertedByte,if_pos (by omega),show (480*r+44)/480=r by omega]

theorem target_tail (k r : Nat) (hr : r<k) : compactTarget k (481*r+44)=480*r+44 := by
  unfold compactTarget
  omega

theorem restored_head_convert (k : Nat) (Q : Proof) (r : Nat)
    (records : 481*k≤Q.length) (hr : r<k) :
    restoredHead k (convert k Q) r=(Q.getD (481*r+45) 0).toNat%4 := by
  rw [restoredHead,getD_convert k Q _ (by omega),converted_tail k Q r hr,merge_high]

theorem restore_convert (k : Nat) (Q : Proof) (records : 481*k≤Q.length)
    (heads : ∀ r<k, (Q.getD (481*r+45) 0).toNat<4)
    (tails : ∀ r<k, (Q.getD (481*r+44) 0).toNat<64) : restore k (convert k Q)=Q := by
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
    rw [if_pos marked,restored_head_convert k Q _ records hr,index,Nat.mod_eq_of_lt low]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · rw [if_neg marked]
    by_cases tail : p<481*k ∧ p%481=44
    · have hr : p/481<k := by omega
      have index : 481*(p/481)+44=p := by omega
      have low := tails (p/481) hr
      rw [if_pos tail,←index,target_tail k _ hr,getD_convert k Q _ (by omega),
        converted_tail k Q _ hr,merge_low,Nat.mod_eq_of_lt low]
      simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    · have bound := compact_target_bound k Q.length p records hq marked
      have absent : ¬(compactTarget k p<480*k ∧ compactTarget k p%480=44) := by
        unfold compactTarget
        unfold compactTarget at bound
        omega
      rw [if_neg tail,getD_convert k Q _ bound,convertedByte,if_neg absent,
        compact_source_target k p marked]

theorem restore_pack (k b : Nat) (P : Proof) (len : P.length=498*k+30*b)
    (leaf : ∀ r<k, P.getD (498*r+46) 0=0)
    (tail : ∀ r<k, (P.getD (498*r+45) 0).toNat<64) :
    restore k (pack k P)=ProofCodec.pack k P := by
  have count : unpackedCount k P.length=15*k+b := by rw [len,unpackedCount];omega
  have records : 481*k≤(ProofCodec.pack k P).length := by
    rw [ProofCodec.pack_length,count]
    unfold ProofCodec.packedLength bodyLength
    omega
  apply restore_convert k (ProofCodec.pack k P) records
  · intro r hr
    rw [ProofCodec.getD_pack k P _ (by rw [count];unfold ProofCodec.packedLength bodyLength;omega),
      count,ProofCodec.packedByte,if_pos (by unfold bodyLength;omega),if_pos (by omega),
      show (481*r+45)/481=r by omega,ProofCodec.headByte_toNat,leaf r hr]
    simpa using Nat.mod_lt (P.getD (498*r+15) 0).toNat (by decide : 0<4)
  · intro r hr
    rw [ProofCodec.getD_pack k P _ (by rw [count];unfold ProofCodec.packedLength bodyLength;omega),
      count,ProofCodec.packedByte,if_pos (by unfold bodyLength;omega),if_neg (by omega),
      packedSource,if_pos (by omega),if_neg (by omega),if_pos (by omega),
      show (481*r+44)/481=r by omega,show (481*r+44)%481=44 by omega]
    exact tail r hr

theorem unpack_pack (k b : Nat) (P : Proof) (len : P.length=498*k+30*b)
    (small : ProofCodec.packedLength k (15*k+b)≤2^33)
    (top : ∀ j<15*k+b, (P.getD (unpackedDigest k j+29) 0).toNat<64)
    (salt : ∀ r<k, (P.getD (498*r+15) 0).toNat<4)
    (leaf : ∀ r<k, P.getD (498*r+46) 0=0)
    (tail : ∀ r<k, (P.getD (498*r+45) 0).toNat<64)
    (leafTop : ∀ r<k, P.getD (498*r+47) 0=0) :
    unpack k (pack k P)=some P := by
  unfold unpack
  rw [restore_pack k b P len leaf tail]
  exact ProofCodec.unpack_pack k b P len small top salt
    (fun r hr => by rw [leaf r hr];decide) leafTop

theorem packed_empty : convert 0 []=[] := by decide
theorem unpack_empty : unpack 0 []=some [] := by decide
theorem unpack_missing_record : unpack 1 []=none := by decide

end CommitGolfCandidate.ProofCodec.HeadStreamZero
