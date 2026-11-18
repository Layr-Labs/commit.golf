import CommitGolfCandidate.ProofCodecBits

/-! Codec v3 keeps the 45 complete head bytes in the main stream. The seven live
head bits follow the existing digest-remainder stream, eight heads per seven bytes. -/
namespace CommitGolfCandidate.ProofCodec.HeadStream
open CommitGolf

def compactSource (k p : Nat) : Nat := p+min k ((p+435)/480)

def head (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  if r<k then (Q.getD (481*r+45) 0).toNat%128 else 0

def headPackedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  let r := 8*(p/7)+p%7
  BitVec.ofNat 8 (head k Q r/2^(p%7)+head k Q (r+1)*2^(7-p%7))

def convertedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<Q.length-k then Q.getD (compactSource k p) 0
  else headPackedByte k Q (p-(Q.length-k))

def convert (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (Q.length-k/8) => convertedByte k Q p.val

def packedLength (k n : Nat) : Nat := ProofCodec.packedLength k n-k/8
def pack (k : Nat) (P : Proof) : Proof := convert k (ProofCodec.pack k P)

@[simp] theorem convert_length (k : Nat) (Q : Proof) : (convert k Q).length=Q.length-k/8 := by
  simp [convert]

theorem getD_convert (k : Nat) (Q : Proof) (p : Nat) (inside : p<Q.length-k/8) :
    (convert k Q).getD p 0=convertedByte k Q p := by
  simp [convert,List.getD_eq_getElem?_getD,inside]

theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length=packedLength k (unpackedCount k P.length) := by
  simp [pack,packedLength,ProofCodec.pack_length]

theorem packed_length_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    packedLength k (15*k+b)≤66800 := BitPacked.packed_length_le k b hk hb

theorem packed_length_max : packedLength 128 (15*128+128)=66800 := by decide

theorem compact_source_bounds (k L p : Nat) (records : 481*k≤L) (inside : p<L-k) :
    p≤compactSource k p ∧ compactSource k p<L := by
  unfold compactSource
  omega

theorem compact_record_source (k p : Nat) (inside : p<480*k) :
    compactSource k p=481*(p/480)+p%480+(if 45≤p%480 then 1 else 0) := by
  unfold compactSource
  by_cases after : 45≤p%480 <;> simp only [after,ite_true,ite_false] <;> omega

theorem compact_footer_source (k p : Nat) (outside : 480*k≤p) :
    compactSource k p=p+k := by
  unfold compactSource
  rw [Nat.min_eq_left (by omega)]

theorem head_lt (k : Nat) (Q : Proof) (r : Nat) : head k Q r<128 := by
  unfold head
  split_ifs <;> omega

theorem head_group_byte (k : Nat) (Q : Proof) (g m : Nat) (hm : m<7) :
    headPackedByte k Q (7*g+m)=
      BitVec.ofNat 8 (head k Q (8*g+m)/2^m+head k Q (8*g+m+1)*2^(7-m)) := by
  simp only [headPackedByte,show (7*g+m)/7=g by omega,show (7*g+m)%7=m by omega]

theorem packed_empty : convert 0 []=[] := by decide

end CommitGolfCandidate.ProofCodec.HeadStream
