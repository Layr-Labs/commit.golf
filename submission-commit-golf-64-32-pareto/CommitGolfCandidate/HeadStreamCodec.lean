import CommitGolfCandidate.ProofCodecBits

/-! The six live head bits follow the digest-remainder stream, four heads per three bytes. -/
namespace CommitGolfCandidate.ProofCodec.HeadStream
open CommitGolf

def compactSource (k p : Nat) : Nat := p+min k ((p+435)/480)

def head (k : Nat) (Q : Proof) (r : Nat) : Nat :=
  if r<k then (Q.getD (481*r+45) 0).toNat%64 else 0

def headPackedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  let r := 4*(p/3)+p%3
  BitVec.ofNat 8 (head k Q r/2^(2*(p%3))+head k Q (r+1)*2^(6-2*(p%3)))

def convertedByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  if p<Q.length-k then Q.getD (compactSource k p) 0
  else headPackedByte k Q (p-(Q.length-k))

def convert (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (Q.length-k/4) => convertedByte k Q p.val

def packedLength (k n : Nat) : Nat := ProofCodec.packedLength k n-k/4
def pack (k : Nat) (P : Proof) : Proof := convert k (ProofCodec.pack k P)

@[simp] theorem convert_length (k : Nat) (Q : Proof) : (convert k Q).length=Q.length-k/4 := by
  simp [convert]

theorem getD_convert (k : Nat) (Q : Proof) (p : Nat) (inside : p<Q.length-k/4) :
    (convert k Q).getD p 0=convertedByte k Q p := by
  simp [convert,List.getD_eq_getElem?_getD,inside]

theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length=packedLength k (unpackedCount k P.length) := by
  simp [pack,packedLength,ProofCodec.pack_length]

theorem packed_length_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    packedLength k (15*k+b)≤66784 := by
  have count : (15*k+b+3)/4≤512 := by omega
  unfold packedLength ProofCodec.packedLength bodyLength
  by_cases full : k=128
  · subst k
    omega
  · omega

theorem packed_length_max : packedLength 128 (15*128+128)=66784 := by decide

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

theorem head_lt (k : Nat) (Q : Proof) (r : Nat) : head k Q r<64 := by
  unfold head
  split_ifs <;> omega

theorem head_group_byte (k : Nat) (Q : Proof) (g m : Nat) (hm : m<3) :
    headPackedByte k Q (3*g+m)=
      BitVec.ofNat 8 (head k Q (4*g+m)/2^(2*m)+head k Q (4*g+m+1)*2^(6-2*m)) := by
  simp only [headPackedByte,show (3*g+m)/3=g by omega,show (3*g+m)%3=m by omega]

theorem packed_empty : convert 0 []=[] := by decide

end CommitGolfCandidate.ProofCodec.HeadStream
