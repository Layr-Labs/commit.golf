import CommitGolfCandidate.ProofCodec
import Batteries.Data.BitVec.Lemmas

/-! Bit compaction of codec v2: omit the unused high bit of each combined record head.
The other 3,847 bits per record and the complete footer/remainder stream keep their order. -/
namespace CommitGolfCandidate.ProofCodec.BitPacked
open CommitGolf

def compactLength (k L : Nat) : Nat := L-k/8
def expandedLength (k L : Nat) : Nat := L+k/8

def omitted (k bit : Nat) : Prop := bit/3848<k ∧ bit%3848=367
instance (k bit : Nat) : Decidable (omitted k bit) := inferInstanceAs (Decidable (_ ∧ _))

def sourceBit (k bit : Nat) : Nat :=
  if bit<3847*k then 3848*(bit/3847)+bit%3847+(if 367≤bit%3847 then 1 else 0)
  else bit+k

def targetBit (k bit : Nat) : Nat := bit-min k ((bit+3480)/3848)

def readBit (P : Proof) (bit : Nat) : Bool := (P.getD (bit/8) 0).getLsbD (bit%8)

def compactByte (k : Nat) (P : Proof) (p : Nat) : Byte :=
  BitVec.ofFnLE fun b : Fin 8 => readBit P (sourceBit k (8*p+b.val))

def expandByte (k : Nat) (Q : Proof) (p : Nat) : Byte :=
  BitVec.ofFnLE fun b : Fin 8 =>
    if omitted k (8*p+b.val) then false else readBit Q (targetBit k (8*p+b.val))

def compact (k : Nat) (P : Proof) : Proof :=
  List.ofFn fun p : Fin (compactLength k P.length) => compactByte k P p.val

def expand (k : Nat) (Q : Proof) : Proof :=
  List.ofFn fun p : Fin (expandedLength k Q.length) => expandByte k Q p.val

theorem source_target (k bit : Nat) (kept : ¬omitted k bit) :
    sourceBit k (targetBit k bit)=bit := by
  by_cases within : bit/3848<k
  · by_cases before : bit%3848<367
    · have quotient : (bit+3480)/3848=bit/3848 := by omega
      have target : targetBit k bit=3847*(bit/3848)+bit%3848 := by
        unfold targetBit
        rw [quotient,Nat.min_eq_right (by omega)]
        omega
      rw [target,sourceBit,if_pos (by omega),
        show (3847*(bit/3848)+bit%3848)/3847=bit/3848 by omega,
        show (3847*(bit/3848)+bit%3848)%3847=bit%3848 by omega,if_neg (by omega)]
      omega
    · have after : 368≤bit%3848 := by unfold omitted at kept;omega
      have quotient : (bit+3480)/3848=bit/3848+1 := by omega
      have target : targetBit k bit=3847*(bit/3848)+(bit%3848-1) := by
        unfold targetBit
        rw [quotient,Nat.min_eq_right (by omega)]
        omega
      rw [target,sourceBit,if_pos (by omega),
        show (3847*(bit/3848)+(bit%3848-1))/3847=bit/3848 by omega,
        show (3847*(bit/3848)+(bit%3848-1))%3847=bit%3848-1 by omega,if_pos (by omega)]
      omega
  · have target : targetBit k bit=bit-k := by
      unfold targetBit
      rw [Nat.min_eq_left (by omega)]
    rw [target,sourceBit,if_neg (by omega)]
    omega

theorem target_bound (k L bit : Nat) (records : 481*k≤L) (inside : bit<8*L) :
    targetBit k bit<8*compactLength k L := by
  unfold targetBit compactLength
  simp only [Nat.min_def]
  split_ifs <;> omega

@[simp] theorem compact_length (k : Nat) (P : Proof) :
    (compact k P).length=compactLength k P.length := by simp [compact]

@[simp] theorem expand_length (k : Nat) (Q : Proof) :
    (expand k Q).length=expandedLength k Q.length := by simp [expand]

theorem read_compact (k : Nat) (P : Proof) (bit : Nat)
    (inside : bit<8*compactLength k P.length) :
    readBit (compact k P) bit=readBit P (sourceBit k bit) := by
  have index : bit/8<compactLength k P.length := by omega
  simp only [readBit,compact,List.getD_eq_getElem?_getD,List.getElem?_ofFn,index,
    ↓reduceDIte,Option.getD_some,compactByte,BitVec.getLsbD_ofFnLE]
  simp only [show bit%8<8 by omega,↓reduceDIte]
  rw [show 8*(bit/8)+bit%8=bit by omega]

theorem expand_compact (k : Nat) (P : Proof) (records : 481*k≤P.length)
    (heads : ∀ r<k, (P.getD (481*r+45) 0).getLsbD 7=false) :
    expand k (compact k P)=P := by
  have small : k/8≤P.length := by omega
  have length : expandedLength k (compactLength k P.length)=P.length := by
    unfold expandedLength compactLength
    omega
  apply List.ext_getElem
  · simp [length]
  intro i hi hp
  suffices equality : (expand k (compact k P)).getD i 0=P.getD i 0 by
    calc
      (expand k (compact k P))[i]=(expand k (compact k P)).getD i 0 := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
        rfl
      _=P.getD i 0 := equality
      _=P[i] := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp]
        rfl
  have index : i<expandedLength k (compact k P).length := by
    simpa only [compact_length,length] using hp
  rw [expand,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos index]
  simp only [Option.getD_some]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  change (expandByte k (compact k P) i).getLsbD b=(P.getD i 0).getLsbD b
  rw [expandByte,BitVec.getLsbD_ofFnLE,dif_pos hb]
  by_cases lost : omitted k (8*i+b)
  · rw [if_pos lost]
    have offset : b=7 := by unfold omitted at lost;omega
    have index : i=481*((8*i+b)/3848)+45 := by unfold omitted at lost;omega
    rw [offset,index]
    exact (heads _ lost.1).symm
  · rw [if_neg lost,read_compact k P _ (target_bound k P.length (8*i+b) records (by omega)),
      source_target k (8*i+b) lost]
    unfold readBit
    rw [show (8*i+b)/8=i by omega,show (8*i+b)%8=b by omega]

def packedLength (k n : Nat) : Nat := compactLength k (ProofCodec.packedLength k n)
def pack (k : Nat) (P : Proof) : Proof := compact k (ProofCodec.pack k P)
def unpack (k : Nat) (Q : Proof) : Option Proof := ProofCodec.unpack k (expand k Q)

theorem packed_length_le (k b : Nat) (hk : k≤128) (hb : b≤128) :
    packedLength k (15*k+b)≤66800 := by
  unfold packedLength compactLength ProofCodec.packedLength ProofCodec.bodyLength
  have : (15*k+b+3)/4≤512 := by omega
  omega

theorem packed_length_max : packedLength 128 (15*128+128)=66800 := by decide

theorem unpack_empty : unpack 0 []=some [] := by decide

theorem unpack_missing_record : unpack 1 []=none := by decide

theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length=packedLength k (unpackedCount k P.length) := by
  simp [pack,packedLength,ProofCodec.pack_length]

theorem headByte_low (P : Proof) (r : Nat) (leaf : (P.getD (498*r+46) 0).toNat<16) :
    (ProofCodec.headByte P r).getLsbD 7=false := by
  rw [←BitVec.testBit_toNat]
  apply Nat.testBit_lt_two_pow
  rw [ProofCodec.headByte_toNat]
  simp only [List.getD_eq_getElem?_getD] at leaf ⊢
  norm_num at leaf ⊢
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
  have heads : ∀ r<k, ((ProofCodec.pack k P).getD (481*r+45) 0).getLsbD 7=false := by
    intro r hr
    rw [ProofCodec.getD_pack k P _ (by rw [count];unfold ProofCodec.packedLength bodyLength;omega),
      count,ProofCodec.packedByte,if_pos (by unfold bodyLength;omega),if_pos (by omega),
      show (481*r+45)/481=r by omega]
    exact headByte_low P r (leaf r hr)
  unfold unpack pack
  rw [expand_compact k (ProofCodec.pack k P) records heads]
  exact ProofCodec.unpack_pack k b P len small top salt
    (fun r hr => lt_trans (leaf r hr) (by decide)) leafTop

end CommitGolfCandidate.ProofCodec.BitPacked
