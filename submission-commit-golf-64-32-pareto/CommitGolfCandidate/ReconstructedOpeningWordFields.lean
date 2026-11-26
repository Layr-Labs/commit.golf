import CommitGolfCandidate.ReconstructedOpeningLinear

namespace CommitGolfCandidate.Reconstruction.OpeningWordFields
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open OpeningCursor OpeningHeaderAddress OpeningNodes Encoding

/-- The record and cap consume the same committed heap cells, including their physical tags. -/
def Heap (m : TwoPermutationPrototype.Memory) (t : CommitStorage.Trapdoor) (ps : Positions) :=
  ∀ (d j : Nat), CommitParents.Cell d j → ∀ w < 4,
    m ((CommitParents.addr d j)/8+w) = (HonestInputs.first t ps).getMem (W (CommitParents.addr d j+8*w))

theorem word (m : TwoPermutationPrototype.Memory) (t : CommitStorage.Trapdoor) (ps : Positions)
    (pos : 0<ps.card) (mem : Heap m t ps) (i : Index) (d : Fin 25) (dep : 0<d.val) (w : Fin 4) :
    m (wordAt i d w) = (Binding.pack (raw t d (sibling i d))).extractLsb' (64*w.val) 64 := by
  let j := sibling i d
  have cell := sibling_cell i d dep
  have read := read_digest_word (HonestInputs.first t ps) (CommitParents.addr d j) w.val
    (CommitParents.aligned d j) w.isLt
  have keep := mem d j cell w.val w.isLt
  have loc : wordAt i d w=(CommitParents.addr d j)/8+w.val := by unfold wordAt CommitParents.addr j heap;omega
  rw [loc,keep,←read,OpeningTrap.first_cell t ps pos d j cell]
  rw [raw,Binding.pack_unpack]

def digit (v : Word) (d : Nat) :=
  (v.toNat%2^(Binding.width d-192)) >>> (lows d-192)

theorem digit_value (m : TwoPermutationPrototype.Memory) (t : CommitStorage.Trapdoor) (ps : Positions)
    (pos : 0<ps.card) (mem : Heap m t ps) (o : Oracle) (k : Generator.Key) (msg : Message)
    (st : CommitStorage.Stored o k msg t) (i : Index) (d : Fin 25) (dep : 0<d.val) :
    digit (m (wordAt i d 3)) d = highDigit (LeafTree.tree o k msg d (sibling i d)) (lows d) := by
  have src := word m t ps pos mem i d dep (3 : Fin 4)
  have eq : m (wordAt i d 3) = (raw t d (sibling i d)).2 := by
    exact src.trans BitVec.extractLsb'_append_eq_left
  rw [eq];exact (fields o k msg t st d (sibling i d) (sibling_cell i d dep) dep).2.2

theorem extract10 (v : Word) : (v <<< (24 : Nat)) >>> (53 : Nat) = W (digit v 10) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 24)%2^64) >>> 53) = ((v.toNat%2^40) >>> 29)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract11 (v : Word) : (v <<< (24 : Nat)) >>> (53 : Nat) = W (digit v 11) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 24)%2^64) >>> 53) = ((v.toNat%2^40) >>> 29)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract12 (v : Word) : (v <<< (24 : Nat)) >>> (53 : Nat) = W (digit v 12) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 24)%2^64) >>> 53) = ((v.toNat%2^40) >>> 29)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract13 (v : Word) : (v <<< (24 : Nat)) >>> (53 : Nat) = W (digit v 13) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 24)%2^64) >>> 53) = ((v.toNat%2^40) >>> 29)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract14 (v : Word) : (v <<< (24 : Nat)) >>> (53 : Nat) = W (digit v 14) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 24)%2^64) >>> 53) = ((v.toNat%2^40) >>> 29)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract15 (v : Word) : (v <<< (23 : Nat)) >>> (56 : Nat) = W (digit v 15) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 23)%2^64) >>> 56) = ((v.toNat%2^41) >>> 33)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract16 (v : Word) : (v <<< (23 : Nat)) >>> (53 : Nat) = W (digit v 16) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 23)%2^64) >>> 53) = ((v.toNat%2^41) >>> 30)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract17 (v : Word) : (v <<< (23 : Nat)) >>> (53 : Nat) = W (digit v 17) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 23)%2^64) >>> 53) = ((v.toNat%2^41) >>> 30)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract18 (v : Word) : (v <<< (22 : Nat)) >>> (53 : Nat) = W (digit v 18) := by
  apply BitVec.eq_of_toNat_eq
  change (((v.toNat <<< 22)%2^64) >>> 53) = ((v.toNat%2^42) >>> 31)%2^64
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem extract19 (v : Word) : OpeningLinear.upper v &&& signExtend12 2047=W (digit v 19) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [OpeningLinear.upper,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,W,BitVec.toNat_ofNat]
  change (((v.toNat >>> 32)%2^32)%2^64) &&& (2^11-1)=((v.toNat%2^43) >>> 32)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.shiftRight_eq_div_pow];omega

end CommitGolfCandidate.Reconstruction.OpeningWordFields
