import CommitGolfCandidate.ReconstructedOpeningNodes
import CommitGolfCandidate.ReconstructedOpeningCursor

namespace CommitGolfCandidate.Reconstruction.OpeningHeaderAddress
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Encoding OpeningCursor TwoPermutationPrototype.RV64
set_option maxRecDepth 12000

abbrev heap : Nat := 4294971424
def basePtr (i : Index) (depth : Nat) := W (heap+32*sibling i depth)
def wordAt (i : Index) (depth w : Nat) := heap/8+4*(sibling i depth+depth)+w

private theorem clear (x : Word) : x &&& signExtend12 4064 = (x >>> (5 : Nat)) <<< (5 : Nat) := by
  have mask : ∀ k : Fin 64, (signExtend12 4064).getLsbD k=decide (5≤k.val) := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and,mask ⟨k,hk⟩,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight]
  by_cases hi : 5≤k
  · simp [hi,hk,show 5+(k-5)=k by omega]
  · simp [hi]

private theorem twice (n shift : Nat) (small : n<2^64) :
    (W n >>> shift) >>> (5 : Nat) = W (n >>> (shift+5)) := by
  apply BitVec.eq_of_toNat_eq
  have lim := (Nat.shiftRight_le n (shift+5)).trans_lt small
  simp only [BitVec.toNat_ushiftRight,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt lim]
  exact (Nat.shiftRight_add _ _ _).symm

theorem compiled (n shift : Nat) (small : n<2^64) :
    (((W n >>> shift) &&& signExtend12 4064) ^^^ signExtend12 32) =
      W (32*((n >>> (shift+5)) ^^^ 1)) := by
  rw [clear]
  change (((W n >>> shift) >>> (5 : Nat)) <<< (5 : Nat)) ^^^ (W 1 <<< (5 : Nat)) = _
  rw [←BitVec.shiftLeft_xor_distrib,twice n shift small,←BitVec.ofNat_xor,BitVec.shiftLeft_eq_mul_twoPow]
  change W ((n >>> (shift+5)) ^^^ 1)*W 32=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

theorem sibling_ptr (i : Index) (depth : Nat) (bound : depth≤19) :
    (((W (2^24+i.val) >>> (19-depth)) &&& signExtend12 4064) ^^^ signExtend12 32)+W heap =
      basePtr i depth := by
  rw [compiled _ _ (by have : i.val<2^24:=i.isLt;omega),show 19-depth+5=24-depth by omega,←BitVec.ofNat_add]
  unfold basePtr sibling
  rw [Nat.add_comm]

theorem offset (i : Index) (depth w : Nat) (imm : BitVec 12)
    (disp : signExtend12 imm=W (32*depth+8*w)) :
    basePtr i depth + signExtend12 imm=wordAddress (wordAt i depth w) := by
  rw [disp,basePtr,←BitVec.ofNat_add]
  apply congrArg (W)
  unfold wordAt heap;omega

/-- The offset within the serialized full tree uses the heap number at the requested
logical depth plus one 32-byte guard cell per preceding level. -/
theorem physical (i : Index) (depth w : Nat) :
    wordAddress (wordAt i depth w) = W (CommitParents.addr depth (sibling i depth)+8*w) := by
  apply congrArg (W)
  unfold wordAt heap CommitParents.addr;omega

theorem word_room (i : Index) (d w : Nat) (pos : 0<d) (lim : d≤24) (slot : w<4) :
    wordAt i d w<704643500 := by
  have h := OpeningNodes.sibling_cell i (⟨d,by omega⟩ : Fin 25) pos
  have h' : sibling i d<2^(d+1) := h.2.2
  have v : 2^(d+1)≤2^25 := Nat.pow_le_pow_right (by decide) (by omega)
  unfold wordAt heap;omega

end CommitGolfCandidate.Reconstruction.OpeningHeaderAddress
