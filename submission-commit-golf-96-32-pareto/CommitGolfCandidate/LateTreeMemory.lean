import CommitGolfCandidate.S4Padding
import CommitGolfCandidate.LateLayers
import CommitGolfCandidate.LateLeafFrame
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem leaf_keeps_gaps (H : Compression) (s : MachineState) (i : Index) (g : Gaps s) : Gaps (writeLeaf H s i) := by
  intro h p k gap
  have top:=padValid _ _ _ gap
  have hi : i.val<16777216:=i.isLt
  apply (write_leaf_frame H s i _ 32 (by unfold rowBase at top;omega) _).trans (g _ _ _ gap)
  constructor
  · right;unfold msgAddr unusedSlotAddr rowAddress;omega
  · left;unfold contentAddr rowAddr;omega
  · exact (node_pad 0 i h p k (by decide) i.isLt gap).symm

theorem level_keeps_gaps (H : Compression) (s : MachineState) (d n : Nat) (ht : d<24)
    (bound : n≤levelCount (d+1)) (g : Gaps s) : Gaps (fillLevel H d n s) := by
  intro h p k gap
  have top:=padValid _ _ _ gap
  exact (fill_preserves H d n s _ 32 bound (by unfold rowBase at top;omega)
    (fun j hj=>(node_pad (d+1) j h p k (by omega) (by omega) gap).symm)).trans (g _ _ _ gap)

def retain (d : Nat) (v : Digest) := S4.retained S4.active (24-d) v
theorem retain_packed (d : Nat) (w : Digest) : retain d w=
    if 0<d ∧ d≤18 then (0 : BitVec 18) ++ w.extractLsb' 0 238
    else if 0<d ∧ d≤22 then (0 : BitVec 16) ++ w.extractLsb' 0 240 else w := by
  unfold retain S4.retained S4.bits S4.active
  simp only [true_and]
  split_ifs <;> first | rfl | omega | contradiction
def layerHash (H : Compression) (h : Nat) : Compression := fun x=>S4.retained S4.active (h+1) (H x)
def treeNode (H : Compression) (base : Nat→Digest) : Nat → Nat → Digest
  | 0,i => if i<levelCount 0 then base i else 0
  | h+1,i => if i<levelCount (h+1) then
      layerHash H h (S4.row h (treeNode H base h (S4.radix h*i)) (treeNode H base h (S4.radix h*i+1)) (treeNode H base h (S4.radix h*i+2)))
    else 0
theorem missing_node (H : Compression) (base : Nat→Digest) (h i : Nat) (out : levelCount h ≤ i) :
    treeNode H base h i=0 := by cases h <;> exact if_neg (Nat.not_lt.mpr out)
def LevelsThrough (H : Compression) (base : Nat→Digest) (d : Nat) (s : MachineState) :=
  ∀ h≤d,∀ i<levelCount h, readBuffer s (nodeAddress h i) 32=treeNode H base h i

theorem rowChild (H : Compression) (base : Nat→Digest) (h p k : Nat) (s : MachineState) (ht : h<24) (hp : p<levelCount (h+1))
    (hk : k<3) (st : LevelsThrough H base h s) (g : Gaps s) :
    readBuffer s (unusedSlotAddr h p k) 32=if k<S4.radix h then treeNode H base h (S4.radix h*p+k) else 0 := by
  by_cases valid : k<S4.radix h
  · rw [if_pos valid]
    by_cases child : S4.radix h*p+k<levelCount h
    · exact (congrArg (fun a=>readBuffer s a 32) (row_slot h p k valid).symm).trans (st h le_rfl _ child)
    · rw [missing_node H base h (S4.radix h*p+k) (by omega)];exact g h p k ⟨ht,hp,hk,Or.inr (by omega)⟩
  · rw [if_neg valid];exact g h p k ⟨ht,hp,hk,Or.inl (by omega)⟩

theorem fill_correct (H : Compression) (base : Nat→Digest) (s : MachineState) (d : Nat)
    (ht : d<LOG_LENGTH) (st : LevelsThrough H base d s) (g : Gaps s) :
    LevelsThrough H base (d+1) (fillLevel (layerHash H d) d (levelCount (d+1)) s) := by
  intro h limit i hi
  by_cases newRow : h=d+1
  · subst h
    have nodeEq : treeNode H base (d+1) i=layerHash H d (S4.row d (treeNode H base d (S4.radix d*i)) (treeNode H base d (S4.radix d*i+1)) (treeNode H base d (S4.radix d*i+2))) := if_pos hi
    rw [filled_parent _ d (levelCount (d+1)) i s ht le_rfl hi,nodeEq,readTriple s]
    apply congrArg (layerHash H d)
    have one:=rowChild H base d i 0 s ht hi (by decide) st g
    have two:=rowChild H base d i 1 s ht hi (by decide) st g
    have three:=rowChild H base d i 2 s ht hi (by decide) st g
    by_cases z : d=0 <;>
      simp only [unusedSlotAddr,S4.radix,S4.row,z,ite_true,ite_false,Nat.add_zero,Nat.mul_zero,↓reduceIte] at one two three ⊢ <;>
      rw [one,two,three] <;> norm_num <;> rfl
  · have lo : h≤d:=by omega
    have bound:=parent_below_salts h i hi
    exact (fill_preserves _ d _ s _ _ le_rfl (by unfold rowBase at bound;omega)
      (fun j _=>Or.inl (earlier_node d h i j lo ht hi))).trans (st h lo i hi)
end CommitGolfCandidate.Late
