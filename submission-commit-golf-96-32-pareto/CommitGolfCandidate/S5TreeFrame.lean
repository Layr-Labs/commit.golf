import CommitGolfCandidate.S5TreeNode
import CommitGolfCandidate.S5PhaseTable
import CommitGolfCandidate.S5LeafContents
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64
def tdBase :=4294975488
def scratchBase :=7113547776
def tagAddr (h : Height) (p : Nat) :=rowAddress h.val p+64
def Apart (a n b m : Nat) := a+n≤b ∨ b+m≤a
theorem apart_symm {a n b m : Nat} (h : Apart a n b m) : Apart b m a n := h.symm

theorem source_address (h : Height) (p : Nat) : rowAddress h.val p=tdBase+levelOffset h.val+96*p := rfl
theorem aligned_node (d p : Nat) : nodeAddress d p%8=0 := nodeAligned d p
theorem gap_ceiling (h : Height) (p : Nat) (small : p<count h) :
    tagAddr h p+32≤tdBase+levelOffset (h.val+1) := by
  unfold tagAddr tdBase;have :=row_after h.val p h.isLt small;omega
theorem gap_limit (h : Height) (p : Nat) (small : p<count h) : tagAddr h p+32≤rowBase :=
  (gap_ceiling h p small).trans (by have :=padded_region (h.val+1);unfold tdBase;omega)

theorem pad_before (h p k d j : Nat) (g : Padding h p k) (before : h<d) :
    unusedSlotAddr h p k+32≤nodeAddress d j := by
  have end_:=padEnd _ _ _ g
  have m:=levelOffset_mono (show h+1≤d by omega)
  unfold nodeAddress;omega

theorem cell_apart {h p k d q z : Nat} (hh : h<24) (hd : d<24) (hp : p<levelCount (h+1))
    (hq : q<levelCount (d+1)) (hk : k<3) (hz : z<3) (diff : h≠d ∨ p≠q ∨ k≠z) :
    Apart (unusedSlotAddr h p k) 32 (unusedSlotAddr d q z) 32 := by
  rcases lt_trichotomy h d with lt|rfl|gt
  · left;have a:=row_after h p hh hp;have b:=levelOffset_mono (show h+1≤d by omega)
    unfold unusedSlotAddr rowAddress at *;omega
  · unfold Apart unusedSlotAddr rowAddress at *;omega
  · right;have a:=row_after d q hd hq;have b:=levelOffset_mono (show d+1≤h by omega)
    unfold unusedSlotAddr rowAddress at *;omega

theorem gap_pad {h : Height} {p : Nat} (small : p<count h) (binary : h.val≠0) : Padding h.val p 2 :=
  ⟨h.isLt,small,by decide,Or.inl (by simp [S4.radix,binary])⟩

theorem distinct_nodes {h i d j : Nat} (hh : h≤24) (hd : d≤24) (hi : i<levelCount h) (hj : j<levelCount d)
    (diff : h≠d ∨ i≠j) : Apart (nodeAddress h i) 32 (nodeAddress d j) 32 := by
  rcases lt_trichotomy h d with lt|rfl|gt
  · left; have en:=nodeEnd h i (by omega) hi;have m:=levelOffset_mono (show h+1≤d by omega)
    unfold nodeAddress at en ⊢;omega
  · by_cases bottom : h=0 <;> simp only [Apart,nodeAddress,bottom,ite_true,ite_false,Late.gapOffset] <;> omega
  · right;have en:=nodeEnd d j (by omega) hj;have m:=levelOffset_mono (show d+1≤h by omega)
    unfold nodeAddress at en ⊢;omega

def gaps (s : MachineState) := ∀ h p k,Padding h p k →
  readBuffer s (unusedSlotAddr h p k+8) 24=0 ∧
  (¬(8≤h ∧ h<16 ∧ k=2) → readBuffer s (unusedSlotAddr h p k) 8=0)

structure TreeState (H : Compression) (base : Nat→Output) (salt : Late.SaltTape) (d : Nat) (s : MachineState) : Prop where
  nodes : ∀ k≤d,∀ i<levelCount k,readBuffer s (nodeAddress k i) 32=treeNode H base k i
  salts : ∀ ix : Index,readBuffer s (saltAddress ix.val) 24=salt ix
  pads : gaps s

def doneRows (H : Compression) (base : Nat→Output) (d n : Nat) (s : MachineState) :=
  ∀ j<n,readBuffer s (nodeAddress (d+1) j) 32=treeNode H base (d+1) j

def physicalChild (s : MachineState) (d p k : Nat) := readBuffer s (unusedSlotAddr d p k) 32

structure NodeEffect (H : Compression) (h : Height) (p : Nat) (s t : MachineState) : Prop where
  value : readBuffer t (nodeAddress (h.val+1) p) 32=nodeHash H h.val (physicalChild s h.val p 0)
    (physicalChild s h.val p 1) (physicalChild s h.val p 2)
  outside : ∀ a n,a+n≤MEMORY_BYTES→Apart a n (nodeAddress (h.val+1) p) 32→
    (chained h→Apart a n (tagAddr h p) 8 ∧ Apart a n scratchBase 96) → readBuffer t a n=readBuffer s a n
end CommitGolfCandidate.S5Machine
