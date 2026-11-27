import CommitGolfCandidate.Stage3cPhaseTable
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tdBase :=4294975488
def scratchBase :=7516200960
def tagAddr (h : Height) (p : Nat) := nodeAddress h.val (2*p)+64
def Apart (a n b m : Nat) := a+n≤b ∨ b+m≤a
theorem apart_symm {a n b m} (h : Apart a n b m) : Apart b m a n := h.symm

theorem level_mono {d k : Nat} (le : d≤k) : levelOffset d≤levelOffset k := by
  have small : levelCount k≤levelCount d:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le_sub_left le LOG_LENGTH)
  unfold levelOffset;omega

theorem node_before {d j k i : Nat} (lower : d<k) (hd : d<LOG_LENGTH) (inside : j<levelCount d) :
    nodeAddress d j+32≤nodeAddress k i := by
  have eqn:=level_successor d hd
  have base:=level_mono (show d+1≤k from lower)
  rw [level_adjacent d hd] at base
  unfold nodeAddress Late.gapOffset;omega

theorem distinct_nodes {d j k i : Nat} (hd : d≤LOG_LENGTH) (hk : k≤LOG_LENGTH)
    (jj : j<levelCount d) (ii : i<levelCount k) (ne : d≠k ∨ j≠i) : Apart (nodeAddress d j) 32 (nodeAddress k i) 32 := by
  rcases lt_trichotomy d k with lt|rfl|gt
  · exact Or.inl (node_before lt (by omega) jj)
  · unfold Apart nodeAddress Late.gapOffset;omega
  · exact Or.inr (node_before gt (by omega) ii)

theorem source_address (h : Height) (p : Nat) :
    nodeAddress h.val (2*p)=tdBase+96*(LENGTH-levelCount h.val+p) := by unfold nodeAddress tdBase levelOffset Late.gapOffset;omega

theorem aligned_node (d p : Nat) : nodeAddress d p%8=0 := by unfold nodeAddress levelOffset Late.gapOffset;omega

theorem node_gap_apart (d i : Nat) (h : Height) (p : Nat) : Apart (nodeAddress d i) 32 (tagAddr h p) 32 := by
  unfold Apart tagAddr nodeAddress levelOffset Late.gapOffset;omega

theorem gap_ceiling (h : Height) (p : Nat) (inside : p<count h) : tagAddr h p+32≤tdBase+levelOffset (h.val+1) := by
  change p<levelCount (h.val+1) at inside
  rw [tagAddr,source_address,level_adjacent h.val h.isLt];unfold levelOffset;omega

theorem distinct_tag (h k : Height) (p q : Nat) (hp : p<count h) (hq : q<count k) (ne : h≠k) :
    Apart (tagAddr h p) 8 (tagAddr k q) 8 := by
  have neq : h.val≠k.val := fun e=>ne (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne neq with lt|gt
  · have finish:=gap_ceiling h p hp;have before:=level_mono (show h.val+1≤k.val from lt)
    left;unfold tagAddr nodeAddress tdBase at *;omega
  · have finish:=gap_ceiling k q hq;have before:=level_mono (show k.val+1≤h.val from gt)
    right;unfold tagAddr nodeAddress tdBase at *;omega

def gaps (s : MachineState) := ∀ h : Height,∀ p<count h,
  readBuffer s (tagAddr h p+8) 24=0 ∧ (¬chained h → readBuffer s (tagAddr h p) 8=0)

structure TreeState (H : Compression) (base : Nat→Output) (salt : Late.SaltTape) (d : Nat) (s : MachineState) : Prop where
  nodes : ∀ k≤d, ∀ i<levelCount k,readBuffer s (nodeAddress k i) 32=treeNode H base k i
  salts : ∀ ix : Index,readBuffer s (saltAddress ix.val) 24=salt ix
  pads : gaps s

def doneRows (H : Compression) (base : Nat→Output) (d n : Nat) (s : MachineState) :=
  ∀ j<n,readBuffer s (nodeAddress (d+1) j) 32=treeNode H base (d+1) j

structure NodeEffect (H : Compression) (h : Height) (p : Nat) (s t : MachineState) : Prop where
  value : readBuffer t (nodeAddress (h.val+1) p) 32=parentDigest H h
    (readBuffer s (nodeAddress h.val (2*p)) 32) (readBuffer s (nodeAddress h.val (2*p+1)) 32)
  outside : ∀ a n,a+n≤MEMORY_BYTES → Apart a n (nodeAddress (h.val+1) p) 32 →
    (chained h → Apart a n (tagAddr h p) 8 ∧ Apart a n scratchBase 96) →
      readBuffer t a n=readBuffer s a n

theorem grow_row {H h p s t base salt} (before : TreeState H base salt h.val s)
    (built : doneRows H base h.val p s) (effect : NodeEffect H h p s t) (inside : p<count h) :
    doneRows H base h.val (p+1) t := by
  intro j hj
  have double:=level_successor h.val h.isLt
  have pfit : p<levelCount (h.val+1):=inside
  by_cases last : j=p
  · subst j;rw [effect.value,before.nodes h.val le_rfl _ (by omega),before.nodes h.val le_rfl _ (by omega)]
    change parentDigest H h _ _=parentDigest H (Binary.height h.val) _ _
    rw [show Binary.height h.val=h from Fin.ext (Nat.mod_eq_of_lt h.isLt)]
  · have good : j<levelCount (h.val+1):=by omega
    have top:=parent_below_salts _ _ good
    refine (effect.outside _ 32 (by change _≤2^36;unfold rowBase at top;omega)
      (distinct_nodes (by have :=h.isLt;change h.val+1≤24;omega) (by have :=h.isLt;change h.val+1≤24;omega) good pfit (Or.inr last)) ?_).trans (built _ (by omega))
    intro _
    obtain a|b:=node_gap_apart (h.val+1) j h p
    · exact ⟨Or.inl a,Or.inl (by unfold scratchBase rowBase at *;omega)⟩
    · exact ⟨Or.inr (by omega),Or.inl (by unfold scratchBase rowBase at *;omega)⟩
end CommitGolfCandidate.Chained.BinaryMachine
