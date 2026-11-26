import CommitGolfCandidate.LateLayers
import CommitGolfCandidate.LateLeafFrame

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def gapAddr (p : Nat) := 4294971424+96*p+64

theorem node_gap (d j p : Nat) :
    nodeAddress d j+32 ≤ gapAddr p ∨ gapAddr p+32 ≤ nodeAddress d j := by
  unfold nodeAddress gapOffset gapAddr levelOffset
  omega

theorem gap_index (d p : Nat) :
    nodeAddress d (2*p)+64 = gapAddr (LENGTH-levelCount d+p) := by
  unfold nodeAddress gapOffset gapAddr levelOffset
  omega

def Gaps (s : MachineState) : Prop := ∀ p < LENGTH, readBuffer s (gapAddr p) 32 = 0

private theorem gap_valid {p : Nat} (small : p < LENGTH) : gapAddr p+32 ≤ rowBase := by
  change p < 16777216 at small
  unfold gapAddr rowBase; omega

theorem leaf_keeps_gaps (h : Compression) (s : MachineState) (i : Index) (g : Gaps s) :
    Gaps (writeLeaf h s i) := by
  intro p hp
  have top := gap_valid hp
  have hi := i.isLt; change i.val < 16777216 at hi
  apply (write_leaf_frame h s i _ 32 (by unfold rowBase at top; omega) _).trans (g p hp)
  constructor
  · right; unfold msgAddr gapAddr; omega
  · left; unfold contentAddr rowAddr; omega
  · exact (node_gap 0 i p).symm

theorem level_keeps_gaps (h : Compression) (s : MachineState) (d n : Nat)
    (bound : n ≤ levelCount (d+1)) (g : Gaps s) : Gaps (fillLevel h d n s) := by
  intro p hp
  have valid := gap_valid hp
  apply (fill_preserves _ _ _ _ _ 32 bound (by unfold rowBase at valid; omega)
    (fun j _ => (node_gap _ j p).symm)).trans (g p hp)

def treeNode (h : Compression) (base : Nat → Digest) : Nat → Nat → Digest
  | 0,j => base j
  | d+1,j => h (parentBlock (treeNode h base d (2*j)) (treeNode h base d (2*j+1)))

def LevelsThrough (h : Compression) (base : Nat → Digest) (d : Nat) (s : MachineState) :=
  ∀ level ≤ d, ∀ i < levelCount level, readBuffer s (nodeAddress level i) 32 = treeNode h base level i

private theorem earlier_node (d level i j : Nat) (le : level ≤ d) (ht : d < LOG_LENGTH) (hi : i < levelCount level) :
    nodeAddress level i+32 ≤ nodeAddress (d+1) j := by
  have bound : levelCount d ≤ levelCount level := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have can := level_count_le level
  have eq := level_successor d ht
  unfold nodeAddress gapOffset levelOffset
  omega

theorem fill_correct (h : Compression) (base : Nat → Digest) (s : MachineState) (d : Nat)
    (ht : d < LOG_LENGTH) (st : LevelsThrough h base d s) (g : Gaps s) :
    LevelsThrough h base (d+1) (fillLevel h d (levelCount (d+1)) s) := by
  intro level hl i hi
  by_cases last : level=d+1
  · subst level
    have eq := level_successor d ht
    have ga : LENGTH-levelCount d+i < LENGTH := by have := level_count_le d; omega
    have zero := g _ ga
    rw [← gap_index d i] at zero
    rw [filled_parent _ _ _ _ _ ht le_rfl hi zero, st d le_rfl (2*i) (by omega), st d le_rfl (2*i+1) (by omega)]
    rfl
  · have le : level ≤ d := by omega
    have before := parent_below_salts level i hi
    apply (fill_preserves _ _ _ _ _ _ le_rfl (by unfold rowBase at before; omega)
      (fun j _ => Or.inl (earlier_node d level i j le ht hi))).trans (st level le i hi)

end CommitGolfCandidate.Late
