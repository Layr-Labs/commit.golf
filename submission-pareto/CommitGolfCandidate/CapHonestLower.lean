import CommitGolfCandidate.CapLowerParser
import CommitGolfCandidate.CapOpenHonestSuffix
import CommitGolfCandidate.CapOpenRecordsHeadSlots
import CommitGolfCandidate.HeapModel
import CommitGolfCandidate.S6Model

/-! The honest lower record authenticates to the stored cap-level node. The
tagged salt, the three other leaf digests of the group and the fourteen
siblings all come from the same committed state; no injectivity or
collision-free assumption is used. The emitted-byte identification is a
separate loader/transcript bridge. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- Address of the leaf digest at `place` of the cell of `group` (72 bytes into the cell). -/
def capHonestCellAddress (group place : Nat) : Nat := 4563407208+368*group+32*place

def capHonestLowerRecord (message : Message) (committed : MachineState)
    (index : Index) : CapLowerRecord where
  index := index
  value := message index
  salt := expandTagged index (committedNonce committed index)
  others := fun place =>
    readBuffer committed (capHonestCellAddress (index.val/4) (capOpenPlace index.val (place.val+1))) 32
  sibling := fun level =>
    heapDigest committed 4294971424 (((4194304+index.val/4)/2^level.val) ^^^ 1)

theorem cap_honest_lower_path (message : Message) (committed : MachineState)
    (index : Index) :
    (capHonestLowerRecord message committed index).path =
      heapPath (heapDigest committed 4294971424) (4194304+index.val/4) 14 := by
  apply List.ext_getElem
  · rw [cap_lower_path_length, heap_path_length]
  · intro level leftBound rightBound
    have inside : level < 14 := by
      simpa only [cap_lower_path_length] using leftBound
    rw [heap_path_get _ _ _ _ inside]
    simp only [CapLowerRecord.path, s6RecordPath, List.getElem_ofFn, capHonestLowerRecord]
    apply Prod.ext
    · have group : index.val/4 < 2^22 := by
        have bounded := index.isLt
        change index.val < 16777216 at bounded
        change index.val/4 < 4194304
        omega
      exact (heap_leaf_direction 22 (index.val/4) level group (by omega)).symm
    · rfl

/-- The leaf digest stored at `place` of the cell of `group` is the reference leaf value. -/
theorem cap_honest_cell_digest (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (group place : Nat) (small : place < 4) (inside : 4*group+place < LENGTH) :
    readBuffer committed (capHonestCellAddress group place) 32 =
      s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed))
        (4*group+place) := by
  have leaf := correct.2.2 ⟨4*group+place, inside⟩
  have quotient : (4*group+place)/4 = group := by omega
  have remainder : (4*group+place)%4 = place := by omega
  simp only [quotient, remainder] at leaf
  rw [s6LeafValues, dif_pos inside, capHonestCellAddress,
    show 4563407208+368*group+32*place = 4563407136+368*group+72+32*place by omega]
  exact leaf

/-- The leaf's own digest is the reference leaf value at its index. -/
theorem cap_honest_own_digest (oracle : Oracle) (message : Message)
    (committed : MachineState) (index : Index) :
    s3LeafDigest oracle.permutation (capHonestLowerRecord message committed index).salt
        (capHonestLowerRecord message committed index).value =
      s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed))
        index.val := by
  rw [s6LeafValues, dif_pos index.isLt]
  rfl

/-- The record's group digest, recomputed from its own leaf and the three cell digests,
is the stored group node. -/
theorem cap_honest_record_group (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (index : Index) :
    s6RecordGroup oracle.permutation (capHonestLowerRecord message committed index).salt
        (capHonestLowerRecord message committed index).value index.val
        (capHonestLowerRecord message committed index).others =
      heapDigest committed 4294971424 (4194304+index.val/4) := by
  have bounded := index.isLt
  change index.val < 16777216 at bounded
  have group : index.val/4 < 2^22 := by norm_num; omega
  have others : (capHonestLowerRecord message committed index).others = fun k =>
      s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed))
        (s6OtherLeaf index.val k.val) := by
    funext k
    have small : capOpenPlace index.val (k.val+1) < 4 := by
      unfold capOpenPlace
      split <;> omega
    have place : s6OtherLeaf index.val k.val = 4*(index.val/4)+capOpenPlace index.val (k.val+1) := by
      simp only [s6OtherLeaf, capOpenPlace, Nat.add_sub_cancel]
    rw [place]
    exact cap_honest_cell_digest oracle message committed correct (index.val/4) _ small
      (by change _ < 16777216; omega)
  rw [others, s6_record_group_honest oracle.permutation _ _ _ index.val
      (cap_honest_own_digest oracle message committed index).symm,
    show (4194304 : Nat) = 2^22 by norm_num,
    correct.2.1 (2^22+index.val/4) (by positivity) (by norm_num; omega),
    s6_heap_group _ _ _ _ _ group]

theorem cap_honest_lower_root (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (index : Index) :
    (capHonestLowerRecord message committed index).root
        (s6Compress oracle.compression) oracle.permutation =
      heapDigest committed 4294971424 (256+(capGroup index).val) := by
  have bounded := index.isLt
  change index.val < 16777216 at bounded
  have parents : ∀ parent, 0 < parent → parent < 4194304 →
      heapDigest committed 4294971424 parent =
        combine (s6Compress oracle.compression) (heapDigest committed 4294971424 (2*parent))
          (heapDigest committed 4294971424 (2*parent+1)) := by
    intro parent positive below
    rw [correct.2.1 parent positive (by norm_num; omega), correct.2.1 (2*parent) (by omega)
      (by norm_num; omega), correct.2.1 (2*parent+1) (by omega) (by norm_num; omega), s6Heap]
    exact reference_heap_parent _ _ _ _ positive (by norm_num; omega)
  unfold CapLowerRecord.root
  change climb (s6Compress oracle.compression)
    (s6RecordGroup oracle.permutation (capHonestLowerRecord message committed index).salt
      (capHonestLowerRecord message committed index).value index.val
      (capHonestLowerRecord message committed index).others)
    (capHonestLowerRecord message committed index).path = _
  rw [cap_honest_lower_path, cap_honest_record_group oracle message committed correct index,
    reconstruct_heap_ancestor (s6Compress oracle.compression)
      (heapDigest committed 4294971424) 4194304 parents 14 (4194304+index.val/4)
      (by omega) (by rw [show (2 : Nat)^14 = 16384 by norm_num]; omega)]
  congr 1
  change (4194304+index.val/4)/16384 = 256+index.val/65536
  omega

end CommitGolfCandidate
