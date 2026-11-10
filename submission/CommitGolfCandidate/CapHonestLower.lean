import CommitGolfCandidate.CapLowerParser
import CommitGolfCandidate.CapOpenHonestSuffix
import CommitGolfCandidate.HeapModel

/-! The honest lower record authenticates to the stored height-seventeen
ancestor. All siblings and salt come from the same actual commitment heap;
no injectivity or collision-free assumption is used. The emitted-byte
identification is a separate loader/transcript bridge. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capHonestLowerRecord (message : Message) (committed : MachineState)
    (index : Index) : CapLowerRecord where
  index := index
  value := message index
  salt := readBuffer committed (5368713248+32*index.val) 32
  sibling := fun level =>
    heapDigest committed 4294971424 (((LENGTH+index.val)/2^level.val) ^^^ 1)

theorem cap_honest_lower_path (message : Message) (committed : MachineState)
    (index : Index) :
    (capHonestLowerRecord message committed index).path =
      heapPath (heapDigest committed 4294971424) (LENGTH+index.val) 17 := by
  apply List.ext_getElem
  · rw [cap_lower_path_length, heap_path_length]
  · intro level leftBound rightBound
    have inside : level < 17 := by
      simpa only [cap_lower_path_length] using leftBound
    rw [heap_path_get _ _ _ _ inside]
    simp only [CapLowerRecord.path, List.getElem_ofFn, capHonestLowerRecord]
    apply Prod.ext
    · exact (heap_leaf_direction 24 index.val level index.isLt (by omega)).symm
    · rfl

theorem cap_honest_lower_root (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (index : Index) :
    (capHonestLowerRecord message committed index).root oracle.compression =
      heapDigest committed 4294971424 (128+(capGroup index).val) := by
  rw [CapLowerRecord.root, cap_honest_lower_path]
  have leaf := correct.2.2 index
  change heapDigest committed 4294971424 (LENGTH+index.val) =
    leafDigest oracle.compression
      (readBuffer committed (5368713248+32*index.val) 32) (message index) at leaf
  change climb oracle.compression
    (leafDigest oracle.compression
      (readBuffer committed (5368713248+32*index.val) 32) (message index))
    (heapPath (heapDigest committed 4294971424) (LENGTH+index.val) 17) = _
  rw [← leaf, reconstruct_heap_ancestor oracle.compression
    (heapDigest committed 4294971424) LENGTH correct.2.1]
  · congr 1
    change (16777216+index.val)/131072 = 128+index.val/131072
    omega
  · have bounded := index.isLt
    omega
  · change 131072 ≤ 16777216+index.val
    omega

end CommitGolfCandidate
