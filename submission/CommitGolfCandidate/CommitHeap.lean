import CommitGolfCandidate.S3LeavesMemory
import CommitGolfCandidate.S6ParentMemory
import CommitGolfCandidate.ParentRefinement

/-! The heap built by the commitment: the appended code (nonce generator, leaf phase with group
calls) leaves every group digest in its heap node (S3LeavesMemory), and the parent sweep makes every
internal node the truncated compression of its children. Cells and nonces lie above the heap and
are kept by the sweep. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem ready_heap (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x9 = BitVec.ofNat 64 4294971424 :=
  (s3_ready_registers message answer).2.2.2.2.2.1

attribute [local irreducible] s3Leaves s6Parents s3CommitReady checkEvaluation

/-- After the leaf phase and the parent sweep, every heap node `1 .. 2^23 - 1` is the tree's node
for the message under the tagged generated nonces. -/
theorem commit_input_tree (oracle : Oracle) (message : Message) (answer : BitVec 256) :
    let leaves := (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
    let finished := (checkEvaluation oracle (s6Parents leaves)).1
    ∀ node, 0 < node → node < 2^23 → heapDigest finished 4294971424 node =
      s6Heap oracle.compression oracle.permutation message
        (expandTaggedVector (s4GenNonce oracle.permutation answer)) node := by
  intro leaves finished node positive inside
  have heap : leaves.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (s3_leaves_register oracle _ (2^18) .x9 (by simp)).trans (ready_heap message answer)
  have top : leaves.getReg .x22 = BitVec.ofNat 64 (4294971424 + 2^28) :=
    s3_leaves_limit oracle _ (2^18) 4294971424 (ready_heap message answer)
  unfold heapDigest s6Heap
  exact s6_parents_heap oracle leaves 4294971424 (base := heap) (top := top) (aligned := by decide)
    (bound := by decide)
    (groups := fun g below => by
      rw [show 4294971424 + 32 * (2^22 + g) = 4429189152 + 32 * g by omega]
      exact s3_leaves_group oracle message answer g below) (node := node) (inside := ⟨positive, inside⟩)

/-- The parent sweep keeps the cells. -/
theorem commit_input_tree_cell (oracle : Oracle) (message : Message) (answer : BitVec 256)
    (index : Index) :
    let leaves := (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
    let finished := (checkEvaluation oracle (s6Parents leaves)).1
    readBuffer finished (4563407136 + 368 * (index.val / 4) + 72 + 32 * (index.val % 4)) 32 =
      s3LeafDigest oracle.permutation (expandTagged index (s4GenNonce oracle.permutation answer index))
        (message index) := by
  intro leaves finished
  have heap : leaves.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (s3_leaves_register oracle _ (2^18) .x9 (by simp)).trans (ready_heap message answer)
  have top : leaves.getReg .x22 = BitVec.ofNat 64 (4294971424 + 2^28) :=
    s3_leaves_limit oracle _ (2^18) 4294971424 (ready_heap message answer)
  have indexBound : index.val < 2^24 := index.isLt
  rw [s6_parents_preserves oracle leaves 4294971424 (base := heap) (top := top) (aligned := by decide)
    (bound := by decide) (count := 32) (outside := Or.inr (by omega)) (bounded := by omega)]
  exact s3_leaves_digest oracle message answer index

/-- The parent sweep keeps the nonces. -/
theorem commit_input_tree_nonce (oracle : Oracle) (message : Message) (answer : BitVec 256)
    (index : Index) :
    let leaves := (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
    let finished := (checkEvaluation oracle (s6Parents leaves)).1
    readBuffer finished (6106911008 + 16 * index.val) 16 = s4GenNonce oracle.permutation answer index := by
  intro leaves finished
  have heap : leaves.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (s3_leaves_register oracle _ (2^18) .x9 (by simp)).trans (ready_heap message answer)
  have top : leaves.getReg .x22 = BitVec.ofNat 64 (4294971424 + 2^28) :=
    s3_leaves_limit oracle _ (2^18) 4294971424 (ready_heap message answer)
  have indexBound : index.val < 2^24 := index.isLt
  rw [s6_parents_preserves oracle leaves 4294971424 (base := heap) (top := top) (aligned := by decide)
    (bound := by decide) (count := 16) (outside := Or.inr (by omega)) (bounded := by omega)]
  exact s3_leaves_nonce oracle message answer index

end CommitGolfCandidate
