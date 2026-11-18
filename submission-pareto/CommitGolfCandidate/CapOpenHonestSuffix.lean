import CommitGolfCandidate.CapOpenLoadedSuffix
import CommitGolfCandidate.CapOpenTrapdoorBytes
import CommitGolfCandidate.CommitOutput

/-! A correctly constructed commitment heap supplies the honest cap tree.
The bytes are still the actual opening output; serialization through the
private-state ABI is proved explicitly. The commitment-distribution handoff
and lower-record authentication remain separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_committed_root_slot (committed : MachineState) (positions : Positions)
    (node : Nat) (bounded : node < 512) :
    readBuffer (capProgram.initialState .opening
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor, positions))
      (capProgram.layout.trapdoor+32*node) 32 =
        heapDigest committed 4294971424 node := by
  exact cap_open_input_trapdoor_roundtrip committed positions (32*node)
    (by change 32*node+32 ≤ 2147483648; omega)

theorem cap_open_committed_cap_parents (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed) :
    ∀ node, 0 < node → node < 256 →
      heapDigest committed 4294971424 node =
        combine (s6Compress oracle.compression) (heapDigest committed 4294971424 (2*node))
          (heapDigest committed 4294971424 (2*node+1)) := by
  intro node positive bounded
  rw [correct.2.1 node positive (by norm_num; omega), correct.2.1 (2*node) (by omega)
    (by norm_num; omega), correct.2.1 (2*node+1) (by omega) (by norm_num; omega), s6Heap]
  exact reference_heap_parent _ _ _ _ positive (by norm_num; omega)

theorem cap_open_honest_boundary_digests (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    capOpenBoundaryDigests
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      capProof (s6Compress oracle.compression)
        (capHeapTree (heapDigest committed 4294971424) 8 1)
        (capHeapView (heapDigest committed 4294971424)
          (capOpenRequestedMarks positions) 8 1) := by
  have selected : capOpenBoundaryDigests
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      (capControlBoundaries (capOpenRequestedMarks positions) 1022 (.visit 1)).map
        (heapDigest committed 4294971424) := by
    apply List.map_congr_left
    intro node member
    have bounded := cap_control_boundaries_nodes (capOpenRequestedMarks positions)
      1022 (.visit 1) (by constructor <;> decide) node member
    exact cap_open_committed_root_slot committed positions node bounded.2
  rw [selected]
  exact cap_heap_serialization (s6Compress oracle.compression) (heapDigest committed 4294971424)
    (capOpenRequestedMarks positions) (cap_open_committed_cap_parents oracle message committed correct)
    (cap_tree_marks_parent _)

end CommitGolfCandidate
