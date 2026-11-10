import CommitGolfCandidate.CapCheckCollectedView
import CommitGolfCandidate.CapCheckMarkedFinal
import CommitGolfCandidate.CopyRefinement

/-! The actual descending mark pass and DFS entry preserve every bounded
root-heap digest. This transfers the collected known-leaf payloads without
assuming internal roots already satisfy any hash equation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer

theorem cap_check_traversal_root_digest (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (node : Nat) (bounded : node<256) :
    capReadRoot (capCheckTraversalInitial state) node=capReadRoot state node := by
  unfold capReadRoot capCheckTraversalInitial
  rw [read_buffer_memory_congr _ _ (cap_check_walk_initial_memory _) _ _]
  have aligned : (12288+32*node)%8=0 := by omega
  rw [read_digest_eq_iff _ _ _ _ aligned aligned]
  intro word inside
  have address : 12288+32*node+8*word<20480 := by omega
  have frame := cap_check_filled_mark_root_word input ordinal state ready roots
    collected (12288+32*node+8*word) address
  simpa only [capCheckMarkedFinal,←BitVec.ofNat_add,Nat.add_assoc] using frame

theorem cap_check_traversal_known_leaves (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    CapCheckKnownLeaves (capCheckTraversalInitial state) 1 (capKnownView roots 7 0) := by
  apply cap_check_known_leaves_frame (capCheckCollectedMarks roots) state
    (capCheckTraversalInitial state) (capKnownView roots 7 0) 1
    (by decide) (by decide) (cap_check_known_root_marks roots)
    (cap_check_collected_root_view state roots collected)
  intro leaf _ bounded _
  exact cap_check_traversal_root_digest input ordinal state ready roots collected leaf bounded

end CommitGolfCandidate
