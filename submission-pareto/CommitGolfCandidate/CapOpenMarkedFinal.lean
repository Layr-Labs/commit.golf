import CommitGolfCandidate.CapOpenFilledMarks
import CommitGolfCandidate.CapOpenWalkInit

/-! Concrete record-to-traversal handoff. The descending pass establishes every
positive cap mark, and its outside-register frame preserves the ABI heap and
proof cursor. The two traversal entry instructions only set control registers. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordsFinal capMarkMachinePass

def capOpenMarkedFinal
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : MachineState :=
  capMarkMachinePass .x22 .x29 (capOpenRecordsFinal trapdoor positions) 256

def capOpenTraversalInitial
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : MachineState :=
  capOpenWalkInitial (capOpenMarkedFinal trapdoor positions)

theorem cap_open_marked_final_ready
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapMarkLoopReady .x22 4372 (capOpenMarkedFinal trapdoor positions) 256 0
      (capOpenRequestedMarks positions) := by
  have ready := cap_open_records_final_ready trapdoor positions positive
  exact cap_mark_pass_finished .x22 .x29 _ 4364 256 _
    (Or.inr rfl) (by decide) (by decide) (cap_tree_marks_parent _)
    (by simpa using ready.pc) ready.marks
    (cap_open_records_final_leaves trapdoor positions)
    (cap_open_records_marks_ready trapdoor positions positive)

theorem cap_open_marked_final_pc
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    (capOpenMarkedFinal trapdoor positions).pc = 4412 := by
  exact (cap_open_marked_final_ready trapdoor positions positive).pc

theorem cap_open_marked_final_register
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧ reg ≠ .x30) :
    (capOpenMarkedFinal trapdoor positions).getReg reg =
      (capOpenRecordsFinal trapdoor positions).getReg reg :=
  cap_mark_pass_register .x22 .x29 _ 256 reg outside

theorem cap_open_traversal_initial_control
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapDfsStateControl false (capOpenTraversalInitial trapdoor positions) (.visit 1) :=
  cap_open_walk_initial_control _ (cap_open_marked_final_pc trapdoor positions positive)

theorem cap_open_traversal_initial_stable
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapDfsStable false (capOpenTraversalInitial trapdoor positions)
      capProgram.layout.trapdoor := by
  have ready := cap_open_records_final_ready trapdoor positions positive
  refine ⟨?_, ?_, ?_, cap_open_walk_initial_root _, ?_⟩
  · exact (cap_open_walk_initial_register _ .x22 (by decide)).trans
      ((cap_open_marked_final_register trapdoor positions .x22 (by decide)).trans ready.marks)
  · exact (cap_open_walk_initial_register _ .x9 (by decide)).trans
      ((cap_open_marked_final_register trapdoor positions .x9 (by decide)).trans ready.roots)
  · exact (cap_open_walk_initial_register _ .x29 (by decide)).trans
      ((cap_open_marked_final_register trapdoor positions .x29 (by decide)).trans
        (cap_open_records_final_leaves trapdoor positions))
  · intro impossible
    contradiction

theorem cap_open_traversal_initial_marks
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapMarksReady (capOpenTraversalInitial trapdoor positions) 256 0
      (capOpenRequestedMarks positions) :=
  cap_marks_ready_memory _ _ 256 0 _ (cap_open_walk_initial_memory _)
    (cap_open_marked_final_ready trapdoor positions positive).ready

theorem cap_open_traversal_initial_cursor
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    (capOpenTraversalInitial trapdoor positions).getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof+576*positions.card) := by
  have ready := cap_open_records_final_ready trapdoor positions positive
  have cursor := ready.cursor
  simp only [capOpenAbiRecordContext, capOpenRequestedIndices, Finset.length_sort,
    Nat.sub_zero] at cursor
  exact (cap_open_walk_initial_register _ .x25 (by decide)).trans
    ((cap_open_marked_final_register trapdoor positions .x25 (by decide)).trans cursor)

end CommitGolfCandidate
