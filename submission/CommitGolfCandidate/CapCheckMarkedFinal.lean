import CommitGolfCandidate.CapCheckFilledMarks
import CommitGolfCandidate.CapCheckWalkInit
import CommitGolfCandidate.CapCheckRecordSelectors

/-! A successful arbitrary-reply record phase hands its collected roots and
actual compression selectors to the checker DFS. The descending mark pass
preserves the input pointers and root heap, and the two entry instructions
establish visit 1. No honest-proof or fixed-oracle assumption is used here. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capMarkMachinePass capMarkLoopRun capCountedRun

def capCheckMarkedFinal (state : MachineState) : MachineState :=
  capMarkMachinePass .x9 .x19 state 256

def capCheckTraversalInitial (state : MachineState) : MachineState :=
  capCheckWalkInitial (capCheckMarkedFinal state)

theorem cap_check_marked_final_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧ reg ≠ .x30) :
    (capCheckMarkedFinal state).getReg reg=state.getReg reg :=
  cap_mark_pass_register .x9 .x19 state 256 reg outside

theorem cap_check_marked_final_pc (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    (capCheckMarkedFinal state).pc=4596 := by
  exact (cap_check_filled_mark_finished input ordinal state ready roots collected).pc

theorem cap_check_traversal_initial_control (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    CapDfsStateControl true (capCheckTraversalInitial state) (.visit 1) :=
  cap_check_walk_initial_control _
    (cap_check_marked_final_pc input ordinal state ready roots collected)

theorem cap_check_traversal_initial_stable (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (selectors : CapCheckSelectors state) :
    CapDfsStable true (capCheckTraversalInitial state) 12288 := by
  have preserved (reg : Reg) (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧
      reg ≠ .x20 ∧ reg ≠ .x23 ∧ reg ≠ .x30 ∧ reg ≠ .x31) :
      (capCheckTraversalInitial state).getReg reg=state.getReg reg :=
    (cap_check_walk_initial_register _ reg
      ⟨outside.2.2.1,outside.2.2.2.2.2⟩).trans
      (cap_check_marked_final_register state reg
        ⟨outside.1,outside.2.1,outside.2.2.1,
          outside.2.2.2.1,outside.2.2.2.2.1⟩)
  refine ⟨?_,?_,?_,cap_check_walk_initial_root _,?_⟩
  · exact (preserved .x9 (by decide)).trans ready.marks
  · exact (preserved .x18 (by decide)).trans ready.roots
  · exact (preserved .x19 (by decide)).trans ready.leaves
  · intro _
    rw [preserved .x5 (by decide),preserved .x11 (by decide),
      preserved .x13 (by decide)]
    exact selectors

theorem cap_check_traversal_initial_marks (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    CapMarksReady (capCheckTraversalInitial state) 256 0 (capCheckCollectedMarks roots) :=
  cap_marks_ready_memory _ _ 256 0 _ (cap_check_walk_initial_memory _)
    (cap_check_filled_mark_finished input ordinal state ready roots collected).ready

theorem cap_check_traversal_initial_high (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    CapHighBytes (capCheckTraversalInitial state) (capProgram.initialState .check input) :=
  cap_high_bytes_memory _ _ _ (cap_check_walk_initial_memory _)
    (cap_check_filled_mark_high_frame input ordinal state ready roots collected)

theorem cap_check_traversal_initial_cursor (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state) :
    (capCheckTraversalInitial state).getReg .x25=
      BitVec.ofNat 64 (capProgram.layout.proof+544*ordinal) :=
  (cap_check_walk_initial_register _ .x25 (by decide)).trans
    ((cap_check_marked_final_register state .x25 (by decide)).trans ready.proof)

theorem cap_check_traversal_initial_end (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state) :
    (capCheckTraversalInitial state).getReg .x22=
      BitVec.ofNat 64 (capProgram.layout.proof+input.proof.length) :=
  (cap_check_walk_initial_register _ .x22 (by decide)).trans
    ((cap_check_marked_final_register state .x22 (by decide)).trans ready.endPointer)

end CommitGolfCandidate
