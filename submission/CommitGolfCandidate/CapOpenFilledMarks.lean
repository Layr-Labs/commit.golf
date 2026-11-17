import CommitGolfCandidate.CapOpenMarksSeen
import CommitGolfCandidate.CapOpenRecordsABI
import CommitGolfCandidate.CapTreeMarks
import CommitGolfCandidate.CapMarkImage

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState capOpenInitializedState capCountedRun

def capOpenRecordsFinal
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : MachineState :=
  capCountedRun capOpenRecordState positions.card
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions)))

def capOpenRequestedMarks (positions : Positions) : Nat → Bool :=
  capTreeMarks (capOpenMarksSeen (capOpenRequestedIndices positions) positions.card)

private theorem mark_workspace_bound (node : Nat) (bound : node < 512) :
    28672+8*node+8 ≤ 32768 := by omega

theorem cap_open_records_final_mark
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (node : Nat) (nodeBound : node < 512) :
    (capOpenRecordsFinal trapdoor positions).getMem (capMarkAddress node) =
      capMarkWord (capOpenMarksSeen (capOpenRequestedIndices positions) positions.card node) := by
  have windows := cap_open_abi_record_windows positions
  have ready := cap_open_abi_record_ready trapdoor positions positive
  have folded := cap_open_records_marks capOpenAbiRecordContext
    (capOpenRequestedIndices positions)
    (capProgram.initialState .opening (trapdoor, positions))
    windows.1 windows.2.1 windows.2.2 (by decide)
    (cap_open_abi_record_inputs trapdoor positions) positions.card _ ready node nodeBound
  have zero := cap_open_initial_workspace_zero trapdoor positions (28672+8*node)
    (mark_workspace_bound node nodeBound)
  rw [cap_open_marks_fold, show
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getMem
      (capMarkAddress node) = 0 from zero] at folded
  exact folded

theorem cap_open_records_marks_ready
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapMarksReady (capOpenRecordsFinal trapdoor positions) 256 255
      (capOpenRequestedMarks positions) := by
  intro node lower upper
  rw [cap_open_records_final_mark trapdoor positions positive node upper,
    capOpenRequestedMarks, cap_tree_marks_leaf _ node (by omega)]

theorem cap_open_records_final_ready
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapOpenRecordsReady capOpenAbiRecordContext (capOpenRequestedIndices positions)
      (capProgram.initialState .opening (trapdoor, positions)) 0
      (capOpenRecordsFinal trapdoor positions) := by
  have windows := cap_open_abi_record_windows positions
  exact cap_open_records_loop_finished _ _ _ windows.1 windows.2.1 windows.2.2
    (cap_open_abi_record_inputs trapdoor positions) positions.card _
    (cap_open_abi_record_ready trapdoor positions positive)

theorem cap_open_records_final_leaves
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenRecordsFinal trapdoor positions).getReg .x29 = 256 := by
  exact (cap_open_records_register positions.card _ .x29 (by decide)).trans
    (cap_open_setup_registers _).2.2.2.2.2.2.2.1

theorem cap_open_filled_mark_execute
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (2552+fuel)
      (capOpenRecordsFinal trapdoor positions) allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capMarkMachinePass .x22 .x29 (capOpenRecordsFinal trapdoor positions) 256)
            allowCoins
          return result.charge 2552 0) := by
  have ready := cap_open_records_final_ready trapdoor positions positive
  exact cap_open_mark_execute _ (capOpenRequestedMarks positions)
    (cap_tree_marks_parent _)
    (by simpa using ready.pc) ready.marks
    (cap_open_records_final_leaves trapdoor positions)
    (cap_open_records_marks_ready trapdoor positions positive) fuel allowCoins

end CommitGolfCandidate
