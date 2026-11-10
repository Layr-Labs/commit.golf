import CommitGolfCandidate.CapCheckRecordsReady
import CommitGolfCandidate.CapTreeMarks
import CommitGolfCandidate.CapMarkImage

/-! A successful collected cap map supplies the actual occupancy leaves.
The descending checker pass then finalizes every internal mark using the
same map shape, while preserving high ABI bytes and the separate root heap.
This theorem does not assume that the map came from honest proof values. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capMarkMachinePass capMarkPass capMarkLoopRun
attribute [local irreducible] capMarkPrefix capCountedRun

private theorem root_word_memory_transport (left middle right : MachineState)
    (address : Word) (memory : left.mem=middle.mem)
    (word : middle.getMem address=right.getMem address) :
    left.getMem address=right.getMem address :=
  (congrFun memory address).trans word

def capCheckCollectedMarks (roots : CapRootMap) : Nat → Bool :=
  capTreeMarks (fun node => (roots (node-128)).isSome)

theorem cap_check_collected_marks_ready (state : MachineState) (roots : CapRootMap)
    (collected : CapCheckCollected state roots) :
    CapMarksReady state 128 127 (capCheckCollectedMarks roots) := by
  intro node lower upper
  have same : 128+(node-128)=node := by omega
  rw [capCheckCollectedMarks,cap_tree_marks_leaf _ node (by omega)]
  have mark := collected.marks (node-128) (by omega)
  rw [same] at mark
  exact mark

theorem cap_check_filled_mark_execute (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (1272+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capMarkMachinePass .x9 .x19 state 128) allowCoins
          return result.charge 1272 0) := by
  exact cap_check_mark_execute state (capCheckCollectedMarks roots)
    (cap_tree_marks_parent _) (by simpa only [ite_true] using ready.pc)
    ready.marks ready.leaves (cap_check_collected_marks_ready state roots collected)
    fuel allowCoins

theorem cap_check_filled_mark_finished (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    CapMarkLoopReady .x9 4556 (capMarkMachinePass .x9 .x19 state 128) 128 0
      (capCheckCollectedMarks roots) := by
  exact cap_mark_pass_finished .x9 .x19 state 4548 128 (capCheckCollectedMarks roots)
    (Or.inl rfl) (by decide) (by decide) (cap_tree_marks_parent _)
    (by simpa only [ite_true] using ready.pc) ready.marks ready.leaves
    (cap_check_collected_marks_ready state roots collected)

theorem cap_check_filled_mark_memory (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    (capMarkMachinePass .x9 .x19 state 128).mem=(capMarkPass state 127).mem := by
  exact cap_mark_pass_memory .x9 .x19 state 4548 128 (capCheckCollectedMarks roots)
    (Or.inl rfl) (by decide) (by decide) (cap_tree_marks_parent _)
    (by simpa only [ite_true] using ready.pc) ready.marks ready.leaves
    (cap_check_collected_marks_ready state roots collected)

theorem cap_check_filled_mark_high_frame (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    CapHighBytes (capMarkMachinePass .x9 .x19 state 128)
      (capProgram.initialState .check input) := by
  exact cap_high_bytes_memory (capMarkPass state 127)
    (capMarkMachinePass .x9 .x19 state 128) (capProgram.initialState .check input)
    (cap_check_filled_mark_memory input ordinal state ready roots collected)
    (cap_mark_pass_frame state (capProgram.initialState .check input)
      128 127 (by decide) (by decide) ready.inputs)

theorem cap_check_filled_mark_root_word (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (address : Nat) (below : address<20480) :
    (capMarkMachinePass .x9 .x19 state 128).getMem (BitVec.ofNat 64 address)=
      state.getMem (BitVec.ofNat 64 address) := by
  exact root_word_memory_transport (capMarkMachinePass .x9 .x19 state 128)
    (capMarkPass state 127) state (BitVec.ofNat 64 address)
    (cap_check_filled_mark_memory input ordinal state ready roots collected)
    (cap_mark_pass_roots state 128 127 address (by decide) (by decide) below)

end CommitGolfCandidate
