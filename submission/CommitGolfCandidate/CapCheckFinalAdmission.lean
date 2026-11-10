import CommitGolfCandidate.CapCheckDfsFinish
import CommitGolfCandidate.CapCheckTraversalReady

/-! Final root/commitment loads are admitted by the actual fixed checker ABI.
The traversal preserves the commitment pointer and its stable low root base;
no successful digest comparison is required for these memory safety facts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_final_abi_access (state : MachineState)
    (roots : state.getReg .x18=BitVec.ofNat 64 12288)
    (claimed : state.getReg .x26=BitVec.ofNat 64 capProgram.layout.commitment) :
    (∀ i < 4, accessValid
      (state.getReg .x18+signExtend12 (BitVec.ofNat 12 (32+8*i))) 8=true) ∧
    (∀ i < 4, accessValid
      (state.getReg .x26+signExtend12 (BitVec.ofNat 12 (8*i))) 8=true) := by
  constructor
  · intro i inside
    rw [roots]
    interval_cases i <;> decide
  · intro i inside
    rw [claimed]
    interval_cases i <;> decide

theorem cap_check_traversal_initial_commitment (input : CheckInput)
    (ordinal : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal 0 state) :
    (capCheckTraversalInitial state).getReg .x26=
      BitVec.ofNat 64 capProgram.layout.commitment :=
  (cap_check_walk_initial_register _ .x26 (by decide)).trans
    ((cap_check_marked_final_register state .x26 (by decide)).trans ready.commitment)

theorem cap_check_loaded_dfs_finish (input : CheckInput)
    (ordinal : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (selectors : CapCheckSelectors state)
    (admitted : input.proof.length≤capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length)
    (fuel : Nat) (sufficient : 8687≤fuel) (allowCoins : Bool) :
    execute (capWalkImage true) fuel (capCheckTraversalInitial state) allowCoins=
      capCheckDfsFinish (capCheckCollectedMarks roots) 510 (.visit 1)
        (capCheckTraversalInitial state) := by
  have traversalReady := cap_check_traversal_initial_ready input ordinal state ready
    roots collected selectors admitted enough
  have admission := cap_check_final_abi_access (capCheckTraversalInitial state)
    traversalReady.stable.roots
    (cap_check_traversal_initial_commitment input ordinal state ready)
  exact cap_check_dfs_finish_execute _ _ 510 (.visit 1) _ traversalReady
    (cap_control_complete _) admission.1 admission.2 fuel sufficient allowCoins

end CommitGolfCandidate
