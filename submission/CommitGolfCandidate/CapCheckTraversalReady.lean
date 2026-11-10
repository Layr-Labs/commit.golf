import CommitGolfCandidate.CapCheckMarkedFinal
import CommitGolfCandidate.CapCheckDfsReady

/-! Actual checker record/mark/entry handoff to the rejection-aware traversal.
The admitted end pointer is unrounded. Minimum lower-record length supplies
only the starting cursor bound; future unknown-node loads use their guards. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_traversal_initial_window (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length) :
    CapCheckCursorWindow (capProgram.layout.proof+input.proof.length)
      (capCheckTraversalInitial state) := by
  have ordinalEq : ordinal=input.positions.card := by
    have partition := ready.partition
    omega
  have bounded := (cap_check_loader_bounds input admitted).1
  have small : capProgram.layout.proof+576*ordinal < 2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  have numeric : ((capCheckTraversalInitial state).getReg .x25).toNat =
      capProgram.layout.proof+576*ordinal := by
    rw [cap_check_traversal_initial_cursor input ordinal state ready]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  refine ⟨?_,?_,
    cap_check_traversal_initial_end input ordinal state ready,bounded⟩
  · rw [numeric]
    norm_num [capProgram,capExperimental,candidate,layout,trapdoorBytes,
      LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES]
    omega
  · rw [numeric,ordinalEq]
    omega

theorem cap_check_traversal_initial_ready (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (selectors : CapCheckSelectors state)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length) :
    CapCheckDfsReady (capProgram.layout.proof+input.proof.length)
      (capCheckCollectedMarks roots) (.visit 1) (capCheckTraversalInitial state) :=
  ⟨cap_check_traversal_initial_control input ordinal state ready roots collected,
    by constructor <;> decide,
    cap_check_traversal_initial_stable input ordinal state ready selectors,
    cap_check_traversal_initial_marks input ordinal state ready roots collected,
    cap_check_traversal_initial_window input ordinal state ready admitted enough⟩

end CommitGolfCandidate
