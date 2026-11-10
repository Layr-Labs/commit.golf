import CommitGolfCandidate.CapCheckCapAcceptance
import CommitGolfCandidate.CapCheckMarkedRoots
import CommitGolfCandidate.CapCheckLoadedWordSuffix
import CommitGolfCandidate.CapCheckCommitmentBytes
import CommitGolfCandidate.CapCheckFinalAdmission

/-! The actual lower-record/mark handoff instantiates cap acceptance with
original ABI words, original commitment and the unrounded trailing bytes.
Earlier duplicate rejection and the empty ABI branch are handled separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer capCheckTraversalInitial

theorem cap_check_loaded_cap_acceptance (oracle : Oracle) (input : CheckInput)
    (ordinal : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (selectors : CapCheckSelectors state)
    (admitted : input.proof.length≤capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length) :
    (checkEvaluation oracle (capCheckDfsFinish (capCheckCollectedMarks roots)
      510 (.visit 1) (capCheckTraversalInitial state))).1.exit=.success ↔
      capDecode oracle.compression (capKnownView roots 7 0)
        (capCheckSuffixWords input (576*input.positions.card))=
          some (input.commitment,[]) ∧
        (input.proof.length-576*input.positions.card)%32=0 := by
  have ordinalEq : ordinal=input.positions.card := by
    have partition := ready.partition
    omega
  have frame := cap_check_traversal_initial_high input ordinal state ready roots collected
  have suffix := cap_check_loaded_word_suffix input (capCheckTraversalInitial state)
    (576*input.positions.card) admitted enough
    (by rw [←ordinalEq]; exact cap_check_traversal_initial_cursor input ordinal state ready)
    (cap_check_traversal_initial_end input ordinal state ready) frame
  have reached := cap_check_traversal_initial_ready input ordinal state ready
    roots collected selectors admitted enough
  have claimed := cap_check_traversal_initial_commitment input ordinal state ready
  have high : 22528≤capProgram.layout.commitment := by decide
  have bound : capProgram.layout.commitment+32≤2^64 := by decide
  have acceptance := cap_check_cap_acceptance oracle
    (capProgram.layout.proof+input.proof.length) (capCheckCollectedMarks roots)
    (capKnownView roots 7 0) (capCheckTraversalInitial state)
    (capProgram.layout.proof+576*input.positions.card)
    (capCheckSuffixWords input (576*input.positions.card))
    ((input.proof.length-576*input.positions.card)%32) capProgram.layout.commitment
    reached suffix (cap_check_known_root_marks roots)
    (cap_check_traversal_known_leaves input ordinal state ready roots collected)
    claimed (by decide) high bound
  rw [cap_high_bytes_read _ (capProgram.initialState .check input) _ 32 high bound frame,
    cap_check_input_commitment input] at acceptance
  exact acceptance

end CommitGolfCandidate
