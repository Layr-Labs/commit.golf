import CommitGolfCandidate.CapCheckLoadedCapAcceptance
import CommitGolfCandidate.CapCheckContinueValue
import CommitGolfCandidate.CapCheckPostRecords

/-! The complete actual record continuation accepts exactly the forward
logical lower-record collection followed by the strict cap decoder. Each
record is hashed before its duplicate check. Failure stops the continuation;
the original ABI suffix retains its full and partial trailing bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] checkEvaluation capCheckRecordsContinue

def CapCheckLoadedAcceptance (oracle : Oracle) (input : CheckInput)
    (roots : CapRootMap) : Prop :=
  capDecode oracle.compression (capKnownView roots 8 0)
    (capCheckSuffixWords input (544*input.positions.card)) =
      some (input.commitment,[]) ∧
    (input.proof.length-544*input.positions.card)%32=0

private theorem some_roots_bind (roots : CapRootMap)
    (next : CapRootMap → Option CapRootMap) :
    (do let value ← some roots; next value) = next roots := rfl

theorem cap_check_records_continue_acceptance (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544*input.positions.card ≤ input.proof.length)
    (ordinal count : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal count state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (zeroSelectors : count=0 → CapCheckSelectors state)
    (fuel : Nat) (sufficient : 671*count+19945 ≤ fuel) (allowCoins : Bool) :
    (checkEvaluation oracle
      (capCheckRecordsContinue count state fuel allowCoins)).1.exit=.success ↔
      ∃ next, capLowerBatchRoots oracle.compression
        ((capCheckLoadedRecords input).drop ordinal) roots=some next ∧
        CapCheckLoadedAcceptance oracle input next := by
  have parsed := cap_check_loaded_records_parsed input admitted enough
  induction count generalizing ordinal state roots fuel with
  | zero =>
    have finished : ordinal=(capCheckLoadedRecords input).length := by
      have partition := ready.partition
      rw [cap_check_loaded_records_length]
      omega
    have execution := cap_check_post_records_execute input ordinal state ready roots
      collected (zeroSelectors rfl) admitted enough (fuel-2554) (by omega) allowCoins
    rw [show 2554+(fuel-2554)=fuel by omega] at execution
    rw [capCheckRecordsContinue,execution,cap_check_evaluation_bind_value,
      check_evaluation_pure]
    change (checkEvaluation oracle (capCheckDfsFinish (capCheckCollectedMarks roots)
      1022 (.visit 1) (capCheckTraversalInitial state))).1.exit=.success ↔ _
    rw [cap_check_loaded_cap_acceptance oracle input ordinal state ready roots collected
      (zeroSelectors rfl) admitted enough,finished,List.drop_length]
    simp only [capLowerBatchRoots,Option.some.injEq,CapCheckLoadedAcceptance]
    constructor
    · intro accepted
      exact ⟨roots,rfl,accepted⟩
    · rintro ⟨next,equal,accepted⟩
      subst next
      exact accepted
  | succ count ih =>
    have present : ordinal < input.positions.card := by have := ready.partition; omega
    have recordPresent : ordinal < (capCheckLoadedRecords input).length := by
      rw [cap_check_loaded_records_length]; exact present
    have digest := cap_check_record_logical oracle input (capCheckLoadedRecords input)
      (input.proof.drop (544*input.positions.card)) parsed.encoded admitted ordinal
      (count+1) state ready present recordPresent
      (parsed.index ordinal recordPresent present) (parsed.value ordinal recordPresent present)
    have loaded : state.getMem (state.getReg .x24)=
        BitVec.ofNat 64 (capCheckLoadedRecords input)[ordinal].index.val := by
      rw [ready.indices,parsed.index ordinal recordPresent present]
      exact cap_check_retained_index input state ordinal present ready.inputs
    have agreement := cap_check_record_insert_agreement oracle state
      (capCheckLoadedRecords input)[ordinal] roots collected loaded ready.scratch
      ready.leaves ready.marks ready.roots ready.one digest
    have dropHead := List.drop_eq_getElem_cons recordPresent
    cases inserted : capInsert roots
        (capGroup (capCheckLoadedRecords input)[ordinal].index).val
        ((capCheckLoadedRecords input)[ordinal].root oracle.compression) with
    | none =>
      have rejected : (checkEvaluation oracle (capCheckRecordRun state)).1.2=false := by
        apply Bool.eq_false_iff.mpr
        intro passed
        have some := agreement.mp passed
        rw [inserted] at some
        contradiction
      have groupRejected : (capCheckGroupResult
          (checkEvaluation oracle (capCheckLowerRecord state)).1).2=false := by
        simpa only [cap_check_record_evaluation,cap_check_record_result_passed] using rejected
      rw [cap_check_continue_exit_head,groupRejected,if_neg (by decide),
        dropHead,capLowerBatchRoots,inserted]
      simp only [Option.bind_none,reduceCtorEq, false_iff]
      rintro ⟨next,impossible,_⟩
      cases impossible
    | some next =>
      have passed : (checkEvaluation oracle (capCheckRecordRun state)).1.2=true :=
        agreement.mpr (by simp only [inserted,Option.isSome_some])
      have groupPassed : (capCheckGroupResult
          (checkEvaluation oracle (capCheckLowerRecord state)).1).2=true := by
        simpa only [cap_check_record_evaluation,cap_check_record_result_passed] using passed
      have nextCollected := cap_check_record_insert_result oracle state
        (capCheckLoadedRecords input)[ordinal] roots next collected loaded ready.scratch
        ready.leaves ready.marks ready.roots ready.one digest inserted
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        (checkEvaluation oracle (capCheckRecordRun state)).1
        (check_evaluation_support oracle (capCheckRecordRun state)) passed
      have selectors := cap_check_record_run_selectors state
        (checkEvaluation oracle (capCheckRecordRun state)).1
        (check_evaluation_support oracle (capCheckRecordRun state)) passed
      have lowerBound := cap_check_lower_record_steps_bound state
      have groupBound := cap_check_group_steps_bound
        (checkEvaluation oracle (capCheckLowerRecord state)).1
      have tail := ih (ordinal+1) (checkEvaluation oracle (capCheckRecordRun state)).1.1
        nextReady next nextCollected (fun _ => selectors)
        (fuel-capCheckLowerRecordSteps state-
          capCheckGroupSteps (checkEvaluation oracle (capCheckLowerRecord state)).1-3)
        (by omega)
      rw [cap_check_continue_exit_head,groupPassed,if_pos rfl,
        dropHead,capLowerBatchRoots,inserted]
      rw [some_roots_bind]
      simpa only [cap_check_record_evaluation] using tail

end CommitGolfCandidate
