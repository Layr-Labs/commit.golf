import CommitGolfCandidate.CapCheckRecordAgreement
import CommitGolfCandidate.CapCheckRecordsRun
import CommitGolfCandidate.CapCheckEvaluationValue

/-! The actual forward record loop agrees with parsed lower records under the
same fixed oracle. Every duplicate is checked after its twenty-five queries.
The parser supplies the index/value identities; this bridge does not let proof
bytes choose ABI values, and does not assume collision freedom. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] checkEvaluation capCheckRecordsRun capCheckRecordRun capCheckLowerRecord

structure CapCheckParsedRecords (input : CheckInput) (records : List CapLowerRecord)
    (suffix : Proof) : Prop where
  encoded : input.proof=capDigestEncoding (capLowerTranscript records)++suffix
  admitted : input.proof.length≤capProgram.sizes.proof
  length : records.length=input.positions.card
  index : ∀ ordinal (inside : ordinal<records.length) (present : ordinal < input.positions.card),
    records[ordinal].index=(input.positions.sort (· ≤ ·))[ordinal]'(by
      simpa using present)
  value : ∀ ordinal (inside : ordinal<records.length) (present : ordinal < input.positions.card),
    records[ordinal].value=
      input.values ((input.positions.attach.sort (fun i j => i.val≤j.val))[ordinal]'(by
        simpa using present))

theorem cap_check_records_evaluation_head (oracle : Oracle) (count : Nat)
    (state : MachineState) :
    (checkEvaluation oracle (capCheckRecordsRun (count+1) state)).1=
      if (checkEvaluation oracle (capCheckRecordRun state)).1.2 then
        (checkEvaluation oracle (capCheckRecordsRun count
          (checkEvaluation oracle (capCheckRecordRun state)).1.1)).1
      else (checkEvaluation oracle (capCheckRecordRun state)).1 := by
  rw [capCheckRecordsRun,cap_check_evaluation_bind_value]
  cases passed : (checkEvaluation oracle (capCheckRecordRun state)).1.2
  · simp only [passed,Bool.false_eq_true,↓reduceIte,check_evaluation_pure]
  · simp only [passed,↓reduceIte]

theorem cap_check_records_logical (oracle : Oracle) (input : CheckInput)
    (records : List CapLowerRecord) (suffix : Proof)
    (parsed : CapCheckParsedRecords input records suffix)
    (ordinal count : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal count state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots) :
    ((capLowerBatchRoots oracle.compression (records.drop ordinal) roots).isSome=true ↔
      (checkEvaluation oracle (capCheckRecordsRun count state)).1.2=true) ∧
    (∀ next : CapRootMap,
      capLowerBatchRoots oracle.compression (records.drop ordinal) roots=some next →
      CapCheckCollected (checkEvaluation oracle (capCheckRecordsRun count state)).1.1 next) := by
  induction count generalizing ordinal state roots with
  | zero =>
    have finished : ordinal=records.length := by
      have partition := ready.partition
      have length := parsed.length
      omega
    rw [finished,List.drop_length]
    constructor
    · simp only [capLowerBatchRoots,Option.isSome_some,capCheckRecordsRun,
        check_evaluation_pure]
    · intro next accepted
      simp only [capLowerBatchRoots,Option.some.injEq] at accepted
      subst next
      simpa only [capCheckRecordsRun,check_evaluation_pure] using collected
  | succ count ih =>
    have present : ordinal < input.positions.card := by have := ready.partition; omega
    have recordPresent : ordinal<records.length := by rw [parsed.length]; exact present
    have digest := cap_check_record_logical oracle input records suffix
      parsed.encoded parsed.admitted ordinal (count+1) state ready present recordPresent
      (parsed.index ordinal recordPresent present) (parsed.value ordinal recordPresent present)
    have loaded : state.getMem (state.getReg .x24)=
        BitVec.ofNat 64 records[ordinal].index.val := by
      rw [ready.indices,parsed.index ordinal recordPresent present]
      exact cap_check_retained_index input state ordinal present ready.inputs
    have agreement := cap_check_record_insert_agreement oracle state records[ordinal] roots
      collected loaded ready.scratch ready.leaves ready.marks ready.roots ready.one digest
    have dropHead := List.drop_eq_getElem_cons recordPresent
    cases inserted : capInsert roots (capGroup records[ordinal].index).val
        (records[ordinal].root oracle.compression) with
    | none =>
      have rejected : (checkEvaluation oracle (capCheckRecordRun state)).1.2=false := by
        apply Bool.eq_false_iff.mpr
        intro passed
        have some := agreement.mp passed
        rw [inserted] at some
        contradiction
      rw [dropHead,capLowerBatchRoots,inserted]
      simp only [Option.bind_none,Option.isSome_none,Bool.false_eq_true,
        cap_check_records_evaluation_head,rejected,↓reduceIte]
      simp
    | some next =>
      have passed : (checkEvaluation oracle (capCheckRecordRun state)).1.2=true := by
        apply agreement.mpr
        simp only [inserted,Option.isSome_some]
      have nextCollected := cap_check_record_insert_result oracle state records[ordinal]
        roots next collected loaded ready.scratch ready.leaves ready.marks ready.roots
        ready.one digest inserted
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        (checkEvaluation oracle (capCheckRecordRun state)).1
        (check_evaluation_support oracle (capCheckRecordRun state)) passed
      have tail := ih (ordinal+1)
        (checkEvaluation oracle (capCheckRecordRun state)).1.1 nextReady next nextCollected
      rw [dropHead,capLowerBatchRoots,inserted]
      simp only [Option.bind_some,cap_check_records_evaluation_head,passed,↓reduceIte]
      exact tail

end CommitGolfCandidate
