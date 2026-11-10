import CommitGolfCandidate.CapCheckProgramAcceptance
import CommitGolfCandidate.CapCheckLoadedMember
import CommitGolfCandidate.CapProbe

/-! Actual accepted nonempty checker inputs admit a complete paid replay.
The replay uses the same ABI values, adversarial lower bytes and canonical cap
words as the image. Its trace is recorded only after each public query. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option autoImplicit false

theorem cap_check_accepted_batch (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).1=true)
    (nonempty : 0 < input.positions.card) :
    ∃ roots, capLowerBatchRoots oracle.compression (capCheckLoadedRecords input)
      (fun _ => none)=some roots ∧
      capDecode oracle.compression (capKnownView roots 7 0)
        (capCheckSuffixWords input (576*input.positions.card))=
          some (input.commitment,[]) := by
  have logical := (cap_check_scheme_acceptance oracle input).mp accepted
  simp only [CapCheckProgramAccepts,show input.positions.card≠0 by omega,ite_false,
    CapCheckLoadedAcceptance] at logical
  obtain ⟨_,_,roots,lower,cap,_⟩ := logical
  exact ⟨roots,lower,cap⟩

theorem cap_check_witness_trace_length (compress : Compression) {height : Nat}
    {view : CapView height} {proof rest : List Digest} {root : Digest}
    {inputs : List (BitVec 512)}
    (witness : CapDecodeWitness compress view proof root rest inputs) :
    inputs.length=capCalls view := by
  induction witness with
  | unknown view root rest unoccupied =>
    cases view <;> simp only [List.length_nil,capCalls,unoccupied,
      Bool.false_eq_true,↓reduceIte]
  | known value proof => rfl
  | node left right proof rest rest' lroot rroot leftInputs rightInputs occupied
      leftDecoded rightDecoded ihLeft ihRight =>
    simp only [List.length_append,List.length_cons,List.length_nil,
      capCalls,occupied,↓reduceIte,ihLeft,ihRight]

theorem cap_check_accepted_replay (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).1=true)
    (nonempty : 0 < input.positions.card) :
    ∃ inputs calls,
      oracle.run (capReplayBatch (capCheckLoadedRecords input)
        (capCheckSuffixWords input (576*input.positions.card)) input.commitment)=
          pure (some inputs,calls) ∧
      inputs.length≤25*input.positions.card+127 := by
  obtain ⟨roots,lower,cap⟩ := cap_check_accepted_batch oracle input accepted nonempty
  obtain ⟨capInputs,witness⟩ := cap_decode_witness oracle.compression
    (capKnownView roots 7 0) (capCheckSuffixWords input (576*input.positions.card))
    [] input.commitment cap
  have capRun := cap_replay_witness_run oracle witness
  refine ⟨capLowerBatchInputs oracle.compression (capCheckLoadedRecords input)++capInputs,
    25*(capCheckLoadedRecords input).length+capInputs.length,?_,?_⟩
  · simp only [capReplayBatch]
    erw [oracle_run_bind,cap_replay_lower_batch_run oracle
      (capCheckLoadedRecords input) _ roots lower]
    simp only [pure_bind]
    erw [oracle_run_bind,capRun]
    simp [oracle_run_pure]
    rfl
  · rw [List.length_append,cap_lower_batch_inputs_length,
      cap_check_loaded_records_length,cap_check_witness_trace_length _ witness]
    have bound := cap_calls_full_bound (capKnownView roots 7 0)
    norm_num at bound
    omega

end CommitGolfCandidate
