import CommitGolfCandidate.CapCheckProgramAcceptance
import CommitGolfCandidate.CapCheckParsedUnique
import CommitGolfCandidate.CapCheckEncodedSuffix

/-! Exact encoded lower records and a valid cap suffix imply acceptance by the
actual checker image. Runtime scheduling, duplicate rejection and byte-tail
exhaustion are supplied by the compiled whole-program acceptance theorem. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option autoImplicit false

theorem cap_check_encoded_accepts (oracle : Oracle) (input : CheckInput)
    (records : List CapLowerRecord) (suffix : List Digest)
    (parsed : CapCheckParsedRecords input records (capDigestEncoding suffix))
    (nonempty : 0 < input.positions.card) (roots : CapRootMap)
    (lower : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation records (fun _ => none)=some roots)
    (cap : capDecode (s6Compress oracle.compression) (capKnownView roots 8 0) suffix=
      some (input.commitment,[])) :
    (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).1=true := by
  have combined : input.proof=
      capDigestEncoding (capLowerTranscript records++suffix) := by
    rw [parsed.encoded]
    simp only [capDigestEncoding,List.flatMap_append]
  have prefixLength : 32*(capLowerTranscript records).length=
      576*input.positions.card := by
    rw [cap_lower_transcript_length,parsed.length]
    omega
  have enough : 576*input.positions.card ≤ input.proof.length := by
    rw [combined,cap_digest_encoding_length,List.length_append]
    rw [←prefixLength]
    omega
  have loaded := cap_check_parsed_records_unique input records
    (capDigestEncoding suffix) parsed
  obtain ⟨suffixWords,tail⟩ := cap_check_encoded_suffix input
    (capLowerTranscript records) suffix combined parsed.admitted
  rw [prefixLength] at suffixWords tail
  apply (cap_check_scheme_acceptance oracle input).mpr
  refine ⟨parsed.admitted,?_⟩
  simp only [show input.positions.card≠0 by omega,ite_false]
  refine ⟨enough,roots,?_,?_⟩
  · rw [loaded]
    exact lower
  · exact ⟨by rw [suffixWords]; exact cap,tail⟩

end CommitGolfCandidate
