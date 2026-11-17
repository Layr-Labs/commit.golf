import CommitGolfCandidate.CapCheckProgramAcceptance
import CommitGolfCandidate.CapCheckLoadedMember
import CommitGolfCandidate.S3CapBinding

/-! Actual accepted nonempty checker inputs expose an accepted lower batch and
cap for the same ABI values, adversarial lower bytes and canonical cap words as
the image. The paid replay of such a batch is `cap_accepted_replay`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option autoImplicit false

theorem cap_check_accepted_batch (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).1=true)
    (nonempty : 0 < input.positions.card) :
    ∃ roots, capLowerBatchRoots oracle.compression oracle.permutation
      (capCheckLoadedRecords input) (fun _ => none)=some roots ∧
      capDecode oracle.compression (capKnownView roots 8 0)
        (capCheckSuffixWords input (544*input.positions.card))=
          some (input.commitment,[]) := by
  have logical := (cap_check_scheme_acceptance oracle input).mp accepted
  simp only [CapCheckProgramAccepts,show input.positions.card≠0 by omega,ite_false,
    CapCheckLoadedAcceptance] at logical
  obtain ⟨_,_,roots,lower,cap,_⟩ := logical
  exact ⟨roots,lower,cap⟩

end CommitGolfCandidate
