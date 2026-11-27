import CommitGolfCandidate.Stage3cCheckSystem
import CommitGolfCandidate.Stage3cReplaySound
import CommitGolfCandidate.Stage3cHonestNormal
import CommitGolfCandidate.Stage3cResources
import CommitGolfCandidate.Stage3cBatchCap
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Open (W)
def checker_of_batch (bat : BatchChecker) : CheckerLaw where
  terminates o x:=(checker_result bat o x).1
  replay:=Pw.Replay.replay_of_wire (fun o x h=>by
    rw [scheme_check_evaluation] at h
    exact (checker_result bat o x).2.2.mp (beq_iff_eq.mp h))
  honest o m ps salt:=by
    let x:=canonicalInput o m ps salt
    have good:=Pw.canonical_valid o m ps salt
    have a:=checker_result bat o x
    change (checked o x).1=true ∧ (checked o x).2≤CHECK_BUDGET ps.card
    rw [checked,scheme_check_evaluation];exact ⟨beq_iff_eq.mpr (a.2.2.mpr good),a.2.1⟩

theorem certified : Certificate Artifact.submission 67840 911200264 186934 :=
  from_checker (checker_of_batch (batch_of_cap cap_judgment))
end CommitGolfCandidate.Chained.BinaryMachine.Check
