import CommitGolfCandidate.FastOpeningImage
import CommitGolfCandidate.Properties

/-! The actual candidate retains commitment/checker images, ABI and fuel, and
replaces the opening image with its checked unrolled implementation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fastSubmission : Submission :=
  { submission with image := fun program => match program with
    | .opening => fastImage
    | program => submission.image program }

theorem fast_initial_opening (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) :
    fastSubmission.initialState .opening (trapdoor,positions)=
      submission.initialState .opening (trapdoor,positions) := rfl

theorem fast_run_commit (message : Message) :
    fastSubmission.run .commit message=submission.run .commit message := rfl

theorem fast_run_check (input : CheckInput) :
    fastSubmission.run .check input=submission.run .check input := rfl

/-- The larger opening remains far below the fixed image limit. All layout
requirements and instruction allowances are inherited without changing their values. -/
theorem fast_admission : fastSubmission.Admission := by
  intro program
  have old := submission_admission program
  cases program with
  | commit => exact old
  | check => exact old
  | opening =>
    refine ⟨⟨?_,old.1.2⟩,old.2⟩
    decide
end CommitGolfCandidate
