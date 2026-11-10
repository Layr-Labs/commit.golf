import CommitGolfCandidate.Compact.FixedImage
import CommitGolfCandidate.Properties

/-! The actual candidate retains commitment/checker images, ABI and fuel, and
replaces the opening image with its checked unrolled implementation. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixedSubmission : Submission :=
  { submission with image := fun program => match program with
    | .opening => fixedImage
    | program => submission.image program }

theorem fixed_initial_opening (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) :
    fixedSubmission.initialState .opening (trapdoor,positions)=
      submission.initialState .opening (trapdoor,positions) := rfl

theorem fixed_run_commit (message : Message) :
    fixedSubmission.run .commit message=submission.run .commit message := rfl

theorem fixed_run_check (input : CheckInput) :
    fixedSubmission.run .check input=submission.run .check input := rfl

/-- The larger opening remains far below the fixed image limit. All layout
requirements and instruction allowances are inherited without changing their values. -/
theorem fixed_admission : fixedSubmission.Admission := by
  intro program
  have old := submission_admission program
  cases program with
  | commit => exact old
  | check => exact old
  | opening =>
    refine ⟨⟨?_,old.1.2⟩,old.2⟩
    decide
end CommitGolfCandidate.Compact
