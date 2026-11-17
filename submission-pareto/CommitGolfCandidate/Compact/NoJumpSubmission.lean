import CommitGolfCandidate.Compact.NoJumpImage
import CommitGolfCandidate.Properties

/-! The actual candidate retains commitment/checker images, ABI and fuel, and
replaces the opening image with its checked unrolled implementation. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def noJumpSubmission : Submission :=
  { submission with image := fun program => match program with
    | .opening => noJumpImage
    | program => submission.image program }

theorem noJump_initial_opening (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) :
    noJumpSubmission.initialState .opening (trapdoor,positions)=
      submission.initialState .opening (trapdoor,positions) := rfl

theorem noJump_run_commit (message : Message) :
    noJumpSubmission.run .commit message=submission.run .commit message := rfl

theorem noJump_run_check (input : CheckInput) :
    noJumpSubmission.run .check input=submission.run .check input := rfl

/-- The larger opening remains far below the fixed image limit. All layout
requirements and instruction allowances are inherited without changing their values. -/
theorem noJump_admission : noJumpSubmission.Admission := by
  intro program
  have old := submission_admission program
  cases program with
  | commit => exact old
  | check => exact old
  | opening =>
    refine ⟨⟨?_,old.1.2⟩,old.2⟩
    decide
end CommitGolfCandidate.Compact
