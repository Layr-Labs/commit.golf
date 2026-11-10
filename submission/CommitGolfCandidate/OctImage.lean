import CommitGolfCandidate.OctTree
import CommitGolfCandidate.QuadImage

/-! Every new branch, parent triple and exit is fetched from the delivered image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem oct_image_first_branch : OctBranchFetched (submission.image .commit) true := by
  intro state pc
  apply commit_fetch state 138 _ (by decide) pc
  rfl

private theorem oct_image_triple (block : Nat) (bounded : block<8) :
    ParentTripleFetched (submission.image .commit) (4656+BitVec.ofNat 64 (12*block)) := by
  intro state
  refine ⟨?_,?_,?_⟩
  · intro pc
    apply commit_fetch state (140+3*block) _ (by omega)
    · interval_cases block <;> simpa using pc
    · interval_cases block <;> rfl
  · intro pc
    apply commit_fetch state (141+3*block) _ (by omega)
    · interval_cases block <;> simpa using pc
    · interval_cases block <;> rfl
  · intro pc
    apply commit_fetch state (142+3*block) _ (by omega)
    · interval_cases block <;> simpa using pc
    · interval_cases block <;> rfl

theorem oct_image_sequence : ParentSequenceFetched (submission.image .commit) 4656 8 := by
  exact ⟨oct_image_triple 0 (by decide),oct_image_triple 1 (by decide),
    oct_image_triple 2 (by decide),oct_image_triple 3 (by decide),
    oct_image_triple 4 (by decide),oct_image_triple 5 (by decide),
    oct_image_triple 6 (by decide),oct_image_triple 7 (by decide),trivial⟩

theorem oct_image_branch : OctBranchFetched (submission.image .commit) false := by
  intro state pc
  apply commit_fetch state 164 _ (by decide) pc
  rfl

theorem oct_image_exit : OctExitFetched (submission.image .commit) := by
  intro state
  constructor
  · intro pc
    apply commit_fetch state 139 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 165 _ (by decide) pc
    rfl

theorem oct_image_parents : OctParentFetched (submission.image .commit) :=
  ⟨fused_image_peeled,fused_image_peel_branch,quad_image_pair,quad_image_entry_branch,
    quad_image_sequence,oct_image_first_branch,oct_image_sequence,oct_image_branch,oct_image_exit⟩

end CommitGolfCandidate
