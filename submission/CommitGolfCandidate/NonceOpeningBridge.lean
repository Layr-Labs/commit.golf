import CommitGolfCandidate.NonceOpeningSupport
import CommitGolfCandidate.CapOpenProgramRun
import CommitGolfCandidate.NonceCompressedAdmission

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 20000
attribute [local irreducible] capOpenEmptyResult capOpenNonemptyResult

def nonceOldOpeningResult (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Execution :=
  if positions.card=0 then capOpenEmptyResult trapdoor positions
  else capOpenNonemptyResult trapdoor positions

theorem nonce_old_opening_run (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    capProgram.run .opening (trapdoor,positions)=pure (nonceOldOpeningResult trapdoor positions) := by
  by_cases empty : positions.card=0
  · rw [cap_open_empty_program_run trapdoor positions empty]
    simp only [nonceOldOpeningResult, if_pos empty]
  · rw [cap_open_nonempty_program_run trapdoor positions (by omega)]
    simp only [nonceOldOpeningResult, if_neg empty]

private theorem nonce_opening_run_execute (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    program.run .opening (trapdoor,positions)=
      execute (program.image .opening) (program.steps .opening)
        (program.initialState .opening (trapdoor,positions)) true := rfl

theorem nonce_old_opening_support (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceOldOpeningResult trapdoor positions ∈ support
      (execute nonceOldOpeningImage (capProgram.steps .opening)
        (capProgram.initialState .opening (trapdoor,positions)) true) := by
  have pureMember : nonceOldOpeningResult trapdoor positions ∈
      support (pure (nonceOldOpeningResult trapdoor positions) : OracleComp World Execution) := by
    simp only [support_pure, Set.mem_singleton_iff]
  have runMember := (congrArg (fun computation =>
    nonceOldOpeningResult trapdoor positions ∈ support computation)
    (nonce_old_opening_run trapdoor positions)).mpr pureMember
  exact (congrArg (fun computation =>
    nonceOldOpeningResult trapdoor positions ∈ support computation)
    (nonce_opening_run_execute capProgram trapdoor positions)).mp runMember

theorem nonce_old_opening_success (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : (nonceOldOpeningResult trapdoor positions).exit=.success := by
  unfold nonceOldOpeningResult
  split <;> simp only [capOpenEmptyResult, capOpenNonemptyResult]

theorem nonce_old_opening_input_trace (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    ∃ count, count ≤ capProgram.steps .opening ∧
      NonceOpeningTrace count (capProgram.initialState .opening (trapdoor,positions))
        (nonceOldOpeningResult trapdoor positions) :=
  nonce_opening_success_trace _ _ _ _ (nonce_old_opening_support trapdoor positions)
    (nonce_old_opening_success trapdoor positions)

theorem nonce_compressed_opening_split (trapdoor : BitVec (8*nonceCompressedProgram.sizes.trapdoor))
    (positions : Positions) :
    ∃ extra, capProgram.steps .opening ≤ extra ∧
      nonceCompressedProgram.run .opening (trapdoor,positions)=
        (do let final ← execute nonceCompactImage extra
              ((nonceOldOpeningResult trapdoor positions).state.setPC 4540) true
            return final.charge (nonceOldOpeningResult trapdoor positions).cycles 0) := by
  obtain ⟨count,bounded,trace⟩:=nonce_old_opening_input_trace trapdoor positions
  let extra := nonceCompressedProgram.steps .opening-count
  have larger : capProgram.steps .opening ≤ extra := by
    change capProgram.steps .opening ≤ 2*capProgram.steps .opening-count
    omega
  refine ⟨extra,larger,?_⟩
  have replay:=nonce_opening_trace_new trace extra true
  have sum : count+extra=nonceCompressedProgram.steps .opening := by
    change count+(2*capProgram.steps .opening-count)=2*capProgram.steps .opening
    omega
  rw [sum] at replay
  have initial := congrArg
    (fun state => execute nonceCompactImage (nonceCompressedProgram.steps .opening) state true)
    (nonce_compressed_initial_same .opening (trapdoor,positions))
  exact (nonce_opening_run_execute nonceCompressedProgram trapdoor positions).trans
    (initial.trans replay)

end CommitGolfCandidate
