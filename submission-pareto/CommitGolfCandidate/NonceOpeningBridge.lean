import CommitGolfCandidate.NonceOpeningTrace
import CommitGolfCandidate.CapOpenProgramRun
import CommitGolfCandidate.NonceCompressedAdmission

/-! Transport of the cap-level opener's run to the delivered opening image. The cap-level run is
deterministic for every fuel and without coins; its HALT at word 110 becomes the jump into the
compaction, with the same charges. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceOldOpeningResult (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Execution :=
  if positions.card=0 then capOpenEmptyResult trapdoor positions
  else capOpenNonemptyResult trapdoor positions

/-- Instructions the cap-level opener executes. -/
def nonceOldOpeningSteps (positions : Positions) : Nat :=
  if positions.card=0 then 33 else capOpenInstructionCount positions

theorem nonce_old_opening_execute (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) (coins : Bool) :
    execute nonceOldOpeningImage (nonceOldOpeningSteps positions + fuel)
      (capProgram.initialState .opening (trapdoor,positions)) coins =
        pure (nonceOldOpeningResult trapdoor positions) := by
  by_cases empty : positions.card=0
  · have pc : (capProgram.initialState .opening (trapdoor, positions)).pc = 4096 := rfl
    have counter : (capProgram.initialState .opening (trapdoor, positions)).getReg .x16 = 0 := by
      change BitVec.ofNat 64 positions.card = 0
      rw [empty]
      rfl
    simp only [nonceOldOpeningSteps, nonceOldOpeningResult, if_pos empty]
    exact cap_open_empty_execute _ pc counter fuel coins
  · have execution := cap_open_loaded_execution trapdoor positions (by omega) fuel coins
    rw [cap_open_dfs_run_pure, pure_bind] at execution
    simp only [nonceOldOpeningSteps, nonceOldOpeningResult, if_neg empty]
    exact execution

theorem nonce_old_opening_run (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    capProgram.run .opening (trapdoor,positions)=pure (nonceOldOpeningResult trapdoor positions) := by
  by_cases empty : positions.card=0
  · rw [cap_open_empty_program_run trapdoor positions empty]
    simp only [nonceOldOpeningResult, if_pos empty]
  · rw [cap_open_nonempty_program_run trapdoor positions (by omega)]
    simp only [nonceOldOpeningResult, if_neg empty]

theorem nonce_old_opening_success (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : (nonceOldOpeningResult trapdoor positions).exit=.success := by
  unfold nonceOldOpeningResult
  split <;> rfl

theorem nonce_old_opening_halt_pc (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : (nonceOldOpeningResult trapdoor positions).state.pc = 4536 := by
  unfold nonceOldOpeningResult
  split <;> rfl

theorem nonce_old_opening_calls (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : (nonceOldOpeningResult trapdoor positions).oracleCalls = 0 := by
  unfold nonceOldOpeningResult
  split <;> rfl

theorem nonce_old_opening_steps_bound (positions : Positions) :
    nonceOldOpeningSteps positions ≤ 29 + 278 * positions.card + 2552 + 2 + 17 * 1022 + 4 := by
  unfold nonceOldOpeningSteps
  split
  · omega
  · have traversal := cap_dfs_instruction_total_bound false
      (capOpenRequestedMarks positions) 1022 (.visit 1)
    unfold capOpenInstructionCount
    omega

private theorem nonce_opening_run_execute (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    program.run .opening (trapdoor,positions)=
      execute (program.image .opening) (program.steps .opening)
        (program.initialState .opening (trapdoor,positions)) true := rfl

theorem nonce_compressed_opening_split (trapdoor : BitVec (8*nonceCompressedProgram.sizes.trapdoor))
    (positions : Positions) :
    ∃ extra, 2 * capProgram.steps .opening - nonceOldOpeningSteps positions ≤ extra ∧
      nonceCompressedProgram.run .opening (trapdoor,positions)=
        (do let final ← execute s6OpeningImage extra
              ((nonceOldOpeningResult trapdoor positions).state.setPC 4864) true
            return final.charge (nonceOldOpeningResult trapdoor positions).cycles 0) := by
  have run := nonce_old_opening_execute trapdoor positions 0 false
  rw [Nat.add_zero] at run
  obtain ⟨count, bounded, trace⟩ := nonce_pure_trace _ _ _ run (nonce_old_opening_success trapdoor positions)
  have fuel : nonceOldOpeningSteps positions ≤ capProgram.steps .opening := by
    unfold nonceOldOpeningSteps
    split
    · decide
    · exact cap_open_program_fuel positions
  refine ⟨nonceCompressedProgram.steps .opening - count, ?_, ?_⟩
  · change 2 * capProgram.steps .opening - nonceOldOpeningSteps positions ≤
      2 * capProgram.steps .opening - count
    omega
  · have replay := nonce_opening_trace_new trace (nonce_old_opening_halt_pc trapdoor positions)
      (nonceCompressedProgram.steps .opening - count) true
    have sum : count + (nonceCompressedProgram.steps .opening - count) = nonceCompressedProgram.steps .opening := by
      change count + (2 * capProgram.steps .opening - count) = 2 * capProgram.steps .opening
      omega
    rw [sum] at replay
    have initial := congrArg
      (fun state => execute s6OpeningImage (nonceCompressedProgram.steps .opening) state true)
      (nonce_compressed_initial_same .opening (trapdoor,positions))
    exact (nonce_opening_run_execute nonceCompressedProgram trapdoor positions).trans
      (initial.trans replay)

end CommitGolfCandidate
