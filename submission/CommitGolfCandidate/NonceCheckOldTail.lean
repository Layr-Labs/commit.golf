import CommitGolfCandidate.NonceCheckCoreEquiv
import CommitGolfCandidate.CapCheckTermination

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def nonceOldCheckTailState (input : CheckInput) : MachineState :=
  execInstrBr (capProgram.initialState .check input) (.ADDI .x26 .x11 0)

private theorem run_check (program : Submission) (input : CheckInput)
    (admitted : input.proof.length ≤ program.sizes.proof) :
    program.run .check input=execute (program.image .check) (program.steps .check)
      (program.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

theorem nonce_old_check_tail_control (input : CheckInput) :
    NonceCheckControl.StateControl (nonceOldCheckTailState input) := by
  refine ⟨Or.inr ?_,Or.inl ?_⟩
  · change NonceCheckControl.CorePC (4100:Word)
    decide
  · rfl

private theorem first_move (input : CheckInput) (fuel : Nat) :
    execute NonceCheckControl.oldImage (1+fuel) (capProgram.initialState .check input) false=
      (do let result ← execute NonceCheckControl.oldImage fuel (nonceOldCheckTailState input) false
          return result.charge 1 0) := by
  have fetched : fetch NonceCheckControl.oldImage (capProgram.initialState .check input)=
      some (.base (.ADDI .x26 .x11 0)) := by
    apply cap_image_fetch _ _ 0 _ (by decide) rfl
    rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step NonceCheckControl.oldImage _ _ _ fuel false fetched (by rfl)]
  rfl

private theorem exit_charge (computation : OracleComp World Execution) (cycles calls : Nat) :
    Execution.exit <$> (do let result ← computation; return result.charge cycles calls)=
      Execution.exit <$> computation := by
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Execution.charge]

theorem nonce_check_tail_exit (input : CheckInput) (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (right : MachineState) (related : NonceStateEquiv (nonceOldCheckTailState input) right) (extra : Nat) :
    Execution.exit <$> execute nonceExpandedImage (capProgram.steps .check-1+extra) right false=
      Execution.exit <$> capProgram.run .check input := by
  have runEq : capProgram.run .check input=execute NonceCheckControl.oldImage (capProgram.steps .check)
      (capProgram.initialState .check input) false := run_check capProgram input admitted
  have stable:=execute_extra_fuel NonceCheckControl.oldImage (capProgram.steps .check) extra
    (capProgram.initialState .check input) false (by
      intro result reached
      exact cap_check_program_terminated input result
        ((congrArg (fun computation => result ∈ support computation) runEq).mpr reached))
  have positive : 0 < capProgram.steps .check := by decide
  rw [runEq,←stable,show capProgram.steps .check+extra=1+(capProgram.steps .check-1+extra) by omega,
    first_move,exit_charge]
  exact nonce_check_core_exit_eq _ _ _ related (nonce_old_check_tail_control input)

end CommitGolfCandidate
