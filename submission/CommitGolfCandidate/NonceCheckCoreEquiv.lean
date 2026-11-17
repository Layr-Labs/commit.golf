import CommitGolfCandidate.NonceCheckControlRun
import CommitGolfCandidate.NonceStateOrdinary
import CommitGolfCandidate.NonceStateSyscalls

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private theorem fetch_pc (image : Image) (left right : MachineState) (pc : left.pc=right.pc) :
    fetch image left=fetch image right := by
  simp only [fetch,pc]

private theorem exit_charge (computation : OracleComp World Execution) (cycles calls : Nat) :
    Execution.exit <$> (do let result ← computation; return result.charge cycles calls)=
      Execution.exit <$> computation := by
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Execution.charge]

theorem nonce_check_core_exit_eq (fuel : Nat) (left right : MachineState)
    (related : NonceStateEquiv left right) (control : NonceCheckControl.StateControl left) :
    Execution.exit <$> execute nonceExpandedImage fuel right false=
      Execution.exit <$> execute NonceCheckControl.oldImage fuel left false := by
  induction fuel generalizing left right with
  | zero => simp only [execute,map_pure]
  | succ fuel ih =>
    have agreement : fetch nonceExpandedImage right=fetch NonceCheckControl.oldImage left :=
      (fetch_pc nonceExpandedImage right left related.pc.symm).trans
        (NonceCheckControl.images_agree left control)
    cases fetched : fetch NonceCheckControl.oldImage left with
    | none =>
      have absent:=agreement.trans fetched
      simp only [execute,fetched,absent,map_pure]
    | some instruction =>
      have newFetched:=agreement.trans fetched
      by_cases syscall : instruction=.base .ECALL
      · subst instruction
        simp only [execute,fetched,newFetched,related.registers .x5,related.registers .x10,
          NonceStateEquiv.oracle_input left right related]
        by_cases oracle : right.getReg .x5=0
        · simp only [if_pos oracle]
          cases queryEq : oracleInput right with
          | none => simp only [queryEq,map_pure]
          | some query =>
            simp only [queryEq,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Execution.charge]
            apply bind_congr
            intro answer
            simp only [related.registers .x12]
            have nextEq:=NonceStateEquiv.oracle_answer left right related (right.getReg .x12) query answer
            have nextControl:=NonceCheckControl.oracle_control left control fetched
              (right.getReg .x12) query answer
            simpa only [map_eq_bind_pure_comp,Function.comp_def] using ih _ _ nextEq nextControl
        · simp only [if_neg oracle]
          by_cases halt : right.getReg .x5=1
          · simp only [if_pos halt,map_pure]
          · simp only [if_neg halt,Bool.false_and,Bool.false_eq_true,ite_false,map_pure]
      · have steps:=NonceStateEquiv.ordinary left right related instruction
          (NonceCheckControl.fetched_checked left instruction fetched)
        cases oldStep : ordinaryStep left instruction with
        | none =>
          cases newStep : ordinaryStep right instruction with
          | none =>
            rw [nonce_execute_fault nonceExpandedImage fuel right false instruction syscall newFetched newStep,
              nonce_execute_fault NonceCheckControl.oldImage fuel left false instruction syscall fetched oldStep]
            simp only [map_pure]
          | some next => rw [oldStep,newStep] at steps; cases steps
        | some oldNext =>
          cases newStep : ordinaryStep right instruction with
          | none => rw [oldStep,newStep] at steps; cases steps
          | some newNext =>
            rw [oldStep,newStep] at steps
            cases steps with
            | next nextEq =>
              rw [execute_ordinary_step nonceExpandedImage instruction right newNext fuel false newFetched newStep,
                execute_ordinary_step NonceCheckControl.oldImage instruction left oldNext fuel false fetched oldStep,
                exit_charge,exit_charge]
              exact ih oldNext newNext nextEq
                (NonceCheckControl.fetched_step_control left oldNext instruction control fetched oldStep)

end CommitGolfCandidate
