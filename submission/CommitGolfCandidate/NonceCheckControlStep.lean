import CommitGolfCandidate.NonceCheckControlTable

namespace CommitGolfCandidate.NonceCheckControl
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def StateControl (state : MachineState) : Prop :=
  (state.pc=0 ∨ CorePC state.pc) ∧ Link state

private theorem set_pc (state : MachineState) (pc : Word) (link : Link state)
    (safe : pc=0 ∨ CorePC pc) : StateControl (state.setPC pc) := by
  exact ⟨safe,by simpa only [Link,MachineState.getReg_setPC] using link⟩

private theorem set_reg_pc (state : MachineState) (rd : Reg) (value pc : Word)
    (outside : rd ≠ .x1) (safe : CorePC pc) (link : Link state) :
    StateControl ((state.setReg rd value).setPC pc) := by
  refine ⟨Or.inr safe,?_⟩
  simpa only [Link,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ outside] using link

theorem checked_base_step (state next : MachineState) (instruction : Instr)
    (safe : checked state.pc (.base instruction)=true) (link : Link state)
    (stepped : ordinaryStep state (.base instruction)=some next) : StateControl next := by
  cases instruction <;> simp only [checked,Bool.false_eq_true,decide_eq_true_eq] at safe
  all_goals simp only [ordinaryStep,reduceCtorEq] at stepped
  all_goals try split at stepped
  all_goals simp only [Option.some.injEq,reduceCtorEq] at stepped
  all_goals subst next
  all_goals first
    | exact set_reg_pc state _ _ _ safe.1 safe.2 link
    | exact ⟨Or.inr safe,link⟩
    | skip
  all_goals try
    simp only [execInstrBr]
    split
    · exact set_pc state _ link (Or.inr safe.2)
    · exact set_pc state _ link (Or.inr safe.1)

  case JAL.isTrue rd offset valid =>
    rcases safe with ⟨destination,pcSafe,linkSafe⟩
    rcases destination with rfl | rfl
    · exact set_pc state _ link (Or.inr pcSafe)
    · refine ⟨Or.inr pcSafe,Or.inr ?_⟩
      change state.pc+4=4256
      exact linkSafe rfl
  case JALR.isTrue rd source offset valid =>
    rcases safe with ⟨rfl,rfl,rfl⟩
    change StateControl (state.setPC ((state.getReg .x1+signExtend12 0) &&& ~~~(1:Word)))
    rcases link with zero | returned
    · rw [zero]
      exact set_pc state 0 (Or.inl zero) (Or.inl rfl)
    · rw [returned]
      exact set_pc state 4256 (Or.inr returned) (Or.inr (by decide))

end CommitGolfCandidate.NonceCheckControl
