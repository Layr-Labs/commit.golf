import CommitGolfCandidate.CapCheckGroupStart

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckGroupBranchState (state : MachineState) : MachineState :=
  state.setPC (if state.getReg .x6 = 0 then 4500 else 4448)

theorem cap_check_group_branch_execute (state : MachineState)
    (pc : state.pc = 4444) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (1+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckGroupBranchState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch ((capExperimental 24).image .check) state =
      some (.base (.BEQ .x6 .x0 56)) := by
    apply cap_image_fetch _ state 87 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.BEQ .x6 .x0 56)) =
      some (capCheckGroupBranchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      capCheckGroupBranchState, MachineState.getReg, signExtend13, pc]
    split <;> simp_all
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem cap_check_group_branch_memory (state : MachineState) :
    (capCheckGroupBranchState state).mem = state.mem := rfl

theorem cap_check_group_branch_register (state : MachineState) (reg : Reg) :
    (capCheckGroupBranchState state).getReg reg = state.getReg reg :=
  MachineState.getReg_setPC

end CommitGolfCandidate
