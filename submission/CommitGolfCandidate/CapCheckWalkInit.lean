import CommitGolfCandidate.CapMarkImage
import CommitGolfCandidate.CapDfsStable

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckWalkNode (state : MachineState) : MachineState :=
  execInstrBr state (.ADDI .x20 .x0 1)

def capCheckWalkInitial (state : MachineState) : MachineState :=
  execInstrBr (capCheckWalkNode state) (.ADDI .x31 .x0 1)

private theorem two_charge (result : Execution) :
    (result.charge 1 0).charge 1 0 = result.charge 2 0 := by
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd]

theorem cap_check_walk_initial_execute (state : MachineState) (pc : state.pc = 4596)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .check) (2+fuel) state allowCoins =
      (do let result ← execute (capProgram.image .check) fuel
            (capCheckWalkInitial state) allowCoins
          return result.charge 2 0) := by
  have first : fetch (capProgram.image .check) state =
      some (.base (.ADDI .x20 .x0 1)) := by
    apply cap_image_fetch _ state 125 _ (by decide) pc
    rfl
  have second : fetch (capProgram.image .check) (capCheckWalkNode state) =
      some (.base (.ADDI .x31 .x0 1)) := by
    apply cap_image_fetch _ _ 126 _ (by decide)
    · simp only [capCheckWalkNode, execInstrBr, MachineState.setPC, pc]
      rfl
    · rfl
  have firstStep : ordinaryStep state (.base (.ADDI .x20 .x0 1)) =
      some (capCheckWalkNode state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, capCheckWalkNode]
  have secondStep : ordinaryStep (capCheckWalkNode state) (.base (.ADDI .x31 .x0 1)) =
      some (capCheckWalkInitial state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, capCheckWalkInitial]
  rw [show 2+fuel = (fuel+1)+1 by omega,
    execute_ordinary_step _ _ state _ (fuel+1) allowCoins first firstStep,
    execute_ordinary_step _ _ _ _ fuel allowCoins second secondStep]
  simp only [instructionCycles, bind_assoc, pure_bind, two_charge]

theorem cap_check_walk_initial_memory (state : MachineState) :
    (capCheckWalkInitial state).mem = state.mem := rfl

theorem cap_check_walk_initial_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x20 ∧ reg ≠ .x31) :
    (capCheckWalkInitial state).getReg reg = state.getReg reg := by
  simp only [capCheckWalkInitial, capCheckWalkNode, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1)]

theorem cap_check_walk_initial_control (state : MachineState) (pc : state.pc = 4596) :
    CapDfsStateControl true (capCheckWalkInitial state) (.visit 1) := by
  constructor
  · simp only [CapDfsStateControl, capCheckWalkInitial, capCheckWalkNode,
      execInstrBr, MachineState.setPC, pc]
    rfl
  · simp only [capCheckWalkInitial, capCheckWalkNode, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : .x31 ≠ .x20),
      MachineState.getReg_setReg_eq, show state.getReg .x0 = 0 from rfl, signExtend12]
    rfl

theorem cap_check_walk_initial_root (state : MachineState) :
    (capCheckWalkInitial state).getReg .x31 = 1 := by
  simp only [capCheckWalkInitial, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, show (capCheckWalkNode state).getReg .x0 = 0 from rfl,
    signExtend12]
  rfl

end CommitGolfCandidate
