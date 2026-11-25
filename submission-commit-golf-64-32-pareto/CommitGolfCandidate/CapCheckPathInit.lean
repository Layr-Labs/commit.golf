import CommitGolfCandidate.CapCheckPathPreparation

/-! The depth-24 checker loads sixteen lower siblings with the actual
three-instruction generic immediate, then executes the nonzero gate.
These four once-per-record instructions are charged separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckPathInitInstructions : List Instr :=
  [.ADDI .x29 .x0 0, .SLLI .x29 .x29 11, .ADDI .x29 .x29 16]

def capCheckPathInitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckPathInitInstructions.take count).foldl execInstrBr state

def capCheckPathInitState (state : MachineState) : MachineState :=
  (capCheckPathInitPrefix state 3).setPC 4272

theorem cap_check_path_init_pc (state : MachineState) (count : Nat) (bounded : count ≤ 3) :
    (capCheckPathInitPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capCheckPathInitPrefix, capCheckPathInitInstructions, List.take,
      List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_path_init_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) (reg : Reg) (outside : reg ≠ .x29) :
    (capCheckPathInitPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capCheckPathInitPrefix, capCheckPathInitInstructions, List.take,
      List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_check_path_init_counter (state : MachineState) :
    (capCheckPathInitPrefix state 3).getReg .x29 = 16 := by
  simp [capCheckPathInitPrefix, capCheckPathInitInstructions, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, signExtend12,
    MachineState.getReg]
  rfl

theorem cap_check_path_init_memory (state : MachineState) :
    (capCheckPathInitState state).mem = state.mem := rfl

attribute [local irreducible] capCheckPathInitPrefix

theorem cap_check_path_init_execute (state : MachineState) (pc : state.pc = 4256)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (4+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckPathInitState state) allowCoins
          return result.charge 4 0) := by
  have setup : execute ((capExperimental 24).image .check) (3+(1+fuel)) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) (1+fuel)
            (capCheckPathInitPrefix state 3) allowCoins
          return result.charge 3 0) := by
    have initial : capCheckPathInitPrefix state 0 = state := by
      unfold capCheckPathInitPrefix
      rfl
    conv_lhs => rw [← initial]
    apply execute_unit_steps (states := capCheckPathInitPrefix state)
    intro i bounded
    refine ⟨.base ((capCheckPathInitInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply cap_image_fetch _ _ (40+i) _ (by omega)
      · rw [cap_check_path_init_pc state i (by omega), pc]
        interval_cases i <;> rfl
      · interval_cases i <;> rfl
    · interval_cases i <;>
        simp only [capCheckPathInitPrefix, capCheckPathInitInstructions, List.take,
          List.foldl, ordinaryStep, memoryArgumentsValid, memAccess] <;> rfl
    · interval_cases i <;> rfl
  have gatePC : (capCheckPathInitPrefix state 3).pc = 4268 := by
    rw [cap_check_path_init_pc state 3 (by decide), pc]
    rfl
  have fetched : fetch ((capExperimental 24).image .check) (capCheckPathInitPrefix state 3) =
      some (.base (.BEQ .x29 .x0 152)) := by
    apply cap_image_fetch _ _ 43 _ (by decide) gatePC
    rfl
  have stepped : ordinaryStep (capCheckPathInitPrefix state 3) (.base (.BEQ .x29 .x0 152)) =
      some (capCheckPathInitState state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ↓reduceIte, execInstrBr,
      cap_check_path_init_counter, show (capCheckPathInitPrefix state 3).getReg .x0 = 0 from rfl,
      show ((16 : Word) == (0 : Word)) = false by decide,
      Bool.false_eq_true, ite_false, gatePC, capCheckPathInitState]
    rfl
  rw [show 4+fuel = 3+(1+fuel) by omega, setup, Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

end CommitGolfCandidate
