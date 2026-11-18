import CommitGolfCandidate.CapMarkImage
import CommitGolfCandidate.CapExperimentalABI

/-! Actual cap-opening setup, including the empty-request branch. The ABI
pointers are retained, the nonce base is computed from the trapdoor, and setup
does not alter memory or require hash-syscall argument selectors. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def capOpenSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0, .ADDI .x24 .x13 0, .ADDI .x25 .x15 0, .ADDI .x27 .x16 0,
   .ADDI .x19 .x0 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 1,
   .SLLI .x19 .x19 11, .ADDI .x19 .x19 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 0,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 432,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 256,
   .ADD .x18 .x9 .x6,
   .ADDI .x22 .x0 0, .SLLI .x22 .x22 11, .ADDI .x22 .x22 14,
   .SLLI .x22 .x22 11, .ADDI .x22 .x22 0,
   .ADDI .x29 .x0 256, .ADDI .x17 .x0 16, .ADDI .x0 .x0 0,
   .ADDI .x31 .x0 1]

def capOpenSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenSetupInstructions.take count).foldl execInstrBr state

def capOpenInitializedState (state : MachineState) : MachineState :=
  (capOpenSetupPrefix state 28).setPC
    (if state.getReg .x16 = 0 then 4524 else 4212)

theorem cap_open_setup_prefix_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 28) :
    (capOpenSetupPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capOpenSetupPrefix, capOpenSetupInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_open_setup_prefix_execute (state : MachineState)
    (pc : state.pc = 4096) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening) (28+fuel) state allowCoins =
      (do let result ← execute (capProgram.image .opening) fuel
            (capOpenSetupPrefix state 28) allowCoins
          return result.charge 28 0) := by
  apply execute_unit_steps (states := capOpenSetupPrefix state)
  intro i bounded
  refine ⟨.base ((capOpenSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ i _ (by omega)
    · rw [cap_open_setup_prefix_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_open_setup_registers (state : MachineState) :
    (capOpenInitializedState state).getReg .x9 = state.getReg .x12 ∧
    (capOpenInitializedState state).getReg .x24 = state.getReg .x13 ∧
    (capOpenInitializedState state).getReg .x25 = state.getReg .x15 ∧
    (capOpenInitializedState state).getReg .x27 = state.getReg .x16 ∧
    (capOpenInitializedState state).getReg .x19 = 4194304 ∧
    (capOpenInitializedState state).getReg .x18 = state.getReg .x12 + 1811939584 ∧
    (capOpenInitializedState state).getReg .x22 = 28672 ∧
    (capOpenInitializedState state).getReg .x29 = 256 ∧
    (capOpenInitializedState state).getReg .x31 = 1 ∧
    (capOpenInitializedState state).getReg .x15 = state.getReg .x15 ∧
    (capOpenInitializedState state).getReg .x16 = state.getReg .x16 := by
  simp [capOpenInitializedState, capOpenSetupPrefix, capOpenSetupInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem cap_open_setup_memory (state : MachineState) :
    (capOpenInitializedState state).mem = state.mem := by
  rfl

theorem cap_open_setup_execute (state : MachineState)
    (pc : state.pc = 4096) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening) (29+fuel) state allowCoins =
      (do let result ← execute (capProgram.image .opening) fuel
            (capOpenInitializedState state) allowCoins
          return result.charge 29 0) := by
  let ready := capOpenSetupPrefix state 28
  have readyPC : ready.pc = 4208 := by
    rw [cap_open_setup_prefix_pc state 28 (by decide), pc]
    rfl
  have count : ready.getReg .x27 = state.getReg .x16 := by
    simpa only [capOpenInitializedState, MachineState.getReg_setPC] using
      (cap_open_setup_registers state).2.2.2.1
  have fetched : fetch (capProgram.image .opening) ready =
      some (.base (.BEQ .x27 .x0 316)) := by
    apply cap_image_fetch _ _ 28 _ (by decide) readyPC
    rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x0 316)) =
      some (capOpenInitializedState state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ↓reduceIte,
      execInstrBr, count, show ready.getReg .x0 = 0 from rfl, readyPC,
      capOpenInitializedState, ready, signExtend13]
    split <;> simp_all only [beq_iff_eq, ↓reduceIte] <;> rfl
  rw [show 29+fuel = 28+(1+fuel) by omega, cap_open_setup_prefix_execute state pc,
    Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp only [instructionCycles, bind_assoc, pure_bind, Execution.charge, Nat.zero_add,
    ← Nat.add_assoc, Nat.reduceAdd]

/-- The nonce stride is an actual initialized register, retained through records. -/
theorem cap_open_setup_nonce_stride (state : MachineState) :
    (capOpenInitializedState state).getReg .x17 = 16 := by
  simp [capOpenInitializedState, capOpenSetupPrefix, capOpenSetupInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

end CommitGolfCandidate
