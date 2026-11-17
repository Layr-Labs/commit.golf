import CommitGolfCandidate.CapCompressionStep

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCheckCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

def capCheckCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckCompressionInstructions.take count).foldl execInstrBr state

def CapCheckCompressionFetched (image : Image) (entry : Word) : Prop :=
  (∀ state : MachineState, ∀ i < 5, state.pc = entry →
    fetch image (capCheckCompressionPrefix state i) =
      some (.base ((capCheckCompressionInstructions[i]?).getD .EBREAK))) ∧
  (∀ state : MachineState, state.pc = entry →
    fetch image (capCheckCompressionPrefix state 5) = some (.base .ECALL))

def capCheckCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  capCompressionAnswer (capCheckCompressionPrefix state 5) answer

def capCheckScratchQuery (input : BitVec 512) : OracleComp World (BitVec 256) :=
  World.query (.inr (.inl input))

theorem cap_check_compression_prefix_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 5) :
    (capCheckCompressionPrefix state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capCheckCompressionPrefix, capCheckCompressionInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_compression_setup (image : Image) (entry : Word)
    (fetched : CapCheckCompressionFetched image entry)
    (state : MachineState) (pc : state.pc = entry)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (5 + fuel) state allowCoins =
      (do let result ← execute image fuel (capCheckCompressionPrefix state 5) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := capCheckCompressionPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckCompressionInstructions[i]?).getD .EBREAK),
    fetched.1 state i bounded pc, ?_, ?_⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_compression_ready (state : MachineState)
    (scratch : state.getReg .x21 = 256) :
    (capCheckCompressionPrefix state 5).getReg .x5 = 0 ∧
    (capCheckCompressionPrefix state 5).getReg .x10 = 256 ∧
    (capCheckCompressionPrefix state 5).getReg .x11 = 64 ∧
    (capCheckCompressionPrefix state 5).getReg .x12 = 256 ∧
    (capCheckCompressionPrefix state 5).getReg .x13 = 0 := by
  simp [capCheckCompressionPrefix, capCheckCompressionInstructions, execInstrBr,
    signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, scratch]
  rfl

theorem cap_check_compression_execute (image : Image) (entry : Word)
    (fetched : CapCheckCompressionFetched image entry)
    (state : MachineState) (pc : state.pc = entry)
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute image (6 + fuel) state allowCoins =
      (do let answer ← capCheckScratchQuery (readBuffer state 256 64)
          let result ← execute image fuel (capCheckCompressionState state answer) allowCoins
          return result.charge 13 1) := by
  let ready := capCheckCompressionPrefix state 5
  have registers := cap_check_compression_ready state scratch
  have querySame : readBuffer ready 256 64 = readBuffer state 256 64 :=
    read_buffer_memory_congr ready state rfl 256 64
  have checked := cap_compression_execute image ready (fetched.2 state pc)
    ⟨registers.1, registers.2.2.1, registers.2.2.2.2⟩
    (by rw [registers.2.1]; decide)
    (by rw [registers.2.2.2.1]; decide)
    (by rw [registers.2.1]; decide)
    (by rw [registers.2.2.2.1]; decide) fuel allowCoins
  unfold capCompressionInput at checked
  rw [registers.2.1] at checked
  change execute image (1 + fuel) ready allowCoins =
    (do let answer ← capCheckScratchQuery (readBuffer ready 256 64)
        let result ← execute image fuel (capCompressionAnswer ready answer) allowCoins
        return result.charge 8 1) at checked
  rw [querySame] at checked
  rw [show 6 + fuel = 5 + (1 + fuel) by omega,
    cap_check_compression_setup image entry fetched state pc, checked]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext answer
  simp [capCheckCompressionState, ready, Execution.charge, ← Nat.add_assoc]

theorem cap_check_compression_pc (state : MachineState) (answer : BitVec 256) :
    (capCheckCompressionState state answer).pc = state.pc + 24 := by
  simp [capCheckCompressionState, capCompressionAnswer, writeBits,
    capCheckCompressionPrefix, capCheckCompressionInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem cap_check_compression_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ≠ .x5 ∧ reg ≠ .x10 ∧ reg ≠ .x11 ∧
      reg ≠ .x12 ∧ reg ≠ .x13) :
    (capCheckCompressionState state answer).getReg reg = state.getReg reg := by
  rw [capCheckCompressionState, cap_compression_register]
  simp only [capCheckCompressionPrefix, capCheckCompressionInstructions,
    List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2.2)]

end CommitGolfCandidate
