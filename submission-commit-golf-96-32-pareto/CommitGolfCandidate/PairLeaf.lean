import CommitGolfCandidate.PairPad
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

def rec_checkCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

def rec_checkCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (rec_checkCompressionInstructions.take count).foldl execInstrBr state

theorem rec_check_compression (state : MachineState) (start : Nat)
    (location : start = 54)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * start))
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (22 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer state 256 64))))
          let result ← execute Late.Check.Normal.checkerImage fuel (Late.Check.Normal.checkCompressionState state answer) allowCoins
          return result.charge 29 1) := by
  have setup (remaining : Nat) :
      execute Late.Check.Normal.checkerImage (5 + remaining) state allowCoins =
        (do let result ← execute Late.Check.Normal.checkerImage remaining
              (rec_checkCompressionPrefix state 5) allowCoins
            return result.charge 5 0) := by
    apply execute_unit_steps (states := rec_checkCompressionPrefix state)
    intro i hi
    refine ⟨.base ((rec_checkCompressionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply patchedFetch _ (192 + start + i) _ (by rcases location with rfl <;> omega)
      · rcases location with rfl <;> interval_cases i <;>
          simp [rec_checkCompressionPrefix, rec_checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := rec_checkCompressionPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (192+start+5)) := by
    dsimp only [ready]
    rcases location with rfl <;>
        simp [rec_checkCompressionPrefix, rec_checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 64 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 := by
    simp [ready, rec_checkCompressionPrefix, rec_checkCompressionInstructions, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, scratch]
    rfl
  have call := rec_padding_call true ready (192+start+5) (by rcases location with rfl; exact Or.inl rfl) readyPC
    registers.1 registers.2.2.2.2
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1, registers.2.2.2.1]; decide) fuel allowCoins
  rw [show 22 + fuel = 5 + (17 + fuel) by omega, setup]
  erw [call]
  simp only [bind_assoc, pure_bind]
  rw [registers.2.1]
  change ((liftM (World.query (.inr (.inl (padInput (readBuffer state 256 64)))))) >>= _) = _
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer state 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have resultState : paddedCompressionState ready answer = Late.Check.Normal.checkCompressionState state answer := by
    unfold paddedCompressionState
    rw [registers.2.2.2.1]
    rfl
  rw [resultState]
  simp [Execution.charge, ← Nat.add_assoc]
end CommitGolfCandidate.PairCap
