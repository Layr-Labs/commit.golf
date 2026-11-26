import CommitGolfCandidate.TruncCheckFetch
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
def dispatchOps : List Instr :=
  [.ADDI .x26 .x11 0, .ADDI .x24 .x13 0, .ADDI .x8 .x14 0,
   .ADDI .x25 .x15 0, .ADDI .x27 .x16 0, .ADDI .x6 .x0 128]

def dispatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (dispatchOps.take count).foldl execInstrBr state

private theorem dispatchRun (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (dispatchPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := dispatchPrefix state)
  intro i hi
  refine ⟨.base ((dispatchOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetchAt _ _ i _ (by omega)
    · interval_cases i <;>
        simp [dispatchPrefix, dispatchOps, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State after initial ABI register copy and dispatch on `x16 = 128` (`4984` for cap
mode, `4124` for normal mode). -/
def dispatched (state : MachineState) : MachineState :=
  (dispatchPrefix state 6).setPC (if state.getReg .x16 = 128 then 5732 else 4124)

theorem patchedDispatch (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (7 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (dispatched state) allowCoins
          return result.charge 7 0) := by
  let ready := dispatchPrefix state 6
  have readyPC : ready.pc = 4120 := by
    simp [ready, dispatchPrefix, dispatchOps, execInstrBr, pc, MachineState.setPC]
  have ready27 : ready.getReg .x27 = state.getReg .x16 := by
    simp [ready, dispatchPrefix, dispatchOps, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have ready6 : ready.getReg .x6 = 128 := by
    dsimp only [ready, dispatchPrefix, dispatchOps, List.take, List.foldl,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have fetched : fetch (submission.image .check) ready = some (.base (.BEQ .x27 .x6 1612)) := by
    apply fetchAt _ ready 6 _ (by decide) readyPC; rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x6 1612)) = some (dispatched state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [ready27, ready6, readyPC]
    simp [dispatched, ready, signExtend13]
    split <;> simp_all
  rw [show 7 + fuel = 6 + (fuel + 1) by omega, dispatchRun state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]



theorem dispatchFrame (s : MachineState) : (dispatched s).getReg .x26=s.getReg .x11 ∧
    (dispatched s).getReg .x24=s.getReg .x13 ∧ (dispatched s).getReg .x8=s.getReg .x14 ∧
    (dispatched s).getReg .x25=s.getReg .x15 ∧ (dispatched s).getReg .x27=s.getReg .x16 ∧
    (dispatched s).getReg .x16=s.getReg .x16 ∧ (dispatched s).getReg .x17=s.getReg .x17 ∧
    (dispatched s).getReg .x19=s.getReg .x19 ∧ (dispatched s).mem=s.mem := by
  simp [dispatched,dispatchPrefix,dispatchOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]
end CommitGolfCandidate.Trunc
