import CommitGolfCandidate.Padding96Bounds
import CommitGolfCandidate.Padding96Execution
import CommitGolfCandidate.Padding96Result

/-! Connect each actual compression call site to the appended adapter. -/
set_option maxRecDepth 10000

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def paddingCallSite (checker : Bool) (index : Nat) : Prop :=
  if checker then index = 61 else index = 77

/-- One jump and the sixteen-instruction adapter cost 24 cycles and one query.
The final PC is the instruction after the original call site. -/
theorem padding_call (checker : Bool) (state : MachineState) (index : Nat)
    (location : paddingCallSite checker index)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (syscall : state.getReg .x5 = 0) (compression : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 96 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (beforePadding : (state.getReg .x12).toNat+32 ≤ (state.getReg .x10).toNat+64)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image (paddingProgram checker)) (17+fuel) state allowCoins =
      (do let answer ← World.query
            (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
          let result ← execute (submission.image (paddingProgram checker)) fuel
            (paddedCompressionState state answer) allowCoins
          return result.charge 24 1) := by
  let instruction := Instr.JAL .x31 (BitVec.ofNat 21 (4*(paddingEntry checker-index)))
  let next := (state.setReg .x31 (state.pc+4)).setPC
    (BitVec.ofNat 64 (4096+4*paddingEntry checker))
  have fetched : fetch (submission.image (paddingProgram checker)) state =
      some (.base instruction) := by
    cases checker <;> rcases location with rfl <;>
      simp only [fetch, pc] <;> rfl
  have stepped : ordinaryStep state (.base instruction) = some next := by
    cases checker <;> rcases location with rfl <;>
      simp [instruction, next, paddingEntry, ordinaryStep, memoryArgumentsValid,
        memAccess, execInstrBr, signExtend21, pc, MachineState.setPC]
  have alignedReturn : (state.pc+4) &&& ~~~1 = state.pc+4 := by
    cases checker <;> rcases location with rfl <;> rw [pc] <;> rfl
  have separate := padding_output_separate (state.getReg .x10) (state.getReg .x12)
    sourceValid destinationValid beforePadding
  rw [show 17+fuel = (16+fuel)+1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rw [padding_execute checker next rfl syscall compression sourceValid destinationValid
    sourceAligned destinationAligned
    (padding_source_words (state.getReg .x10) sourceValid sourceAligned) fuel allowCoins]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query
      (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  change (do
    let result ← execute (submission.image (paddingProgram checker)) fuel
      (paddingFinishPrefix (writeBits (paddingSetupPrefix next 9)
        (state.getReg .x12) answer) 6) allowCoins
    pure ((result.charge 23 1).charge 1 0)) = _
  have finished : paddingFinishPrefix (writeBits (paddingSetupPrefix next 9)
      (state.getReg .x12) answer) 6 = paddedCompressionState state answer :=
    padding_finished state _ answer alignedReturn separate
  rw [finished]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
