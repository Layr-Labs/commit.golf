import CommitGolfCandidate.PairPad
import CommitGolfCandidate.TruncCheckFetch
namespace CommitGolfCandidate.Trunc.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
set_option maxRecDepth 14000
set_option maxHeartbeats 1500000


theorem rec_padding_fetch (checker : Bool) (state : MachineState) (index : Nat)
    (inside : index < 16)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (paddingEntry checker + index))) :
    fetch (Trunc.submission.image (paddingProgram checker)) state =
      some (.base ((paddingInstructions[index]?).getD .EBREAK)) := by
  have pcNat : state.pc.toNat = 4096 + 4 * (paddingEntry checker + index) := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    cases checker <;> simp only [paddingEntry, Bool.false_eq_true, ↓reduceIte] <;> omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * (paddingEntry checker + index) - 4096) / 4 =
      paddingEntry checker + index := by omega
  rw [quotient]
  cases checker <;> interval_cases index <;> rfl

theorem rec_padding_execute (checker : Bool) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*paddingEntry checker))
    (syscall : state.getReg .x5 = 0) (compression : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 96 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceWords : ∀ word : Fin 4,
      accessValid (state.getReg .x10+BitVec.ofNat 64 (64+8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image (paddingProgram checker)) (16+fuel) state allowCoins =
      (do let answer ← World.query
            (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
          let written := writeBits (paddingSetupPrefix state 9) (state.getReg .x12) answer
          let result ← execute (Trunc.submission.image (paddingProgram checker)) fuel
            (paddingFinishPrefix written 6) allowCoins
          return result.charge 23 1) := by
  have setup (remaining : Nat) :
      execute (Trunc.submission.image (paddingProgram checker)) (9+remaining) state allowCoins =
        (do let result ← execute (Trunc.submission.image (paddingProgram checker)) remaining
              (paddingSetupPrefix state 9) allowCoins
            return result.charge 9 0) := by
    apply execute_unit_steps (states := paddingSetupPrefix state)
    intro i hi
    refine ⟨.base ((paddingSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · have fetched := rec_padding_fetch checker (paddingSetupPrefix state i) i (by omega) (by
        interval_cases i <;>
          simp [paddingSetupPrefix, paddingSetupInstructions, execInstrBr,
            MachineState.setPC, pc, BitVec.add_assoc, Nat.mul_add, ← BitVec.ofNat_add, Nat.add_assoc])
      interval_cases i <;> exact fetched
    · have source := padding_setup_register state i (by omega) .x10
        (by decide) (by decide) (by decide) (by decide) (by decide)
      have s0 := sourceWords ⟨0, by decide⟩
      have s1 := sourceWords ⟨1, by decide⟩
      have s2 := sourceWords ⟨2, by decide⟩
      have s3 := sourceWords ⟨3, by decide⟩
      have valid : memoryArgumentsValid (paddingSetupPrefix state i)
          ((paddingSetupInstructions[i]?).getD .EBREAK) = true := by
        interval_cases i <;>
          simp only [paddingSetupInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, memoryArgumentsValid, memAccess, source, signExtend12] <;>
          first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
      interval_cases i <;>
        simp only [paddingSetupInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at valid ⊢ <;>
        simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  let ready := paddingSetupPrefix state 9
  have readyPC : ready.pc = BitVec.ofNat 64 (4096+4*(paddingEntry checker+9)) := by
    simp [ready, padding_setup_shape, pc, MachineState.setPC, Nat.mul_add, ← BitVec.ofNat_add, Nat.add_assoc]
  have fetched : fetch (Trunc.submission.image (paddingProgram checker)) ready = some (.base .ECALL) :=
    rec_padding_fetch checker ready 9 (by decide) readyPC
  have call : ready.getReg .x5 = 0 :=
    (padding_setup_register state 9 (by decide) .x5
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans syscall
  have destination : ready.getReg .x12 = state.getReg .x12 :=
    padding_setup_register state 9 (by decide) .x12
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have input := padding_setup_input state compression sourceValid destinationValid
    sourceAligned destinationAligned
  have finish (answer : BitVec 256) :
      execute (Trunc.submission.image (paddingProgram checker)) (6+fuel)
          (writeBits ready (state.getReg .x12) answer) allowCoins =
        (do let result ← execute (Trunc.submission.image (paddingProgram checker)) fuel
              (paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 6) allowCoins
            return result.charge 6 0) := by
    let written := writeBits ready (state.getReg .x12) answer
    apply execute_unit_steps (states := paddingFinishPrefix written)
    intro i hi
    refine ⟨.base ((paddingFinishInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · have fetched := rec_padding_fetch checker (paddingFinishPrefix written i) (10+i) (by omega) (by
        have writtenPC : written.pc = BitVec.ofNat 64 (4096+4*(paddingEntry checker+10)) := by
          change ready.pc+4 = _
          rw [readyPC]
          erw [← BitVec.ofNat_add]
          congr 1 <;> omega
        interval_cases i <;>
          simp [paddingFinishPrefix, paddingFinishInstructions, execInstrBr,
            MachineState.setPC, writtenPC, Nat.mul_add, ← BitVec.ofNat_add, Nat.add_assoc])
      interval_cases i <;> exact fetched
    · have source : (paddingFinishPrefix written i).getReg .x10 = state.getReg .x10 := by
        rw [padding_finish_register _ _ (by omega) _ (by decide), writeBits_register]
        exact padding_setup_register state 9 (by decide) .x10
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have s0 := sourceWords ⟨0, by decide⟩
      have s1 := sourceWords ⟨1, by decide⟩
      have s2 := sourceWords ⟨2, by decide⟩
      have s3 := sourceWords ⟨3, by decide⟩
      have valid : memoryArgumentsValid (paddingFinishPrefix written i)
          ((paddingFinishInstructions[i]?).getD .EBREAK) = true := by
        interval_cases i <;>
          simp only [paddingFinishInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, memoryArgumentsValid, memAccess, source, signExtend12] <;>
          first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
      interval_cases i <;>
        simp only [paddingFinishInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at valid ⊢ <;>
        simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  rw [show 16+fuel = 9+((6+fuel)+1) by omega, setup, execute, fetched, if_pos call, input]
  simp only [writeOracleAnswer, destination, bind_assoc, pure_bind]
  have destination' : (paddingSetupPrefix state 9).getReg .x12 = state.getReg .x12 := destination
  simp only [destination']
  apply congrArg (fun continuation =>
    (liftM (World.query
      (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  change (do
    let result ← execute (Trunc.submission.image (paddingProgram checker)) (6+fuel)
      (writeBits ready (state.getReg .x12) answer) allowCoins
    pure ((result.charge 8 1).charge 9 0)) = _
  rw [finish answer]
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, ← Nat.add_assoc]
  rfl

theorem rec_padding_call (checker : Bool) (state : MachineState) (index : Nat)
    (location : rec_paddingCallSite checker index)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (syscall : state.getReg .x5 = 0) (compression : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 96 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (beforePadding : (state.getReg .x12).toNat+32 ≤ (state.getReg .x10).toNat+64)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image (paddingProgram checker)) (17+fuel) state allowCoins =
      (do let answer ← World.query
            (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
          let result ← execute (Trunc.submission.image (paddingProgram checker)) fuel
            (paddedCompressionState state answer) allowCoins
          return result.charge 24 1) := by
  let instruction := Instr.JAL .x31 (BitVec.ofInt 21 (4*((paddingEntry checker : Int)-index)))
  let next := (state.setReg .x31 (state.pc+4)).setPC
    (BitVec.ofNat 64 (4096+4*paddingEntry checker))
  have fetched : fetch (Trunc.submission.image (paddingProgram checker)) state =
      some (.base instruction) := by
    cases checker <;> rcases location with rfl | rfl <;>
      simp only [fetch, pc] <;> rfl
  have stepped : ordinaryStep state (.base instruction) = some next := by
    cases checker <;> rcases location with rfl | rfl <;>
      simp [instruction, next, paddingEntry, ordinaryStep, memoryArgumentsValid,
        memAccess, execInstrBr, signExtend21, pc, MachineState.setPC]
  have alignedReturn : (state.pc+4) &&& ~~~1 = state.pc+4 := by
    cases checker <;> rcases location with rfl | rfl <;> rw [pc] <;> rfl
  have separate := padding_output_separate (state.getReg .x10) (state.getReg .x12)
    sourceValid destinationValid beforePadding
  rw [show 17+fuel = (16+fuel)+1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rw [rec_padding_execute checker next rfl syscall compression sourceValid destinationValid
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
    let result ← execute (Trunc.submission.image (paddingProgram checker)) fuel
      (paddingFinishPrefix (writeBits (paddingSetupPrefix next 9)
        (state.getReg .x12) answer) 6) allowCoins
    pure ((result.charge 23 1).charge 1 0)) = _
  have finished : paddingFinishPrefix (writeBits (paddingSetupPrefix next 9)
      (state.getReg .x12) answer) 6 = paddedCompressionState state answer :=
    padding_finished state _ answer alignedReturn separate
  rw [finished]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate.Trunc.Check
