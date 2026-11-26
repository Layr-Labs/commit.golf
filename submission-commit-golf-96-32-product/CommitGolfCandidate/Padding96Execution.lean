import CommitGolfCandidate.Padding96

/-! Exact execution of the appended adapter in the commitment and checker images. -/
set_option maxHeartbeats 2000000

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Only the checker image contains the adapter (the commitment's parents are direct
calls on the zero-gapped heap); both flag values denote the checker. -/
def paddingProgram (_checker : Bool) : Program := .check
def paddingEntry (_checker : Bool) : Nat := 163
def paddingInstructions : List Instr :=
  paddingSetupInstructions ++ [.ECALL] ++ paddingFinishInstructions

theorem padding_fetch (checker : Bool) (state : MachineState) (index : Nat)
    (inside : index < 16)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (paddingEntry checker + index))) :
    fetch (submission.image (paddingProgram checker)) state =
      some (.base ((paddingInstructions[index]?).getD .EBREAK)) := by
  have pcNat : state.pc.toNat = 4096 + 4 * (paddingEntry checker + index) := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    cases checker <;> simp only [paddingEntry, Bool.false_eq_true, ↓reduceIte] <;> omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * (paddingEntry checker + index) - 4096) / 4 =
      paddingEntry checker + index := by omega
  rw [quotient]
  cases checker <;> interval_cases index <;> rfl

theorem padding_setup_register (state : MachineState) (count : Nat) (bounded : count ≤ 9)
    (reg : Reg) (not14 : reg ≠ .x14) (not15 : reg ≠ .x15)
    (not16 : reg ≠ .x16) (not17 : reg ≠ .x17) (not11 : reg ≠ .x11) :
    (paddingSetupPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [paddingSetupPrefix, paddingSetupInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not14),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not15),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not16),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not17),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11)]

theorem padding_finish_register (state : MachineState) (count : Nat) (bounded : count ≤ 6)
    (reg : Reg) (not11 : reg ≠ .x11) :
    (paddingFinishPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  have zeroWrite (state : MachineState) (value : Word) : state.setReg .x0 value = state := rfl
  interval_cases count <;>
    simp only [paddingFinishPrefix, paddingFinishInstructions, List.take, List.foldl, execInstrBr, zeroWrite,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11)]

theorem padding_setup_input (state : MachineState)
    (compression : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 96 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0) :
    oracleInput (paddingSetupPrefix state 9) =
      some (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))) := by
  have r10 := padding_setup_register state 9 (by decide) .x10
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have r12 := padding_setup_register state 9 (by decide) .x12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have r13 := padding_setup_register state 9 (by decide) .x13
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have r11 : (paddingSetupPrefix state 9).getReg .x11 = 96 := by
    rw [padding_setup_shape]
    simp [MachineState.getReg_setReg_eq]
  have memory : readBuffer (paddingSetupPrefix state 9) (state.getReg .x10).toNat 96 =
      padInput (readBuffer state (state.getReg .x10).toNat 64) := by
    rw [padding_setup_shape]
    change readBuffer (padMemory state (state.getReg .x10)) (state.getReg .x10).toNat 96 = _
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using pad_memory_read state (state.getReg .x10).toNat sourceAligned
  have kind : (paddingSetupPrefix state 9).getReg .x13 = 0 := r13.trans compression
  simp [oracleInput, r10, r11, r12, kind, sourceValid, destinationValid,
    sourceAligned, destinationAligned, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
    memory]
  rw [kind]
  simp [memory]
  change Sum.inl (BitVec.setWidth COMPRESSION_INPUT_LENGTH
    (padInput (readBuffer state (state.getReg .x10).toNat 64))) = _
  rw [BitVec.setWidth_eq]
  rfl

/-- Nine ordinary setup instructions, one eight-cycle query, and six ordinary
restoration/return instructions. The caller's jump is charged separately. -/
theorem padding_execute (checker : Bool) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*paddingEntry checker))
    (syscall : state.getReg .x5 = 0) (compression : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 96 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceWords : ∀ word : Fin 4,
      accessValid (state.getReg .x10+BitVec.ofNat 64 (64+8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image (paddingProgram checker)) (16+fuel) state allowCoins =
      (do let answer ← World.query
            (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
          let written := writeBits (paddingSetupPrefix state 9) (state.getReg .x12) answer
          let result ← execute (submission.image (paddingProgram checker)) fuel
            (paddingFinishPrefix written 6) allowCoins
          return result.charge 23 1) := by
  have setup (remaining : Nat) :
      execute (submission.image (paddingProgram checker)) (9+remaining) state allowCoins =
        (do let result ← execute (submission.image (paddingProgram checker)) remaining
              (paddingSetupPrefix state 9) allowCoins
            return result.charge 9 0) := by
    apply execute_unit_steps (states := paddingSetupPrefix state)
    intro i hi
    refine ⟨.base ((paddingSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · have fetched := padding_fetch checker (paddingSetupPrefix state i) i (by omega) (by
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
  have fetched : fetch (submission.image (paddingProgram checker)) ready = some (.base .ECALL) :=
    padding_fetch checker ready 9 (by decide) readyPC
  have call : ready.getReg .x5 = 0 :=
    (padding_setup_register state 9 (by decide) .x5
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans syscall
  have destination : ready.getReg .x12 = state.getReg .x12 :=
    padding_setup_register state 9 (by decide) .x12
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have input := padding_setup_input state compression sourceValid destinationValid
    sourceAligned destinationAligned
  have finish (answer : BitVec 256) :
      execute (submission.image (paddingProgram checker)) (6+fuel)
          (writeBits ready (state.getReg .x12) answer) allowCoins =
        (do let result ← execute (submission.image (paddingProgram checker)) fuel
              (paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 6) allowCoins
            return result.charge 6 0) := by
    let written := writeBits ready (state.getReg .x12) answer
    apply execute_unit_steps (states := paddingFinishPrefix written)
    intro i hi
    refine ⟨.base ((paddingFinishInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · have fetched := padding_fetch checker (paddingFinishPrefix written i) (10+i) (by omega) (by
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
    let result ← execute (submission.image (paddingProgram checker)) (6+fuel)
      (writeBits ready (state.getReg .x12) answer) allowCoins
    pure ((result.charge 8 1).charge 9 0)) = _
  rw [finish answer]
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, ← Nat.add_assoc]
  rfl

end CommitGolfCandidate
