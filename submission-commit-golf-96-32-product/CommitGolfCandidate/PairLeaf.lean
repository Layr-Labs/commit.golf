import CommitGolfCandidate.PairControl

import CommitGolfCandidate.Check

import CommitGolfCandidate.PairPad

namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 1400000

def rec_checkCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

def rec_checkCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (rec_checkCompressionInstructions.take count).foldl execInstrBr state

theorem rec_check_compression (state : MachineState) (start : Nat)
    (location : start = 54)
    (pc : state.pc = BitVec.ofNat 64 (4964 + 4 * start))
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (22 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer state 256 64))))
          let result ← execute (submission.image .check) fuel (checkCompressionState state answer) allowCoins
          return result.charge 29 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .check) (5 + remaining) state allowCoins =
        (do let result ← execute (submission.image .check) remaining
              (rec_checkCompressionPrefix state 5) allowCoins
            return result.charge 5 0) := by
    apply execute_unit_steps (states := rec_checkCompressionPrefix state)
    intro i hi
    refine ⟨.base ((rec_checkCompressionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply patchedFetch _ (217 + start + i) _ (by rcases location with rfl <;> omega)
      · rcases location with rfl <;> interval_cases i <;>
          simp [rec_checkCompressionPrefix, rec_checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := rec_checkCompressionPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (217+start+5)) := by
    dsimp only [ready]
    rcases location with rfl <;>
        simp [rec_checkCompressionPrefix, rec_checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 64 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 := by
    simp [ready, rec_checkCompressionPrefix, rec_checkCompressionInstructions, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, scratch]
    rfl
  have call := rec_padding_call true ready (217+start+5) (by rcases location with rfl; exact Or.inl rfl) readyPC
    registers.1 registers.2.2.2.2
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1, registers.2.2.2.1]; decide) fuel allowCoins
  simp only [paddingProgram, ↓reduceIte] at call
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
  have resultState : paddedCompressionState ready answer = checkCompressionState state answer := by
    unfold paddedCompressionState
    rw [registers.2.2.2.1]
    rfl
  rw [resultState]
  simp [Execution.charge, ← Nat.add_assoc]

def rec_checkLeafCallInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 96,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

def rec_checkLeafCallPrefix (state : MachineState) (count : Nat) : MachineState :=
  (rec_checkLeafCallInstructions.take count).foldl execInstrBr state

theorem rec_check_leaf_call_registers (state : MachineState) (scratch : state.getReg .x21 = 256) :
    (rec_checkLeafCallPrefix state 5).getReg .x5 = 0 ∧ (rec_checkLeafCallPrefix state 5).getReg .x10 = 256 ∧
      (rec_checkLeafCallPrefix state 5).getReg .x11 = 96 ∧ (rec_checkLeafCallPrefix state 5).getReg .x12 = 256 ∧
      (rec_checkLeafCallPrefix state 5).getReg .x13 = 0 := by
  simp [rec_checkLeafCallPrefix, rec_checkLeafCallInstructions, execInstrBr,
    signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, scratch]
  rfl

theorem rec_check_leaf_compression (state : MachineState) (start : Nat)
    (location : start = 172 ∨ start = 196)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery state)))
          let result ← execute (submission.image .check) fuel
            (checkLeafCompressionState state answer) allowCoins
          return result.charge 13 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .check) (5 + remaining) state allowCoins =
        (do let result ← execute (submission.image .check) remaining
              (rec_checkLeafCallPrefix state 5) allowCoins
            return result.charge 5 0) := by
    apply execute_unit_steps (states := rec_checkLeafCallPrefix state)
    intro i hi
    refine ⟨.base ((rec_checkLeafCallInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply patchedFetch _ (start + i) _ (by rcases location with rfl | rfl <;> omega)
      · rcases location with rfl | rfl <;> interval_cases i <;>
          simp [rec_checkLeafCallPrefix, rec_checkLeafCallInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl | rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := rec_checkLeafCallPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (start + 5)) := by
    dsimp only [ready]
    rcases location with rfl | rfl <;>
      simp [rec_checkLeafCallPrefix, rec_checkLeafCallInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 96 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 :=
    rec_check_leaf_call_registers state scratch
  have fetched : fetch (submission.image .check) ready = some (.base .ECALL) := by
    apply patchedFetch _ (start + 5) _ (by rcases location with rfl | rfl <;> omega) readyPC
    rcases location with rfl | rfl <;> rfl
  have input : oracleInput ready = some (.inl (leafQuery state)) := by
    have sameMem (address : Word) : ready.getMem address = state.getMem address := rfl
    have memory : readBuffer ready 256 96 = readBuffer state 256 96 := by
      unfold readBuffer
      simp only [MachineState.getByte, sameMem]
    have kind := registers.2.2.2.2
    simp [oracleInput, registers.2.1, registers.2.2.1, registers.2.2.2.1, kind,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid, MEMORY_BYTES]
    rw [memory]
    rfl
  rw [show 6 + fuel = 5 + (fuel + 1) by omega, setup, execute, fetched, if_pos registers.1, input]
  simp only [writeOracleAnswer, registers.2.2.2.1, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery state)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have r12 : (rec_checkLeafCallPrefix state 5).getReg .x12 = 256 := registers.2.2.2.1
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, checkLeafCompressionState, r12,
    ← Nat.add_assoc]
  congr

def rec_checkLeafInitCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 24, .LD .x6 .x8 8, .SD .x21 .x6 32,
   .LD .x6 .x8 16, .SD .x21 .x6 40, .LD .x6 .x8 24, .SD .x21 .x6 48,
   .LD .x6 .x8 32, .SD .x21 .x6 56, .LD .x6 .x8 40, .SD .x21 .x6 64,
   .LD .x6 .x8 48, .SD .x21 .x6 72, .LD .x6 .x8 56, .SD .x21 .x6 80,
   .LD .x6 .x8 64, .SD .x21 .x6 88]

def rec_checkLeafInitCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (rec_checkLeafInitCopyInstructions.take count).foldl execInstrBr state

theorem rec_check_init_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 18)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (rec_checkLeafInitCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [rec_checkLeafInitCopyPrefix, rec_checkLeafInitCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem rec_check_leaf_init_copy (state : MachineState) (pc : state.pc = 4712)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 9,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (18 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafInitCopyState state) allowCoins
          return result.charge 18 0) := by
  apply execute_unit_steps (states := rec_checkLeafInitCopyPrefix state)
  intro i hi
  refine ⟨.base ((rec_checkLeafInitCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply patchedFetch _ (154 + i) _ (by omega)
    · interval_cases i <;>
        simp [rec_checkLeafInitCopyPrefix, rec_checkLeafInitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := rec_check_init_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (rec_check_init_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have s4 := sourceValid ⟨4, by decide⟩
    have s5 := sourceValid ⟨5, by decide⟩
    have s6 := sourceValid ⟨6, by decide⟩
    have s7 := sourceValid ⟨7, by decide⟩
    have s8 := sourceValid ⟨8, by decide⟩
    have valid : memoryArgumentsValid (rec_checkLeafInitCopyPrefix state i)
        ((rec_checkLeafInitCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [rec_checkLeafInitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12]
      · exact s0
      · rfl
      · exact s1
      · rfl
      · exact s2
      · rfl
      · exact s3
      · rfl
      · exact s4
      · rfl
      · exact s5
      · rfl
      · exact s6
      · rfl
      · exact s7
      · rfl
      · exact s8
      · rfl
    interval_cases i <;>
      simp only [rec_checkLeafInitCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem rec_check_leaf_init_post (state : MachineState) (pc : state.pc = 4808)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafInitPostState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x8 (state.getReg .x8 + 64)).setPC 4812
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x8 .x8 64)) := by
    apply patchedFetch _ 178 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.ADDI .x28 .x0 3)) := by
    apply patchedFetch _ 179 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 64)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, next]
  have s1 : ordinaryStep next (.base (.ADDI .x28 .x0 3)) = some (checkLeafInitPostState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next,
      checkLeafInitPostState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem rec_check_leaf_init (state : MachineState) (pc : state.pc = 4712)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 9,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (26 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))
          let result ← execute (submission.image .check) fuel (checkLeafInitStepState state answer) allowCoins
          return result.charge 33 1) := by
  have copyPC : (checkLeafInitCopyState state).pc = BitVec.ofNat 64 (4096 + 4 * 172) := by
    change (rec_checkLeafInitCopyPrefix state 18).pc = BitVec.ofNat 64 (4096 + 4 * 172)
    simp [checkLeafInitCopyState, rec_checkLeafInitCopyPrefix, rec_checkLeafInitCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyScratch : (checkLeafInitCopyState state).getReg .x21 = 256 :=
    (rec_check_init_copy_register state 18 (by decide) .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkLeafCompressionState (checkLeafInitCopyState state) answer).pc = 4808 := by
    rw [check_leaf_compression_pc, copyPC]; rfl
  rw [show 26 + fuel = 18 + (6 + (2 + fuel)) by omega,
    rec_check_leaf_init_copy state pc scratch sourceValid,
    rec_check_leaf_compression _ 172 (Or.inl rfl) copyPC copyScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  rw [rec_check_leaf_init_post _ (compressionPC answer)]
  simp [checkLeafInitStepState, Execution.charge, ← Nat.add_assoc]

theorem rec_check_leaf_init_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31]) :
    (checkLeafInitStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28, not14, not15, not16, not17, not31⟩
  simp only [checkLeafInitStepState, checkLeafInitPostState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (check_leaf_compression_register _ answer reg not5 not10 not11 not12 not13).trans
    (rec_check_init_copy_register state 18 (by decide) reg not6)

def rec_checkLeafCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56,
   .LD .x6 .x8 32, .SD .x21 .x6 64, .LD .x6 .x8 40, .SD .x21 .x6 72,
   .LD .x6 .x8 48, .SD .x21 .x6 80, .LD .x6 .x8 56, .SD .x21 .x6 88]

def rec_checkLeafCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (rec_checkLeafCopyInstructions.take count).foldl execInstrBr state

theorem rec_check_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 16)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (rec_checkLeafCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [rec_checkLeafCopyPrefix, rec_checkLeafCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem rec_check_leaf_copy (state : MachineState) (pc : state.pc = 4816)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (16 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafCopyState state) allowCoins
          return result.charge 16 0) := by
  apply execute_unit_steps (states := rec_checkLeafCopyPrefix state)
  intro i hi
  refine ⟨.base ((rec_checkLeafCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply patchedFetch _ (180 + i) _ (by omega)
    · interval_cases i <;>
        simp [rec_checkLeafCopyPrefix, rec_checkLeafCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := rec_check_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (rec_check_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have s4 := sourceValid ⟨4, by decide⟩
    have s5 := sourceValid ⟨5, by decide⟩
    have s6 := sourceValid ⟨6, by decide⟩
    have s7 := sourceValid ⟨7, by decide⟩
    have valid : memoryArgumentsValid (rec_checkLeafCopyPrefix state i)
        ((rec_checkLeafCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [rec_checkLeafCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12]
      · exact s0
      · rfl
      · exact s1
      · rfl
      · exact s2
      · rfl
      · exact s3
      · rfl
      · exact s4
      · rfl
      · exact s5
      · rfl
      · exact s6
      · rfl
      · exact s7
      · rfl
    interval_cases i <;>
      simp only [rec_checkLeafCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem rec_check_leaf_next (state : MachineState) (pc : state.pc = 4904)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafNextState state) allowCoins
          return result.charge 3 0) := by
  let advanced := (state.setReg .x8 (state.getReg .x8 + 64)).setPC 4908
  let next := (advanced.setReg .x28 (state.getReg .x28 - 1)).setPC 4912
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x8 .x8 64)) := by
    apply patchedFetch _ 202 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) advanced = some (.base (.ADDI .x28 .x28 4095)) := by
    apply patchedFetch _ 203 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) next = some (.base (.BNE .x28 .x0 8096)) := by
    apply patchedFetch _ 204 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 64)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, advanced]
  have s1 : ordinaryStep advanced (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep next (.base (.BNE .x28 .x0 8096)) = some (checkLeafNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, checkLeafNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem rec_check_leaf_block (state : MachineState) (pc : state.pc = 4816)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (25 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))
          let result ← execute (submission.image .check) fuel (checkLeafStepState state answer) allowCoins
          return result.charge 32 1) := by
  have copyPC : (checkLeafCopyState state).pc = BitVec.ofNat 64 (4096 + 4 * 196) := by
    change (rec_checkLeafCopyPrefix state 16).pc = BitVec.ofNat 64 (4096 + 4 * 196)
    simp [checkLeafCopyState, rec_checkLeafCopyPrefix, rec_checkLeafCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyScratch : (checkLeafCopyState state).getReg .x21 = 256 :=
    (rec_check_copy_register state 16 (by decide) .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkLeafCompressionState (checkLeafCopyState state) answer).pc = 4904 := by
    rw [check_leaf_compression_pc, copyPC]
    rfl
  rw [show 25 + fuel = 16 + (6 + (3 + fuel)) by omega, rec_check_leaf_copy state pc scratch sourceValid,
    rec_check_leaf_compression _ 196 (Or.inr rfl) copyPC copyScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  rw [rec_check_leaf_next _ (compressionPC answer)]
  simp [checkLeafStepState, Execution.charge, ← Nat.add_assoc]

theorem rec_check_leaf_loop (state : MachineState) (count : Nat) (bounded : count ≤ 3)
    (pc : 0 < count → state.pc = 4816) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 8 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (25 * count + fuel) state allowCoins =
      (do let finished ← checkLeafLoop state count
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (32 * count) count) := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 8) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (checkLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(check_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (checkLeafStepState state answer).pc = 4816 := by
      rw [check_leaf_block_pc]
      have nonzero : state.getReg .x28 - 1 ≠ 0 := by
        rw [← (check_leaf_block_registers state answer).2.1, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 8 * count) :
        accessValid ((checkLeafStepState state answer).getReg .x8 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 8) (by omega)
      rw [(check_leaf_block_registers state answer).1]
      have address : state.getReg .x8 + 64 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 8)) := by
        rw [show 8 * (word + 8) = 64 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 25 * (count + 1) + fuel = 25 + (25 * count + fuel) by omega,
      rec_check_leaf_block state (pc (by omega)) scratch currentValid]
    simp only [checkLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    change BitVec 256 at answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer)
      ((check_leaf_block_registers state answer).2.2.1.trans scratch) (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem rec_check_leaf_return (state : MachineState) (pc : state.pc = 4916)
    (link : state.getReg .x1 = 5068) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (state.setPC 5068) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply patchedFetch _ 205 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 5068) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem rec_check_leaf_subroutine (state : MachineState) (pc : state.pc = 4712)
    (link : state.getReg .x1 = 5068) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (102 + fuel) state allowCoins =
      (do let finished ← checkLeafSubroutineRun state
          let result ← execute (submission.image .check) fuel (finished.setPC 5068) allowCoins
          return result.charge 130 4) := by
  have initSource : ∀ word : Fin 9,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => sourceValid word.val (by omega)
  rw [show 102 + fuel = 26 + (25 * 3 + (1 + fuel)) by omega,
    rec_check_leaf_init state pc scratch initSource]
  simp only [checkLeafSubroutineRun, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have iregs := check_leaf_init_registers state answer
  have loopSource : ∀ word < 8 * 3,
      accessValid ((checkLeafInitStepState state answer).getReg .x8 +
        BitVec.ofNat 64 (8 * word)) 8 = true := by
    intro word hw
    rw [iregs.1]
    have address : state.getReg .x8 + 64 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 8)) := by
      rw [show 8 * (word + 8) = 64 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [address]
    exact sourceValid (word + 8) (by omega)
  rw [rec_check_leaf_loop (checkLeafInitStepState state answer) 3 (by decide)
    (fun _ => iregs.2.2.2.2) iregs.2.1 (iregs.2.2.1.trans scratch) loopSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := check_leaf_loop_finished _ 3 (by decide) iregs.2.1 finished reachable
  have finalLink : finished.getReg .x1 = 5068 := done.2.1.trans (iregs.2.2.2.1.trans link)
  rw [rec_check_leaf_return finished (done.2.2 (by decide)) finalLink]
  simp [Execution.charge, ← Nat.add_assoc]

theorem rec_check_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31]) :
    (checkLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28, not14, not15, not16, not17, not31⟩
  simp only [checkLeafStepState, checkLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (check_leaf_compression_register _ answer reg not5 not10 not11 not12 not13).trans
    (rec_check_copy_register state 16 (by decide) reg not6)

end CommitGolfCandidate.PairCap
