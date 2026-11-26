import CommitGolfCandidate.Opening

import CommitGolfCandidate.PairImage

namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 2000000

private theorem pair_opening_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 97) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .opening).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .opening) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .opening).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

private theorem pair_opening_setup_prefix (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (19 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSetupPrefix state 19) allowCoins
          return result.charge 19 0) := by
  apply execute_unit_steps (states := openingSetupPrefix state)
  intro i hi
  refine ⟨.base ((openingSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [openingSetupPrefix, openingSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem pair_opening_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (20 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingInitializedState state) allowCoins
          return result.charge 20 0) := by
  let ready := openingSetupPrefix state 19
  have readyPC : ready.pc = 4172 := by
    simp [ready, openingSetupPrefix, openingSetupInstructions, execInstrBr, pc, MachineState.setPC]
  have readyCount : ready.getReg .x27 = state.getReg .x16 := by
    simpa only [openingInitializedState, MachineState.getReg_setPC] using
      (opening_setup_registers state).2.2.2.1
  have fetched : fetch (submission.image .opening) ready =
      some (.base (.BEQ .x27 .x0 140)) := by
    apply pair_opening_fetch ready 19 _ (by decide) readyPC
    rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x0 140)) =
      some (openingInitializedState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [readyCount, show ready.getReg .x0 = 0 from rfl, readyPC]
    simp [openingInitializedState, ready, signExtend13]
    split <;> simp_all
  rw [show 20 + fuel = 19 + (fuel + 1) by omega, pair_opening_setup_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

def pair_openingDepthState (state : MachineState) : MachineState :=
  if state.getReg .x27 = 128 then
    (((state.setReg .x30 24).setReg .x6 128).setReg .x30 16).setPC 4192
  else
    ((state.setReg .x30 24).setReg .x6 128).setPC 4192

theorem pair_opening_depth_register (state : MachineState) (reg : Reg)
    (not6 : reg ≠ .x6) (not30 : reg ≠ .x30) :
    (pair_openingDepthState state).getReg reg = state.getReg reg := by
  unfold pair_openingDepthState
  split <;> simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not30),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not6)]

theorem pair_opening_depth_value (state : MachineState) :
    (pair_openingDepthState state).getReg .x30 =
      if state.getReg .x27 = 128 then 16 else 24 := by
  unfold pair_openingDepthState
  split <;> simp [MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

theorem pair_opening_depth_pc (state : MachineState) :
    (pair_openingDepthState state).pc = 4192 := by
  unfold pair_openingDepthState; split <;> rfl

theorem pair_opening_depth_memory (state : MachineState) :
    (pair_openingDepthState state).mem = state.mem := by
  unfold pair_openingDepthState; split <;> rfl

theorem pair_opening_depth_select (state : MachineState) (pc : state.pc = 4176)
    (fuel : Nat) (allowCoins : Bool) :
    let cost := if state.getReg .x27 = 128 then 4 else 3
    execute (submission.image .opening) (cost + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (pair_openingDepthState state) allowCoins
          return result.charge cost 0) := by
  let s1 := (state.setReg .x30 24).setPC 4180
  let s2 := ((state.setReg .x30 24).setReg .x6 128).setPC 4184
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x30 .x0 24)) := by
    apply pair_opening_fetch state 20 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) s1 = some (.base (.ADDI .x6 .x0 128)) := by
    apply pair_opening_fetch s1 21 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .opening) s2 = some (.base (.BNE .x27 .x6 8)) := by
    apply pair_opening_fetch s2 22 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x30 .x0 24)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st1 : ordinaryStep s1 (.base (.ADDI .x6 .x0 128)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  by_cases cap : state.getReg .x27 = 128
  · simp only [cap, ↓reduceIte, pair_openingDepthState]
    have capR : state.regs .x27 = 128 := by simpa [MachineState.getReg] using cap
    let s3 := ((state.setReg .x30 24).setReg .x6 128).setPC 4188
    have st2 : ordinaryStep s2 (.base (.BNE .x27 .x6 8)) = some s3 := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s2, s3,
        capR, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    have f3 : fetch (submission.image .opening) s3 = some (.base (.ADDI .x30 .x0 16)) := by
      apply pair_opening_fetch s3 23 _ (by decide) rfl; rfl
    have st3 : ordinaryStep s3 (.base (.ADDI .x30 .x0 16)) =
        some ((((state.setReg .x30 24).setReg .x6 128).setReg .x30 16).setPC 4192) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s3,
        MachineState.getReg, MachineState.setReg, MachineState.setPC]
    rw [show 4 + fuel = (((fuel + 1) + 1) + 1) + 1 by omega]
    rw [execute_ordinary_step _ _ _ _ _ _ f0 st0,
      execute_ordinary_step _ _ _ _ _ _ f1 st1,
      execute_ordinary_step _ _ _ _ _ _ f2 st2,
      execute_ordinary_step _ _ _ _ _ _ f3 st3]
    simp [instructionCycles, Execution.charge, ← Nat.add_assoc]
  · simp only [cap, ↓reduceIte, pair_openingDepthState]
    have capR : state.regs .x27 ≠ 128 := by simpa [MachineState.getReg] using cap
    have st2 : ordinaryStep s2 (.base (.BNE .x27 .x6 8)) =
        some (((state.setReg .x30 24).setReg .x6 128).setPC 4192) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s2,
        MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact capR
    rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega]
    rw [execute_ordinary_step _ _ _ _ _ _ f0 st0,
      execute_ordinary_step _ _ _ _ _ _ f1 st1,
      execute_ordinary_step _ _ _ _ _ _ f2 st2]
    simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem pair_opening_fetch_decrement (state : MachineState)
    (pc : state.pc = 4292) :
    fetch (submission.image .opening) state = some (.base (.ADDI .x28 .x28 4095)) := by
  apply pair_opening_fetch state 49 _ (by decide) pc
  rfl

private theorem pair_opening_fetch_branch (state : MachineState)
    (pc : state.pc = 4296) :
    fetch (submission.image .opening) state = some (.base (.BNE .x28 .x0 8128)) := by
  apply pair_opening_fetch state 50 _ (by decide) pc
  rfl

theorem pair_opening_latch (state : MachineState) (pc : state.pc = 4292)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingLatchState state) allowCoins
          return result.charge 2 0) := by
  have first := pair_opening_fetch_decrement state pc
  let next := (state.setReg .x28 (state.getReg .x28 - 1)).setPC 4296
  have second := pair_opening_fetch_branch next rfl
  have step : ordinaryStep state (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, BitVec.sub_eq_add_neg]
  have branch : ordinaryStep next (.base (.BNE .x28 .x0 8128)) =
      some (openingLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, openingLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, first, step, second, branch, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem pair_opening_next (state : MachineState) (pc : state.pc = 4300)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingNextState state) allowCoins
          return result.charge 3 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x24 .x24 8)) := by
    apply pair_opening_fetch state 51 _ (by decide) pc
    rfl
  let advanced := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4304
  let next := (advanced.setReg .x27 (state.getReg .x27 - 1)).setPC 4308
  have second : fetch (submission.image .opening) advanced =
      some (.base (.ADDI .x27 .x27 4095)) := by
    apply pair_opening_fetch advanced 52 _ (by decide) rfl
    rfl
  have third : fetch (submission.image .opening) next =
      some (.base (.BNE .x27 .x0 8076)) := by
    apply pair_opening_fetch next 53 _ (by decide) rfl
    rfl
  have step₁ : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, pc]
  have step₂ : ordinaryStep advanced (.base (.ADDI .x27 .x27 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, next, BitVec.sub_eq_add_neg, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  have step₃ : ordinaryStep next (.base (.BNE .x27 .x0 8076)) =
      some (openingNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, openingNextState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, first, step₁, second, step₂, third, step₃, instructionCycles,
    bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem pair_opening_done_gate (state : MachineState) (pc : state.pc = 4312)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingDoneGateState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x6 128).setPC 4316
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x6 .x0 128)) := by
    apply pair_opening_fetch state 54 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) next = some (.base (.BNE .x16 .x6 140)) := by
    apply pair_opening_fetch next 55 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x6 .x0 128)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s1 : ordinaryStep next (.base (.BNE .x16 .x6 140)) = some (openingDoneGateState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, next,
      openingDoneGateState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem pair_opening_exit (state : MachineState) (pc : state.pc = 4456)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (7 + fuel) state allowCoins =
      pure ⟨.success, openingExitState state, 10, 0⟩ := by
  let s₁ := (state.setReg .x6 0).setPC 4460
  let s₂ := (state.setReg .x6 0).setPC 4464
  let s₃ := (state.setReg .x6 784).setPC 4468
  let s₄ := ((state.setReg .x6 784).setReg .x11 (state.getReg .x16 * 784)).setPC 4472
  let s₅ := (((state.setReg .x6 784).setReg .x11 (state.getReg .x16 * 784)).setReg
    .x5 1).setPC 4476
  let s₆ := openingExitState state
  have fetch0 : fetch (submission.image .opening) state =
      some (.base (.ADDI .x6 .x0 0)) := by
    apply pair_opening_fetch state 90 _ (by decide) pc; rfl
  have fetch1 : fetch (submission.image .opening) s₁ =
      some (.base (.SLLI .x6 .x6 11)) := by
    apply pair_opening_fetch s₁ 91 _ (by decide) rfl; rfl
  have fetch2 : fetch (submission.image .opening) s₂ =
      some (.base (.ADDI .x6 .x6 784)) := by
    apply pair_opening_fetch s₂ 92 _ (by decide) rfl; rfl
  have fetch3 : fetch (submission.image .opening) s₃ =
      some (.base (.MUL .x11 .x16 .x6)) := by
    apply pair_opening_fetch s₃ 93 _ (by decide) rfl; rfl
  have fetch4 : fetch (submission.image .opening) s₄ =
      some (.base (.ADDI .x5 .x0 1)) := by
    apply pair_opening_fetch s₄ 94 _ (by decide) rfl; rfl
  have fetch5 : fetch (submission.image .opening) s₅ =
      some (.base (.ADDI .x10 .x0 0)) := by
    apply pair_opening_fetch s₅ 95 _ (by decide) rfl; rfl
  have fetch6 : fetch (submission.image .opening) s₆ =
      some (.base .ECALL) := by
    apply pair_opening_fetch s₆ 96 _ (by decide) rfl; rfl
  have step0 : ordinaryStep state (.base (.ADDI .x6 .x0 0)) = some s₁ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₁, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp [pc]
  have step1 : ordinaryStep s₁ (.base (.SLLI .x6 .x6 11)) = some s₂ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₁, s₂, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp; funext reg; by_cases h : reg = .x6 <;> simp [h]
  have step2 : ordinaryStep s₂ (.base (.ADDI .x6 .x6 784)) = some s₃ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₂, s₃, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp; funext reg; by_cases h : reg = .x6 <;> simp [h]
  have step3 : ordinaryStep s₃ (.base (.MUL .x11 .x16 .x6)) = some s₄ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₃, s₄, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step4 : ordinaryStep s₄ (.base (.ADDI .x5 .x0 1)) = some s₅ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₄, s₅, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step5 : ordinaryStep s₅ (.base (.ADDI .x10 .x0 0)) = some s₆ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₅, s₆, openingExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  rw [Nat.add_comm 7 fuel]
  simp only [execute, fetch0, step0, fetch1, step1, fetch2, step2, fetch3, step3,
    fetch4, step4, fetch5, step5, fetch6, instructionCycles, bind_assoc, pure_bind]
  dsimp only [s₆, openingExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [Execution.charge]

theorem pair_opening_copy (state : MachineState) (start : Nat)
    (location : start = 39 ∨ start = 60 ∨ start = 70)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := openingCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ (start + i) _ (by rcases location with rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;>
        simp [openingCopyPrefix, openingCopyInstructions, execInstrBr, pc,
          MachineState.setPC]
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have sourceReg := opening_copy_prefix_register state i (by omega) .x23 (by decide)
    have destinationReg := opening_copy_prefix_register state i (by omega) .x25 (by decide)
    have valid : memoryArgumentsValid (openingCopyPrefix state i)
        ((openingCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [openingCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [openingCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem pair_opening_salt_copy (state : MachineState) (pc : state.pc = 4204)
    (sourceValid : ∀ word : Fin 2,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSaltCopyState state) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := openingSaltCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingSaltCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ (27 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingSaltCopyPrefix, openingSaltCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have sourceReg := opening_salt_copy_prefix_register state i (by omega) .x23 (by decide)
    have destinationReg := opening_salt_copy_prefix_register state i (by omega) .x25 (by decide)
    have valid : memoryArgumentsValid (openingSaltCopyPrefix state i)
        ((openingSaltCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [openingSaltCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact d0 | exact d1
    interval_cases i <;>
      simp only [openingSaltCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

private theorem pair_opening_path_prepare (state : MachineState) (pc : state.pc = 4232)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathPreparedState state) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := openingPathPrefix state)
  intro i hi
  refine ⟨.base ((openingPathInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ (34 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPathPrefix, openingPathInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem pair_opening_path_advance (state : MachineState) (pc : state.pc = 4284)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathAdvancedState state) allowCoins
          return result.charge 2 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x25 .x25 32)) := by
    apply pair_opening_fetch state 47 _ (by decide) pc; rfl
  let next := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4288
  have second : fetch (submission.image .opening) next =
      some (.base (.SRLI .x20 .x20 1)) := by
    apply pair_opening_fetch next 48 _ (by decide) rfl; rfl
  have step : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have shift : ordinaryStep next (.base (.SRLI .x20 .x20 1)) =
      some (openingPathAdvancedState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      next, openingPathAdvancedState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [show 2 + fuel = (fuel + 1) + 1 by omega]
  rw [execute_ordinary_step _ _ _ _ _ _ first step,
    execute_ordinary_step _ _ _ _ _ _ second shift]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem pair_opening_path_iteration (state : MachineState) (pc : state.pc = 4232)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + (((state.getReg .x20 ^^^ 1) + (state.getReg .x20 >>> 1)) <<< 5) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (17 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathState state) allowCoins
          return result.charge 17 0) := by
  let ready := openingPathPreparedState state
  let copied := openingCopyState ready
  have readyPC : ready.pc = 4252 := by
    simp [ready, openingPathPreparedState, openingPathPrefix, openingPathInstructions,
      execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4284 := by rw [opening_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 4,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_path_source]
    exact sourceValid word
  have writes : ∀ word : Fin 4,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_path_prepare_register state .x25 (by decide) (by decide) (by decide)]
    exact destinationValid word
  rw [show 17 + fuel = 5 + (8 + (2 + (2 + fuel))) by omega,
    pair_opening_path_prepare state pc,
    pair_opening_copy ready 39 (Or.inl rfl) readyPC reads writes,
    pair_opening_path_advance copied copiedPC,
    pair_opening_latch (openingPathAdvancedState copied) rfl]
  simp [openingPathState, ready, copied, Execution.charge, ← Nat.add_assoc]

theorem pair_opening_path_loop (remaining : Nat) (bounded : remaining ≤ LOG_LENGTH)
    (state : MachineState) (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4232)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (nodeBound : (state.getReg .x20).toNat < 2 ^ 25)
    (outputBound : (state.getReg .x25).toNat + 32 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (17 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathState^[remaining] state) allowCoins
          return result.charge (17 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      simp only [LOG_LENGTH] at bounded; omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPathState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_path_registers state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (openingPathState state).pc = 4232 := by
      intro positive
      rw [opening_path_pc, counter, subtract, if_neg]
      intro zero
      have := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt small] at this
      omega
    have nextHeap : (openingPathState state).getReg .x9 = state.getReg .x9 :=
      (opening_path_registers state).2.2.2.2
    have nextNode : ((openingPathState state).getReg .x20).toNat < 2 ^ 25 := by
      rw [(opening_path_registers state).2.1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have outputNat : ((openingPathState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 32 := by
      rw [(opening_path_registers state).1, BitVec.toNat_add]
      change ((state.getReg .x25).toNat + 32) % 2 ^ 64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at outputBound
      omega
    have nextOutputBound : ((openingPathState state).getReg .x25).toNat +
        32 * remaining ≤ MEMORY_BYTES := by rw [outputNat]; omega
    have nextOutputAligned : ((openingPathState state).getReg .x25).toNat % 8 = 0 := by
      rw [outputNat]; omega
    have reads := opening_sibling_access (state.getReg .x9) (state.getReg .x20)
      heapBound heapAligned nodeBound
    have writes := opening_digest_access_valid (state.getReg .x25) (by omega) outputAligned
    rw [show 17 * (remaining + 1) + fuel = 17 + (17 * remaining + fuel) by omega,
      pair_opening_path_iteration state (pc (by omega)) reads writes,
      ih (by omega) (openingPathState state) nextCounter nextPC
        (by simpa only [nextHeap] using heapBound)
        (by simpa only [nextHeap] using heapAligned)
        nextNode nextOutputBound nextOutputAligned]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm,
      Nat.add_left_comm]

private theorem pair_opening_position_prepare (state : MachineState) (pc : state.pc = 4192)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPreparedState state) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := openingPositionPrefix state)
  intro i hi
  refine ⟨.base ((openingPositionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ (24 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPositionPrefix, openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i
    · simpa [openingPositionPrefix, openingPositionInstructions, ordinaryStep,
        memoryArgumentsValid, memAccess, signExtend12] using indexValid
    · rfl
    · rfl
  · interval_cases i <;> rfl

private theorem pair_opening_salt_advance (state : MachineState) (pc : state.pc = 4220)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSaltAdvancedState state) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := openingSaltPrefix state)
  intro i hi
  refine ⟨.base ((openingSaltInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ (31 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingSaltPrefix, openingSaltInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem pair_opening_position_setup (state : MachineState) (pc : state.pc = 4192)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (sourceValid : ∀ word : Fin 2,
      accessValid (state.getReg .x18 + (state.getMem (state.getReg .x24) <<< 4) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (10 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPathState state) allowCoins
          return result.charge 10 0) := by
  let ready := openingPositionPreparedState state
  let copied := openingSaltCopyState ready
  have readyPC : ready.pc = 4204 := by
    simp [ready, openingPositionPreparedState, openingPositionPrefix,
      openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4220 := by rw [opening_salt_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 2,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [(opening_position_prepared state).2]
    exact sourceValid word
  have writes : ∀ word : Fin 2,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)]
    exact destinationValid word
  rw [show 10 + fuel = 3 + (4 + (3 + fuel)) by omega,
    pair_opening_position_prepare state pc indexValid,
    pair_opening_salt_copy ready readyPC reads writes,
    pair_opening_salt_advance copied copiedPC]
  simp [openingPositionPathState, ready, copied, Execution.charge, ← Nat.add_assoc]

theorem pair_opening_position (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ LOG_LENGTH) (state : MachineState)
    (pc : state.pc = 4192)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 28 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + (16 + 32 * pathDepth) ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (13 + 17 * pathDepth + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionState pathDepth state) allowCoins
          return result.charge (13 + 17 * pathDepth) 0) := by
  let path := openingPositionPathState state
  have pathPC : path.pc = 4232 := by
    change (openingPositionPathState state).pc = 4232
    rw [openingPositionPathState, (opening_salt_advanced _).2.2.2, opening_salt_copy_pc]
    simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
      execInstrBr, pc, MachineState.setPC]
  have pathCounter : path.getReg .x28 = BitVec.ofNat 64 pathDepth :=
    (opening_position_path_registers state).2.2.trans depthReg
  have pathHeap : path.getReg .x9 = state.getReg .x9 :=
    opening_position_path_register state .x9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have pathNode : (path.getReg .x20).toNat < 2 ^ 25 := by
    rw [(opening_position_path_registers state).2.1, leaves, BitVec.toNat_add]
    change ((state.getMem (state.getReg .x24)).toNat + 16777216) % 2 ^ 64 < 2 ^ 25
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 16 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 16) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at outputBound
    omega
  have pathOutput : (path.getReg .x25).toNat + 32 * pathDepth ≤ MEMORY_BYTES := by
    rw [outputNat]; omega
  have pathAligned : (path.getReg .x25).toNat % 8 = 0 := by rw [outputNat]; omega
  have finishedPC : (openingPathState^[pathDepth] path).pc = 4300 :=
    (opening_path_finished pathDepth depthPos depthBound path pathCounter).1
  have reads := opening_salt_access (state.getReg .x18) (state.getMem (state.getReg .x24))
    saltBound saltAligned indexBound
  have writes := opening_salt_access_valid (state.getReg .x25) (by omega) outputAligned
  rw [show 13 + 17 * pathDepth + fuel = 10 + (17 * pathDepth + (3 + fuel)) by omega,
    pair_opening_position_setup state pc indexValid reads writes,
    pair_opening_path_loop pathDepth depthBound path pathCounter (fun _ => pathPC)
      (by simpa only [pathHeap] using heapBound)
      (by simpa only [pathHeap] using heapAligned) pathNode pathOutput pathAligned,
    pair_opening_next _ finishedPC]
  simp only [openingPositionState, path, bind_assoc, pure_bind]
  apply bind_congr
  intro res
  congr 1
  simp only [Execution.charge, Execution.mk.injEq, true_and]
  constructor <;> omega

theorem pair_opening_positions_loop (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ LOG_LENGTH)
    (remaining : Nat) (bounded : remaining ≤ LENGTH)
    (state : MachineState) (counter : state.getReg .x27 = BitVec.ofNat 64 remaining)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (pc : 0 < remaining → state.pc = 4192)
    (indices : ∀ offset < remaining,
      (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24)
    (indexSpace : (state.getReg .x24).toNat + 8 * remaining ≤ (state.getReg .x25).toNat)
    (indexAligned : (state.getReg .x24).toNat % 8 = 0)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 28 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + (16 + 32 * pathDepth) * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) ((13 + 17 * pathDepth) * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            ((openingPositionState pathDepth)^[remaining] state) allowCoins
          return result.charge ((13 + 17 * pathDepth) * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      norm_num [LENGTH, LOG_LENGTH] at bounded; omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have prog := opening_position_progress pathDepth state
    have nextCounter : (openingPositionState pathDepth state).getReg .x27 = BitVec.ofNat 64 remaining := by
      rw [prog.2.2.1, counter, subtract]
    have nextDepth : (openingPositionState pathDepth state).getReg .x30 = BitVec.ofNat 64 pathDepth :=
      prog.2.2.2.2.trans depthReg
    have nextPC : 0 < remaining → (openingPositionState pathDepth state).pc = 4192 := by
      intro positive
      rw [opening_position_pc, counter, subtract, if_neg]
      intro zero
      have equal := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at equal
      rw [Nat.mod_eq_of_lt small] at equal
      omega
    have nextIndex : ((openingPositionState pathDepth state).getReg .x24).toNat =
        (state.getReg .x24).toNat + 8 := by
      rw [prog.1]
      exact opening_address_add (state.getReg .x24) 8 (by omega)
    have recordLe : (state.getReg .x25).toNat + (16 + 32 * pathDepth) ≤ MEMORY_BYTES := by
      have : (16 + 32 * pathDepth) * 1 ≤ (16 + 32 * pathDepth) * (remaining + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have nextOutput : ((openingPositionState pathDepth state).getReg .x25).toNat =
        (state.getReg .x25).toNat + (16 + 32 * pathDepth) := by
      rw [prog.2.1]
      exact opening_address_add (state.getReg .x25) (16 + 32 * pathDepth) recordLe
    have nextIndices : ∀ offset < remaining,
        ((openingPositionState pathDepth state).getMem
          ((openingPositionState pathDepth state).getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
      intro offset offsetBound
      have address : (openingPositionState pathDepth state).getReg .x24 + BitVec.ofNat 64 (8 * offset) =
          state.getReg .x24 + BitVec.ofNat 64 (8 * (offset + 1)) := by
        rw [prog.1]
        simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        rw [BitVec.add_comm (8 : Word)]
        rfl
      rw [address, opening_position_memory_below pathDepth]
      · exact indices (offset + 1) (by omega)
      · exact recordLe
      · rw [opening_address_add _ _ (by omega)]
        omega
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, indexAligned⟩
    have indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24 := by
      simpa using indices 0 (by omega)
    have nextBases := opening_position_bases pathDepth state
    have stepSplit : (13 + 17 * pathDepth) * (remaining + 1) + fuel =
        (13 + 17 * pathDepth) + ((13 + 17 * pathDepth) * remaining + fuel) := by
      rw [Nat.mul_succ]; omega
    rw [stepSplit,
      pair_opening_position pathDepth depthPos depthBound state (pc (by omega)) depthReg
        indexValid indexBound leaves saltBound saltAligned heapBound heapAligned
        recordLe outputAligned,
      ih (by omega) (openingPositionState pathDepth state) nextCounter nextDepth nextPC nextIndices
        (by rw [nextIndex, nextOutput]; omega) (by rw [nextIndex]; omega)
        (by simpa only [nextBases.2.2] using leaves)
        (by simpa only [nextBases.2.1] using saltBound)
        (by simpa only [nextBases.2.1] using saltAligned)
        (by simpa only [nextBases.1] using heapBound)
        (by simpa only [nextBases.1] using heapAligned)
        (by rw [nextOutput]; rw [Nat.mul_succ] at outputBound; omega)
        (by rw [nextOutput]; omega)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

theorem pair_opening_cap_setup (state : MachineState) (pc : state.pc = 4320)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapSetupState state) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := openingCapSetupPrefix state)
  intro i hi
  refine ⟨.base ((openingCapSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply pair_opening_fetch _ (56 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingCapSetupPrefix, openingCapSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem pair_opening_cap_mid (state : MachineState) (pc : state.pc = 4368)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapMidState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x23 (state.getReg .x23 + 32)).setPC 4372
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x23 .x23 32)) := by
    apply pair_opening_fetch state 68 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) next = some (.base (.ADDI .x25 .x25 32)) := by
    apply pair_opening_fetch next 69 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x23 .x23 32)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.ADDI .x25 .x25 32)) = some (openingCapMidState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next,
      openingCapMidState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

private theorem pair_opening_cap_next (state : MachineState) (pc : state.pc = 4408)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapNextState state) allowCoins
          return result.charge 4 0) := by
  let s1 := (state.setReg .x23 (state.getReg .x23 + 64)).setPC 4412
  let s2 := (s1.setReg .x25 (state.getReg .x25 + 32)).setPC 4416
  let s3 := (s2.setReg .x28 (state.getReg .x28 - 1)).setPC 4420
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x23 .x23 64)) := by
    apply pair_opening_fetch state 78 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) s1 = some (.base (.ADDI .x25 .x25 32)) := by
    apply pair_opening_fetch s1 79 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .opening) s2 = some (.base (.ADDI .x28 .x28 4095)) := by
    apply pair_opening_fetch s2 80 _ (by decide) rfl; rfl
  have f3 : fetch (submission.image .opening) s3 = some (.base (.BNE .x28 .x0 8108)) := by
    apply pair_opening_fetch s3 81 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x23 .x23 64)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x25 .x25 32)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st2 : ordinaryStep s2 (.base (.ADDI .x28 .x28 4095)) = some s3 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2, s3,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have st3 : ordinaryStep s3 (.base (.BNE .x28 .x0 8108)) = some (openingCapNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s1, s2, s3,
      openingCapNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, st0, f1, st1, f2, st2, f3, st3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem pair_opening_cap_pair_iteration (state : MachineState) (pc : state.pc = 4336)
    (srcBound : (state.getReg .x23).toNat + 64 ≤ MEMORY_BYTES)
    (srcAligned : (state.getReg .x23).toNat % 8 = 0)
    (dstBound : (state.getReg .x25).toNat + 64 ≤ MEMORY_BYTES)
    (dstAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (22 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapPairState state) allowCoins
          return result.charge 22 0) := by
  let c1 := openingCopyState state
  let m := openingCapMidState c1
  let c2 := openingCopyState m
  have c1PC : c1.pc = 4368 := by rw [opening_copy_pc, pc]; rfl
  have c2PC : c2.pc = 4408 := by rw [opening_copy_pc]; rfl
  have s1 := opening_digest_access_valid (state.getReg .x23) (by omega) srcAligned
  have d1 := opening_digest_access_valid (state.getReg .x25) (by omega) dstAligned
  have mSrc : m.getReg .x23 = state.getReg .x23 + 32 := by
    simp [m, openingCapMidState, c1, opening_copy_register, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have mDst : m.getReg .x25 = state.getReg .x25 + 32 := by
    simp [m, openingCapMidState, c1, opening_copy_register, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have mSrcNat : (m.getReg .x23).toNat = (state.getReg .x23).toNat + 32 := by
    rw [mSrc]; exact opening_address_add _ 32 (by omega)
  have mDstNat : (m.getReg .x25).toNat = (state.getReg .x25).toNat + 32 := by
    rw [mDst]; exact opening_address_add _ 32 (by omega)
  have s2 := opening_digest_access_valid (m.getReg .x23) (by rw [mSrcNat]; omega) (by rw [mSrcNat]; omega)
  have d2 := opening_digest_access_valid (m.getReg .x25) (by rw [mDstNat]; omega) (by rw [mDstNat]; omega)
  rw [show 22 + fuel = 8 + (2 + (8 + (4 + fuel))) by omega,
    pair_opening_copy state 60 (Or.inr (Or.inl rfl)) pc s1 d1,
    pair_opening_cap_mid c1 c1PC,
    pair_opening_copy m 70 (Or.inr (Or.inr rfl)) rfl s2 d2,
    pair_opening_cap_next c2 c2PC]
  simp [openingCapPairState, c1, m, c2, Execution.charge, ← Nat.add_assoc]

theorem pair_opening_cap_loop (remaining : Nat) (bounded : remaining ≤ 64) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4336)
    (srcBound : (state.getReg .x23).toNat + 96 * remaining ≤ MEMORY_BYTES)
    (srcAligned : (state.getReg .x23).toNat % 8 = 0)
    (dstBound : (state.getReg .x25).toNat + 64 * remaining ≤ MEMORY_BYTES)
    (dstAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (22 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapPairState^[remaining] state) allowCoins
          return result.charge (22 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingCapPairState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_cap_pair_registers state).2.2, counter, subtract]
    have nextPC : 0 < remaining → (openingCapPairState state).pc = 4336 := by
      intro positive
      rw [opening_cap_pair_pc, counter, subtract, if_neg]
      intro zero
      have := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    have nextSrc : ((openingCapPairState state).getReg .x23).toNat =
        (state.getReg .x23).toNat + 96 := by
      rw [(opening_cap_pair_registers state).1]
      exact opening_address_add _ 96 (by omega)
    have nextDst : ((openingCapPairState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 64 := by
      rw [(opening_cap_pair_registers state).2.1]
      exact opening_address_add _ 64 (by omega)
    rw [show 22 * (remaining + 1) + fuel = 22 + (22 * remaining + fuel) by omega,
      pair_opening_cap_pair_iteration state (pc (by omega)) (by omega) srcAligned (by omega) dstAligned,
      ih (by omega) (openingCapPairState state) nextCounter nextPC
        (by rw [nextSrc]; omega) (by rw [nextSrc]; omega)
        (by rw [nextDst]; omega) (by rw [nextDst]; omega)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

end CommitGolfCandidate.PairCap
