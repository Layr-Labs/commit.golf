import CommitGolfCandidate.PairWords

import CommitGolfCandidate.TruncOpenPaths

import CommitGolfCandidate.TruncCheckFetch

namespace CommitGolfCandidate.Trunc.Open

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap

set_option maxRecDepth 18000

set_option maxHeartbeats 1600000

theorem setupRun (s : MachineState) (pc : s.pc = 4484)
    
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (18+fuel) s coins =
    (do let next ← execute (Trunc.submission.image .opening) fuel (setupState s) coins
        return next.charge 18 0) := by
  apply execute_unit_steps (states := blockPrefix setupOps s)
  intro i bound
  refine ⟨.base ((setupOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply openingFetch _ (97+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, setupOps, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> first | rfl | simp [blockPrefix, setupOps, ordinaryStep, memoryArgumentsValid,
      memAccess, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      signExtend12] at *
  · interval_cases i <;> rfl

theorem headRun (s : MachineState) (pc : s.pc = 4556)
    (ok : accessValid (s.getReg .x24 + signExtend12 4088) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (11+fuel) s coins =
    (do let next ← execute (Trunc.submission.image .opening) fuel (headState s) coins
        return next.charge 11 0) := by
  apply execute_unit_steps (states := blockPrefix headOps s)
  intro i bound
  refine ⟨.base ((headOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply openingFetch _ (115+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, headOps, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i
    · rfl
    · have valid : memoryArgumentsValid (blockPrefix headOps s 1) (.LD .x20 .x24 0) = true := by
        change accessValid ((s.getReg .x24 + signExtend12 4088) + 0) 8 = true
        simpa using ok
      change (if memoryArgumentsValid (blockPrefix headOps s 1) (.LD .x20 .x24 0) then some _ else none) = _
      rw [valid]; rfl
    all_goals rfl
  · interval_cases i <;> rfl

theorem finishRun (s : MachineState) (pc : s.pc = 4640)
    
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (5+fuel) s coins =
    (do let next ← execute (Trunc.submission.image .opening) fuel (finishState s) coins
        return next.charge 5 0) := by
  apply execute_unit_steps (states := blockPrefix finishOps s)
  intro i bound
  refine ⟨.base ((finishOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply openingFetch _ (136+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, finishOps, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> first | rfl | simp [blockPrefix, finishOps, ordinaryStep, memoryArgumentsValid,
      memAccess, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      signExtend12] at *
  · interval_cases i <;> rfl

theorem copyRun (state : MachineState) 
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 126))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .opening) (8 + fuel) state allowCoins =
      (do let result ← execute (Trunc.submission.image .opening) fuel
            (openingCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := openingCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply openingFetch _ (126 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingCopyPrefix, openingCopyInstructions, execInstrBr, pc,
          MachineState.setPC]
    · interval_cases i <;> rfl
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

end CommitGolfCandidate.Trunc.Open
