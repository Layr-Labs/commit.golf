import CommitGolfCandidate.PairImage
import CommitGolfCandidate.Opening

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 500000
set_option maxRecDepth 12000

theorem opFetch (s : MachineState) (i : Nat) (op : Instr) (hi : i < 142)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*i))
    (decoded : ((submission.image .opening).code[i]?).bind decodeInstruction = some (.base op)) :
    fetch (submission.image .opening) s = some (.base op) := by
  have h : s.pc.toNat = 4096+4*i := by rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  rw [fetch, h, if_pos (by omega), show (4096+4*i-4096)/4=i by omega]
  cases he : (submission.image .opening).code[i]? <;> simpa [he] using decoded

def blockPrefix (ops : List Instr) (s : MachineState) (i : Nat) : MachineState :=
  (ops.take i).foldl execInstrBr s

def setupOps : List Instr :=
  [.ADDI .x24 .x0 1536, .SLLI .x24 .x24 11, .ADDI .x24 .x24 2, .SLLI .x24 .x24 11, .ADDI .x24 .x24 1056, .ADDI .x18 .x0 1, .SLLI .x18 .x18 11, .ADDI .x18 .x18 544, .SLLI .x18 .x18 11, .ADDI .x18 .x18 35, .SLLI .x18 .x18 11, .ADDI .x18 .x18 32, .ADDI .x19 .x0 1024, .SLLI .x19 .x19 11, .ADDI .x19 .x19 8, .SLLI .x19 .x19 11, .ADDI .x19 .x19 32, .ADDI .x28 .x0 128]

def setupState (s : MachineState) : MachineState := blockPrefix setupOps s 18

theorem setupRun (s : MachineState) (pc : s.pc = 4484)
    
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .opening) (18+fuel) s coins =
    (do let next ← execute (submission.image .opening) fuel (setupState s) coins
        return next.charge 18 0) := by
  apply execute_unit_steps (states := blockPrefix setupOps s)
  intro i bound
  refine ⟨.base ((setupOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opFetch _ (97+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, setupOps, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> first | rfl | simp [blockPrefix, setupOps, ordinaryStep, memoryArgumentsValid,
      memAccess, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      signExtend12] at *
  · interval_cases i <;> rfl

def headOps : List Instr :=
  [.ADDI .x24 .x24 4088, .LD .x20 .x24 0, .SRLI .x20 .x20 16, .ANDI .x20 .x20 255, .XORI .x7 .x20 1, .SRLI .x6 .x20 1, .ADD .x7 .x7 .x6, .SLLI .x7 .x7 5, .ADD .x23 .x19 .x7, .SLLI .x6 .x6 5, .ADD .x25 .x18 .x6]

def headState (s : MachineState) : MachineState := blockPrefix headOps s 11

theorem headRun (s : MachineState) (pc : s.pc = 4556)
    (ok : accessValid (s.getReg .x24 + signExtend12 4088) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .opening) (11+fuel) s coins =
    (do let next ← execute (submission.image .opening) fuel (headState s) coins
        return next.charge 11 0) := by
  apply execute_unit_steps (states := blockPrefix headOps s)
  intro i bound
  refine ⟨.base ((headOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opFetch _ (115+i) _ (by omega)
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

def finishOps : List Instr :=
  [.ADDI .x11 .x0 35, .SLLI .x11 .x11 11, .ADDI .x11 .x11 0, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0]

def finishState (s : MachineState) : MachineState := blockPrefix finishOps s 5

theorem finishRun (s : MachineState) (pc : s.pc = 4640)
    
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .opening) (5+fuel) s coins =
    (do let next ← execute (submission.image .opening) fuel (finishState s) coins
        return next.charge 5 0) := by
  apply execute_unit_steps (states := blockPrefix finishOps s)
  intro i bound
  refine ⟨.base ((finishOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opFetch _ (136+i) _ (by omega)
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
    execute (submission.image .opening) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := openingCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opFetch _ (126 + i) _ (by omega)
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

end CommitGolfCandidate.PairCap
