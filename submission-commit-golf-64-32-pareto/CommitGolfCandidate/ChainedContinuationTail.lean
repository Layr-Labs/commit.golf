import CommitGolfCandidate.ChainedContinuationFrame

/-! The loop tail advances its domain counter and branches after each full reply. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem tail_prefix_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base+40)
    (valid : accessValid (s.getReg .x10+32) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (4+fuel) s coins =
      (do let result ← execute image fuel (ordinaryPrefix s 10 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := ordinaryPrefix s 10)
  intro i inside
  refine ⟨.base (continuationOp (10+i)),?_,?_,?_⟩
  · apply code ⟨10+i,by omega⟩
    interval_cases i <;>
      simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,pc,BitVec.add_assoc]
  · have rawValid : accessValid (s.regs .x10+32) 8 = true := valid
    interval_cases i <;>
      simp [ordinaryPrefix,continuationOps,continuationOp,ordinaryStep,memoryArgumentsValid,memAccess,
        execInstrBr,MachineState.setPC,MachineState.getReg,MachineState.setReg,MachineState.setMem]
    all_goals exact rawValid
  · interval_cases i <;> rfl

def tailAfter (s : MachineState) : MachineState :=
  execInstrBr (ordinaryPrefix s 10 4) (.BNE .x18 .x0 8172)

private theorem branch_execution (image : Image) (s : MachineState) (fuel : Nat) (coins : Bool)
    (fetched : fetch image s = some (.base (.BNE .x18 .x0 8172))) :
    execute image (fuel+1) s coins =
      (do let result ← execute image fuel (execInstrBr s (.BNE .x18 .x0 8172)) coins
          return result.charge 1 0) := by
  exact execute_ordinary_step image _ _ _ fuel coins fetched rfl

theorem tail_prefix_pc (s : MachineState) : (ordinaryPrefix s 10 4).pc = s.pc+16 := by
  simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem tail_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base+40)
    (valid : accessValid (s.getReg .x10+32) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (5+fuel) s coins =
      (do let result ← execute image fuel (tailAfter s) coins
          return result.charge 5 0) := by
  rw [show 5+fuel = 4+(fuel+1) by omega,tail_prefix_execution image base code s pc valid]
  have fetched : fetch image (ordinaryPrefix s 10 4) = some (.base (.BNE .x18 .x0 8172)) := by
    apply code ⟨14,by decide⟩
    rw [tail_prefix_pc,pc,BitVec.add_assoc]
    rfl
  rw [branch_execution image _ fuel coins fetched]
  simp only [tailAfter]
  simp [Execution.charge,← Nat.add_assoc]

private theorem branch_register (s : MachineState) (a b reg : Reg) (offset : BitVec 13) :
    (execInstrBr s (.BNE a b offset)).getReg reg = s.getReg reg := by
  change (if s.getReg a != s.getReg b then s.setPC (s.pc+signExtend13 offset)
    else s.setPC (s.pc+4)).getReg reg = _
  split <;> rfl

private theorem branch_pc (s : MachineState) :
    (execInstrBr s (.BNE .x18 .x0 8172)).pc =
      if s.getReg .x18 != (0 : Word) then s.pc+signExtend13 8172 else s.pc+4 := by
  change (if s.getReg .x18 != (0 : Word) then s.setPC (s.pc+signExtend13 8172)
    else s.setPC (s.pc+4)).pc = _
  split <;> rfl

private theorem branch_memory (s : MachineState) (query : Word) :
    (execInstrBr s (.BNE .x18 .x0 8172)).getMem query = s.getMem query := by
  by_cases taken : s.getReg .x18 != (0 : Word)
  · have step : execInstrBr s (.BNE .x18 .x0 8172) = s.setPC (s.pc+signExtend13 8172) := by
      exact ite_eq_left taken
    rw [step]
    exact MachineState.getMem_setPC
  · have step : execInstrBr s (.BNE .x18 .x0 8172) = s.setPC (s.pc+4) := by
      exact ite_eq_right taken
    rw [step]
    exact MachineState.getMem_setPC

theorem tail_memory_outside (s : MachineState) (query : Word)
    (outside : query ≠ s.getReg .x10+signExtend12 32) :
    (tailAfter s).getMem query = s.getMem query := by
  rw [tailAfter,branch_memory]
  change (execInstrBr (ordinaryPrefix s 10 3) (.ADDI .x18 .x18 4095)).getMem query = _
  simp only [execInstrBr,MachineState.getMem_setPC,MachineState.getMem_setReg]
  change (execInstrBr (ordinaryPrefix s 10 2) (.SD .x10 .x29 32)).getMem query = _
  rw [word_store_frame]
  · rfl
  · exact outside

theorem tail_low_word (s : MachineState) (i : Fin 4) :
    (tailAfter s).getMem (s.getReg .x10+BitVec.ofNat 64 (8*i.val)) =
      s.getMem (s.getReg .x10+BitVec.ofNat 64 (8*i.val)) := by
  apply tail_memory_outside
  intro same
  have different : ∀ j : Fin 4, BitVec.ofNat 64 (8*j.val) ≠ signExtend12 32 := by decide +kernel
  exact different i ((BitVec.add_right_inj _).mp same)

theorem tail_tag (s : MachineState) :
    (tailAfter s).getMem (s.getReg .x10+32) = s.getMem (s.getReg .x10+32)+1 := by
  rw [tailAfter,branch_memory]
  change (execInstrBr (ordinaryPrefix s 10 3) (.ADDI .x18 .x18 4095)).getMem _ = _
  simp only [execInstrBr,MachineState.getMem_setPC,MachineState.getMem_setReg]
  change ((ordinaryPrefix s 10 2).setMem (s.getReg .x10+32)
    ((ordinaryPrefix s 10 2).getReg .x29)).getMem (s.getReg .x10+32) = _
  rw [MachineState.getMem_setMem_eq]
  rfl

theorem tail_register (s : MachineState) (reg : Reg) (not29 : reg ≠ .x29) (not18 : reg ≠ .x18) :
    (tailAfter s).getReg reg = s.getReg reg := by
  rw [tailAfter]
  rw [branch_register]
  cases reg <;>
    simp_all [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,MachineState.getReg,
      MachineState.setReg,MachineState.setMem]

theorem tail_counter (s : MachineState) (remaining : Nat) (small : remaining < 8)
    (counter : s.getReg .x18 = BitVec.ofNat 64 (remaining+1)) :
    (tailAfter s).getReg .x18 = BitVec.ofNat 64 remaining := by
  rw [tailAfter]
  rw [branch_register]
  change s.getReg .x18+signExtend12 4095 = _
  rw [counter]
  interval_cases remaining <;> rfl

theorem tail_pc (s : MachineState) (base : Word) (pc : s.pc = base+40)
    (remaining : Nat) (small : remaining < 8)
    (counter : s.getReg .x18 = BitVec.ofNat 64 (remaining+1)) :
    (tailAfter s).pc = if remaining = 0 then base+60 else base+36 := by
  have cnt : (ordinaryPrefix s 10 4).getReg .x18 = BitVec.ofNat 64 remaining := by
    change s.getReg .x18+signExtend12 4095 = _
    rw [counter]
    interval_cases remaining <;> rfl
  have here : (ordinaryPrefix s 10 4).pc = base+56 := by
    simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,pc,BitVec.add_assoc]
  rw [tailAfter]
  rw [branch_pc,cnt,here]
  interval_cases remaining <;> simp [BitVec.add_assoc]
  all_goals rfl

end CommitGolfCandidate.Chained.Native
