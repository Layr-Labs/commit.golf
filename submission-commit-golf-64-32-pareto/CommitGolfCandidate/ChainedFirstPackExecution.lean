import CommitGolfCandidate.ChainedFirstPackCode

/-! Checked native execution of the child-packing fragment. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

private theorem prefix_succ (s : MachineState) (count : Nat) (bound : count < 31) :
    firstPackPrefix s (count+1) = execInstrBr (firstPackPrefix s count) (firstPackOp count) := by
  interval_cases count <;> rfl

private theorem step_bases (s : MachineState) (i : Fin 31) :
    (execInstrBr s (firstPackOp i.val)).getReg .x10 = s.getReg .x10 ∧
    (execInstrBr s (firstPackOp i.val)).getReg .x14 = s.getReg .x14 := by
  fin_cases i <;> constructor <;> rfl

theorem first_pack_bases (s : MachineState) (count : Nat) (bound : count ≤ 31) :
    (firstPackPrefix s count).getReg .x10 = s.getReg .x10 ∧
    (firstPackPrefix s count).getReg .x14 = s.getReg .x14 := by
  induction count with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step := step_bases (firstPackPrefix s count) ⟨count,by omega⟩
    exact ⟨step.1.trans (ih (by omega)).1,step.2.trans (ih (by omega)).2⟩

private theorem step_pc (s : MachineState) (i : Fin 30) :
    (execInstrBr s (firstPackOp i.val)).pc = s.pc+4 := by
  fin_cases i <;> rfl

theorem first_pack_pc (s : MachineState) (count : Nat) (bound : count ≤ 30) :
    (firstPackPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [firstPackPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step := step_pc (firstPackPrefix s count) ⟨count,by omega⟩
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1

private theorem ordinary (s : MachineState) (i : Fin 31)
    (source target : Word) (src : s.getReg .x14 = source) (dst : s.getReg .x10 = target)
    (inputs : ∀ k : Fin 8, accessValid (source+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (outputs : ∀ k : Fin 8, accessValid (target+BitVec.ofNat 64 (8*k.val)) 8 = true) :
    ordinaryStep s (.base (firstPackOp i.val)) = some (execInstrBr s (firstPackOp i.val)) := by
  fin_cases i <;>
    dsimp only [firstPackOp,firstPackOps] <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,src,dst]
  all_goals first
    | have valid := inputs (0 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (1 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (2 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (3 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (4 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (5 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (6 : Fin 8); simpa [signExtend12] using valid
    | have valid := inputs (7 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (0 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (1 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (2 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (3 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (4 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (5 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (6 : Fin 8); simpa [signExtend12] using valid
    | have valid := outputs (7 : Fin 8); simpa [signExtend12] using valid

theorem first_pack_execution (image : Image) (base : Word) (code : FirstPackAt image base)
    (s : MachineState) (pc : s.pc = base)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (outputs : ∀ k : Fin 8, accessValid (s.getReg .x10+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (31+fuel) s coins =
      (do let result ← execute image fuel (firstPackPrefix s 31) coins
          return result.charge 31 0) := by
  apply execute_unit_steps (states := firstPackPrefix s)
  intro i inside
  refine ⟨.base (firstPackOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [first_pack_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    exact ordinary _ ⟨i,inside⟩ _ _ (first_pack_bases s i (by omega)).2
      (first_pack_bases s i (by omega)).1 inputs outputs
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native
