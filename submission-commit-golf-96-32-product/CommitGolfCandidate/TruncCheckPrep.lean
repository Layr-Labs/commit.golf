import CommitGolfCandidate.PairPath
import CommitGolfCandidate.TruncCheckLeaf

namespace CommitGolfCandidate.Trunc.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
open CommitGolfCandidate.Late.Check.Normal
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000

theorem rec_check_path_copy (state : MachineState) (start : Nat)
    (location : start = 29 ∨ start = 37 ∨ start = 46 )
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * start))
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (rec_pathCopySource start) + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (8 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (Late.Check.Normal.checkPathCopyState state start) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := rec_pathCopyPrefix state start)
  intro i hi
  refine ⟨.base (((rec_pathCopyInstructions start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply sharedFetch _ (192 + start + i) _ (by unfold untouched; rcases location with rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;>
        simp [rec_pathCopyPrefix, rec_pathCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := rec_path_copy_register state start i (by omega) (rec_pathCopySource start)
      (by rcases location with rfl | rfl | rfl <;> decide)
    have scratchReg := (rec_path_copy_register state start i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (rec_pathCopyPrefix state start i)
        (((rec_pathCopyInstructions start)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [rec_pathCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          (rcases location with rfl | rfl | rfl <;> rfl)
    interval_cases i <;>
      simp only [rec_pathCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem rec_check_path_branch (state : MachineState) (pc : state.pc = 4972)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (2 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (rec_checkPathBranchState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC 4976
  have f0 : fetch (Trunc.wireImage true) state = some (.base (.ANDI .x7 .x20 1)) := by
    apply sharedFetch _ 219 _ (by unfold untouched; decide) pc; rfl
  have f1 : fetch (Trunc.wireImage true) next = some (.base (.BEQ .x7 .x0 72)) := by
    apply sharedFetch _ 220 _ (by unfold untouched; decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ANDI .x7 .x20 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.BEQ .x7 .x0 72)) = some (rec_checkPathBranchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, rec_checkPathBranchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem rec_path_jump (state : MachineState) (pc : state.pc = 5044)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (1 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (state.setPC 5080) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (Trunc.wireImage true) state = some (.base (.JAL .x0 36)) := by
    apply sharedFetch _ 237 _ (by unfold untouched; decide) pc; rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 36)) = some (state.setPC 5080) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setReg, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem rec_check_path_preparation (state : MachineState) (pc : state.pc = 4972)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (rec_checkPathPreparedState state) allowCoins
          return result.charge (Late.Check.Normal.pathPreparationSteps (state.getReg .x20)) 0) := by
  let branched := rec_checkPathBranchState state
  have scratchB : branched.getReg .x21 = 256 :=
    (rec_path_branch_register state .x21 (by decide)).trans scratch
  have sourceB (word : Fin 4) :
      accessValid (branched.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [rec_path_branch_register state .x25 (by decide)]
    exact sourceValid word
  by_cases even : state.getReg .x20 &&& 1 = 0
  · have branchPC : branched.pc = 5048 := if_pos even
    have source : ∀ word : Fin 4,
        accessValid (branched.getReg (rec_pathCopySource 46) + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceB
    simp only [Late.Check.Normal.pathPreparationSteps, even, if_true, rec_checkPathPreparedState]
    rw [show 10 + fuel = 2 + (8 + fuel) by omega, rec_check_path_branch state pc,
      rec_check_path_copy branched 46 (Or.inr (Or.inr rfl)) branchPC scratchB source]
    simp [Execution.charge, branched, ← Nat.add_assoc]
  · have branchPC : branched.pc = 4980 := if_neg even
    have source : ∀ word : Fin 4,
        accessValid (branched.getReg (rec_pathCopySource 29) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
      intro ⟨word, bounded⟩
      change accessValid (branched.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true
      rw [scratchB]
      interval_cases word <;> rfl
    let moved := Late.Check.Normal.checkPathCopyState branched 29
    have movedPC : moved.pc = 5012 := by rw [Late.Check.Normal.check_path_copy_pc, branchPC]; rfl
    have movedScratch : moved.getReg .x21 = 256 :=
      (Late.Check.Normal.check_path_copy_register branched 29 .x21 (by decide)).trans scratchB
    have movedSource (word : Fin 4) :
        accessValid (moved.getReg (rec_pathCopySource 37) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
      change accessValid (moved.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true
      rw [Late.Check.Normal.check_path_copy_register branched 29 .x25 (by decide)]
      exact sourceB word
    have jumpPC : (Late.Check.Normal.checkPathCopyState moved 37).pc = 5044 := by
      rw [Late.Check.Normal.check_path_copy_pc, movedPC]; rfl
    simp only [Late.Check.Normal.pathPreparationSteps, even, if_false, rec_checkPathPreparedState]
    rw [show 19 + fuel = 2 + (8 + (8 + (1 + fuel))) by omega, rec_check_path_branch state pc,
      rec_check_path_copy branched 29 (Or.inl rfl) branchPC scratchB source,
      rec_check_path_copy moved 37 (Or.inr (Or.inl rfl)) movedPC movedScratch movedSource,
      rec_path_jump _ jumpPC]
    simp [Execution.charge, branched, moved, ← Nat.add_assoc]
end CommitGolfCandidate.Trunc.Check
