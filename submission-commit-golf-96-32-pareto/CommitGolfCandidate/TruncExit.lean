import CommitGolfCandidate.TruncFetch
import CommitGolfCandidate.CommitParents
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
private theorem exitFetch (s : MachineState) (i : Nat) (op : Instr) (bound : 785≤ i ∧ i<796)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i))
    (decoded : ((CommitGolfCandidate.submission.image .commit).code[i]?).bind decodeInstruction=some (.base op)) :
    fetch (submission.image .commit) s=some (.base op) :=
  fetchAt _ s i op (by omega) pc (by rw [originalWord i bound.2 (by omega) (by omega) (by omega)];exact decoded)
private def commitRootCopyInstructions : List Instr :=
  [.LD .x6 .x9 32, .SD .x26 .x6 0,
   .LD .x6 .x9 40, .SD .x26 .x6 8,
   .LD .x6 .x9 48, .SD .x26 .x6 16,
   .LD .x6 .x9 56, .SD .x26 .x6 24]

private def commitRootCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitRootCopyInstructions.take count).foldl execInstrBr state


theorem commit_root_copy_expansion (state : MachineState) :
    commitRootCopyState state =
      ([.LD .x6 .x9 32, .SD .x26 .x6 0, .LD .x6 .x9 40, .SD .x26 .x6 8,
        .LD .x6 .x9 48, .SD .x26 .x6 16, .LD .x6 .x9 56, .SD .x26 .x6 24] :
        List Instr).foldl execInstrBr state := rfl

private theorem root_copy_prefix_reg (state : MachineState) (count : Nat) (hc : count ≤ 8)
    (reg : Reg) (n6 : reg ≠ .x6) :
    (commitRootCopyPrefix state count).getReg reg = state.getReg reg := by
  have memReg (s : MachineState) (a v : Word) (r : Reg) :
      (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl
  interval_cases count <;>
    simp only [commitRootCopyPrefix, commitRootCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memReg, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n6)]


set_option maxHeartbeats 1600000 in
theorem commit_root_copy (state : MachineState) (pc : state.pc = 7236)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitRootCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := commitRootCopyPrefix state)
  intro i hi
  refine ⟨.base ((commitRootCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply exitFetch _ (785 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitRootCopyPrefix, commitRootCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · have hf := commit_filtered_epilogue i (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · have r9 := root_copy_prefix_reg state i (by omega) .x9 (by decide)
    have r26 := root_copy_prefix_reg state i (by omega) .x26 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitRootCopyPrefix state i)
        ((commitRootCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp (config := { decide := true }) only [commitRootCopyInstructions,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          memoryArgumentsValid, memAccess, signExtend12, r9, r26] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitRootCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem commit_exit (state : MachineState) (pc : state.pc = 7268) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 7272
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply exitFetch _ 793 _ (by decide) pc
    rw [commit_code_word_at _ _ (commit_filtered_epilogue 8 (by decide))]; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply exitFetch _ 794 _ (by decide) rfl
    rw [commit_code_word_at _ _ (commit_filtered_epilogue 9 (by decide))]; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply exitFetch _ 795 _ (by decide) rfl
    rw [commit_code_word_at _ _ (commit_filtered_epilogue 10 (by decide))]; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, MachineState.getReg]
  have s1 : ordinaryStep next (.base (.ADDI .x10 .x0 0)) = some (commitExitState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, commitExitState, MachineState.getReg, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, instructionCycles, bind_assoc, pure_bind]
  simp [commitExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC, Execution.charge]


end CommitGolfCandidate.Trunc
