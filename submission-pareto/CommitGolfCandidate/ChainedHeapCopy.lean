import CommitGolfCandidate.ChainedLevelCall

/-! The delivered four-word heap copy and its register/memory frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def copyOps : List Instr := [
  .LD .x20 .x10 0,.SD .x7 .x20 0,.LD .x20 .x10 8,.SD .x7 .x20 8,
  .LD .x20 .x10 16,.SD .x7 .x20 16,.LD .x20 .x10 24,.SD .x7 .x20 24]

def copyOp (index : Nat) : Instr := (copyOps[index]?).getD .EBREAK
def copyPrefix (s : MachineState) (count : Nat) : MachineState := (copyOps.take count).foldl execInstrBr s
def copyPC (h : Height) : Word := 184628+BitVec.ofNat 64 (4*(13+20*h.val))

theorem copy_pc_eq (h : Height) : copyPC h = levelPC h+32 := by fin_cases h <;> rfl

theorem copy_prefix_pc (s : MachineState) (count : Nat) (small : count ≤ 8) :
    (copyPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [copyPrefix,copyOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem copy_bases (s : MachineState) (count : Nat) (small : count ≤ 8) :
    (copyPrefix s count).getReg .x10 = s.getReg .x10 ∧
    (copyPrefix s count).getReg .x7 = s.getReg .x7 := by
  interval_cases count <;> exact ⟨rfl,rfl⟩

theorem copy_register (s : MachineState) (reg : Reg) (kept : reg ≠ .x20) :
    (copyPrefix s 8).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept rfl).elim | rfl

private theorem copy_fetch (h : Height) (i : Fin 8) (s : MachineState)
    (pc : s.pc = 184628+BitVec.ofNat 64 (4*(13+20*h.val+i.val))) :
    fetch chainedCommitImage s = some (.base (copyOp i.val)) := by
  have opEq : chainedParentOp (13+20*h.val+i.val) = copyOp i.val := by
    fin_cases h <;> fin_cases i <;> rfl
  simpa only [opEq] using chained_parent_at ⟨13+20*h.val+i.val,by have := h.isLt; have := i.isLt; omega⟩ s pc

private theorem copy_prefix_succ (s : MachineState) (count : Nat) (small : count < 8) :
    copyPrefix s (count+1) = execInstrBr (copyPrefix s count) (copyOp count) := by
  interval_cases count <;> rfl

private theorem copy_ordinary (s : MachineState) (i : Fin 8) (source target : Word)
    (src : s.getReg .x10 = source) (dst : s.getReg .x7 = target)
    (inputs : ∀ k : Fin 4, accessValid (source+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (outputs : ∀ k : Fin 4, accessValid (target+BitVec.ofNat 64 (8*k.val)) 8 = true) :
    ordinaryStep s (.base (copyOp i.val)) = some (execInstrBr s (copyOp i.val)) := by
  fin_cases i <;> dsimp only [copyOp,copyOps] <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,src,dst]
  all_goals first
    | have valid := inputs (0 : Fin 4); simpa [signExtend12] using valid
    | have valid := inputs (1 : Fin 4); simpa [signExtend12] using valid
    | have valid := inputs (2 : Fin 4); simpa [signExtend12] using valid
    | have valid := inputs (3 : Fin 4); simpa [signExtend12] using valid
    | have valid := outputs (0 : Fin 4); simpa [signExtend12] using valid
    | have valid := outputs (1 : Fin 4); simpa [signExtend12] using valid
    | have valid := outputs (2 : Fin 4); simpa [signExtend12] using valid
    | have valid := outputs (3 : Fin 4); simpa [signExtend12] using valid

theorem copy_execution (s : MachineState) (h : Height) (pc : s.pc = copyPC h)
    (inputs : ∀ k : Fin 4, accessValid (s.getReg .x10+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (outputs : ∀ k : Fin 4, accessValid (s.getReg .x7+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (8+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (copyPrefix s 8) coins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := copyPrefix s)
  intro i inside
  refine ⟨.base (copyOp i),?_,?_,?_⟩
  · apply copy_fetch h ⟨i,inside⟩
    rw [copy_prefix_pc s i (by omega),pc]
    unfold copyPC
    rw [BitVec.add_assoc,←BitVec.ofNat_add,
      show 4*(13+20*h.val)+4*i = 4*(13+20*h.val+i) by omega]
  · rw [copy_prefix_succ s i inside]
    exact copy_ordinary _ ⟨i,inside⟩ _ _ (copy_bases s i (by omega)).1
      (copy_bases s i (by omega)).2 inputs outputs
  · interval_cases i <;> rfl

private theorem copy_step_memory (s : MachineState) (i : Fin 8) (query : Word)
    (outside : ∀ j : Fin 4, query ≠ s.getReg .x7+BitVec.ofNat 64 (8*j.val)) :
    (execInstrBr s (copyOp i.val)).getMem query = s.getMem query := by
  fin_cases i <;> dsimp only [copyOp,copyOps]
  all_goals first | rfl | apply word_store_frame
  all_goals first | exact outside (0 : Fin 4) | exact outside (1 : Fin 4) |
    exact outside (2 : Fin 4) | exact outside (3 : Fin 4)

theorem copy_memory_outside (s : MachineState) (query : Word)
    (outside : ∀ j : Fin 4, query ≠ s.getReg .x7+BitVec.ofNat 64 (8*j.val))
    (count : Nat) (small : count ≤ 8) : (copyPrefix s count).getMem query = s.getMem query := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [copy_prefix_succ s count (by omega),copy_step_memory _ ⟨count,by omega⟩ query]
    · exact ih (by omega)
    · intro j
      rw [(copy_bases s count (by omega)).2]
      exact outside j

end CommitGolfCandidate.Chained.Native
