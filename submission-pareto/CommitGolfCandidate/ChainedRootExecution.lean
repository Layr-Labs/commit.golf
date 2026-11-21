import CommitGolfCandidate.ChainedParentLevels

/-! Delivered root copying and successful halt, without the legacy parent image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
attribute [local irreducible] execute

def chainedRootPrefix (s : MachineState) (count : Nat) : MachineState :=
  (parentRootOps.take count).foldl execInstrBr s

theorem chained_root_prefix_pc (s : MachineState) (pc : s.pc = 186568) (i : Nat) (inside : i < 11) :
    (chainedRootPrefix s i).pc = BitVec.ofNat 64 (186568+4*i) := by
  interval_cases i <;>
    simp only [chainedRootPrefix,parentRootOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl

private theorem chained_root_fetch (s : MachineState) (i : Fin 11)
    (pc : s.pc = BitVec.ofNat 64 (186568+4*i.val)) :
    fetch chainedCommitImage s = some (.base ((parentRootOps[i.val]?).getD .ECALL)) := by
  have here : s.pc = (184628 : Word)+BitVec.ofNat 64 (4*(485+i.val)) := by
    rw [pc]
    change BitVec.ofNat 64 (186568+4*i.val) = BitVec.ofNat 64 184628+BitVec.ofNat 64 (4*(485+i.val))
    rw [←BitVec.ofNat_add]
    congr 1
    omega
  have opEq : chainedParentOp (485+i.val) = (parentRootOps[i.val]?).getD .ECALL := by
    fin_cases i <;> rfl
  simpa only [opEq] using chained_parent_at ⟨485+i.val,by have := i.isLt; omega⟩ s here

private theorem chained_root_access (s : MachineState) (heap : s.getReg .x9 = 4294971424)
    (out : s.getReg .x8 = 4294971392) (i : Nat) (inside : i < 10) :
    memoryArgumentsValid (chainedRootPrefix s i) ((parentRootOps[i]?).getD .EBREAK) = true := by
  interval_cases i
  · change accessValid (s.getReg .x9+32) 8 = true; rw [heap]; decide
  · change accessValid (s.getReg .x8+0) 8 = true; rw [out]; decide
  · change accessValid (s.getReg .x9+40) 8 = true; rw [heap]; decide
  · change accessValid (s.getReg .x8+8) 8 = true; rw [out]; decide
  · change accessValid (s.getReg .x9+48) 8 = true; rw [heap]; decide
  · change accessValid (s.getReg .x8+16) 8 = true; rw [out]; decide
  · change accessValid (s.getReg .x9+56) 8 = true; rw [heap]; decide
  · change accessValid (s.getReg .x8+24) 8 = true; rw [out]; decide
  · rfl
  · rfl

theorem chained_root_execution (s : MachineState) (pc : s.pc = 186568)
    (heap : s.getReg .x9 = 4294971424) (out : s.getReg .x8 = 4294971392) (fuel : Nat) :
    execute chainedCommitImage (11+fuel) s true = pure ⟨.success,chainedRootPrefix s 10,11,0⟩ := by
  have run (left : Nat) : execute chainedCommitImage (10+left) s true =
      (do let result ← execute chainedCommitImage left (chainedRootPrefix s 10) true
          return result.charge 10 0) := by
    apply execute_unit_steps (states := chainedRootPrefix s)
    intro i inside
    refine ⟨.base ((parentRootOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · have fetched := chained_root_fetch (chainedRootPrefix s i) ⟨i,by omega⟩ (chained_root_prefix_pc s pc i (by omega))
      interval_cases i <;> exact fetched
    · have access := chained_root_access s heap out i inside
      interval_cases i <;>
        simp only [parentRootOps,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at access ⊢ <;>
        simp only [ordinaryStep,access,↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  have fetched := chained_root_fetch (chainedRootPrefix s 10) ⟨10,by decide⟩ (chained_root_prefix_pc s pc 10 (by decide))
  have halt : (chainedRootPrefix s 10).getReg .x5 = 1 := rfl
  have success : (chainedRootPrefix s 10).getReg .x10 = 0 := rfl
  rw [show 11+fuel = 10+(fuel+1) by omega,run]
  unfold execute
  rw [fetched]
  simp only [halt,success]
  rfl

end CommitGolfCandidate.Chained.Native
