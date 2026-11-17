import CommitGolfCandidate.TwoPermutationWideLeafMemory

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
def leafPC (slot : Fin 256) (offset : Nat) : Word := wideLeafPC slot.val offset
def leafInstr (slot : Fin 256) (offset : Nat) : Instr := ((leafInstructions slot)[offset]?).getD .EBREAK
theorem fetch_leaf (slot : Fin 256) (i : Nat) (inside : i<14) (s : MachineState) (pc : s.pc=leafPC slot i) :
    fetch wideCommitImage s=some (.base (leafInstr slot i)) := wide_fetch_leaf slot ⟨i,inside⟩ s pc

theorem leaf_pc_add (slot : Fin 256) (i j : Nat) :
    leafPC slot i + BitVec.ofNat 64 (4*j)=leafPC slot (i+j) := by
  unfold leafPC wideLeafPC
  rw [←BitVec.ofNat_add];congr 1 <;> omega
def firstPrefix (s : MachineState) (slot : Fin 256) (i : Nat) : MachineState :=
  ((firstInstructions slot).take i).foldl execInstrBr s

def secondPrefix (s : MachineState) (slot : Fin 256) (i : Nat) : MachineState :=
  ((secondInstructions slot).take i).foldl execInstrBr s

theorem first_ordinary_run (s : MachineState) (slot : Fin 256) (fuel : Nat) (allowCoins : Bool)
    (pc : s.pc = leafPC slot 0)
    (valid : ∀ i < 8, memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i) = true) :
    execute wideCommitImage (8+fuel) s allowCoins =
      (do let r ← execute wideCommitImage fuel ((firstInstructions slot).foldl execInstrBr s) allowCoins
          return r.charge 8 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := firstPrefix s slot)
  intro i hi
  refine ⟨.base (leafInstr slot i), fetch_leaf slot i (by omega) _ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [firstPrefix,firstInstructions,execInstrBr,MachineState.setPC,pc,
      leafPC,wideLeafPC,BitVec.add_assoc,BitVec.ofNat_add,Nat.add_mul,Nat.mul_add,Nat.add_assoc]
  · have v := valid i hi
    interval_cases i <;>
      simp only [leafInstr,leafInstructions,firstInstructions,List.cons_append,List.nil_append,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at v ⊢ <;>
      simp only [ordinaryStep,v,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem second_ordinary_run (s : MachineState) (slot : Fin 256) (fuel : Nat) (allowCoins : Bool)
    (pc : s.pc = leafPC slot 9)
    (valid : ∀ i < 3, memoryArgumentsValid (secondPrefix s slot i) (leafInstr slot (9+i)) = true) :
    execute wideCommitImage (3+fuel) s allowCoins =
      (do let r ← execute wideCommitImage fuel ((secondInstructions slot).foldl execInstrBr s) allowCoins
          return r.charge 3 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := secondPrefix s slot)
  intro i hi
  refine ⟨.base (leafInstr slot (9+i)), fetch_leaf slot (9+i) (by omega) _ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [secondPrefix,secondInstructions,execInstrBr,MachineState.setPC,pc,
      leafPC,wideLeafPC,BitVec.add_assoc,BitVec.ofNat_add,Nat.add_mul,Nat.mul_add,Nat.add_assoc]
  · have v := valid i hi
    interval_cases i <;>
      simp only [leafInstr,leafInstructions,firstInstructions,secondInstructions,List.cons_append,List.nil_append,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some, Nat.reduceAdd] at v ⊢ <;>
      simp only [ordinaryStep,v,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl


end TwoPermutationPrototype.RV64.WideLeaves
