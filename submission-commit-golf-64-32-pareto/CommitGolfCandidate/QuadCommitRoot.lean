import CommitGolfCandidate.QuadCommitTreeSetup
import CommitGolfCandidate.TwoPermutationRoot

namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
attribute [local irreducible] image leafCode quadCode quad2Code parentCode decodeInstruction execute

private theorem root_decoded (i : Fin 11) :
    (rootWords[i.val]?).bind decodeInstruction=some (.base (((rootOps++[.ECALL])[i.val]?).getD .EBREAK)) := by
  revert i;decide +kernel

theorem fetch_root (s : MachineState) (i : Nat) (inside : i<11)
    (pc : s.pc=BitVec.ofNat 64 (801952+4*i)) :
    fetch image s=some (.base (((rootOps++[.ECALL])[i]?).getD .EBREAK)) := by
  apply fetch_code_index s (199464+i) (by omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at (parentPrefix++parentCode++parentLatchWords) rootWords []
    (by unfold image parentPrefix quad2Prefix quadPrefix;simp only [List.append_assoc,List.append_nil]) i
    (Nat.lt_of_lt_of_le inside (by decide))
  rw [List.length_append,List.length_append,parent_prefix_length,parent_code_length] at atIndex
  change image.code[199464+i]?=_ at atIndex
  rw [atIndex];exact root_decoded ⟨i,inside⟩

private theorem root_access (s : MachineState) (heap : s.getReg .x9=4294971424)
    (out : s.getReg .x8=4294971392) (i : Nat) (hi : i<10) :
    memoryArgumentsValid (rootPrefix s i) ((rootOps[i]?).getD .EBREAK) = true := by
  interval_cases i
  · change accessValid (s.getReg .x9+32) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+0) 8=true;rw [out];decide
  · change accessValid (s.getReg .x9+40) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+8) 8=true;rw [out];decide
  · change accessValid (s.getReg .x9+48) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+16) 8=true;rw [out];decide
  · change accessValid (s.getReg .x9+56) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+24) 8=true;rw [out];decide
  · rfl
  · rfl

theorem execute_root (state : MachineState) (pc : state.pc=801952)
    (heap : state.getReg .x9=4294971424) (out : state.getReg .x8=4294971392) (fuel : Nat) :
    execute image (11+fuel) state true = pure ⟨.success,rootPrefix state 10,11,0⟩ := by
  have prefixPC (i : Nat) (inside : i<11) :
      (rootPrefix state i).pc=BitVec.ofNat 64 (801952+4*i) := by
    interval_cases i <;>
      simp only [rootPrefix,rootOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
  have run (left : Nat) :
      execute image (10+left) state true =
        (do let result ← execute image left (rootPrefix state 10) true
            return result.charge 10 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := rootPrefix state)
    intro i inside
    refine ⟨.base ((rootOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · have fetched := fetch_root (rootPrefix state i) i (by omega) (prefixPC i (by omega))
      interval_cases i <;> exact fetched
    · have access := root_access state heap out i inside
      interval_cases i <;>
        simp only [rootOps,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at access ⊢ <;>
        simp only [ordinaryStep,access,↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch image (rootPrefix state 10)=some (.base .ECALL) :=
    fetch_root (rootPrefix state 10) 10 (by decide) (prefixPC 10 (by decide))
  have halt : (rootPrefix state 10).getReg .x5=1 := rfl
  have success : (rootPrefix state 10).getReg .x10=0 := rfl
  rw [show 11+fuel=10+(fuel+1) by omega,run,execute,fetched]
  simp only [halt,success]
  rfl

end TwoPermutationPrototype.Quad.Commit
