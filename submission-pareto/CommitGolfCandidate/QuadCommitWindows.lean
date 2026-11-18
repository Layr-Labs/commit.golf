import CommitGolfCandidate.QuadCommitGeometry
import CommitGolfCandidate.TwoPermutationHeapInvariant

/-! The quad permutation input is exactly nine zero words followed by four digest windows. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem quad_input_zero_word (c : Fin 4 → BitVec 256) (k : Fin 9) :
    (quadInput c).extractLsb' (64*k.val) 64=0 := by
  change (((((c 3 ++ c 2) ++ c 1) ++ c 0) ++ (0#576))).extractLsb' (64*k.val) 64=0
  rw [BitVec.extractLsb'_append_eq_of_add_le (by have := k.isLt;omega : 64*k.val+64≤576)]
  simp

theorem quad_input_digest_word (c : Fin 4 → BitVec 256) (slot k : Fin 4) :
    (quadInput c).extractLsb' (64*(9+4*slot.val+k.val)) 64 = (c slot).extractLsb' (64*k.val) 64 := by
  change (((((c 3 ++ c 2) ++ c 1) ++ c 0) ++ (0#576))).extractLsb' (64*(9+4*slot.val+k.val)) 64 = (c slot).extractLsb' (64*k.val) 64
  have hk := k.isLt
  fin_cases slot <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit hbit
  all_goals simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append]
  all_goals simp only [show decide (bit<64)=true by exact decide_eq_true hbit,Bool.true_and]
  all_goals split_ifs <;> first | omega | (congr 1 <;> omega)

/-- Convert the word-memory invariant into the exact 1600-bit syscall input. -/
theorem quad_buffer_eq (s : MachineState) (g : Nat) (c : Fin 4 → BitVec 256)
    (zeros : ∀ k : Fin 9, memoryView s (groupWord g+k.val)=0)
    (leaves : ∀ slot k : Fin 4, memoryView s (leafWord (4*g+slot.val)+k.val)=
      (c slot).extractLsb' (64*k.val) 64) :
    readBuffer s (8*groupWord g) 200=quadInput c := by
  apply aligned_buffer_eq s _ 200 (by decide)
  intro k hk
  by_cases low : k<9
  · rw [zeros ⟨k,low⟩]
    exact (quad_input_zero_word c ⟨k,low⟩).symm
  · let slot : Fin 4 := ⟨(k-9)/4,by omega⟩
    let word : Fin 4 := ⟨(k-9)%4,Nat.mod_lt _ (by decide)⟩
    have offset : 9+4*slot.val+word.val=k := by dsimp [slot,word];omega
    have address : groupWord g+k=leafWord (4*g+slot.val)+word.val := by
      unfold leafWord groupWord
      have hslot := slot.isLt
      omega
    rw [address,leaves]
    have slice := quad_input_digest_word c slot word
    rw [offset] at slice
    exact slice.symm

end TwoPermutationPrototype.Quad.Commit
