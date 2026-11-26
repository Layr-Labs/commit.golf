import CommitGolfCandidate.QuadCommitGeometry

deriving instance DecidableEq for CommitGolf.Riscv.Instruction

/-! Fetch helpers for the penta tree phase. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image leafCode levelsCode decodeInstruction

namespace Leaves
theorem leaf_code_word_count : leafCode.length = 45164 := leaf_code_length
end Leaves

theorem repeated_code_at {α : Type} (chunk : List α) (n j k : Nat) (hj : j<n) (hk : k<chunk.length) :
    ((List.replicate n chunk).flatten)[chunk.length*j+k]?=chunk[k]? := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons]
    cases j with
    | zero => simpa only [Nat.mul_zero,Nat.zero_add] using (List.getElem?_append_left hk)
    | succ j =>
      rw [Nat.mul_succ]
      rw [List.getElem?_append_right (by omega)]
      rw [show chunk.length*j+chunk.length+k-chunk.length=chunk.length*j+k by omega]
      exact ih j (by omega)

theorem fetch_code_index (s : MachineState) (index : Nat) (bounded : index<2^32)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*index)) (instruction : Instr)
    (decoded : (image.code[index]?).bind decodeInstruction=some (.base instruction)) :
    fetch image s=some (.base instruction) := by
  have numeric : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    omega
  rw [fetch,numeric,if_pos (by omega),show (4096+4*index-4096)/4=index by omega]
  cases result : image.code[index]? with
  | none => simp [result] at decoded
  | some w => simpa [result] using decoded

theorem code_segment_at (head chunk suffix : List (BitVec 32))
    (code : image.code=head++chunk++suffix) (j : Nat) (inside : j<chunk.length) :
    image.code[head.length+j]?=chunk[j]? := by
  rw [code,List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact List.getElem?_append_left inside

end TwoPermutationPrototype.Quad.Commit
