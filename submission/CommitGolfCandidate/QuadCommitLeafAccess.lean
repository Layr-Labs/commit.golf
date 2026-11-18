import CommitGolfCandidate.QuadCommitLeafFrame

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000


theorem first_accesses (s : MachineState) (slot : Fin 4096) (i : Nat) (hi : i<1) :
    memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i)=true := by interval_cases i <;> rfl

private theorem second_accesses_core (prev : MachineState) (slot : Fin 4096)
    (start salts i : Nat) (bound : start+37≤2^33) (nonceBound : salts+256≤2^33)
    (tag : prev.getReg .x10+56=wordAddress (start+12)) (nonce : prev.getReg .x22+nonceOffset slot=wordAddress salts)
    (hi : i<7) : memoryArgumentsValid (secondPrefix prev slot i) (leafInstr slot (2+i))=true := by
  interval_cases i
  · rfl
  · change accessValid (prev.getReg .x10+56+0) 8=true
    rw [tag];exact leaf_word_access _ 0 (by omega)
  · change accessValid (prev.getReg .x22+signExtend12 (BitVec.ofNat 12 (16*(slot.val%256)))) 8=true
    rw [nonce_offset_eq,nonce];simpa using leaf_word_access salts 0 (by omega)
  · change accessValid (prev.getReg .x10+56+8) 8=true
    rw [tag];exact leaf_word_access _ 1 (by omega)
  · change accessValid (prev.getReg .x22+signExtend12 (BitVec.ofNat 12 (16*(slot.val%256)+8))) 8=true
    rw [nonce_offset_succ,←BitVec.add_assoc,nonce];exact leaf_word_access salts 1 (by omega)
  · change accessValid (prev.getReg .x10+56+16) 8=true
    rw [tag];exact leaf_word_access _ 2 (by omega)
  · rfl

theorem second_accesses (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (i : Nat) (hi : i<7) :
    let prev := repliedA s slot start a
    memoryArgumentsValid (secondPrefix prev slot i) (leafInstr slot (2+i))=true := by
  let prev := repliedA s slot start a
  have bound := ready.sourceBound
  have nonceBound := ready.nonceBound
  have tag : prev.getReg .x10+56=wordAddress (start+12) := by
    rw [show prev.getReg .x10=wordAddress (start+5) from after_a_input_cursor _ _ _ _ _ _ ready _]
    exact (wordAddress_add (start+5) 7).symm
  have nonce : prev.getReg .x22+nonceOffset slot=wordAddress salts := by
    rw [after_a_reg _ _ _ _ _ (by decide) (by decide)];exact ready.nonces
  exact second_accesses_core prev slot start salts i bound nonceBound tag nonce hi

end TwoPermutationPrototype.Quad.Commit.Leaves
