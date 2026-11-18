import CommitGolfCandidate.TwoPermutationPackedLeafFrame

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
private theorem nonce_immediates_table : ∀ slot : Fin 256,
    signExtend12 (BitVec.ofNat 12 (2048+16*slot.val)) = centeredOffset (8*(2*slot.val)) ∧
    signExtend12 (BitVec.ofNat 12 (2048+16*slot.val+8)) = centeredOffset (8*(2*slot.val+1)) := by decide +kernel

private theorem nonce_immediates (slot : Fin 4096) :
    signExtend12 (BitVec.ofNat 12 (2048+16*(slot.val%256))) = centeredOffset (8*(2*(slot.val%256))) ∧
    signExtend12 (BitVec.ofNat 12 (2048+16*(slot.val%256)+8)) = centeredOffset (8*(2*(slot.val%256)+1)) :=
  nonce_immediates_table ⟨slot.val%256, Nat.mod_lt _ (by decide)⟩

theorem first_accesses (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (i : Nat) (hi : i < 8) :
    memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i) = true := by
  have a := ready.sourceBound
  have b := ready.nonceBound
  have u := slot.isLt
  interval_cases i
  · change accessValid (s.getReg .x10 + 0) 8 = true
    rw [ready.source]; exact leaf_word_access start 0 (by omega)
  · change accessValid (s.getReg .x10 + 8) 8 = true
    rw [ready.source]; exact leaf_word_access start 1 (by omega)
  · change accessValid (s.getReg .x10 + 16) 8 = true
    rw [ready.source]; exact leaf_word_access start 2 (by omega)
  · change accessValid (s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (2048+16*(slot.val%256)))) 8 = true
    rw [ready.nonces,(nonce_immediates slot).1,centered_add];exact leaf_word_access _ _ (by omega)
  · change accessValid (s.getReg .x10 + 24) 8 = true
    rw [ready.source]; exact leaf_word_access start 3 (by omega)
  · change accessValid (s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (2048+16*(slot.val%256)+8))) 8 = true
    rw [ready.nonces,(nonce_immediates slot).2,centered_add];exact leaf_word_access _ _ (by omega)
  · change accessValid (s.getReg .x10 + 32) 8 = true
    rw [ready.source]; exact leaf_word_access start 4 (by omega)
  · rfl

theorem second_accesses (s : MachineState) (slot : Fin 4096) (i : Nat) (hi : i<2) :
    memoryArgumentsValid (secondPrefix s slot i) (leafInstr slot (9+i)) = true := by
  interval_cases i <;> rfl

theorem after_a_control (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (a : BitVec 1600) :
    let after := repliedA s slot start a
    after.getReg .x5 = 0 ∧ after.getReg .x11 = 200 ∧ after.getReg .x13 = 1 ∧
      after.getReg .x20 = s.getReg .x20 ∧ after.pc = leafPC slot 9 := by
  obtain ⟨d0,d1⟩ := leaf_nonce_separate _ _ _ _ _ _ ready
  have ⟨_,_,_,r5,r11,r13,hpc⟩ := first_execution s slot d0 d1
  simp only [repliedA,CommitGolfCandidate.writeBits_register,preparedA]
  refine ⟨r5.trans ready.selector,r11.trans ready.size,r13.trans ready.primitive,rfl,?_⟩
  change ((firstInstructions slot).foldl execInstrBr s).pc + 4 = _
  rw [hpc,pc,BitVec.add_assoc]
  exact leaf_pc_add slot 0 9


end TwoPermutationPrototype.RV64.PackedLeaves
