import CommitGolfCandidate.TwoPermutationWideLeafFrame

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem first_accesses (s : MachineState) (slot : Fin 256) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (i : Nat) (hi : i < 2) :
    memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i) = true := by
  have b := ready.sourceBound
  interval_cases i
  · change accessValid (s.getReg .x10 + 0) 8 = true
    rw [ready.source]; exact leaf_word_access (start+4) 0 (by omega)
  · rfl

theorem second_accesses (s : MachineState) (slot : Fin 256) (start salts : Nat)
    (source : s.getReg .x10 = wordAddress (start+4)) (tape : s.getReg .x22 = wordAddress salts)
    (bound : start + 37 ≤ 2^33) (nb : salts + 256 ≤ 2^33) (i : Nat) (hi : i < 7) :
    memoryArgumentsValid (secondPrefix s slot i) (leafInstr slot (3+i)) = true := by
  have off := nonce_offsets slot
  have src : s.getReg .x10 + 64 = wordAddress (start+12) := by
    rw [source]; exact address_plus _ 8 _ (by omega)
  interval_cases i
  · rfl
  · change accessValid (s.getReg .x10 + 64 + 0) 8 = true
    rw [src]; exact leaf_word_access _ 0 (by omega)
  · change accessValid (s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (16*(slot.val%128)))) 8 = true
    rw [tape,off.1,show 16*(slot.val%128)=8*(2*(slot.val%128)) by omega]
    exact leaf_word_access _ _ (by omega)
  · change accessValid (s.getReg .x10 + 64 + 40) 8 = true
    rw [src]; exact leaf_word_access (start+12) 5 (by omega)
  · change accessValid (s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (16*(slot.val%128)+8))) 8 = true
    rw [tape,off.2,show 16*(slot.val%128)+8=8*(2*(slot.val%128)+1) by omega]
    exact leaf_word_access _ _ (by omega)
  · change accessValid (s.getReg .x10+64+48) 8=true
    rw [src]; exact leaf_word_access (start+12) 6 (by omega)
  · rfl

theorem after_a_control (s : MachineState) (slot : Fin 256) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (a : BitVec 1600) :
    let after := repliedA s slot start a
    after.getReg .x5=0 ∧ after.getReg .x11=200 ∧ after.getReg .x13=1 ∧
    after.getReg .x20=s.getReg .x20 ∧ after.pc=leafPC slot 3 := by
  have ⟨_,_,_,r5,r11,r13,hpc⟩ := first_execution s slot
  simp only [repliedA,CommitGolfCandidate.writeBits_register,preparedA]
  refine ⟨r5.trans ready.selector,r11.trans ready.size,r13.trans ready.primitive,rfl,?_⟩
  change ((firstInstructions slot).foldl execInstrBr s).pc + 4=_
  rw [hpc,pc,BitVec.add_assoc]
  exact leaf_pc_add slot 0 3

end TwoPermutationPrototype.RV64.WideLeaves
