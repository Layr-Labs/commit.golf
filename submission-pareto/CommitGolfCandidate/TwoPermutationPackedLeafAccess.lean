import CommitGolfCandidate.TwoPermutationPackedLeafFrame

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
private theorem cancel_bias (base disp : Word) :
    (base + 2048) + (-2048 + disp) = base + disp := by
  have inner : (2048 : Word) + (-2048 + disp) = disp := by
    rw [← BitVec.add_assoc, show (2048 : Word) + -2048 = 0 by decide]
    simp
  rw [BitVec.add_assoc, inner]

private theorem nonce_access_addr (salts : Nat) (slot : Fin 4096) :
    (wordAddress salts + 2048) + nonceDisp (slot.val % 256) =
      wordAddress salts + BitVec.ofNat 64 (8 * (2 * (slot.val % 256))) := by
  have mod : (slot.val % 256) % 256 = slot.val % 256 := Nat.mod_mod _ _
  unfold nonceDisp
  rw [mod, cancel_bias]
  refine congrArg (wordAddress salts + ·) ?_
  refine congrArg (BitVec.ofNat 64) ?_
  omega

private theorem nonce_access_addr_hi (salts : Nat) (slot : Fin 4096) :
    (wordAddress salts + 2048) + (nonceDisp (slot.val % 256) + 8) =
      wordAddress salts + BitVec.ofNat 64 (8 * (2 * (slot.val % 256) + 1)) := by
  have mod : (slot.val % 256) % 256 = slot.val % 256 := Nat.mod_mod _ _
  unfold nonceDisp
  rw [mod, ← BitVec.add_assoc, cancel_bias]
  change (wordAddress salts + BitVec.ofNat 64 (16 * (slot.val % 256))) + BitVec.ofNat 64 8 = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine congrArg (wordAddress salts + ·) ?_
  refine congrArg (BitVec.ofNat 64) ?_
  omega


theorem first_accesses (s : MachineState) (slot : Fin 4096) (i : Nat) (hi : i<1) :
    memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i)=true := by interval_cases i <;> rfl

private theorem second_accesses_core (prev : MachineState) (slot : Fin 4096)
    (start salts i : Nat) (bound : start+37≤2^33) (nonceBound : salts+512≤2^33)
    (tag : prev.getReg .x10+56=wordAddress (start+12)) (nonce : prev.getReg .x22=wordAddress salts+2048)
    (hi : i<7) : memoryArgumentsValid (secondPrefix prev slot i) (leafInstr slot (2+i))=true := by
  interval_cases i
  · rfl
  · change accessValid (prev.getReg .x10+56+0) 8=true
    rw [tag];exact leaf_word_access _ 0 (by omega)
  · change accessValid (prev.getReg .x22+signExtend12 (BitVec.ofNat 12 (2048+16*(slot.val%256)))) 8=true
    rw [nonce,(nonce_offsets slot).1,nonce_access_addr salts slot]
    exact leaf_word_access salts (2*(slot.val%256)) (by omega)
  · change accessValid (prev.getReg .x10+56+8) 8=true
    rw [tag];exact leaf_word_access _ 1 (by omega)
  · change accessValid (prev.getReg .x22+signExtend12 (BitVec.ofNat 12 (2048+16*(slot.val%256)+8))) 8=true
    rw [nonce,(nonce_offsets slot).2,nonce_access_addr_hi salts slot]
    exact leaf_word_access salts (2*(slot.val%256)+1) (by omega)
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
  have nonce : prev.getReg .x22=wordAddress salts+2048 := (after_a_reg _ _ _ _ _ (by decide) (by decide)).trans ready.nonces
  exact second_accesses_core prev slot start salts i bound nonceBound tag nonce hi

end TwoPermutationPrototype.RV64.PackedLeaves
