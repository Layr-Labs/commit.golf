import CommitGolfCandidate.QuadNodeBlock

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] ByteCopy.copyField ByteCopy.copyRun ByteCopy.copyStep quadSlotPrefix quadSlotLatch

/-- Natural addresses in memory do not alias through RV64 truncation. -/
theorem quad_byte_address_ne (a b : Nat) (ha : a<2^64) (hb : b<2^64) (different : a≠b) :
    BitVec.ofNat 64 a≠BitVec.ofNat 64 b := by
  intro same
  have eq := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at eq
  exact different eq

theorem quad_target_bound (r : Fin 4) : 12872≤quadTarget r ∧ quadTarget r+32≤13000 := by
  unfold quadTarget
  have := (quadNextSlot r).isLt
  omega

/-- Memory contract for all three actual rotation iterations. Each result digest
comes from the original proof; bytes outside all three destination slots survive. -/
theorem quad_rotation_bytes (s : MachineState) (r : Fin 4) (proof : Nat)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=3)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) (above : 32768≤proof) :
    (∀ i<32, (quadRotation s).getByte (BitVec.ofNat 64 (quadTarget r+i))=
      s.getByte (BitVec.ofNat 64 (proof+i))) ∧
    (∀ i<32, (quadRotation s).getByte (BitVec.ofNat 64 (quadTarget (quadNextSlot r)+i))=
      s.getByte (BitVec.ofNat 64 (proof+32+i))) ∧
    (∀ i<32, (quadRotation s).getByte (BitVec.ofNat 64 (quadTarget (quadNextSlot (quadNextSlot r))+i))=
      s.getByte (BitVec.ofNat 64 (proof+64+i))) ∧
    (∀ q : Word, (∀ i<32, q≠BitVec.ofNat 64 (quadTarget r+i)) →
      (∀ i<32, q≠BitVec.ofNat 64 (quadTarget (quadNextSlot r)+i)) →
      (∀ i<32, q≠BitVec.ofNat 64 (quadTarget (quadNextSlot (quadNextSlot r))+i)) →
      (quadRotation s).getByte q=s.getByte q) := by
  have p := quad_slot_post s r proof 3 (by decide) (by decide) pc base offset src counter (by omega) even
  have q := quad_slot_post (quadSlot s) (quadNextSlot r) (proof+32) 2 (by decide) (by decide)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega) (by omega)
  have b₀ := quad_slot_bytes s r proof 3 (by decide) (by decide) pc base offset src counter
    (by omega) even (by have := quad_target_bound r; omega)
  have b₁ := quad_slot_bytes (quadSlot s) (quadNextSlot r) (proof+32) 2 (by decide) (by decide)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega) (by omega)
    (by have := quad_target_bound (quadNextSlot r); omega)
  have b₂ := quad_slot_bytes (quadSlot (quadSlot s)) (quadNextSlot (quadNextSlot r)) (proof+64) 1
    (by decide) (by decide) q.1 q.2.1 q.2.2.1
    (by simpa only [show proof+32+32=proof+64 by omega] using q.2.2.2.1) q.2.2.2.2
    (by omega) (by omega) (by have := quad_target_bound (quadNextSlot (quadNextSlot r)); omega)
  have separate (a b : Fin 4) (ne : quadNextSlot a≠quadNextSlot b) (i j : Nat) (hi : i<32) (hj : j<32) :
      BitVec.ofNat 64 (quadTarget a+i)≠BitVec.ofNat 64 (quadTarget b+j) := by
    have ra := quad_target_bound a
    have rb := quad_target_bound b
    apply quad_byte_address_ne _ _ (by omega) (by omega)
    intro equal
    have same : (quadNextSlot a).val=(quadNextSlot b).val := by unfold quadTarget at equal; omega
    exact ne (Fin.ext same)
  have ne₀₁ : quadNextSlot r≠quadNextSlot (quadNextSlot r) := by fin_cases r <;> decide
  have ne₀₂ : quadNextSlot r≠quadNextSlot (quadNextSlot (quadNextSlot r)) := by fin_cases r <;> decide
  have ne₁₂ : quadNextSlot (quadNextSlot r)≠quadNextSlot (quadNextSlot (quadNextSlot r)) := by fin_cases r <;> decide
  have proofFrame (a : Fin 4) (atByte : Nat) (lo : proof≤atByte) (hi : atByte<proof+96) :
      ∀ i<32, BitVec.ofNat 64 atByte≠BitVec.ofNat 64 (quadTarget a+i) := by
    intro i small
    have lim := quad_target_bound a
    have maxMemory : MEMORY_BYTES<2^64 := by decide
    exact quad_byte_address_ne _ _ (by omega) (by omega) (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    exact (b₂.2 _ (fun j hj => separate _ _ ne₀₂ i j hi hj)).trans
      ((b₁.2 _ (fun j hj => separate _ _ ne₀₁ i j hi hj)).trans (b₀.1 i hi))
  · intro i hi
    exact (b₂.2 _ (fun j hj => separate _ _ ne₁₂ i j hi hj)).trans
      ((b₁.1 i hi).trans (b₀.2 _ (proofFrame r _ (by omega) (by omega))))
  · intro i hi
    exact (b₂.1 i hi).trans ((b₁.2 _ (proofFrame (quadNextSlot r) _ (by omega) (by omega))).trans
      (b₀.2 _ (proofFrame r _ (by omega) (by omega))))
  · intro atByte a b c
    exact (b₂.2 atByte c).trans ((b₁.2 atByte b).trans (b₀.2 atByte a))

end TwoPermutationPrototype.Quad.Checker
