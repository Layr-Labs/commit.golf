import CommitGolfCandidate.TwoPermutationPackedCapHash

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.Checker (write_bits_word_outside)

theorem cap_hash_parent_register (state : MachineState) (parent : Nat) (answer : BitVec 256) (r : Reg)
    (scratch : r ≠ .x31) :
    (capHashReply state parent answer).getReg r = (capParent state).getReg r := by
  simp only [capHashReply, maskAfter, execInstrBr, MachineState.setWord32, MachineState.getReg_setPC,
    arm_getReg_set_mem, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]
  rw [cap_compression_register]

theorem cap_hash_register (state : MachineState) (parent : Nat) (answer : BitVec 256) (r : Reg)
    (node : r ≠ .x6) (source : r ≠ .x10) (dest : r ≠ .x12) (scratch : r ≠ .x31) :
    (capHashReply state parent answer).getReg r = state.getReg r :=
  (cap_hash_parent_register state parent answer r scratch).trans (cap_parent_register state r node source dest)

private theorem cap_pc_frame (state : MachineState) (pc : Word) (word : Nat) :
    memoryView (state.setPC pc) word = memoryView state word := rfl

attribute [local irreducible] writeBits capParent maskAfter

theorem cap_hash_frame {state : MachineState} {node : Nat}
    (ready : CapHashReady state node) (answer : BitVec 256) (word : Nat)
    (bound : word < 2^61) (outside : word < 2048+4*(node/2) ∨ 2048+4*(node/2)+4 ≤ word) :
    memoryView (capHashReply state (node/2) answer) word = memoryView state word := by
  have destinationBound := ready.bound
  obtain ⟨_, _, _, dest, mem⟩ := cap_parent_post state ready.pc
  have dst : (capParent state).getReg .x12 = wordAddress (2048+4*(node/2)) := by
    rw [dest, ready.roots, ready.nodeReg]
    have shifted : BitVec.ofNat 64 node >>> 1 = BitVec.ofNat 64 (node/2) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : node < 2^64), Nat.mod_eq_of_lt (by omega : node/2 < 2^64),
        Nat.shiftRight_eq_div_pow]
    rw [shifted, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (node/2) * BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
    congr 1
    omega
  have address : ((capCompressionAnswer (capParent state) answer).setPC 0x1af0).getReg .x12 + signExtend12 28 =
      BitVec.ofNat 64 (8*(2048+4*(node/2))+24+4) := by
    rw [MachineState.getReg_setPC, cap_compression_register, dst, wordAddress,
      show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  unfold capHashReply
  rw [cap_pc_frame, masked_slot_frame _ .x12 _ address (by omega) (by decide) word (by omega) (by omega) (by omega),
    cap_pc_frame]
  unfold capCompressionAnswer
  rw [dst, write_bits_word_outside _ answer _ _ (by omega) bound (by omega)]
  exact congrFun mem _

end TwoPermutationPrototype.Packed.Checker
