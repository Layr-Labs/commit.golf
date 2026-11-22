import CommitGolfCandidate.TwoPermutationPackedCapFetch
import CommitGolfCandidate.K3T238ArmMask
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest

/-! # Cap helpers for the T238 checker blocks

Single jumps between the cap words and the appended blocks, and the 238-bit cap parent: a compression
reply written at an aligned slot, then the four-word mask on its top doubleword, reads back as `pad238`. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

attribute [local irreducible] execute

/-- `jal x0` from word `w` to word `target`. -/
theorem cap_jal_hop (s : MachineState) (w target : Nat) (off : BitVec 21) (bound : w < 1024)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (decoded : (packedImage.code[w]?).bind decodeInstruction = some (.base (.JAL .x0 off)))
    (lands : BitVec.ofNat 64 (4096+4*w) + signExtend21 off = BitVec.ofNat 64 (4096+4*target)) :
    GroupHop s (s.setPC (BitVec.ofNat 64 (4096+4*target))) 1 := by
  intro fuel
  have fetched := cap_fetch s w _ bound pc decoded
  have stepped : ordinaryStep s (.base (.JAL .x0 off)) = some (s.setPC (BitVec.ofNat 64 (4096+4*target))) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, lands]
    rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem cap_ofNat_ne {a b : Nat} (left : a < 2^64) (right : b < 2^64) (different : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b :=
  fun same => different (Opening.nat_address_injective left right same)

/-- The doublewords of a reply written at an aligned address. -/
theorem written_dword (state : MachineState) (slot k : Nat) (answer : BitVec 256)
    (aligned : slot % 8 = 0) (inside : k < 4) :
    (writeBits state (BitVec.ofNat 64 slot) answer).getMem (BitVec.ofNat 64 (slot+8*k)) =
      answer.extractLsb' (64*k) 64 := by
  have written := write_bits_digest state slot 0 answer (by decide) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] at written
  rw [← read_digest_word _ _ _ aligned inside, written]

/-- After the mask, a slot whose four doublewords held `answer` reads back as `pad238 answer`. -/
theorem masked_slot_digest (s : MachineState) (r : Reg) (slot : Nat) (answer : BitVec 256)
    (aligned : slot % 8 = 0) (fits : slot+32 < 2^64)
    (address : s.getReg r + signExtend12 28 = BitVec.ofNat 64 (slot+24+4)) (keep : r ≠ .x31)
    (words : ∀ k < 4, s.getMem (BitVec.ofNat 64 (slot+8*k)) = answer.extractLsb' (64*k) 64) :
    readBuffer (maskAfter s r 28) slot 32 = pad238 answer := by
  have post := mask_post s r 28 (slot+24) address (by omega) keep
  have low (k : Nat) (small : k < 3) :
      (maskAfter s r 28).getMem (BitVec.ofNat 64 (slot+8*k)) = answer.extractLsb' (64*k) 64 := by
    rw [post.other _ (cap_ofNat_ne (by omega) (by omega) (by omega))]
    exact words k (by omega)
  apply read_pad238 _ slot aligned answer
  · simpa using low 0 (by decide)
  · simpa using low 1 (by decide)
  · simpa using low 2 (by decide)
  · rw [post.word, top238_shift]
    have top := words 3 (by decide)
    simp only [show slot+8*3 = slot+24 by omega] at top
    rw [top]

/-- The mask changes only the doubleword at `slot+24`. -/
theorem masked_slot_frame (s : MachineState) (r : Reg) (slot : Nat)
    (address : s.getReg r + signExtend12 28 = BitVec.ofNat 64 (slot+24+4)) (aligned : slot % 8 = 0)
    (keep : r ≠ .x31) (word : Nat) (outside : 8*word ≠ slot+24) (bounded : 8*word < 2^64) (fits : slot+24 < 2^64) :
    memoryView (maskAfter s r 28) word = memoryView s word := by
  have post := mask_post s r 28 (slot+24) address (by omega) keep
  exact post.other _ (cap_ofNat_ne bounded fits outside)

end TwoPermutationPrototype.Packed.Checker
