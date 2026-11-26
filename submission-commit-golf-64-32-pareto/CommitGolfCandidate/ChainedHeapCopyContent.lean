import CommitGolfCandidate.ChainedHeapCopy
import CommitGolfCandidate.ChainedMaskValue

/-! Byte-exact readback of the copied digest under source/destination separation. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def copyWord (s : MachineState) (index : Nat) : MachineState :=
  execInstrBr (execInstrBr s (.LD .x20 .x10 (BitVec.ofNat 12 (8*index))))
    (.SD .x7 .x20 (BitVec.ofNat 12 (8*index)))

private theorem copy_pair (s : MachineState) (count : Nat) (small : count < 4) :
    copyPrefix s (2*(count+1)) = copyWord (copyPrefix s (2*count)) count := by
  interval_cases count <;> rfl

private theorem copy_word_memory (s : MachineState) (index : Nat) (small : index < 4) (query : Word) :
    (copyWord s index).getMem query =
      if query == s.getReg .x7+BitVec.ofNat 64 (8*index)
      then s.getMem (s.getReg .x10+BitVec.ofNat 64 (8*index)) else s.getMem query := by
  interval_cases index <;> rfl

private theorem copy_offset_eq (a b : Fin 4) :
    BitVec.ofNat 64 (8*a.val) = BitVec.ofNat 64 (8*b.val) ↔ a.val = b.val := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    have ha := a.isLt
    have hb := b.isLt
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8*a.val < 2^64 by omega),
      Nat.mod_eq_of_lt (show 8*b.val < 2^64 by omega)] at numeric
    omega
  · intro equal
    rw [equal]

theorem copy_target_word (s : MachineState) (i : Fin 4) (pairs : Nat) (small : pairs ≤ 4)
    (separate : ∀ a b : Fin 4,
      s.getReg .x10+BitVec.ofNat 64 (8*a.val) ≠ s.getReg .x7+BitVec.ofNat 64 (8*b.val)) :
    (copyPrefix s (2*pairs)).getMem (s.getReg .x7+BitVec.ofNat 64 (8*i.val)) =
      if i.val < pairs then s.getMem (s.getReg .x10+BitVec.ofNat 64 (8*i.val))
      else s.getMem (s.getReg .x7+BitVec.ofNat 64 (8*i.val)) := by
  induction pairs with
  | zero => simp [copyPrefix]
  | succ pairs ih =>
    have before : pairs < 4 := by omega
    rw [copy_pair s pairs before,copy_word_memory _ pairs before,
      (copy_bases s (2*pairs) (by omega)).1,(copy_bases s (2*pairs) (by omega)).2]
    simp only [beq_iff_eq]
    by_cases same : i.val = pairs
    · have hit : s.getReg .x7+BitVec.ofNat 64 (8*i.val) =
          s.getReg .x7+BitVec.ofNat 64 (8*pairs) := by rw [same]
      rw [ite_eq_left hit,copy_memory_outside s _ (separate ⟨pairs,before⟩) (2*pairs) (by omega)]
      simp only [same,ite_eq_left (Nat.lt_succ_self pairs)]
    · have miss : s.getReg .x7+BitVec.ofNat 64 (8*i.val) ≠
          s.getReg .x7+BitVec.ofNat 64 (8*pairs) := by
        intro equal
        exact same ((copy_offset_eq i ⟨pairs,before⟩).mp ((BitVec.add_right_inj _).mp equal))
      rw [ite_eq_right miss,ih (by omega)]
      by_cases earlier : i.val < pairs
      · rw [ite_eq_left earlier,ite_eq_left (show i.val < pairs+1 by omega)]
      · rw [ite_eq_right earlier,ite_eq_right (show ¬i.val < pairs+1 by omega)]

theorem copy_value (s : MachineState)
    (sourceAligned : (s.getReg .x10).toNat % 8 = 0) (targetAligned : (s.getReg .x7).toNat % 8 = 0)
    (separate : ∀ a b : Fin 4,
      s.getReg .x10+BitVec.ofNat 64 (8*a.val) ≠ s.getReg .x7+BitVec.ofNat 64 (8*b.val)) :
    readBuffer (copyPrefix s 8) (s.getReg .x7).toNat 32 = readBuffer s (s.getReg .x10).toNat 32 := by
  apply output_ext_words
  intro i
  rw [read_digest_word _ _ i.val targetAligned i.isLt,read_digest_word _ _ i.val sourceAligned i.isLt]
  simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  simpa only [ite_eq_left i.isLt] using copy_target_word s i 4 (by decide) separate

end CommitGolfCandidate.Chained.Native
