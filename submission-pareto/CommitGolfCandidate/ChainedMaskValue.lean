import CommitGolfCandidate.ChainedContinuationReturn
import CommitGolfCandidate.ChainedSchedule
import CommitGolfCandidate.Memory

/-! The final native word mask truncates the whole digest at the scheduled width. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def finalValue (h : Height) (value : Output) : Output := BitVec.ofNat 256 (value.toNat % 2^(width h))
def finalMask (h : Height) : Word := BitVec.ofNat 64 (2^(width h-192)-1)

private theorem mask_bit (h : Height) (k : Nat) :
    (finalMask h).getLsbD k = decide (k < width h-192 ∧ k < 64) := by
  unfold finalMask
  rw [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]
  by_cases low : k < width h-192 <;> by_cases inside : k < 64 <;> simp [low,inside]

theorem final_top_word (h : Height) (value : Output) :
    (finalValue h value).extractLsb' 192 64 = value.extractLsb' 192 64 &&& finalMask h := by
  have lo := width_lower h
  have hi := width_upper h
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and,mask_bit,BitVec.getLsbD_extractLsb',finalValue,
    BitVec.getLsbD_extractLsb',BitVec.getLsbD_ofNat,Nat.testBit_mod_two_pow,BitVec.testBit_toNat]
  by_cases low : k < width h-192
  · simp [low,hk,show 192+k < width h by omega,show 192+k < 256 by omega]
  · simp [low,show ¬192+k < width h by omega]

theorem final_low_word (h : Height) (value : Output) (k : Nat) (small : k < 3) :
    (finalValue h value).extractLsb' (64*k) 64 = value.extractLsb' (64*k) 64 := by
  have lo := width_lower h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [finalValue,BitVec.getLsbD_extractLsb',BitVec.getLsbD_extractLsb',BitVec.getLsbD_ofNat,
    Nat.testBit_mod_two_pow,BitVec.testBit_toNat]
  simp [hi,show 64*k+i < width h by omega,show 64*k+i < 256 by omega]

theorem mask_memory (s : MachineState) (query : Word) :
    (ordinaryPrefix s 15 4).getMem query =
      if query == s.getReg .x10+24 then s.getMem (s.getReg .x10+24) &&& s.getReg .x16
      else s.getMem query := by
  rfl

theorem output_ext_words (left right : Output)
    (words : ∀ i : Fin 4, left.extractLsb' (64*i.val) 64 = right.extractLsb' (64*i.val) 64) :
    left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have word := congrArg (fun v : Word => v.getLsbD (k%64)) (words ⟨k/64,by omega⟩)
  rw [BitVec.getLsbD_extractLsb',BitVec.getLsbD_extractLsb'] at word
  simpa only [show k%64 < 64 by omega,decide_true,Bool.true_and,
    show 64*(k/64)+k%64 = k by omega] using word

theorem mask_value (s : MachineState) (buffer : Word) (h : Height)
    (source : s.getReg .x10 = buffer) (aligned : buffer.toNat % 8 = 0)
    (mask : s.getReg .x16 = finalMask h) :
    readBuffer (ordinaryPrefix s 15 4) buffer.toNat 32 = finalValue h (readBuffer s buffer.toNat 32) := by
  apply output_ext_words
  intro i
  fin_cases i
  all_goals norm_num only [Fin.val_mk,Nat.reduceMul]
  all_goals first
    | rw [final_low_word h _ 0 (by decide)]
    | rw [final_low_word h _ 1 (by decide)]
    | rw [final_low_word h _ 2 (by decide)]
    | rw [final_top_word]
  all_goals first
    | rw [read_digest_word _ _ 0 aligned (by decide),read_digest_word _ _ 0 aligned (by decide)]
    | rw [read_digest_word _ _ 1 aligned (by decide),read_digest_word _ _ 1 aligned (by decide)]
    | rw [read_digest_word _ _ 2 aligned (by decide),read_digest_word _ _ 2 aligned (by decide)]
    | rw [read_digest_word _ _ 3 aligned (by decide),read_digest_word _ _ 3 aligned (by decide)]
  all_goals simp [mask_memory,source,mask,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.add_right_inj]

end CommitGolfCandidate.Chained.Native
