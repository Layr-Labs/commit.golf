import CommitGolf.Riscv
import Mathlib.Tactic
import RiscvZkvm.Rv64.Logic.ByteOps

/-! Word-level facts for the aligned opening copies. These concern the actual
RV64 little-endian memory operations, independently of any machine image.
Address decomposition follows the public ProjectedHalfword helper's pattern. -/
namespace CommitGolfCandidate.OpeningWordCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 800000

theorem replace_word_as_halves (old : Word) (value : BitVec 32) (slot : Nat)
    (inside : slot < 2) :
    replaceWord32 old slot value =
      replaceHalfword (replaceHalfword old (2*slot) (value.extractLsb' 0 16))
        (2*slot+1) (value.extractLsb' 16 16) := by
  interval_cases slot <;>
    simp only [replaceWord32, replaceHalfword]
  all_goals
    ext i hi
    interval_cases i <;> simp [BitVec.truncate, BitVec.zeroExtend]

theorem extract_word_low_half (old : Word) (slot : Nat) (inside : slot < 2) :
    (extractWord32 old slot).extractLsb' 0 16 = extractHalfword old (2*slot) := by
  interval_cases slot <;>
    simp only [extractWord32, extractHalfword]
  all_goals
    ext i hi
    interval_cases i <;> simp [BitVec.truncate]

theorem extract_word_high_half (old : Word) (slot : Nat) (inside : slot < 2) :
    (extractWord32 old slot).extractLsb' 16 16 = extractHalfword old (2*slot+1) := by
  interval_cases slot <;>
    simp only [extractWord32, extractHalfword]
  all_goals
    ext i hi
    interval_cases i <;> simp [BitVec.truncate]

theorem scratch_after_shift (value : BitVec 32) :
    (value.zeroExtend 64 >>> 16) = (value.extractLsb' 16 16).zeroExtend 64 := by
  ext i hi
  interval_cases i <;> simp [BitVec.zeroExtend]

theorem byte_offset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& 7 = address.toNat % 8
  rw [show (7 : Nat) = 2^3-1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem next_halfword_same_slot (address : Word) (aligned : address.toNat % 4 = 0) :
    alignToDword (address+2) = alignToDword address ∧
      byteOffset (address+2) = byteOffset address+2 := by
  have bound := address.isLt
  have add_value : (address+2).toNat = address.toNat+2 := by
    rw [BitVec.toNat_add]
    change (address.toNat+2)%2^64 = address.toNat+2
    exact Nat.mod_eq_of_lt (by omega)
  have offsets : byteOffset (address+2) = byteOffset address+2 := by
    rw [byte_offset_mod, byte_offset_mod, add_value]
    omega
  have split := alignToDword_add_byteOffset (address+2)
  rw [offsets, BitVec.ofNat_add, ← BitVec.add_assoc] at split
  have same :
      alignToDword (address+2)+BitVec.ofNat 64 (byteOffset address)+2 =
        alignToDword address+BitVec.ofNat 64 (byteOffset address)+2 :=
    split.trans (congrArg (· + 2) (alignToDword_add_byteOffset address)).symm
  have common := congrArg (fun value : Word => value-2-BitVec.ofNat 64 (byteOffset address)) same
  exact ⟨by simpa only [BitVec.add_sub_cancel] using common, offsets⟩

/-- A four-byte aligned store is exactly the pair of its low and high halfword
stores, including every byte outside the destination word. -/
theorem store_word_as_halves (state : MachineState) (address : Word) (value : BitVec 32)
    (aligned : address.toNat % 4 = 0) :
    state.setWord32 address value =
      (state.setHalfword address (value.extractLsb' 0 16)).setHalfword
        (address+2) (value.extractLsb' 16 16) := by
  have next := next_halfword_same_slot address aligned
  have offset : byteOffset address = 0 ∨ byteOffset address = 4 := by
    rw [byte_offset_mod]
    omega
  rcases offset with offset | offset <;>
    simp only [MachineState.setWord32, MachineState.setHalfword, next.1, next.2,
      offset, Nat.reduceAdd, Nat.reduceDiv, MachineState.getMem_setMem_eq]
  all_goals
    rw [replace_word_as_halves _ _ _ (by decide)]
    cases state
    simp [MachineState.setMem]
    funext query
    by_cases equal : query = alignToDword address <;> simp [equal]

/-- Both halfword reads of an aligned word agree with its little-endian split. -/
theorem load_word_as_halves (state : MachineState) (address : Word)
    (aligned : address.toNat % 4 = 0) :
    (state.getWord32 address).extractLsb' 0 16 = state.getHalfword address ∧
      (state.getWord32 address).extractLsb' 16 16 = state.getHalfword (address+2) := by
  have next := next_halfword_same_slot address aligned
  have offset : byteOffset address = 0 ∨ byteOffset address = 4 := by
    rw [byte_offset_mod]
    omega
  rcases offset with offset | offset <;>
    simp only [MachineState.getWord32, MachineState.getHalfword, next.1, next.2,
      offset, Nat.reduceAdd, Nat.reduceDiv]
  all_goals
    exact ⟨extract_word_low_half _ _ (by decide), extract_word_high_half _ _ (by decide)⟩

/-- The first store of a pair cannot affect its second source read when their
containing doublewords differ. The opening layout provides a much larger gap. -/
theorem load_high_after_store (state : MachineState) (source target : Word)
    (value : BitVec 16) (aligned : source.toNat % 4 = 0)
    (separate : alignToDword source ≠ alignToDword target) :
    (state.setHalfword target value).getHalfword (source+2) = state.getHalfword (source+2) := by
  simp only [MachineState.getHalfword, MachineState.setHalfword,
    (next_halfword_same_slot source aligned).1, MachineState.getMem_setMem_ne separate]

/-- Algebraic form of the two old LHU/SH pairs, including the exact last LHU
value left in x31. The program counter is handled by the execution lemma. -/
theorem copy_word_as_halves (state : MachineState) (source target : Word)
    (sourceAligned : source.toNat % 4 = 0) (targetAligned : target.toNat % 4 = 0)
    (separate : alignToDword source ≠ alignToDword target) :
    (state.setWord32 target (state.getWord32 source)).setReg .x31
        (((state.getWord32 source).zeroExtend 64) >>> 16) =
      ((state.setHalfword target (state.getHalfword source)).setHalfword (target+2)
        ((state.setHalfword target (state.getHalfword source)).getHalfword (source+2))).setReg
          .x31 (((state.setHalfword target (state.getHalfword source)).getHalfword (source+2)).zeroExtend 64) := by
  rw [load_high_after_store state source target _ sourceAligned separate,
    store_word_as_halves state target _ targetAligned, scratch_after_shift,
    (load_word_as_halves state source sourceAligned).1,
    (load_word_as_halves state source sourceAligned).2]

end CommitGolfCandidate.OpeningWordCopy
