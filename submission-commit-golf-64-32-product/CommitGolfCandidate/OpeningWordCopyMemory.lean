import CommitGolfCandidate.OpeningWordCopyBits

namespace CommitGolfCandidate.OpeningWordCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 800000

/-- Memory-only versions of the two copy paths. The register and PC effects
are established separately by the instruction-execution proof. -/
def halfMemory : Nat → MachineState → Word → Word → MachineState
  | 0, state, _, _ => state
  | count+1, state, source, target =>
      halfMemory count (state.setHalfword target (state.getHalfword source)) (source+2) (target+2)

def wordMemory : Nat → MachineState → Word → Word → MachineState
  | 0, state, _, _ => state
  | count+1, state, source, target =>
      wordMemory count (state.setWord32 target (state.getWord32 source)) (source+4) (target+4)

theorem nat_word_aligned (address : Nat) (fit : address < 2^64) (aligned : address%4=0) :
    (BitVec.ofNat 64 address).toNat % 4 = 0 := by
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit] using aligned

theorem separated_dwords (source target : Nat) (gap : source+8 ≤ target)
    (fit : target < 2^64) :
    alignToDword (BitVec.ofNat 64 source) ≠ alignToDword (BitVec.ofNat 64 target) := by
  have sourceFit : source < 2^64 := by omega
  have left : (alignToDword (BitVec.ofNat 64 source)).toNat ≤ source := by
    change ((BitVec.ofNat 64 source) &&& ~~~7#64).toNat ≤ source
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceFit]
    exact Nat.and_le_left
  have right := congrArg BitVec.toNat (alignToDword_add_byteOffset (BitVec.ofNat 64 target))
  have offset : byteOffset (BitVec.ofNat 64 target) < 8 := byteOffset_lt_8
  have alignLe : (alignToDword (BitVec.ofNat 64 target)).toNat ≤ target := by
    change ((BitVec.ofNat 64 target) &&& ~~~7#64).toNat ≤ target
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
    exact Nat.and_le_left
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at right
  simp only [Nat.mod_eq_of_lt fit,
    Nat.mod_eq_of_lt (by omega : byteOffset (BitVec.ofNat 64 target) < 2^64)] at right
  have noWrap : (alignToDword (BitVec.ofNat 64 target)).toNat +
      byteOffset (BitVec.ofNat 64 target) < 2^64 := by
    have bound := (alignToDword (BitVec.ofNat 64 target)).isLt
    have zero := alignToDword_byteOffset_zero (BitVec.ofNat 64 target)
    change ((alignToDword (BitVec.ofNat 64 target)) &&& 7#64).toNat = 0 at zero
    rw [BitVec.toNat_and] at zero
    change (alignToDword (BitVec.ofNat 64 target)).toNat &&& (2^3-1) = 0 at zero
    rw [Nat.and_two_pow_sub_one_eq_mod] at zero
    omega
  rw [Nat.mod_eq_of_lt noWrap] at right
  intro equal
  have eqNat := congrArg BitVec.toNat equal
  omega

/-- Under the opening layout's source/destination gap, word copies are exactly
the original halfword memory writes, with every other machine-state field kept. -/
theorem wordMemory_as_halves (count : Nat) (state : MachineState) (source target : Nat)
    (sourceAligned : source%4=0) (targetAligned : target%4=0)
    (gap : source+4*count+8 ≤ target) (fit : target+4*count ≤ 2^64) :
    wordMemory count state (BitVec.ofNat 64 source) (BitVec.ofNat 64 target) =
      halfMemory (2*count) state (BitVec.ofNat 64 source) (BitVec.ofNat 64 target) := by
  induction count generalizing state source target with
  | zero => rfl
  | succ count ih =>
    have sourceFit : source < 2^64 := by omega
    have targetFit : target < 2^64 := by omega
    have sourceAl := nat_word_aligned source sourceFit sourceAligned
    have targetAl := nat_word_aligned target targetFit targetAligned
    have separate := separated_dwords source target (by omega) targetFit
    have pair : state.setWord32 (BitVec.ofNat 64 target) (state.getWord32 (BitVec.ofNat 64 source)) =
        (state.setHalfword (BitVec.ofNat 64 target) (state.getHalfword (BitVec.ofNat 64 source))).setHalfword
          (BitVec.ofNat 64 target+2)
          ((state.setHalfword (BitVec.ofNat 64 target) (state.getHalfword (BitVec.ofNat 64 source))).getHalfword
            (BitVec.ofNat 64 source+2)) := by
      rw [load_high_after_store state _ _ _ sourceAl separate,
        store_word_as_halves state _ _ targetAl,
        (load_word_as_halves state _ sourceAl).1, (load_word_as_halves state _ sourceAl).2]
    rw [wordMemory, show 2*(count+1)=(2*count+1)+1 by omega, halfMemory, halfMemory]
    rw [pair]
    simp only [BitVec.add_assoc, show (2:Word)+2=(4:Word) by rfl]
    have recurse := ih (state.setWord32 (BitVec.ofNat 64 target)
      (state.getWord32 (BitVec.ofNat 64 source))) (source+4) (target+4)
      (by omega) (by omega) (by omega) (by omega)
    rw [pair] at recurse
    have add4 (base : Nat) : BitVec.ofNat 64 base+(4:Word)=BitVec.ofNat 64 (base+4) := by
      change BitVec.ofNat 64 base+BitVec.ofNat 64 4=_
      exact (BitVec.ofNat_add base 4).symm
    rw [add4 source,add4 target]
    exact recurse

end CommitGolfCandidate.OpeningWordCopy
