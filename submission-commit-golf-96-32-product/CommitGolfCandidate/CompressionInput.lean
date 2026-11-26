import CommitGolf.Oracle

/-! The initial 96-byte construction embeds each pair of digests into the
track's compression domain by appending 32 zero bytes in memory. The embedding
preserves all 512 input bits. It does not introduce another oracle: every
compression query is a query to the track's actual 768-bit domain. -/

namespace CommitGolfCandidate
open CommitGolf

def padInput (input : BitVec 512) : BitVec COMPRESSION_INPUT_LENGTH :=
  (0 : BitVec 256) ++ input

@[simp] theorem padInput_low (input : BitVec 512) :
    (padInput input).extractLsb' 0 512 = input := by
  exact BitVec.extractLsb'_append_eq_right

@[simp] theorem padInput_digest (high low : BitVec 256) :
    (padInput (high ++ low)).extractLsb' 0 256 = low := by
  exact (BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 256 ≤ 512)).trans
    BitVec.extractLsb'_append_eq_right

theorem padInput_injective : Function.Injective padInput := by
  intro input other same
  simpa only [padInput_low] using
    congrArg (fun value : BitVec COMPRESSION_INPUT_LENGTH => value.extractLsb' 0 512) same

@[simp] theorem padInput_eq_iff (input other : BitVec 512) :
    padInput input = padInput other ↔ input = other :=
  padInput_injective.eq_iff

end CommitGolfCandidate
