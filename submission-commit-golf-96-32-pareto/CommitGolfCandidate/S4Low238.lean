import CommitGolfCandidate.TruncBirthday

/-!
# The 238-bit tree witness

Internal nodes keep the low 238 bits of a compression reply. A tree conflict is then two different compression
inputs whose replies agree on those bits (`CompressionWitness238`); a 240-bit agreement is one.
This module only needs the compression rows, so checker modules can import it without the probability side.
-/

namespace CommitGolfCandidate

def low238 (value : BitVec 256) : BitVec 238 := value.extractLsb' 0 238

theorem low238_of_low240 {a b : BitVec 256} (same : low240 a = low240 b) : low238 a = low238 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have wide : i < 240 := by omega
  have bit := congrArg (fun v : BitVec 240 => v.getLsbD i) same
  simp only [low238, low240, BitVec.getLsbD_extractLsb', hi, wide, decide_true, Bool.true_and] at bit ⊢
  exact bit

end CommitGolfCandidate

