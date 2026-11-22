import CommitGolfCandidate.TwoPermutationBindingBridge

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

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate

def CompressionWitness238 (rows : List PublicRow) : Prop :=
  ∃ (input₀ input₁ : BitVec 512) (reply₀ reply₁ : BitVec 256),
    PublicRow.compression input₀ reply₀ ∈ rows ∧ PublicRow.compression input₁ reply₁ ∈ rows ∧
      input₀ ≠ input₁ ∧ low238 reply₀ = low238 reply₁

theorem CompressionWitness.to238 {rows : List PublicRow} (hit : CompressionWitness rows) :
    CompressionWitness238 rows := by
  obtain ⟨x, y, a, b, left, right, different, equal⟩ := hit
  exact ⟨x, y, a, b, left, right, different, low238_of_low240 equal⟩

theorem CompressionWitness238.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (hit : CompressionWitness238 earlier) : CompressionWitness238 later := by
  obtain ⟨x, y, a, b, left, right, different, equal⟩ := hit
  exact ⟨x, y, a, b, contained _ left, contained _ right, different, equal⟩

end TwoPermutationPrototype.Sampling
