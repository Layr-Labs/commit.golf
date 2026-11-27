import CommitGolfCandidate.CompressionROM
import CommitGolfCandidate.Stage3cSurvival

/-! A fresh full-width reply hits any previously determined truncated target set. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

private def joinBits (w : Nat) (bounded : w ≤ 256) : BitVec (256-w) × BitVec w ≃ BitVec 256 where
  toFun pair := (pair.1 ++ pair.2).cast (by omega)
  invFun value := (value.extractLsb' w (256-w),lowBits w value)
  left_inv := by
    rintro ⟨high,low⟩
    refine Prod.ext ?_ ?_
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append]
      omega
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [lowBits,BitVec.getLsbD_extractLsb',BitVec.getLsbD_append,hi]
  right_inv := by
    intro value
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [lowBits,BitVec.getLsbD_cast,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
    by_cases low : i < w
    · simp [low]
    · have h1 : i-w < 256-w := by omega
      have h2 : w+(i-w) = i := by omega
      simp [low,h1,h2]

theorem uniform_lowBits_targets (w : Nat) (bounded : w ≤ 256) (targets : Finset (BitVec w)) :
    Pr{let reply ← $ᵗ BitVec 256}[lowBits w reply ∈ targets] ≤ (targets.card : ENNReal)/2^w := by
  classical
  rw [← SampleableType.prEvent_uniformSample_equiv (joinBits w bounded)]
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro high
  have project : ∀ low, lowBits w (joinBits w bounded (high,low)) = low := fun low =>
    congrArg Prod.snd ((joinBits w bounded).left_inv (high,low))
  simp_rw [project]
  rw [SampleableType.prEvent_uniformSample]
  have event : (Finset.univ.filter fun low => low ∈ targets) = targets := by ext low; simp
  rw [event,show Fintype.card (BitVec w) = 2^w by simp,Nat.cast_pow,Nat.cast_ofNat]

end CommitGolfCandidate
