import CommitGolfCandidate.Leaf238PinnedStep

/-! Finite answer probabilities and a common per-query hazard envelope. -/

namespace CommitGolfCandidate.JointOracle238
open CommitGolf OracleComp OracleSpec Permutation
open TwoPermutationPrototype.Sampling
set_option exponentiation.threshold 2100

theorem sampleSet_bound {α : Type} [Fintype α] (A : Finset α) (hne : A.Nonempty)
    (event : α → Prop) (cap : Nat) [DecidablePred event]
    (count : (A.filter event).card ≤ cap) :
    Pr{let answer ← sampleSet A hne}[event answer.val] ≤ (cap : ENNReal)/A.card := by
  classical
  have inject : (Finset.univ.filter fun x : A => event x.val).card ≤ (A.filter event).card := by
    refine Finset.card_le_card_of_injOn (fun x => x.val) ?_ ?_
    · intro x hx
      exact Finset.mem_filter.2 ⟨x.property,(Finset.mem_filter.1 hx).2⟩
    · intro x _ y _ same
      exact Subtype.ext same
  let : Nonempty A := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  let : SampleableType A := SampleableType.ofFintype A
  change Pr{let answer ← $ᵗ A}[event answer.val] ≤ _
  rw [SampleableType.prEvent_uniformSample,Fintype.card_coe]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (inject.trans count)) _

theorem permutation_hazard (r known : Nat) (bounded : r ≤ known) (small : known < 2^238) :
    ((r*pairFiber238+2^896 : Nat) : ENNReal)/((2^1600-r : Nat) : ENNReal) ≤
      ((known+1 : Nat) : ENNReal)/2^238 := by
  have rSmall : r ≤ 2^238 := by omega
  have rCard : r ≤ 2^1600 := by omega
  have denominator : (0 : ℝ) < ((2^1600-r : Nat) : ℝ) := by
    exact_mod_cast (show 0 < 2^1600-r by omega)
  have rate : ((r*pairFiber238+2^896 : Nat) : ℝ)/((2^1600-r : Nat) : ℝ) ≤
      ((known+1 : Nat) : ℝ)/2^238 := by
    rw [div_le_iff₀ denominator]
    rw [Nat.cast_sub rCard]
    push_cast
    have rr : (r : ℝ) ≤ known := by exact_mod_cast bounded
    have rs : (r : ℝ) ≤ 2^238 := by exact_mod_cast rSmall
    have rn : (0 : ℝ) ≤ r := by positivity
    have kn : (0 : ℝ) ≤ known := by positivity
    have square : (r : ℝ)^2 ≤ (2^238 : ℝ)^2 := by nlinarith
    have tail : (r : ℝ)*2^1135 ≤ (2^238 : ℝ)*2^1135 := by gcongr
    norm_num only [pairFiber238, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [square, tail, rs, rr]

  have converted := ENNReal.ofReal_le_ofReal rate
  simpa only [ENNReal.ofReal_div_of_pos denominator,
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^238),
    ENNReal.ofReal_natCast,
    show ENNReal.ofReal ((2 : ℝ)^238) = (2 : ENNReal)^238 from by norm_num] using converted

end CommitGolfCandidate.JointOracle238
