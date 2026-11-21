import CommitGolfCandidate.TwoPermutationPinnedStoredLeaf

/-!
# Sharp replay margin

The full-state union bound behind a pinned-leaf or quartet bad event is at most `q / 2^130`:
pairs contribute `calls^2 / 2 · 2^1346 ≤ q · 2^1467`, single answers `calls · 2^1400 ≤ q · 2^1432`,
over `2^1600 - calls ≥ 2^1599`. The same argument at `q / 2^124` is `replay_extra_margin`.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
set_option maxRecDepth 16384
set_option exponentiation.threshold 2100

/-- Margin of a union bound on the full 1600-bit state at `q/2^130` (unary count up to `2^1400`). -/
theorem replay_margin_130 (q calls k v : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (kBound : k ≤ 2^1346) (vBound : v ≤ 2^1400) :
    unionBound (2^1600) k v calls ≤ (q : ℝ)/2^130 := by
  have one : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have limit : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have replayLimit : (calls : ℝ) ≤ (q : ℝ) + 2^31 := by exact_mod_cast replayed
  have nonneg : (0 : ℝ) ≤ calls := by positivity
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have K : (k : ℝ) ≤ 2^1346 := by exact_mod_cast kBound
  have V : (v : ℝ) ≤ 2^1400 := by exact_mod_cast vBound
  have callUpper : (calls : ℝ) ≤ 2^121 := by
    linarith [show (2 : ℝ)^120 + 2^31 ≤ 2^121 by norm_num]
  have denom : (2 : ℝ)^1599 ≤ 2^1600 - (calls : ℝ) := by
    linarith [show (2 : ℝ)^1599 + 2^121 ≤ 2^1600 by norm_num]
  have denomPos : 0 < (2 : ℝ)^1600 - calls :=
    lt_of_lt_of_le (by positivity : 0 < (2 : ℝ)^1599) denom
  have squareBound : (calls : ℝ)^2 ≤ (q : ℝ)*2^122 := by
    let extra : ℝ := 2^31
    have leSum : (calls : ℝ) ≤ q + extra := replayLimit
    have sq := mul_nonneg (sub_nonneg.mpr leSum) (by positivity : 0 ≤ (q : ℝ) + extra + calls)
    have qsq := mul_le_mul_of_nonneg_right limit qNonneg
    have esq : 2*extra^2 ≤ 2^65 := by norm_num [extra]
    have nq := mul_le_mul_of_nonneg_right one (by positivity : (0 : ℝ) ≤ 2^65)
    have slack : (2 : ℝ)^121 + 2^65 ≤ 2^122 := by norm_num
    have pad := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith [sq_nonneg ((q : ℝ) - extra)]
  have linearBound : (calls : ℝ) ≤ (q : ℝ)*2^32 := by
    have scale := mul_le_mul_of_nonneg_right one (by positivity : (0 : ℝ) ≤ 2^31)
    have slack : (1 : ℝ)+2^31 ≤ 2^32 := by norm_num
    have envelope := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith
  have pair : ((calls : ℝ) * ((calls : ℝ)-1)/2) * (k : ℝ) ≤ (calls : ℝ)^2 * 2^1346 := by
    have factor : (calls : ℝ) * ((calls : ℝ)-1)/2 ≤ (calls : ℝ)^2 := by
      nlinarith [sq_nonneg (calls : ℝ)]
    exact (mul_le_mul_of_nonneg_right factor (by positivity : 0 ≤ (k : ℝ))).trans
      (mul_le_mul_of_nonneg_left K (by positivity))
  have tail : (calls : ℝ) * (v : ℝ) ≤ (calls : ℝ) * 2^1400 :=
    mul_le_mul_of_nonneg_left V nonneg
  have pairBound := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ 2^1346)
  have tailBound := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^1400)
  have lower := mul_le_mul_of_nonneg_left denom (by positivity : (0 : ℝ) ≤ (q : ℝ)/2^130)
  have unified : (2 : ℝ)^122*2^1346 + 2^32*2^1400 ≤ 2^1599/2^130 := by norm_num
  have scale := mul_le_mul_of_nonneg_left unified qNonneg
  simp only [unionBound, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_iff₀ denomPos).2
  nlinarith

/-- The trace-level route to a fixed-compression replay bound at `q / 2^130`: a witness in the
stored rows forces a bad trace. -/
theorem replayed_event_130 {α : Type} (compress : Compression) (program : OracleComp World α)
    (witness : List PublicRow → Prop) (bad : BadSpec PermState) (q calls : Nat)
    (bounded : PublicQueryBound (recordRows program) calls)
    (extract : ∀ trace rows, PinnedRowsStored rows trace → witness rows → ¬ bad.Good trace)
    (prob : (toStrat compress (recordRows program)).prob PState.init
      (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) ≤ (q : ℝ)/2^130) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      witness result.2] ≤ (q : ENNReal)/2^130 := by
  classical
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have records := pinned_recorded_table compress program PState.init Trace.WF.nil
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have evidence : st.prob PState.init (fun result _ => witness result.2) ≤
      st.prob PState.init (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    intro result finish facts hit
    exact ⟨extract finish.trace result.2 facts.1.2 hit, by simpa [PState.init] using facts.2.2⟩
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal (evidence.trans prob)).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- Two `q / 2^130` terms make one `q / 2^129`. -/
theorem two_halves_130 (q : Nat) :
    (q : ENNReal)/2^130 + (q : ENNReal)/2^130 = (q : ENNReal)/2^129 := by
  rw [← ENNReal.add_div, ← two_mul,
    show (2 : ENNReal)^130 = 2 * 2^129 by rw [show (130 : Nat) = 1+129 by decide, pow_add]; norm_num]
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

/-- Leaf binding at `q / 2^129` (both kinds); the shape of `PeerLeafLayout`, which says `q / 2^123`. -/
structure PeerLeafLayoutSharp : Prop where
  bound : ∀ {α : Type} (compress : Compression) (program : OracleComp World α) (q calls : Nat),
    1 ≤ q → q ≤ 2^120 → calls ≤ q+2^31 → PublicQueryBound (recordRows program) calls →
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitness result.2] ≤ (q : ENNReal)/2^129

theorem PeerLeafLayoutSharp.toPeerLeafLayout (layout : PeerLeafLayoutSharp) : PeerLeafLayout :=
  ⟨fun compress program q calls positive small replayed bounded =>
    (layout.bound compress program q calls positive small replayed bounded).trans
      (ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _)⟩

end TwoPermutationPrototype.Sampling
