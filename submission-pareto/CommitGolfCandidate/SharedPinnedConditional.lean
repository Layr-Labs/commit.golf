import CommitGolfCandidate.SharedPinnedAdaptive

/-! Conditional hiding with complementary preBound and observer budgets. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
local instance SharedPinnedConditionalDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def sharedPinnedCharge (before after : Nat) : ℝ :=
  2*(before : ℝ)/2^122 + (after : ℝ)*(2/2^122 + 2^25/2^1343)

theorem shared_conditional_distance {I Output : Type} [Fintype I] [DecidableEq I]
    {base : Cache} {count : Nat} (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (valid : state.high.Valid count) (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (position : I → Index) (unique : Function.Injective position)
    (first : Bool → I → Block) (message : Bool → I → Words 32)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ w nonce addr, addr ∈ pinnedNonceAddresses position (first w) (message w) nonce →
      addr ∉ state.opened)
    (compress : Compression) (observer : (I → BitVec 256) → OracleComp World Output)
    (before after : Nat) (bounded : ∀ digest, QueryBounded (observer digest) after)
    (preBound : base.entries.length ≤ before) (sites : Fintype.card I ≤ 2^24) :
    let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    measureTVDist (pinnedConditionalActual state opened position (first false) (message false) execute)
      (pinnedConditionalActual state opened position (first true) (message true) execute) ≤
      sharedPinnedCharge before after := by
  let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  let actual (w : Bool) := pinnedConditionalActual state opened position (first w) (message w) execute
  let programmed (w : Bool) := pinnedConditionalProgrammed state opened position (first w) (message w) execute
  have pre (w : Bool) : measureTVDist (actual w) (programmed w) ≤ (before : ℝ)/2^122 :=
    (pinned_conditional_actual_programmed_distance state opened position (first w) (message w) execute
      valid unique room (disjoint w)).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast preBound) (by positivity))
  let rate : ENNReal := 2/2^122 + 2*(Fintype.card I : ENNReal)/2^1343
  have rateBound : rate.toReal ≤ (2 : ℝ)/2^122 + 2^25/2^1343 := by
    unfold rate
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    have card : (Fintype.card I : ℝ) ≤ 2^24 := by exact_mod_cast sites
    norm_num
    linarith
  have post : measureTVDist (programmed false) (programmed true) ≤
      (after : ℝ)*(2/2^122 + 2^25/2^1343) := by
    change measureTVDist (samplePinnedLowFn I >>= _) (samplePinnedLowFn I >>= _) ≤ _
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro digest
    apply measureTVDist_bind_left_le_of_forall_le (samplePinnedBasePermutation state opened) _ _ (by positivity)
    intro p
    have left := shared_rows_left state position first message digest
      (fun rows => execute digest (p.programRows rows))
    have right := shared_rows_right state position first message digest
      (fun rows => execute digest (p.programRows rows))
    have payment := shared_adaptive_programmed_distance
      (sharedPinnedRows state position first message digest) rate (by unfold rate; finiteness)
      compress p (observer digest) after (bounded digest)
      (fun row => shared_rows_hit_le state valid position unique first message digest room row)
    have limit : ((after : ENNReal)*rate).toReal ≤ (after : ℝ)*(2/2^122 + 2^25/2^1343) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      exact mul_le_mul_of_nonneg_left rateBound (by positivity)
    unfold measureTVDist at payment ⊢
    rw [left.evalDist_eq, right.evalDist_eq] at payment
    exact payment.trans limit
  have middle := measureTVDist_triangle (actual false) (programmed false) (actual true)
  have tail := measureTVDist_triangle (programmed false) (programmed true) (actual true)
  rw [measureTVDist_comm (programmed true) (actual true)] at tail
  exact middle.trans ((add_le_add (pre false) (tail.trans (add_le_add post (pre true)))).trans_eq
    (by unfold sharedPinnedCharge; ring))

end TwoPermutationPrototype.Sampling
