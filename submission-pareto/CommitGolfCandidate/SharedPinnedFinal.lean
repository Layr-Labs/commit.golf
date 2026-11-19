import CommitGolfCandidate.TwoPermutationPinnedFinalHiding
import CommitGolfCandidate.SharedPinnedRestricted
import CommitGolfCandidate.HidingPrefixBudget

/-! Final hiding bound retaining the actual two-stage query split. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses hidingLeafDigests
noncomputable local instance SharedPinnedFinalFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance SharedPinnedFinalDiscrete {α : Type} : MeasurableSpace α := ⊤


noncomputable def sharedTotalCharge (budget : Nat) : ℝ :=
  2*(budget : ℝ)/2^122 + (budget : ℝ)*(2^25/2^1343)

theorem shared_charge_split (budget calls : Nat) (within : calls ≤ budget) :
    sharedPinnedCharge calls (budget-calls) ≤ sharedTotalCharge budget := by
  unfold sharedPinnedCharge sharedTotalCharge
  rw [Nat.cast_sub within]
  have nn : 0 ≤ (calls : ℝ) := Nat.cast_nonneg _
  have error : 0 ≤ (calls : ℝ)*(2^25/(2:ℝ)^1343) := mul_nonneg nn (by positivity)
  nlinarith

theorem shared_final_margin (budget : Nat) :
    2 * ((3 * LENGTH : ℝ) * (((budget : ℝ) + 3 * LENGTH) / 2^1343)) +
      (2*(budget : ℝ)/2^122 + (budget : ℝ)*(2^25/2^1343)) ≤
      3*((budget : ℝ)+1)/2^122 := by
  have nn : 0 ≤ (budget : ℝ) := Nat.cast_nonneg _
  norm_num [LENGTH, LOG_LENGTH]
  linarith

theorem shared_final_reference_hiding_sharp {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) (small : budget+1 ≤ 2^120) :
    measureTVDist (pinnedViewReference adversary build compress false)
      (pinnedViewReference adversary build compress true) ≤ 3 * ((budget : ℝ) + 1) / 2^122 := by
  let maximum := budget + 3 * LENGTH
  let err : ℝ := 2 * ((3 * LENGTH : ℝ) * ((maximum : ℝ) / 2^1343)) + sharedTotalCharge budget
  have numeric : err ≤ 3 * ((budget : ℝ) + 1) / 2^122 := by
    unfold err maximum sharedTotalCharge
    push_cast
    exact shared_final_margin budget
  apply le_trans _ numeric
  have nonneg : 0 ≤ err := by unfold err sharedTotalCharge; positivity
  unfold measureTVDist
  rw [(pinned_eager_posterior_eq adversary build compress false).evalDist_eq,
      (pinned_eager_posterior_eq adversary build compress true).evalDist_eq]
  unfold pinnedViewPosterior
  let chooser := lazyRun compress adversary.choose (PermutationCache.empty Block)
  change measureTVDist (chooser >>= _) (chooser >>= _) ≤ err
  apply pinned_restricted_bind_support_le chooser _ _ _ nonneg
  intro prior reached
  let challenge := prior.1
  let base := prior.2
  let choices := ($ᵗ OpenedSalts challenge.positions)
  obtain ⟨calls, callsLe, cacheCalls, boundedCalls⟩ :=
    hiding_prefix_split adversary bounded compress prior reached
  have cacheLe : base.entries.length ≤ budget := cacheCalls.trans callsLe
  have room : base.entries.length + 3 * LENGTH ≤ maximum := by unfold maximum; omega
  have cap : maximum ≤ 2^121 := pinned_hiding_room budget small
  have agree : ∀ i ∈ challenge.positions, challenge.message₀ i = challenge.message₁ i := by
    intro i visible
    exact congrFun challenge.agree ⟨i, visible⟩
  change measureTVDist (choices >>= _) (choices >>= _) ≤ err
  apply measureTVDist_bind_left_le_of_forall_le choices _ _ nonneg
  intro opened
  let observer (tape : DigestTape) :=
    let (root, proof) := build compress challenge.positions opened tape
    adversary.observe challenge.aux root proof
  let observe (tape : DigestTape) (p : BiPermutation Block) :=
    fixedOracleRun (fixedOracle compress p) (observer tape)
  let left := challenge.message₀
  let right := challenge.message₁
  let restricted (which : Bool) :=
    pinnedRestrictedWorld base challenge.positions left right opened which observe
  let real (which : Bool) := do
    let closed ← samplePinnedHiddenNonces challenge.positions
    let p ← base.sample
    let message := if which then right else left
    observe (hidingLeafDigests p.val message (mergeSaltTape opened closed)) p.val
  have boundObserver : ∀ tape, QueryBounded (observer tape) (budget-calls) := by
    intro tape
    exact boundedCalls _ _
  have inner : measureTVDist (restricted false) (restricted true) ≤ sharedTotalCharge budget :=
    (shared_restricted_two_world base challenge.positions left right opened compress observer calls (budget-calls)
      boundObserver cacheCalls (room.trans cap)).trans (shared_charge_split budget calls callsLe)
  have each (which : Bool) : measureTVDist (restricted which) (real which) ≤
      (3 * LENGTH : ℝ) * ((maximum : ℝ) / 2^1343) := by
    unfold restricted real measureTVDist
    rw [(pinned_reorder_hidden_sampler base challenge.positions left right opened which observe).evalDist_eq]
    change measureTVDist (_ >>= _) (_ >>= _) ≤ _
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro closed
    apply pinned_closed_restricted_world_near base challenge.positions left right opened closed which
      agree observe maximum room cap
    intro result reached
    obtain ⟨length, _, covered⟩ := pinned_full_const_frame base [] (pinnedFirstAddresses left right) result reached
    rw [pinned_first_addresses_length] at length
    exact ⟨length, covered⟩
  change measureTVDist (real false) (real true) ≤ err
  have one := measureTVDist_triangle (real false) (restricted false) (real true)
  have two := measureTVDist_triangle (restricted false) (restricted true) (real true)
  rw [measureTVDist_comm (real false) (restricted false)] at one
  exact one.trans ((add_le_add (each false) (two.trans (add_le_add inner (each true)))).trans_eq (by unfold err; ring))

theorem pinned_final_reference_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (pinnedViewReference adversary build compress false)
      (pinnedViewReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2^120) := by
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : budget+1 ≤ 2^120
  · apply (shared_final_reference_hiding_sharp adversary build compress budget bounded small).trans
    have nonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · refine (measureTVDist_le_one _ _).trans ?_
    have large : 2^120 ≤ budget + 1 := by omega
    have castLarge : (2 : ℝ)^120 ≤ (budget : ℝ) + 1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^120)).2 (by simpa using castLarge)

end TwoPermutationPrototype.Sampling
