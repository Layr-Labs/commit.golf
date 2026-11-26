import CommitGolfCandidate.ReconstructedHidingHonestOutput
import CommitGolfCandidate.ReconstructedHidingMarkedAlgebra

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic HidingReplay TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
attribute [local irreducible] guardedView queryDigests checkedQueries tapeFromReplies pinnedFullLeafDigests
local instance smoothDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def honestCost : ℝ := (2*LENGTH:ℝ)*((groupCount:ℝ)/((2:ℝ)^1600-2^122))

section Game
variable {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (q : Nat) (build : TranscriptBuilder)
    (c : Compression) (b : Bool) (ch : Hiding.HidingChallenge S n) (base : Cache) (z : Key × GenReplies)

noncomputable def guardedObserver (op : OpenedSalts ch.positions) (ds : DigestTape) : OracleComp World O :=
  let view := build c ch.positions op ds
  guardedView a q ch.aux view.1 view.2

noncomputable def smoothObserve (op : OpenedSalts ch.positions) (allow : Reply → Reply → Bool) (start : Bool)
    (ds : DigestTape) (p : BiPermutation Block) : ProbComp (O × Bool) :=
  fixedOracleRun (fixedOracle c p) (checkedQueries allow (guardedObserver a q build c ch op ds) start)

open Classical in
noncomputable def smoothBranch : ProbComp (O × Bool) := do
  let r := widenTape (tapeFromReplies z.2)
  let p ← base.sample
  let m := if b then ch.message₁ else ch.message₀
  let ds := pinnedFullLeafDigests p.val m r
  smoothObserve a q build c ch (fun i => r i.val) (genPermit z.1 z.2)
    (decide (baseGood base (pinnedFirstAddresses ch.message₀ ch.message₁) z)) ds p.val

open Classical in
theorem marked_branch_shape :
    markedBranch a q build c b ch base z =
      (do
        let r := widenTape (tapeFromReplies z.2)
        let allow := genPermit z.1 z.2
        let p ← base.sample
        let m := if b then ch.message₁ else ch.message₀
        let ds := pinnedFullLeafDigests p.val m r
        let v ← smoothObserve a q build c ch (fun i => r i.val) allow
          (cacheAllow allow base && allLeafFlags allow p.val m r) ds p.val
        pure (v.1,v.2 && decide (Function.Injective z.2))) := by
  unfold markedBranch
  apply bind_congr
  intro p
  let m := if b then ch.message₁ else ch.message₀
  let r := widenTape (tapeFromReplies z.2)
  let allow := genPermit z.1 z.2
  have h := checked_digests_flags (fixedOracle c p.val) allow m r (cacheAllow allow base)
  simp only [fixedOracle,Equiv.apply_symm_apply] at h
  unfold afterChoose
  rw [checked_bind,fixed_oracle_run_bind]
  let step := fixedOracleRun (fixedOracle c p.val) (checkedQueries allow (queryDigests m r) (cacheAllow allow base))
  let next := fun v : DigestTape × Bool => smoothObserve a q build c ch (fun i => r i.val) allow v.2 v.1 p.val
  let marker := fun v : O × Bool => (pure (v.1,v.2 && decide (Function.Injective z.2)) : ProbComp _)
  change ((step >>= next) >>= marker) = (next (pinnedFullLeafDigests p.val m r,cacheAllow allow base && allLeafFlags allow p.val m r) >>= marker)
  have answer : step = pure (pinnedFullLeafDigests p.val m r,cacheAllow allow base && allLeafFlags allow p.val m r) := h
  rw [answer,pure_bind]

theorem smooth_branch_retained (ev : O → Prop) (room : base.entries.length+2*LENGTH ≤ 2^122) :
    (Pr{let v ← smoothBranch a q build c b ch base z}[retained ev v]).toReal ≤
      (Pr{let v ← markedBranch a q build c b ch base z}[retained ev v]).toReal+honestCost := by
  classical
  let m := if b then ch.message₁ else ch.message₀
  let raw := pinnedFirstAddresses ch.message₀ ch.message₁
  let r := widenTape (tapeFromReplies z.2)
  let allow := genPermit z.1 z.2
  let good := baseGood base raw z
  let run (p : Completion base.entries) (start : Bool) := smoothObserve a q build c ch (fun i => r i.val)
    allow start (pinnedFullLeafDigests p.val m r) p.val
  let keep (v : O × Bool) := (v.1,v.2 && decide (Function.Injective z.2))
  let f (p : Completion base.entries) := run p (decide good)
  let g (p : Completion base.entries) := do
    let v ← run p (cacheAllow allow base && allLeafFlags allow p.val m r)
    pure (keep v)
  rw [marked_branch_shape]
  change (Pr{let v ← (base.sample >>= f)}[retained ev v]).toReal ≤ (Pr{let v ← (base.sample >>= g)}[retained ev v]).toReal+_
  by_cases admitted : good
  · have cgood := base_gen_cache base raw z admitted
    have inj := base_replies_inj base raw z admitted
    have key := base_first_safe base ch.message₀ ch.message₁ z admitted b
    have cost := honest_output_loss base c m r z.1 z.2 cgood key room
    refine (real_bind_mark base.sample f g (retained ev) (fun p => allLeafFlags allow p.val m r=false) ?_).trans
      (add_le_add le_rfl cost)
    intro p _ clear
    have pass : allLeafFlags allow p.val m r = true := Bool.eq_true_of_not_eq_false clear
    have outside : g p = f p := by
      have same : keep = id := by funext v; simp [keep,inj]
      simp only [g,f,show cacheAllow allow base=true from cgood,pass,Bool.true_and,admitted,decide_true,same,id_eq,bind_pure]
    rw [outside]
  · have left (p : Completion base.entries) : Pr{let v ← f p}[retained ev v]=0 := by
      simp only [f,admitted,decide_false,run,smoothObserve]
      exact checked_closed_zero _ _ _ ev
    have bound := real_bind_add base.sample f g (retained ev) 0 (fun p _ => by rw [left p,ENNReal.toReal_zero,add_zero]; exact ENNReal.toReal_nonneg)
    rw [add_zero] at bound
    exact bound.trans (le_add_of_nonneg_right (by unfold honestCost; norm_num))

end Game
end CommitGolfCandidate.Reconstruction.HidingTape
