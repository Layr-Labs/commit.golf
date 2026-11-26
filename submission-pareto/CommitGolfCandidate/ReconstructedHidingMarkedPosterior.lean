import CommitGolfCandidate.ReconstructedHidingCheckedHonest
import CommitGolfCandidate.ReconstructedHidingRetainedGame

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] keptKey keptReplies
local instance stageDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem checked_posterior {S A : Type} (c : Compression) (choose : OracleComp World S)
    (next : S → OracleComp World A) (allow : Reply → Reply → Bool) :
    (($ᵗ Perm) >>= fun π => fixedOracleRun ⟨c,π⟩ (checkedQueries allow (choose >>= next) true)) =ᵈ
      (do let (v,cache) ← lazyRun c choose (PermutationCache.empty Block)
          let p ← cache.sample
          fixedOracleRun (fixedOracle c p.val) (checkedQueries allow (next v) (cacheAllow allow cache))) := by
  let base := PermutationCache.empty Block
  let selected := checkedQueries allow choose true
  let run (π : Perm) := fixedOracleRun ⟨c,π⟩ (checkedQueries allow (choose >>= next) true)
  let finish (v : S × Bool) (p : BiPermutation Block) :=
    fixedOracleRun (fixedOracle c p) (checkedQueries allow (next v.1) v.2)
  let : SampleableType (Completion base.entries) := base.completionSampler
  apply (uniform_transport_bind emptyTransport run).trans
  trans (base.sample >>= fun p => eagerRun c p.val selected >>= fun v => finish v p.val)
  · apply EvalDistEq.bind_right base.sample
    intro p
    simp only [run,checked_bind,fixed_oracle_run_bind,←eager_fixed_handler,emptyTransport,Equiv.apply_symm_apply]
    apply EvalDistEq.bind_right
    intro v
    have same := eager_fixed_handler c ((BiPermutation.equiv Block).symm p.val) (checkedQueries allow (next v.1) v.2)
    rw [Equiv.apply_symm_apply] at same
    rw [same]
    rfl
  · apply (adaptive_posterior_equivalence c selected base finish).trans
    have descent : lazyRun c selected base = (fun v : S × Cache => ((v.1,cacheAllow allow v.2),v.2)) <$> lazyRun c choose base :=
      checked_lazy_cache allow c choose base
    rw [descent,bind_map_left]

noncomputable def afterChoose {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (q : Nat)
    (build : TranscriptBuilder) (c : Compression) (b : Bool) (salts : PrivateSalts) (ch : Hiding.HidingChallenge S n) :
    OracleComp World O := do
  let r := widenTape salts
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let v := build c ch.positions (fun i => r i.val) ds
  guardedView a q ch.aux v.1 v.2

open Classical in
noncomputable def markedBranch {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (q : Nat) (build : TranscriptBuilder) (c : Compression) (b : Bool) (ch : Hiding.HidingChallenge S n)
    (cache : Cache) (s : Key × GenReplies) : ProbComp (O × Bool) := do
  let allow := genPermit s.1 s.2
  let p ← cache.sample
  let v ← fixedOracleRun (fixedOracle c p.val) (checkedQueries allow
    (afterChoose a q build c b (tapeFromReplies s.2) ch) (cacheAllow allow cache))
  pure (v.1,v.2 && decide (Function.Injective s.2))

noncomputable def markedPosterior {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (q : Nat) (build : TranscriptBuilder) (c : Compression) (b : Bool) : ProbComp (O × Bool) := do
  let (ch,cache) ← lazyRun c a.choose (PermutationCache.empty Block)
  let s ← $ᵗ (Key × GenReplies)
  markedBranch a q build c b ch cache s

theorem marked_posterior_eq {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (q : Nat) (build : TranscriptBuilder) (c : Compression) (b : Bool) :
    markedIndependent c (fun r => chainPublicComp a q build c b (widenTape r)) =ᵈ
      markedPosterior a q build c b := by
  classical
  let prior := lazyRun c a.choose (PermutationCache.empty Block)
  let seeds := ($ᵗ (Key × GenReplies))
  let finish (s : Key × GenReplies) (p : Hiding.HidingChallenge S n × Cache) :=
    markedBranch a q build c b p.1 p.2 s
  trans (seeds >>= fun s => prior >>= finish s)
  · unfold markedIndependent seeds
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [bind_assoc,pure_bind]
    apply EvalDistEq.bind_right
    intro k
    apply EvalDistEq.bind_right
    intro y
    let next := afterChoose a q build c b (tapeFromReplies y)
    let mark : O×Bool → ProbComp (O×Bool) := fun v => pure (v.1,v.2 && decide (Function.Injective y))
    have paired := (checked_posterior c a.choose next (genPermit k y)).bind_left mark
    simp only [bind_assoc] at paired
    exact paired
  · exact EvalDistEq.of_evalDist_eq (distribution_bind_comm seeds prior finish)

end CommitGolfCandidate.Reconstruction.HidingTape
