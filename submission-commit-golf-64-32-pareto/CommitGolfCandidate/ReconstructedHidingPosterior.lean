import CommitGolfCandidate.ReconstructedHidingTranscript
import CommitGolfCandidate.ReconstructedHidingOpenings
import CommitGolfCandidate.ReconstructedHidingPinned
import CommitGolfCandidate.TwoPermutationPinnedEagerPosterior

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048

noncomputable local instance posteriorSalt : SampleableType PrivateSalts := by classical exact SampleableType.ofFintype _
noncomputable local instance posteriorOpen (p : Positions) : SampleableType (OpenIx p → Salt) := by
  classical exact SampleableType.ofFintype _
noncomputable local instance posteriorClosed (p : Positions) : SampleableType (ClosedIx p → Salt) := by
  classical exact SampleableType.ofFintype _

theorem sample_salt_split {A : Type} (p : Positions) (next : PrivateSalts → ProbComp A) :
    (($ᵗ PrivateSalts) >>= next) =ᵈ (do
      let op ← $ᵗ (OpenIx p → Salt)
      let cl ← $ᵗ (ClosedIx p → Salt)
      next (joinSalts p op cl)) := by
  apply (uniform_transport_bind (transportOfEquiv (openClose p)) next).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc,pure_bind]
  rfl

noncomputable def independentReference {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (c : Compression) (b : Bool) : ProbComp O := do
  let p ← (PermutationCache.empty Block).sample
  let ch ← eagerRun c p.val a.choose
  let r ← $ᵗ PrivateSalts
  observeTranscriptView a (pinnedHonestView build) c ch b p.val (widenTape r)

noncomputable def independentPosterior {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (c : Compression) (b : Bool) : ProbComp O := do
  let (ch,base) ← lazyRun c a.choose (PermutationCache.empty Block)
  let op ← $ᵗ (OpenIx ch.positions → Salt)
  let cl ← $ᵗ (ClosedIx ch.positions → Salt)
  let p ← base.sample
  let m := if b then ch.message₁ else ch.message₀
  let full := widenTape (joinSalts ch.positions op cl)
  let digest := pinnedFullLeafDigests p.val m full
  pinnedObserveTape a build c ch (fun i => (op i).setWidth 128) digest p.val

theorem sampled_independent_reference {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (b : Bool) :
    sampledIndependent a build b =ᵈ (($ᵗ Compression) >>= fun c => independentReference a build c b) := by
  unfold sampledIndependent Oracle.sample
  simp only [bind_assoc,pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro c
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (π : Perm) := do
    let ch ← fixedOracleRun ⟨c,π⟩ a.choose
    let r ← $ᵗ PrivateSalts
    observeTranscriptView a (pinnedHonestView build) c ch b (BiPermutation.equiv Block π) (widenTape r)
  apply (uniform_transport_bind emptyTransport next).trans
  unfold independentReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next,← eager_fixed_handler,emptyTransport,Equiv.apply_symm_apply]
  rfl

theorem independent_eager_posterior {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (c : Compression) (b : Bool) :
    independentReference a build c b =ᵈ independentPosterior a build c b := by
  let finish := fun ch p => ($ᵗ PrivateSalts) >>= fun s =>
    observeTranscriptView a (pinnedHonestView build) c ch b p (widenTape s)
  apply (adaptive_posterior_equivalence c a.choose (PermutationCache.empty Block) finish).trans
  unfold independentPosterior
  apply EvalDistEq.bind_right
  rintro ⟨ch,base⟩
  let observe (p : Completion base.entries) (s : PrivateSalts) :=
    observeTranscriptView a (pinnedHonestView build) c ch b p.val (widenTape s)
  apply (EvalDistEq.bind_right base.sample (fun p => sample_salt_split ch.positions (observe p))).trans
  let tail (op : OpenIx ch.positions → Salt) (p : Completion base.entries) :=
    ($ᵗ (ClosedIx ch.positions → Salt)) >>= fun cl => observe p (joinSalts ch.positions op cl)
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm base.sample ($ᵗ (OpenIx ch.positions → Salt))
    (fun p op => tail op p))).trans
  apply EvalDistEq.bind_right
  intro op
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm base.sample ($ᵗ (ClosedIx ch.positions → Salt))
    (fun p cl => observe p (joinSalts ch.positions op cl)))).trans
  apply EvalDistEq.bind_right
  intro cl
  apply EvalDistEq.bind_right
  intro p
  have opened : (fun i : {i : Index // i ∈ ch.positions} => widenTape (joinSalts ch.positions op cl) i.val) =
      (fun i => (op i).setWidth 128) := by
    funext i
    apply congrArg (fun v : Salt => v.setWidth 128)
    exact dite_eq_left i.property
  unfold observe observeTranscriptView pinnedHonestView pinnedObserveTape
  rw [opened]
  rfl

end CommitGolfCandidate.Reconstruction.HidingTape
