import CommitGolfCandidate.ReconstructedHidingSampler
import CommitGolfCandidate.ReconstructedHidingCache

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp TwoPermutationPrototype.Sampling CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
local instance integralDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem uniform_ind {X : Type} [Fintype X] [SampleableType X] (e : X → Prop) :
    (Pr{let x ← $ᵗ X}[e x]).toReal = mean (fun x => ind (e x)) := by
  classical
  rw [SampleableType.prEvent_uniformSample,ENNReal.toReal_div,
    ENNReal.toReal_natCast,ENNReal.toReal_natCast]
  simp only [mean,avg,sum_ind,Finset.card_univ]

theorem uniform_bind_mean {X A : Type} [Fintype X] [SampleableType X]
    (next : X → ProbComp A) (e : A → Prop) :
    (Pr{let a ← (($ᵗ X) >>= next)}[e a]).toReal = mean (fun x => (Pr{let a ← next x}[e a]).toReal) := by
  classical
  have eq : Pr{let a ← (($ᵗ X) >>= next)}[e a] =
      ENNReal.ofReal (mean fun x => (Pr{let a ← next x}[e a]).toReal) := by
    rw [prEvent_bind_eq_sum_fintype,← sum_inv_card_mul_ofReal _ (fun _ => ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro x _
    rw [SampleableType.prEvent_uniformSample_eq_singleton,ENNReal.ofReal_toReal (prEvent_ne_top _)]
  rw [eq,ENNReal.toReal_ofReal (avg_nonneg (fun _ _ => ENNReal.toReal_nonneg))]

noncomputable def UniformSource.seedSample {A : Type} {p : ProbComp A} (rep : UniformSource p) : ProbComp rep.Seed := by
  classical
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  let : SampleableType rep.Seed := SampleableType.ofFintype _
  exact $ᵗ rep.Seed

theorem UniformSource.law {A : Type} {p : ProbComp A} (rep : UniformSource p) :
    p =ᵈ (rep.read <$> rep.seedSample) := by
  classical
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  let : SampleableType rep.Seed := SampleableType.ofFintype _
  apply evalDistEq_of_forall_prEvent_eq_output
  intro a
  rw [prEvent_map]
  apply le_antisymm
  all_goals
    apply (ENNReal.toReal_le_toReal (prEvent_ne_top _) (prEvent_ne_top _)).mp
    rw [rep.event]
    simp only [UniformSource.seedSample,uniform_ind]
    exact le_rfl

theorem UniformSource.read_support {A : Type} {p : ProbComp A} (rep : UniformSource p) (s : rep.Seed) :
    rep.read s ∈ support p := by
  classical
  rw [support_eq_of_evalDistEq rep.law,support_map]
  refine ⟨s,?_,rfl⟩
  simp [UniformSource.seedSample]

theorem UniformSource.bind_mean {B A : Type} {p : ProbComp B} (rep : UniformSource p)
    (next : B → ProbComp A) (e : A → Prop) :
    (Pr{let a ← (p >>= next)}[e a]).toReal =
      @mean rep.Seed rep.finite (fun s => (Pr{let a ← next (rep.read s)}[e a]).toReal) := by
  classical
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  let : SampleableType rep.Seed := SampleableType.ofFintype _
  rw [(rep.law.bind_left next).prEvent_eq e,bind_map_left]
  exact uniform_bind_mean _ _

theorem cache_bind_mean {A : Type} (c : Cache) (next : Equiv.Perm Block → ProbComp A) (e : A → Prop) :
    (Pr{let a ← (c.sample >>= fun p => next ((BiPermutation.equiv Block).symm p.val))}[e a]).toReal =
      avg (cacheTrace c).ext (fun π => (Pr{let a ← next π}[e a]).toReal) := by
  classical
  let : Fintype (Completion c.entries) := cacheCompletionFinite c
  let : SampleableType (Completion c.entries) := c.completionSampler
  exact (@uniform_bind_mean (Completion c.entries) A (cacheCompletionFinite c) c.completionSampler _ _).trans (completion_mean c (fun π => (Pr{let a ← next π}[e a]).toReal))

end CommitGolfCandidate.Reconstruction.HidingTraffic
