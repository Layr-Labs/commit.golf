import CommitGolfCandidate.ReconstructedHidingIntegrate
import CommitGolfCandidate.SharedPinnedAdaptive

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp TwoPermutationPrototype.Sampling CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean)
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
local instance programDiscrete {α : Type} : MeasurableSpace α := ⊤

abbrev Paired := List Row × List Row
def rowInputs (r : Paired) := ((r.1++r.2).map Prod.fst).toFinset
def rowOutputs (r : Paired) := ((r.1++r.2).map Prod.snd).toFinset
def sideRows (w : Bool) (r : Paired) := if w then r.2 else r.1

private theorem untouched (p : Equiv.Perm Block) (r : Paired) (w : Bool) (x : Block)
    (off : ¬(x ∈ rowInputs r ∨ p x ∈ rowOutputs r)) :
    (((BiPermutation.equiv Block p).programRows (sideRows w r)).forward x) = p x := by
  apply BiPermutation.program_rows_forward_unchanged
  intro row included
  have both : row ∈ r.1++r.2 := by cases w <;> simp_all [sideRows]
  constructor
  · intro eq
    exact off (Or.inl (List.mem_toFinset.mpr (List.mem_map.mpr ⟨row,both,eq.symm⟩)))
  · intro eq
    exact off (Or.inr (List.mem_toFinset.mpr (List.mem_map.mpr ⟨row,both,eq.symm⟩)))

noncomputable def changedRun {A : Type} (c : Compression) (base : Cache) (pairs : ProbComp Paired)
    (g : OracleComp World A) (w : Bool) : ProbComp A := do
  let rs ← pairs
  let p ← base.sample
  fixedOracleRun (fixedOracle c (p.val.programRows (sideRows w rs))) g

attribute [local irreducible] cacheTrace

/-- TV comparison for the actual VCVio oracle interface, with two correlated
programmed row lists. It counts both inputs and outputs on a cached row but
charges their joint probability. New rows have one chosen and one random end. -/
theorem changed_distance {A : Type} (c : Compression) (base : Cache) (pairs : ProbComp Paired)
    (g : OracleComp World A) (q : Nat) (bounded : PublicQueryBound g q)
    (u Q : Nat) (δ : ℝ) (nonneg : 0 ≤ δ) (room : Q < Fintype.card Block)
    (fit : base.entries.length+q ≤ Q)
    (number : ∀ r ∈ support pairs, (r.1++r.2).length ≤ u)
    (directIn : ∀ x, (Pr{let r ← pairs}[x ∈ rowInputs r]).toReal ≤ δ)
    (directOut : ∀ y, (Pr{let r ← pairs}[y ∈ rowOutputs r]).toReal ≤ δ)
    (cacheRisk : ∀ x y, (x,y) ∈ base.entries →
      (Pr{let r ← pairs}[x ∈ rowInputs r ∨ y ∈ rowOutputs r]).toReal ≤ δ) :
    measureTVDist (changedRun c base pairs g false) (changedRun c base pairs g true)
      ≤ (q:ℝ)*(δ+u/((Fintype.card Block:ℝ)-Q)) := by
  classical
  let rep := Classical.choice (uniform_source pairs)
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  let ins (k : rep.Seed) := rowInputs (rep.read k)
  let outs (k : rep.Seed) := rowOutputs (rep.read k)
  let perm (w : Bool) (k : rep.Seed) (p : Equiv.Perm Block) :=
    (BiPermutation.equiv Block).symm ((BiPermutation.equiv Block p).programRows (sideRows w (rep.read k)))
  let st : PState Block := ⟨cacheTrace base,(cacheTrace base).length⟩
  let strategy := toStrat c g
  have pay := adaptive_hit_bound (cacheTrace base) (cache_well base) ins outs u Q δ nonneg room
    (fun k => (List.toFinset_card_le _).trans (by simpa only [List.length_map] using number (rep.read k) (rep.read_support k)))
    (fun k => (List.toFinset_card_le _).trans (by simpa only [List.length_map] using number (rep.read k) (rep.read_support k)))
    (fun x => ((rep.event (fun s => x ∈ rowInputs s)).symm.le.trans (directIn x)))
    (fun y => ((rep.event (fun s => y ∈ rowOutputs s)).symm.le.trans (directOut y)))
    (fun x y known => ((rep.event (fun s => x ∈ rowInputs s ∨ y ∈ rowOutputs s)).symm.le.trans
      (cacheRisk x y ((cache_pair base x y).mp known))))
    strategy q (to_strat_QB c bounded) (by have := cache_length base; omega)
  have event (ev : A → Prop) (w : Bool) : (Pr{let a ← changedRun c base pairs g w}[ev a]).toReal =
      mean (fun k : rep.Seed => avg (cacheTrace base).ext (fun p =>
        strategy.eager (perm w k p) st (fun a _ => ind (ev a)))) := by
    unfold changedRun
    rw [rep.bind_mean]
    apply avg_congr
    intro k _
    let next (p : Equiv.Perm Block) := fixedOracleRun ⟨c,perm w k p⟩ g
    have sw : (base.sample >>= fun p => fixedOracleRun (fixedOracle c (p.val.programRows (sideRows w (rep.read k)))) g) =
        (base.sample >>= fun p => next ((BiPermutation.equiv Block).symm p.val)) := by
      simp only [next,perm,Equiv.apply_symm_apply,fixedOracle]
    rw [sw,cache_bind_mean]
    apply avg_congr
    intro π _
    change (Pr{let a ← fixedOracleRun ⟨c,perm w k π⟩ g}[ev a]).toReal = _
    rw [fixed_run_prob c (perm w k π) g ev st,ENNReal.toReal_ofReal (Strat.eager_nonneg _
      (fun _ _ => ind_nonneg _) _ _)]
  have direction (l r : Bool) (ev : A → Prop) :
      (Pr{let a ← changedRun c base pairs g l}[ev a]).toReal ≤
        (Pr{let a ← changedRun c base pairs g r}[ev a]).toReal + (q:ℝ)*(δ+u/((Fintype.card Block:ℝ)-Q)) := by
    rw [event ev l,event ev r]
    have close := completion_worlds (cacheTrace base) (cache_well base) (cache_has_completion base)
      ins outs (perm l) (perm r)
      (fun k p _ x off => ⟨untouched p (rep.read k) l x off,untouched p (rep.read k) r x off⟩)
      strategy ev
    exact close.trans (add_le_add le_rfl pay)
  have pos : 0 < (Fintype.card Block:ℝ)-Q := sub_pos.mpr (by exact_mod_cast room)
  apply tv_le_of_events _ _ _ (mul_nonneg (Nat.cast_nonneg _) (add_nonneg nonneg (div_nonneg (Nat.cast_nonneg _) pos.le)))
  intro ev
  have forward := direction false true ev
  have backward := direction true false ev
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end CommitGolfCandidate.Reconstruction.HidingTraffic
