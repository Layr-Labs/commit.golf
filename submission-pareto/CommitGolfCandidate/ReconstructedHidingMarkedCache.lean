import CommitGolfCandidate.ReconstructedHidingMarkedPath
import CommitGolfCandidate.ReconstructedHidingProgram

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp TwoPermutationPrototype.Sampling CommitGolfCandidate.Permutation HidingTape
open CommitGolfCandidate.Permutation.NonceChain (mean accept)
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local irreducible] cacheTrace checkedQueries toStrat Trace.ext

noncomputable def markedCache {S A : Type} (c : Compression) (table : Cache) (seed : ProbComp S)
    (π : S → Perm → Perm) (allow : S → Reply → Reply → Bool) (gate : S → Bool)
    (g : OracleComp World A) : ProbComp (A × Bool) := do
  let s ← seed
  let p ← table.sample
  fixedOracleRun ⟨c,π s ((BiPermutation.equiv Block).symm p.val)⟩ (checkedQueries (allow s) g (gate s))

theorem marked_cache_mean {S A : Type} (c : Compression) (table : Cache) (seed : ProbComp S) (rep : UniformSource seed)
    (π : S → Perm → Perm) (allow : S → Reply → Reply → Bool) (gate : S → Bool) (g : OracleComp World A)
    (ev : A × Bool → Prop) :
    let st : PState Reply := ⟨cacheTrace table,(cacheTrace table).length⟩
    (Pr{let v ← markedCache c table seed π allow gate g}[ev v]).toReal =
      @mean rep.Seed rep.finite (fun k => avg (cacheTrace table).ext (fun p =>
        (toStrat c (checkedQueries (allow (rep.read k)) g (gate (rep.read k)))).eager (π (rep.read k) p) st
          (fun a _ => ind (ev a)))) := by
  dsimp only
  unfold markedCache
  rw [rep.bind_mean]
  apply avg_congr
  intro k _
  let st : PState Reply := ⟨cacheTrace table,(cacheTrace table).length⟩
  let run (p : Perm) :=
    fixedOracleRun ⟨c,π (rep.read k) p⟩ (checkedQueries (allow (rep.read k)) g (gate (rep.read k)))
  change (Pr{let v ← (table.sample >>= fun p => run ((BiPermutation.equiv Block).symm p.val))}[ev v]).toReal = _
  rw [cache_bind_mean]
  apply avg_congr
  intro p _
  change (Pr{let v ← fixedOracleRun ⟨c,π (rep.read k) p⟩ _}[ev v]).toReal = _
  rw [fixed_run_prob c _ _ ev st]
  exact ENNReal.toReal_ofReal (Strat.eager_nonneg _ (fun _ _ => ind_nonneg _) _ _)

theorem marked_cache_lower {S A : Type} (c : Compression) (table : Cache) (seed : ProbComp S)
    (perm : S → Perm → Perm) (origin allowed : S → Reply → Reply → Bool) (gate actualFlag : S → Bool)
    (pass : ∀ s ∈ support seed, gate s=true → actualFlag s=true)
    (agree : ∀ s ∈ support seed, gate s=true → ∀ p ∈ (cacheTrace table).ext, ∀ x,
      origin s x (p x)=true → perm s p x=p x ∧ allowed s x (p x)=true)
    (g : OracleComp World A) (ev : A → Prop) :
    (Pr{let v ← markedCache c table seed (fun _ p => p) origin gate g}[ev v.1 ∧ v.2=true]).toReal ≤
      (Pr{let v ← markedCache c table seed perm allowed actualFlag g}[ev v.1 ∧ v.2=true]).toReal := by
  classical
  let rep := Classical.choice (uniform_source seed)
  rw [marked_cache_mean c table seed rep,marked_cache_mean c table seed rep]
  apply avg_mono
  intro k _
  apply avg_mono
  intro p old
  cases h : gate (rep.read k) with
  | false =>
    exact (spoiled_eager _ c p g _ (fun v => ind (ev v.1 ∧ v.2=true)) 0 (fun _ => ind_neg (by simp))).le.trans
      (Strat.eager_nonneg _ (fun _ _ => ind_nonneg _) _ _)
  | true =>
    have supportS := rep.read_support k
    have same := agree (rep.read k) supportS h p old
    rw [pass (rep.read k) supportS h]
    exact marked_lower (origin (rep.read k)) (allowed (rep.read k)) c p (perm (rep.read k) p)
      (fun x hx => same x hx) g ⟨cacheTrace table,(cacheTrace table).length⟩ ev

theorem marked_cache_loss {S A : Type} (c : Compression) (table : Cache) (seed : ProbComp S)
    (ins outs : S → Finset Reply) (gate : S → Bool) (g : OracleComp World A) (q : Nat) (bounded : PublicQueryBound g q)
    (u Q : Nat) (δ : ℝ) (nonneg : 0≤δ) (room : Q < Fintype.card Reply) (fit : table.entries.length+q ≤ Q)
    (sizeIn : ∀ s ∈ support seed, (ins s).card ≤ u) (sizeOut : ∀ s ∈ support seed, (outs s).card ≤ u)
    (directIn : ∀ x, (Pr{let s ← seed}[x ∈ ins s]).toReal ≤ δ)
    (directOut : ∀ y, (Pr{let s ← seed}[y ∈ outs s]).toReal ≤ δ)
    (cacheRisk : ∀ x y, (x,y)∈table.entries → (Pr{let s ← seed}[x∈ins s ∨ y∈outs s]).toReal ≤ δ) :
    (Pr{let v ← markedCache c table seed (fun _ p => p) (permitSets ins outs) gate g}[v.2=false]).toReal ≤
      (Pr{let s ← seed}[gate s=false]).toReal + (q:ℝ)*(δ+u/((Fintype.card Reply:ℝ)-Q)) := by
  classical
  let rep := Classical.choice (uniform_source seed)
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  let ti (k : rep.Seed) := ins (rep.read k)
  let out (k : rep.Seed) := outs (rep.read k)
  let t := cacheTrace table
  let st : PState Reply := ⟨t,t.length⟩
  let str := toStrat c g
  have pay := adaptive_hit_bound t (cache_well table) ti out u Q δ nonneg room
    (fun k => sizeIn _ (rep.read_support k)) (fun k => sizeOut _ (rep.read_support k))
    (fun x => (rep.event (fun s => x∈ins s)).symm.le.trans (directIn x))
    (fun y => (rep.event (fun s => y∈outs s)).symm.le.trans (directOut y))
    (fun x y known => (rep.event (fun s => x∈ins s ∨ y∈outs s)).symm.le.trans
      (cacheRisk x y ((cache_pair table x y).mp known))) str q (to_strat_QB c bounded)
    (by have h := cache_length table; change (cacheTrace table).length+q≤Q; omega)
  rw [marked_cache_mean c table seed rep,rep.event]
  refine le_trans ?_ (add_le_add le_rfl pay)
  rw [←avg_add]
  apply avg_mono
  intro k _
  cases h : gate (rep.read k) with
  | false =>
    rw [ind_pos rfl]
    refine (avg_le (by norm_num : (0:ℝ)≤1) (fun p _ => (spoiled_eager _ c p g st _ 1 (fun _ => ind_pos rfl)).le)).trans ?_
    have positive := Strat.exp_nonneg (fun (b : Bool) (_ : PState Reply) => ind_nonneg (b=true)) (stopOnHit ti out k str) st
    exact le_add_of_nonneg_right ((stop_exp ti out k str st) ▸ positive)
  | true =>
    rw [ind_neg (by decide : ¬true=false),zero_add]
    change avg t.ext (fun p => (toStrat c (checkedQueries (permitSets ins outs (rep.read k)) g true)).eager p st
      (fun v _ => ind (v.2=false))) ≤ _
    have eq (p : Perm) := marked_failure ti out k c p g st
    refine le_of_eq ((avg_congr (fun p _ => eq p)).trans ?_)
    unfold avg
    change (∑ p ∈ st.trace.ext, (stopOnHit ti out k str).eager p st (fun b _ => accept b)) / t.ext.card = _
    rw [(stopOnHit ti out k str).sum_eager st (cache_well table) _]
    have nz : (t.ext.card:ℝ) ≠ 0 := by exact_mod_cast (cache_has_completion table).card_ne_zero
    change (t.ext.card:ℝ) * (stopOnHit ti out k str).exp st _ / t.ext.card = _
    rw [mul_div_cancel_left₀ _ nz]
    exact stop_exp ti out k str st

end CommitGolfCandidate.Reconstruction.HidingTraffic
