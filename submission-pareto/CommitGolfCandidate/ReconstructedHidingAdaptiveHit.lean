import CommitGolfCandidate.ReconstructedHidingAdaptiveRun

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {S K A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype K] [Nonempty K]

open Classical in
noncomputable def hitProb (ins outs : K → Finset S) (k : K) : Strat S A → Trace S → ℝ
  | .done _, _ => 0
  | .rand _ next,t => avg univ fun i => hitProb ins outs k (next i) t
  | .fwd x next,t => avg (t.fwdAns x) fun y =>
      if touches ins outs k x y then 1 else hitProb ins outs k (next y) (t.stepF x y)
  | .inv y next,t => avg (t.invAns y) fun x =>
      if touches ins outs k x y then 1 else hitProb ins outs k (next x) (t.stepI x y)

theorem tally_nonneg (base : Trace S) (ins outs : K → Finset S) (k : K)
    (g : Strat S A) (t : Trace S) : 0 ≤ tally base ins outs k g t := by
  induction g generalizing t with
  | done a => exact le_refl _
  | rand m n ih => exact avg_nonneg (fun i _ => ih i t)
  | fwd x n ih => exact avg_nonneg (fun y _ => add_nonneg (ind_nonneg _) (ih y (t.stepF x y)))
  | inv y n ih => exact avg_nonneg (fun x _ => add_nonneg (ind_nonneg _) (ih x (t.stepI x y)))

def clean (base t : Trace S) (ins outs : K → Finset S) (k : K) : Prop :=
  ∀ e ∈ t, ¬containsPair base e.inp e.out → ¬touches ins outs k e.inp e.out

private theorem hit_billable (base t : Trace S) (ins outs : K → Finset S) (k : K)
    (clear : clean base t ins outs k) (x y : S) (hit : touches ins outs k x y) :
    billable base t x y := by
  by_cases original : containsPair base x y
  · exact Or.inl original
  · refine Or.inr ?_
    rintro ⟨e,known,input,output⟩
    subst x; subst y
    exact clear e known original hit

private theorem clean_cons (base t : Trace S) (ins outs : K → Finset S) (k : K) (e : Entry S)
    (clear : clean base t ins outs k) (safe : ¬touches ins outs k e.inp e.out) :
    clean base (e::t) ins outs k := by
  intro row present original
  rcases List.mem_cons.mp present with rfl | old
  · exact safe
  · exact clear row old original

private theorem clean_fwd (base t : Trace S) (ins outs : K → Finset S) (k : K) (x y : S)
    (clear : clean base t ins outs k) (safe : ¬touches ins outs k x y) : clean base (t.stepF x y) ins outs k := by
  unfold Trace.stepF
  split
  · exact clear
  · exact clean_cons base t ins outs k ⟨.fwd,x,y⟩ clear safe

private theorem clean_inv (base t : Trace S) (ins outs : K → Finset S) (k : K) (x y : S)
    (clear : clean base t ins outs k) (safe : ¬touches ins outs k x y) : clean base (t.stepI x y) ins outs k := by
  unfold Trace.stepI
  split
  · exact clear
  · exact clean_cons base t ins outs k ⟨.inv,x,y⟩ clear safe

theorem hit_le_tally (base : Trace S) (ins outs : K → Finset S) (k : K) (g : Strat S A)
    (t : Trace S) (clear : clean base t ins outs k) :
    hitProb ins outs k g t ≤ tally base ins outs k g t := by
  classical
  induction g generalizing t with
  | done _ => exact le_refl _
  | rand m n ih => exact avg_mono (fun i _ => ih i t clear)
  | fwd x next ih =>
    apply avg_mono
    intro y _
    by_cases hit : touches ins outs k x y
    · rw [ite_eq_left hit,ind_pos ⟨hit_billable base t ins outs k clear x y hit,hit⟩]
      exact le_add_of_nonneg_right (tally_nonneg base ins outs k (next y) (t.stepF x y))
    · rw [ite_eq_right hit,ind_neg (fun h => hit h.2),zero_add]
      exact ih y (t.stepF x y) (clean_fwd base t ins outs k x y clear hit)
  | inv y next ih =>
    apply avg_mono
    intro x _
    by_cases hit : touches ins outs k x y
    · rw [ite_eq_left hit,ind_pos ⟨hit_billable base t ins outs k clear x y hit,hit⟩]
      exact le_add_of_nonneg_right (tally_nonneg base ins outs k (next x) (t.stepI x y))
    · rw [ite_eq_right hit,ind_neg (fun h => hit h.2),zero_add]
      exact ih x (t.stepI x y) (clean_inv base t ins outs k x y clear hit)

/-- A full adaptive observer incurs a single chosen-endpoint cost per query
plus the random-reply collision probability. This holds for every partial
bijection installed before observation. -/
theorem adaptive_hit_bound (base : Trace S) (well : base.WF) (ins outs : K → Finset S)
    (u Q : Nat) (δ : ℝ) (nonneg : 0 ≤ δ) (room : Q < Fintype.card S)
    (countIn : ∀ k, (ins k).card ≤ u) (countOut : ∀ k, (outs k).card ≤ u)
    (pickIn : ∀ x, mean (fun k => ind (x ∈ ins k)) ≤ δ)
    (pickOut : ∀ y, mean (fun k => ind (y ∈ outs k)) ≤ δ)
    (cached : ∀ x y, containsPair base x y → mean (fun k => ind (touches ins outs k x y)) ≤ δ)
    (g : Strat S A) (n : Nat) (bounded : g.QB n) (fit : base.length+n ≤ Q) :
    mean (fun k => hitProb ins outs k g base) ≤ (n:ℝ)*(δ+u/((Fintype.card S:ℝ)-Q)) := by
  refine (avg_mono (fun k _ => hit_le_tally base ins outs k g base ?_)).trans
    (tally_bound base ins outs u Q δ nonneg room countIn countOut pickIn pickOut cached
      g n bounded base well fit)
  intro e known absent
  exact (absent ⟨e,known,rfl,rfl⟩).elim

end CommitGolfCandidate.Reconstruction.HidingTraffic
