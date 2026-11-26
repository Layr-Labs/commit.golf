import CommitGolfCandidate.ReconstructedHidingView

namespace CommitGolfCandidate.Reconstruction.HidingReplay
open CommitGolf OracleComp CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain
local instance commonDiscrete {α : Type} : MeasurableSpace α := ⊤

/-- Each world can keep the mass of the same successful reference executions.
Their total variation then costs one copy of the discarded mass. -/
theorem distance_of_common_executions {R A : Type} (ref : ProbComp R) (value : R → A)
    (good : R → Prop) (world : Bool → ProbComp A) (ε : ℝ) (nonneg : 0 ≤ ε)
    (discard : (Pr{let r ← ref}[¬ good r]).toReal ≤ ε)
    (preserve : ∀ w (ev : A → Prop), Pr{let r ← ref}[good r ∧ ev (value r)]
      ≤ Pr{let a ← world w}[ev a]) :
    measureTVDist (world false) (world true) ≤ ε := by
  apply tv_le_of_events _ _ _ nonneg
  intro ev
  let yes := fun r => good r ∧ ev (value r)
  let no := fun r => good r ∧ ¬ev (value r)
  have split : Pr{let r ← ref}[good r] ≤ Pr{let r ← ref}[yes r] + Pr{let r ← ref}[no r] :=
    (prEvent_mono ref good (fun r => yes r ∨ no r) (by
      intro r known
      by_cases h : ev (value r)
      · exact Or.inl ⟨known,h⟩
      · exact Or.inr ⟨known,h⟩)).trans (prEvent_or_le ref yes no)
  have bound (w z : Bool) : (Pr{let a ← world w}[ev a]).toReal -
      (Pr{let a ← world z}[ev a]).toReal ≤ ε := by
    have covered := split.trans (add_le_add (preserve z ev) (preserve w (fun a => ¬ev a)))
    have num := (ENNReal.toReal_le_toReal (prEvent_ne_top _)
      (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _,prEvent_ne_top _⟩)).mpr covered
    rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _),prEvent_not_eq_one_sub,
      ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,ENNReal.toReal_one] at num
    have fail := discard
    rw [prEvent_not_eq_one_sub,ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,
      ENNReal.toReal_one] at fail
    linarith
  exact abs_sub_le_iff.mpr ⟨bound false true,by linarith [bound true false]⟩

/-- Conditioning on a fixed list of hidden permutation rows dominates every
accepting reference transcript on which those rows are fresh. Additional shared
requirements may be imposed on accepting transcripts by strengthening 'keeps'. -/
theorem common_row_lower {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (g : Strat S Bool) (rows : List (S × S)) (keeps : PState S → Prop)
    (fresh : ∀ st, keeps st → Fresh rows st.trace) :
    g.exp PState.init (fun b st => ind (b = true ∧ keeps st)) ≤
      (Fintype.card S : ℝ)^rows.length * rowWeight g rows := by
  classical
  rw [rowWeight_eq,← Strat.exp_mul_left]
  apply Strat.exp_mono
  intro b st
  have pos : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases h : b = true ∧ keeps st
  · obtain ⟨rfl,kept⟩ := h
    rw [ind_pos ⟨rfl,kept⟩,ite_eq_left (Eq.refl true)]
    have likelihood := check_fresh rows st (fresh st kept)
    rw [one_div_pow] at likelihood
    simpa [mul_comm] using (div_le_iff₀ (pow_pos pos rows.length)).mp likelihood
  · rw [ind_neg h]
    apply mul_nonneg (pow_nonneg pos.le _)
    cases b
    · exact le_refl _
    · exact (checkEdges rows).prob_nonneg st _

end CommitGolfCandidate.Reconstruction.HidingReplay
