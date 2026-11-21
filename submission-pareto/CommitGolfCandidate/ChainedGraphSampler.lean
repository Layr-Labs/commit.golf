import CommitGolfCandidate.ChainedGraphAdaptive

/-! Lazy compression sampling with a chronological graph and both permutation directions. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec

def emptyTrace : Trace where
  size := 0
  input := Fin.elim0
  output := Fin.elim0
  fresh := by intro i; exact Fin.elim0 i

theorem good_empty (enc : Encoding) : Good enc emptyTrace where
  outputs := by intro i; exact Fin.elim0 i
  no_guesses := by intro i; exact Fin.elim0 i

def Trace.insert (trace : Trace) (input : Input) (output : Output)
    (missing : ¬∃ i, trace.input i = input) : Trace :=
  trace.append input output (fun i equal => missing ⟨i,equal⟩)

noncomputable def graphHandler (permutation : Perm) : QueryImpl World (StateT Trace ProbComp) := by
  classical
  exact fun query => match query with
    | .inl coins => do
      let answer ← (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins))
      return answer
    | .inr (.inl input) => fun trace =>
      if cached : ∃ i, trace.input i = input then pure (trace.output cached.choose,trace)
      else do
        let output ← $ᵗ Output
        pure (output,trace.insert input output cached)
    | .inr (.inr (.inl input)) => pure (permutation input)
    | .inr (.inr (.inr input)) => pure (permutation.symm input)

theorem handler_preserves (permutation : Perm) (query : PublicSpec.Domain)
    (trace : Trace) (known : Nat) (bounded : trace.size ≤ known)
    (result : PublicSpec.Range query × Trace)
    (reached : result ∈ support ((graphHandler permutation (.inr query)).run trace)) :
    result.2.size ≤ known+1 := by
  classical
  rcases query with input | input | input
  · change result ∈ support (if cached : ∃ i, trace.input i = input then
        pure (trace.output cached.choose,trace)
        else do let output ← $ᵗ Output; pure (output,trace.insert input output cached)) at reached
    split at reached
    · simp only [support_pure,Set.mem_singleton_iff] at reached
      subst result
      exact Nat.le_succ_of_le bounded
    · obtain ⟨output,_,same⟩ := (mem_support_bind_iff _ _ _).mp reached
      subst result
      exact Nat.add_le_add_right bounded 1
  · change result ∈ support (pure (permutation input,trace)) at reached
    simp only [support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact Nat.le_succ_of_le bounded
  · change result ∈ support (pure (permutation.symm input,trace)) at reached
    simp only [support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact Nat.le_succ_of_le bounded

theorem handler_hazard (enc : Encoding) (permutation : Perm) (query : PublicSpec.Domain)
    (trace : Trace) (known : Nat) (bounded : trace.size ≤ known) (good : Good enc trace) :
    Pr{let result ← (graphHandler permutation (.inr query)).run trace}[¬Good enc result.2] ≤
      ((2*known : Nat) : ENNReal)/2^256 := by
  classical
  rcases query with input | input | input
  · change prEvent ((fun result => ¬Good enc result.2) <$>
      (if cached : ∃ i, trace.input i = input then pure (trace.output cached.choose,trace)
      else do let output ← $ᵗ Output; pure (output,trace.insert input output cached))) ≤ _
    split
    · rw [prEvent_pure]
      simp only [good,not_true_eq_false,ite_false]
      exact zero_le
    · rename_i missing
      rw [bind_pure_comp,Functor.map_map]
      change Pr{let output ← $ᵗ Output}[¬Good enc (trace.insert input output missing)] ≤ _
      calc
        _ ≤ Pr{let output ← $ᵗ Output}[output ∈ badTargets enc trace] :=
          prEvent_mono_of_support _ _ _ fun output _ bad => by
            by_contra safe
            exact bad (good_append enc trace good input output _ safe)
        _ ≤ ((2*trace.size : Nat) : ENNReal)/2^256 := fresh_target_probability enc trace
        _ ≤ _ := ENNReal.div_le_div_right
          (Nat.cast_le.mpr (Nat.mul_le_mul_left 2 bounded)) _
  · change prEvent ((fun result => ¬Good enc result.2) <$> pure (permutation input,trace)) ≤ _
    rw [prEvent_pure]
    simp only [good,not_true_eq_false,ite_false]
    exact zero_le
  · change prEvent ((fun result => ¬Good enc result.2) <$> pure (permutation.symm input,trace)) ≤ _
    rw [prEvent_pure]
    simp only [good,not_true_eq_false,ite_false]
    exact zero_le

noncomputable def graphModel (enc : Encoding) (permutation : Perm) : GraphBudget Trace where
  handler := graphHandler permutation
  valid trace known := trace.size ≤ known
  bad trace := ¬Good enc trace
  coins _ _ := by simp [graphHandler]
  preserves := handler_preserves permutation
  fresh query trace known bounded safe := handler_hazard enc permutation query trace known bounded
    (not_not.mp safe)

theorem adaptive_graph_bound (enc : Encoding) (permutation : Perm) {α : Type}
    (program : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound program budget) :
    Pr{let result ← (graphModel enc permutation).run program emptyTrace}[¬Good enc result.2] ≤
      ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  exact GraphBudget.from_empty (graphModel enc permutation) program budget bounded emptyTrace
    (Nat.le_refl 0) (not_not.mpr (good_empty enc))

end CommitGolfCandidate.Chained
