import CommitGolfCandidate.ChainedJointObserver
import CommitGolfCandidate.ChainedSourceUniform

/-! The graph exception bound for the actual lazy joint source engine. -/
namespace CommitGolfCandidate.Chained.Observer
open CommitGolf OracleComp OracleSpec

theorem graph_probability (enc : Encoding) (s : State) (query : PublicSpec.Domain) :
    Pr{let result ← (handler (.inr query)).run s}[¬ Good enc result.2.graph] =
      Pr{let answer ← (JointOracle238.handler (.inr query)).run s.base}[
        ¬ Good enc (observe s.graph (.inr query) answer.1)] := by
  change Pr{let result ← (do
    let answer ← (JointOracle238.handler (.inr query)).run s.base
    pure (answer.1,(⟨answer.2,observe s.graph (.inr query) answer.1⟩ : State)))}[
      ¬ Good enc result.2.graph] = _
  simp only [bind_pure_comp,Functor.map_map]

theorem graph_hazard (enc : Encoding) (s : State) (known : Nat) (valid : Valid s)
    (counted : s.base.count ≤ known) (good : Good enc s.graph) (query : PublicSpec.Domain) :
    Pr{let result ← (handler (.inr query)).run s}[¬ Good enc result.2.graph] ≤
      ((2*known : Nat) : ENNReal)/2^256 := by
  classical
  rw [graph_probability]
  rcases query with input | input | output
  · change Pr{let answer ← (match s.base.cache input with
      | some reply => pure (reply,s.base.bump)
      | none => do let reply ← $ᵗ CompressionSpec.Range input; pure (reply,s.base.store input reply))}[
        ¬ Good enc (observe s.graph (.inr (.inl input)) answer.1)] ≤ _
    by_cases found : ∃ i, s.graph.input i = input
    · have hit : s.base.cache input = some (s.graph.output (Classical.choose found)) :=
        (congrArg (fun cache : CompressionCache => cache input) valid.1).trans
          (s.graph.cache_of_row (Classical.choose found) input (Classical.choose_spec found))
      rw [hit,prEvent_pure]
      simp only [observe,dif_pos found,good,not_true_eq_false,ite_false]
      exact zero_le
    · have miss : s.base.cache input = none :=
        (congrArg (fun cache : CompressionCache => cache input) valid.1).trans
          ((s.graph.cache_none_iff input).mpr found)
      rw [miss,bind_pure_comp,Functor.map_map]
      simp only [observe,dif_neg found]
      calc
        _ ≤ Pr{let reply ← $ᵗ CompressionSpec.Range input}[reply ∈ badTargets enc s.graph] :=
          prEvent_mono_of_support _ _ _ fun reply _ bad => by
            by_contra safe
            exact bad (good_append enc s.graph good input reply _ safe)
        _ = Pr{let reply ← $ᵗ Output}[reply ∈ badTargets enc s.graph] := source_uniform_event input _
        _ ≤ ((2*s.graph.size : Nat) : ENNReal)/2^256 := fresh_target_probability enc s.graph
        _ ≤ _ := by
          have size := graph_size s valid
          exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _
  · change Pr{let answer ← (do
      let reply ← JointOracle238.sampleSet (s.base.trace.fwdAns input) (s.base.wf.fwdAns_nonempty input)
      pure (reply.val,s.base.forward input reply.val reply.property))}[¬ Good enc s.graph] ≤ _
    simp only [good,not_true_eq_false,prEvent_false]
    exact zero_le
  · change Pr{let answer ← (do
      let reply ← JointOracle238.sampleSet (s.base.trace.invAns output) (s.base.wf.invAns_nonempty output)
      pure (reply.val,s.base.inverse reply.val output reply.property))}[¬ Good enc s.graph] ≤ _
    simp only [good,not_true_eq_false,prEvent_false]
    exact zero_le

noncomputable def graphModel (enc : Encoding) : GraphBudget State where
  handler := handler
  valid s known := Valid s ∧ s.base.count ≤ known
  bad s := ¬ Good enc s.graph
  coins := handler_coins
  preserves := by
    intro query s known consistent result reached
    refine ⟨preserves query s consistent.1 result reached,?_⟩
    rw [handler_count query s result reached]
    omega
  fresh := by
    intro query s known consistent safe
    exact graph_hazard enc s known consistent.1 consistent.2 (not_not.mp safe) query

theorem graph_from_empty {α : Type} (enc : Encoding) (program : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound program budget) :
    Pr{let result ← run program State.empty}[¬ Good enc result.2.graph] ≤
      ((budget*(budget-1) : Nat) : ENNReal)/2^256 :=
  GraphBudget.from_empty (graphModel enc) program budget bounded State.empty
    ⟨valid_empty,by decide⟩ (not_not.mpr (good_empty enc))

end CommitGolfCandidate.Chained.Observer
