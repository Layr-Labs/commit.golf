import CommitGolfCandidate.ChainedGraphCache
import CommitGolfCandidate.ChainedGraphSampler
import CommitGolfCandidate.JointOracle238State

/-! The existing joint sampler is the engine; the graph only observes its answers. -/
namespace CommitGolfCandidate.Chained.Observer
open CommitGolf OracleComp OracleSpec Permutation

structure State where
  base : JointOracle238.State
  graph : Chained.Trace

def State.empty : State := ⟨JointOracle238.State.empty,emptyTrace⟩

def Valid (s : State) : Prop := s.base.cache = s.graph.cache ∧ s.base.keys = s.graph.keys

noncomputable def observe (graph : Chained.Trace) (query : World.Domain) (answer : World.Range query) : Chained.Trace := by
  classical
  exact match query with
  | .inr (.inl input) =>
    if found : ∃ i, graph.input i = input then graph
    else graph.append input answer (fun i same => found ⟨i,same⟩)
  | _ => graph

noncomputable def handler : QueryImpl World (StateT State ProbComp) := fun query s => do
  let result ← (JointOracle238.handler query).run s.base
  pure (result.1,⟨result.2,observe s.graph query result.1⟩)

theorem handler_project (query : World.Domain) (s : State) :
    (do let result ← (handler query).run s; pure (result.1,result.2.base)) =
      (JointOracle238.handler query).run s.base := by
  change (do
    let result ← (do
      let answer ← (JointOracle238.handler query).run s.base
      pure (answer.1,(⟨answer.2,observe s.graph query answer.1⟩ : State)))
    pure (result.1,result.2.base)) = _
  simp only [bind_assoc,pure_bind,Prod.mk.eta,bind_pure]

theorem handler_coins (coins : unifSpec.Domain) (s : State) :
    (handler (.inl coins)).run s =
      (do let answer ← (liftM (unifSpec.query coins) : ProbComp _); pure (answer,s)) := by
  change (do
    let result ← (JointOracle238.handler (.inl coins)).run s.base
    pure (result.1,(⟨result.2,s.graph⟩ : State))) = _
  rw [JointOracle238.handler_coins]
  simp only [bind_assoc,pure_bind]

theorem valid_empty : Valid State.empty := by
  constructor
  · apply QueryCache.ext
    intro input
    exact ((emptyTrace.cache_none_iff input).mpr (fun ⟨row,_⟩ => Fin.elim0 row)).symm
  · exact (Finset.card_eq_zero.mp emptyTrace.keys_card).symm

theorem graph_size (s : State) (valid : Valid s) : s.graph.size+s.base.trace.length ≤ s.base.count := by
  have same : s.base.keys.card = s.graph.size :=
    (congrArg Finset.card valid.2).trans s.graph.keys_card
  exact (Nat.add_le_add_right same.symm.le _).trans s.base.size

theorem valid_bump (s : State) (valid : Valid s) : Valid ⟨s.base.bump,s.graph⟩ := valid

theorem valid_store (s : State) (valid : Valid s) (input : Input) (reply : Output)
    (fresh : ∀ i, s.graph.input i ≠ input) :
    Valid ⟨s.base.store input reply,s.graph.append input reply fresh⟩ := by
  classical
  constructor
  · exact (congrArg (fun cache : CompressionCache => cache.cacheQuery input reply) valid.1).trans
      (s.graph.cache_append input reply fresh).symm
  · exact (congrArg (fun keys : Finset Input => insert input keys) valid.2).trans
      (s.graph.keys_append input reply fresh).symm

theorem preserves (query : PublicSpec.Domain) (s : State) (valid : Valid s)
    (result : PublicSpec.Range query × State) (reached : result ∈ support ((handler (.inr query)).run s)) :
    Valid result.2 := by
  classical
  change result ∈ support (do
    let answer ← (JointOracle238.handler (.inr query)).run s.base
    pure (answer.1,(⟨answer.2,observe s.graph (.inr query) answer.1⟩ : State))) at reached
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at reached
  obtain ⟨answer,sampled,rfl⟩ := reached
  rcases query with input | input | output
  · change answer ∈ support (match s.base.cache input with
      | some reply => pure (reply,s.base.bump)
      | none => do let reply ← $ᵗ CompressionSpec.Range input; pure (reply,s.base.store input reply)) at sampled
    by_cases found : ∃ i, s.graph.input i = input
    · have hit : s.base.cache input = some (s.graph.output (Classical.choose found)) :=
        (congrArg (fun cache : CompressionCache => cache input) valid.1).trans
          (s.graph.cache_of_row (Classical.choose found) input (Classical.choose_spec found))
      rw [hit,support_pure,Set.mem_singleton_iff] at sampled
      subst answer
      simpa only [observe,dif_pos found] using valid_bump s valid
    · have miss : s.base.cache input = none :=
        (congrArg (fun cache : CompressionCache => cache input) valid.1).trans
          ((s.graph.cache_none_iff input).mpr found)
      rw [miss] at sampled
      simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
      obtain ⟨reply,_,rfl⟩ := sampled
      simpa only [observe,dif_neg found] using valid_store s valid input reply (fun i same => found ⟨i,same⟩)
  · change answer ∈ support (do
      let reply ← JointOracle238.sampleSet (s.base.trace.fwdAns input) (s.base.wf.fwdAns_nonempty input)
      pure (reply.val,s.base.forward input reply.val reply.property)) at sampled
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
    obtain ⟨reply,_,rfl⟩ := sampled
    exact valid
  · change answer ∈ support (do
      let reply ← JointOracle238.sampleSet (s.base.trace.invAns output) (s.base.wf.invAns_nonempty output)
      pure (reply.val,s.base.inverse reply.val output reply.property)) at sampled
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
    obtain ⟨reply,_,rfl⟩ := sampled
    exact valid

theorem handler_count (query : PublicSpec.Domain) (s : State)
    (result : PublicSpec.Range query × State) (reached : result ∈ support ((handler (.inr query)).run s)) :
    result.2.base.count = s.base.count+1 := by
  have projected : (result.1,result.2.base) ∈ support ((JointOracle238.handler (.inr query)).run s.base) := by
    rw [← handler_project]
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
    exact ⟨result,reached,rfl⟩
  exact JointOracle238.handler_count query s.base _ projected

theorem observe_parent (enc : Encoding) (graph : Chained.Trace) (query : PublicSpec.Domain)
    (answer : PublicSpec.Range query) (good : Good enc (observe graph (.inr query) answer)) : Good enc graph := by
  classical
  rcases query with input | input | output
  · by_cases found : ∃ i, graph.input i = input
    · simpa only [observe,dif_pos found] using good
    · have extended : Good enc (graph.append input answer (fun i same => found ⟨i,same⟩)) := by
        simpa only [observe,dif_neg found] using good
      exact good_of_append enc graph _ _ _ extended
  · exact good
  · exact good

theorem handler_graph (query : PublicSpec.Domain) (s : State)
    (result : PublicSpec.Range query × State) (reached : result ∈ support ((handler (.inr query)).run s)) :
    result.2.graph = observe s.graph (.inr query) result.1 := by
  change result ∈ support (do
    let answer ← (JointOracle238.handler (.inr query)).run s.base
    pure (answer.1,(⟨answer.2,observe s.graph (.inr query) answer.1⟩ : State))) at reached
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at reached
  obtain ⟨answer,_,rfl⟩ := reached
  rfl

noncomputable def run {α : Type} (program : OracleComp World α) (s : State) : ProbComp (α × State) :=
  (simulateQ handler program).run s

noncomputable def sourceRun {α : Type} (program : OracleComp World α) (s : JointOracle238.State) :
    ProbComp (α × JointOracle238.State) := (simulateQ JointOracle238.handler program).run s

theorem run_project {α : Type} (program : OracleComp World α) (s : State) :
    (do let result ← run program s; pure (result.1,result.2.base)) = sourceRun program s.base := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure value => simp [run,sourceRun]
  | query_bind query next ih =>
    have rawStep : run ((liftM (World.query query) : OracleComp World _) >>= next) s =
        (handler query).run s >>= fun result => run (next result.1) result.2 := by
      simp [run,simulateQ_bind,StateT.run_bind]
    have sourceStep : sourceRun ((liftM (World.query query) : OracleComp World _) >>= next) s.base =
        (JointOracle238.handler query).run s.base >>= fun result => sourceRun (next result.1) result.2 := by
      simp [sourceRun,simulateQ_bind,StateT.run_bind]
    rw [rawStep,sourceStep,← handler_project]
    simp only [bind_assoc,pure_bind]
    congr 1
    funext result
    exact ih result.1 result.2

end CommitGolfCandidate.Chained.Observer
