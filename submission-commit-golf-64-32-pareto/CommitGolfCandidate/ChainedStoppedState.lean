import CommitGolfCandidate.ChainedJointObserver
import CommitGolfCandidate.ChainedCounterVector
import CommitGolfCandidate.ChainedCompletionWork
import CommitGolfCandidate.ChainedFinalHazard
import CommitGolfCandidate.ChainedLeafHazard

/-! Predictable counters stop after a graph exception, a win, or the public horizon. -/
namespace CommitGolfCandidate.Chained.Stopped
open CommitGolf OracleComp OracleSpec
open scoped BigOperators

structure State where
  oracle : Observer.State
  counts : Counters.Index → Nat
  won : Prop

def leafGood (s : Observer.State) : Prop :=
  (TwoPermutationPrototype.Sampling.s3PinCallW 238).badSpec.Good s.base.trace

def rawBad (enc : Encoding) (calls width : Height → Nat) (s : Observer.State) : Prop :=
  ¬ leafGood s ∨ FinalCollision enc calls width s.graph

def Active (limit : Nat) (enc : Encoding) (s : State) : Prop :=
  s.oracle.base.count < limit ∧ Good enc s.oracle.graph ∧ ¬ s.won

noncomputable def kind (limit : Nat) (enc : Encoding) (calls : Height → Nat)
    (s : State) (query : PublicSpec.Domain) : Option Counters.Index := by
  classical
  exact if Active limit enc s then match query with
    | .inl input => if found : ∃ i, s.oracle.graph.input i = input then none
      else Counters.interiorKind (prediction enc calls s.oracle.graph input (fun i same => found ⟨i,same⟩))
    | .inr _ => some none
  else none

noncomputable def finish (limit : Nat) (enc : Encoding) (calls width : Height → Nat)
    (s : State) (query : PublicSpec.Domain) (next : Observer.State) : State :=
  ⟨next,Weighted.advance s.counts (kind limit enc calls s query),
    s.won ∨ (s.oracle.base.count < limit ∧ Good enc next.graph ∧ rawBad enc calls width next)⟩

noncomputable def handler (limit : Nat) (enc : Encoding) (calls width : Height → Nat) :
    QueryImpl World (StateT State ProbComp) := fun query s => match query with
  | .inl coins => do
      let answer ← (liftM (unifSpec.query coins) : ProbComp _)
      pure (answer,s)
  | .inr query => do
      let answer ← (Observer.handler (.inr query)).run s.oracle
      pure (answer.1,finish limit enc calls width s query answer.2)

structure Core (limit : Nat) (enc : Encoding) (calls width : Height → Nat) (s : State) : Prop where
  observer : Observer.Valid s.oracle
  leaf_pos : 1 ≤ s.counts none
  graph_leaf : s.oracle.graph.size+s.counts none ≤ s.oracle.base.count+1
  work : Weighted.work (Counters.rate calls) s.counts ≤ s.oracle.base.count+1
  live : s.oracle.base.count ≤ limit → Good enc s.oracle.graph → ¬ s.won →
    (∀ h, s.counts (some h) = completedCount enc calls s.oracle.graph h) ∧
    s.oracle.base.trace.length+1 ≤ s.counts none ∧ leafGood s.oracle ∧
    ¬ FinalCollision enc calls width s.oracle.graph

theorem finish_counts (limit : Nat) (enc : Encoding) (calls width : Height → Nat)
    (s : State) (query : PublicSpec.Domain) (next : Observer.State) :
    (finish limit enc calls width s query next).counts = Weighted.advance s.counts (kind limit enc calls s query) := rfl

theorem finish_clean {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (s : State) (query : PublicSpec.Domain) (next : Observer.State)
    (counted : next.base.count = s.oracle.base.count+1) (within : next.base.count ≤ limit)
    (good : Good enc next.graph) (safe : ¬ (finish limit enc calls width s query next).won) :
    leafGood next ∧ ¬ FinalCollision enc calls width next.graph := by
  have budget : s.oracle.base.count < limit := by omega
  have clean : ¬ rawBad enc calls width next := fun bad => safe (Or.inr ⟨budget,good,bad⟩)
  exact ⟨not_not.mp (fun bad => clean (Or.inl bad)),fun bad => clean (Or.inr bad)⟩

theorem forecast_step {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (s : State) (known : Nat) (core : Core limit enc calls width s)
    (counted : s.oracle.base.count ≤ known)
    (small : 2*limit < 2^256) (query : PublicSpec.Domain) :
    Weighted.work (Counters.rate calls) (Weighted.advance s.counts (kind limit enc calls s query)) ≤ known+2 := by
  classical
  by_cases active : Active limit enc s
  · have budget := active.1
    have live := core.live (by omega) active.2.1 active.2.2
    rcases query with input | input | output
    · by_cases found : ∃ i, s.oracle.graph.input i = input
      · simpa only [kind,if_pos active,dif_pos found,Weighted.advance] using
          core.work.trans (by omega : s.oracle.base.count+1 ≤ known+2)
      · simp only [kind,if_pos active,dif_neg found,Counters.work_advance_interior]
        have graphBound := Observer.graph_size s.oracle core.observer
        have sized : 2*s.oracle.graph.size < 2^256 := by omega
        have predicted := predicted_work (calls := calls) (input := input)
          (fresh := fun i same => found ⟨i,same⟩) active.2.1 sized
        have same : (∑ h, calls h*(s.counts (some h)+bump
            (prediction enc calls s.oracle.graph input (fun i same => found ⟨i,same⟩)) h)) =
            ∑ h, calls h*(completedCount enc calls s.oracle.graph h+bump
              (prediction enc calls s.oracle.graph input (fun i same => found ⟨i,same⟩)) h) := by
          apply Finset.sum_congr rfl
          intro h _
          rw [live.1 h]
        rw [same]
        have := core.graph_leaf
        omega
    · simp only [kind,if_pos active,Counters.work_advance_leaf]
      have := core.work
      omega
    · simp only [kind,if_pos active,Counters.work_advance_leaf]
      have := core.work
      omega
  · simpa only [kind,if_neg active,Weighted.advance] using
      core.work.trans (by omega : s.oracle.base.count+1 ≤ known+2)

theorem forecast {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (s : State) (known : Nat) (core : Core limit enc calls width s)
    (counted : s.oracle.base.count ≤ known) (remaining : known < limit)
    (small : 2*limit < 2^256) (query : PublicSpec.Domain) :
    Weighted.work (Counters.rate calls) (Weighted.advance s.counts (kind limit enc calls s query)) ≤ limit+1 :=
  (forecast_step s known core counted small query).trans (by omega)

theorem advance_ge (counts : Counters.Index → Nat) (chosen : Option Counters.Index) (i : Counters.Index) :
    counts i ≤ Weighted.advance counts chosen i := by
  cases chosen with
  | none => rfl
  | some k =>
    by_cases same : i=k
    · subst i
      simp [Weighted.advance]
    · simp [Weighted.advance,Function.update_of_ne same]

theorem graph_leaf_step (limit : Nat) (enc : Encoding) (calls : Height → Nat)
    (s : State) (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    (Observer.observe s.oracle.graph (.inr query) answer).size+
      Weighted.advance s.counts (kind limit enc calls s query) none ≤
      s.oracle.graph.size+s.counts none+1 := by
  classical
  by_cases active : Active limit enc s
  · rcases query with input | input | output
    · by_cases found : ∃ i, s.oracle.graph.input i = input
      · simp only [Observer.observe,dif_pos found,kind,if_pos active,Weighted.advance]
        omega
      · simp only [Observer.observe,dif_neg found,kind,if_pos active,Counters.advance_interior_leaf,Trace.append]
        omega
    · simp only [Observer.observe,kind,if_pos active,Counters.advance_leaf_leaf]
      omega
    · simp only [Observer.observe,kind,if_pos active,Counters.advance_leaf_leaf]
      omega
  · simp only [kind,if_neg active,Weighted.advance]
    rcases query with input | input | output
    · by_cases found : ∃ i, s.oracle.graph.input i = input
      · simp only [Observer.observe,dif_pos found]
        omega
      · simp only [Observer.observe,dif_neg found,Trace.append]
        omega
    · change s.oracle.graph.size+s.counts none ≤ _
      omega
    · change s.oracle.graph.size+s.counts none ≤ _
      omega

theorem live_step {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (s : State) (core : Core limit enc calls width s)
    (query : PublicSpec.Domain) (result : PublicSpec.Range query × Observer.State)
    (reached : result ∈ support ((Observer.handler (.inr query)).run s.oracle))
    (within : result.2.base.count ≤ limit) (good : Good enc result.2.graph)
    (safe : ¬ (finish limit enc calls width s query result.2).won) :
    (∀ h, (finish limit enc calls width s query result.2).counts (some h) =
      completedCount enc calls result.2.graph h) ∧
    result.2.base.trace.length+1 ≤ (finish limit enc calls width s query result.2).counts none := by
  classical
  have counted := Observer.handler_count query s.oracle result reached
  have graph := Observer.handler_graph query s.oracle result reached
  have parent : Good enc s.oracle.graph :=
    Observer.observe_parent enc s.oracle.graph query result.1 (by rw [← graph]; exact good)
  have budget : s.oracle.base.count < limit := by omega
  have oldSafe : ¬ s.won := fun won => safe (Or.inl won)
  have active : Active limit enc s := ⟨budget,parent,oldSafe⟩
  have old := core.live (by omega) parent oldSafe
  have size := Observer.graph_size s.oracle core.observer
  have sized : 2*s.oracle.graph.size < 2^256 := by omega
  change result ∈ support (do
    let answer ← (JointOracle238.handler (.inr query)).run s.oracle.base
    pure (answer.1,(⟨answer.2,Observer.observe s.oracle.graph (.inr query) answer.1⟩ : Observer.State))) at reached
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at reached
  obtain ⟨answer,sampled,rfl⟩ := reached
  rcases query with input | input | output
  · change answer ∈ support (match s.oracle.base.cache input with
      | some reply => pure (reply,s.oracle.base.bump)
      | none => do let reply ← $ᵗ CompressionSpec.Range input; pure (reply,s.oracle.base.store input reply)) at sampled
    by_cases found : ∃ i, s.oracle.graph.input i = input
    · have hit : s.oracle.base.cache input = some (s.oracle.graph.output (Classical.choose found)) :=
        (congrArg (fun cache : CompressionCache => cache input) core.observer.1).trans
          (s.oracle.graph.cache_of_row (Classical.choose found) input (Classical.choose_spec found))
      rw [hit,support_pure,Set.mem_singleton_iff] at sampled
      subst answer
      simpa only [finish,kind,if_pos active,dif_pos found,Weighted.advance,Observer.observe,
        JointOracle238.State.bump] using ⟨old.1,old.2.1⟩
    · have miss : s.oracle.base.cache input = none :=
        (congrArg (fun cache : CompressionCache => cache input) core.observer.1).trans
          ((s.oracle.graph.cache_none_iff input).mpr found)
      rw [miss] at sampled
      simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
      obtain ⟨reply,_,rfl⟩ := sampled
      have extended : Good enc (s.oracle.graph.append input reply (fun i same => found ⟨i,same⟩)) := by
        simpa only [Observer.observe,dif_neg found] using good
      constructor
      · intro h
        simpa only [finish,kind,if_pos active,dif_neg found,Counters.advance_interior_height,
          Observer.observe,counter_update reply extended sized,old.1 h] using
          (rfl : completedCount enc calls s.oracle.graph h+bump
            (prediction enc calls s.oracle.graph input (fun i same => found ⟨i,same⟩)) h = _)
      · simpa only [finish,kind,if_pos active,dif_neg found,Counters.advance_interior_leaf,
          JointOracle238.State.store] using old.2.1
  · change answer ∈ support (do
      let reply ← JointOracle238.sampleSet (s.oracle.base.trace.fwdAns input) (s.oracle.base.wf.fwdAns_nonempty input)
      pure (reply.val,s.oracle.base.forward input reply.val reply.property)) at sampled
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
    obtain ⟨reply,_,rfl⟩ := sampled
    constructor
    · simpa only [finish,kind,if_pos active,Counters.advance_leaf_height,Observer.observe] using old.1
    · simp only [finish,kind,if_pos active,Counters.advance_leaf_leaf,JointOracle238.State.forward]
      have := Permutation.Trace.length_stepF_le s.oracle.base.trace input reply.val
      have := old.2.1
      omega
  · change answer ∈ support (do
      let reply ← JointOracle238.sampleSet (s.oracle.base.trace.invAns output) (s.oracle.base.wf.invAns_nonempty output)
      pure (reply.val,s.oracle.base.inverse reply.val output reply.property)) at sampled
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
    obtain ⟨reply,_,rfl⟩ := sampled
    constructor
    · simpa only [finish,kind,if_pos active,Counters.advance_leaf_height,Observer.observe] using old.1
    · simp only [finish,kind,if_pos active,Counters.advance_leaf_leaf,JointOracle238.State.inverse]
      have := Permutation.Trace.length_stepI_le s.oracle.base.trace reply.val output
      have := old.2.1
      omega

theorem preserves_core {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (s : State) (core : Core limit enc calls width s)
    (query : PublicSpec.Domain) (result : PublicSpec.Range query × Observer.State)
    (reached : result ∈ support ((Observer.handler (.inr query)).run s.oracle)) :
    Core limit enc calls width (finish limit enc calls width s query result.2) := by
  have counted := Observer.handler_count query s.oracle result reached
  refine ⟨Observer.preserves query s.oracle core.observer result reached,?_,?_,?_,?_⟩
  · exact core.leaf_pos.trans (advance_ge _ _ _)
  · have step := graph_leaf_step limit enc calls s query result.1
    rw [← Observer.handler_graph query s.oracle result reached] at step
    have := core.graph_leaf
    change result.2.graph.size+Weighted.advance s.counts (kind limit enc calls s query) none ≤ result.2.base.count+1
    omega
  · have step := forecast_step s s.oracle.base.count core (le_refl _) small query
    change Weighted.work (Counters.rate calls) (Weighted.advance s.counts (kind limit enc calls s query)) ≤ result.2.base.count+1
    omega
  · intro within good safe
    have live := live_step small s core query result reached within good safe
    have clean := finish_clean s query result.2 counted within good safe
    exact ⟨live.1,live.2,clean.1,clean.2⟩

end CommitGolfCandidate.Chained.Stopped
