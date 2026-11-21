import CommitGolfCandidate.ChainedStoppedState
import CommitGolfCandidate.ChainedSourceUniform

/-! One predictable hazard for final replies and both permutation directions. -/
namespace CommitGolfCandidate.Chained.Stopped
open CommitGolf OracleComp OracleSpec

theorem won_probability (limit : Nat) (enc : Encoding) (calls width : Height → Nat)
    (s : State) (query : PublicSpec.Domain) :
    Pr{let result ← (handler limit enc calls width (.inr query)).run s}[result.2.won] =
      Pr{let answer ← (JointOracle238.handler (.inr query)).run s.oracle.base}[
        (finish limit enc calls width s query
          ⟨answer.2,Observer.observe s.oracle.graph (.inr query) answer.1⟩).won] := by
  change Pr{let result ← (do
    let answer ← (do
      let raw ← (JointOracle238.handler (.inr query)).run s.oracle.base
      pure (raw.1,(⟨raw.2,Observer.observe s.oracle.graph (.inr query) raw.1⟩ : Observer.State)))
    pure (answer.1,finish limit enc calls width s query answer.2))}[result.2.won] = _
  simp only [bind_assoc,pure_bind,bind_pure_comp,Functor.map_map]

theorem interior_hazard_eq {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (s : State) (core : Core limit enc calls width s) (active : Active limit enc s)
    (input : Input) (found : ¬ ∃ i, s.oracle.graph.input i = input) :
    Weighted.hazard (Counters.widths width) s.counts (kind limit enc calls s (.inl input)) =
      finalHazard enc calls width s.oracle.graph input (fun i same => found ⟨i,same⟩) := by
  classical
  have live := core.live (Nat.le_of_lt active.1) active.2.1 active.2.2
  simp only [kind,if_pos active,dif_neg found,Counters.interiorKind,finalHazard]
  cases predicted : prediction enc calls s.oracle.graph input (fun i same => found ⟨i,same⟩) with
  | none => rfl
  | some id =>
    obtain ⟨height,seed⟩ := id
    simp only [Option.map_some,Weighted.hazard,Counters.widths,live.1 height]

theorem fresh_hazard {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    (s : State) (core : Core limit enc calls width s) (safe : ¬ s.won) (query : PublicSpec.Domain) :
    Pr{let result ← (handler limit enc calls width (.inr query)).run s}[result.2.won] ≤
      Weighted.hazard (Counters.widths width) s.counts (kind limit enc calls s query) := by
  classical
  by_cases active : Active limit enc s
  · have budget := active.1
    have live := core.live (Nat.le_of_lt budget) active.2.1 safe
    have graphBound := Observer.graph_size s.oracle core.observer
    have sized : 2*s.oracle.graph.size < 2^256 := by omega
    have leafBound : s.oracle.base.trace.length ≤ s.counts none-1 := by have := live.2.1; omega
    have leafCount : s.counts none-1+1 = s.counts none := by have := core.leaf_pos; omega
    rw [won_probability]
    rcases query with input | input | output
    · change Pr{let answer ← (match s.oracle.base.cache input with
        | some reply => pure (reply,s.oracle.base.bump)
        | none => do let reply ← $ᵗ CompressionSpec.Range input; pure (reply,s.oracle.base.store input reply))}[
          (finish limit enc calls width s (.inl input)
            ⟨answer.2,Observer.observe s.oracle.graph (.inr (.inl input)) answer.1⟩).won] ≤ _
      by_cases found : ∃ i, s.oracle.graph.input i = input
      · have hit : s.oracle.base.cache input = some (s.oracle.graph.output (Classical.choose found)) :=
          (congrArg (fun cache : CompressionCache => cache input) core.observer.1).trans
            (s.oracle.graph.cache_of_row (Classical.choose found) input (Classical.choose_spec found))
        rw [hit,prEvent_pure]
        have impossible : ¬ (finish limit enc calls width s (.inl input)
            ⟨s.oracle.base.bump,s.oracle.graph⟩).won := by
          rintro (won | ⟨_,_,bad⟩)
          · exact safe won
          · rcases bad with leaf | interior
            · exact leaf live.2.2.1
            · exact live.2.2.2 interior
        simpa only [Observer.observe,dif_pos found,impossible,ite_false] using
          (zero_le : (0 : ENNReal) ≤ Weighted.hazard (Counters.widths width) s.counts
            (kind limit enc calls s (.inl input)))
      · have miss : s.oracle.base.cache input = none :=
          (congrArg (fun cache : CompressionCache => cache input) core.observer.1).trans
            ((s.oracle.graph.cache_none_iff input).mpr found)
        rw [miss]
        simp only [bind_pure_comp,Functor.map_map]
        have probability : Pr{let reply ← $ᵗ CompressionSpec.Range input}[
            (finish limit enc calls width s (.inl input)
              ⟨s.oracle.base.store input reply,s.oracle.graph.append input reply (fun i same => found ⟨i,same⟩)⟩).won] ≤
            finalHazard enc calls width s.oracle.graph input (fun i same => found ⟨i,same⟩) := by
          calc
            _ ≤ Pr{let reply ← $ᵗ CompressionSpec.Range input}[
                Good enc (s.oracle.graph.append input reply (fun i same => found ⟨i,same⟩)) ∧
                FinalCollision enc calls width (s.oracle.graph.append input reply (fun i same => found ⟨i,same⟩))] :=
              prEvent_mono_of_support _ _ _ fun reply _ event => by
                rcases event with won | ⟨_,good,bad⟩
                · exact (safe won).elim
                · refine ⟨good,?_⟩
                  rcases bad with leaf | interior
                  · exact (leaf live.2.2.1).elim
                  · exact interior
            _ = Pr{let reply ← $ᵗ Output}[
                Good enc (s.oracle.graph.append input reply (fun i same => found ⟨i,same⟩)) ∧
                FinalCollision enc calls width (s.oracle.graph.append input reply (fun i same => found ⟨i,same⟩))] :=
              source_uniform_event input _
            _ ≤ _ := fresh_final_hazard active.2.1 sized live.2.2.2 widthBound
        simpa only [Observer.observe,dif_neg found,interior_hazard_eq s core active input found] using probability
    · change Pr{let answer ← (do
        let reply ← JointOracle238.sampleSet (s.oracle.base.trace.fwdAns input) (s.oracle.base.wf.fwdAns_nonempty input)
        pure (reply.val,s.oracle.base.forward input reply.val reply.property))}[
          (finish limit enc calls width s (.inr (.inl input)) ⟨answer.2,s.oracle.graph⟩).won] ≤ _
      simp only [bind_pure_comp,Functor.map_map]
      calc
        _ ≤ Pr{let reply ← JointOracle238.sampleSet (s.oracle.base.trace.fwdAns input) (s.oracle.base.wf.fwdAns_nonempty input)}[
            ¬ (TwoPermutationPrototype.Sampling.s3PinCallW 238).badSpec.Good (s.oracle.base.trace.stepF input reply.val)] :=
          prEvent_mono_of_support _ _ _ fun reply _ event => by
            rcases event with won | ⟨_,_,bad⟩
            · exact (safe won).elim
            · rcases bad with leaf | interior
              · exact leaf
              · exact (live.2.2.2 interior).elim
        _ ≤ _ := by
          simpa only [kind,if_pos active,Weighted.hazard,Counters.widths,leafCount] using
            leaf_forward_hazard s.oracle.base.trace s.oracle.base.wf live.2.2.1 (s.counts none-1) leafBound input
    · change Pr{let answer ← (do
        let reply ← JointOracle238.sampleSet (s.oracle.base.trace.invAns output) (s.oracle.base.wf.invAns_nonempty output)
        pure (reply.val,s.oracle.base.inverse reply.val output reply.property))}[
          (finish limit enc calls width s (.inr (.inr output)) ⟨answer.2,s.oracle.graph⟩).won] ≤ _
      simp only [bind_pure_comp,Functor.map_map]
      calc
        _ ≤ Pr{let reply ← JointOracle238.sampleSet (s.oracle.base.trace.invAns output) (s.oracle.base.wf.invAns_nonempty output)}[
            ¬ (TwoPermutationPrototype.Sampling.s3PinCallW 238).badSpec.Good (s.oracle.base.trace.stepI reply.val output)] :=
          prEvent_mono_of_support _ _ _ fun reply _ event => by
            rcases event with won | ⟨_,_,bad⟩
            · exact (safe won).elim
            · rcases bad with leaf | interior
              · exact leaf
              · exact (live.2.2.2 interior).elim
        _ ≤ _ := by
          simpa only [kind,if_pos active,Weighted.hazard,Counters.widths,leafCount] using
            leaf_inverse_hazard s.oracle.base.trace s.oracle.base.wf live.2.2.1 (s.counts none-1) leafBound output
  · have impossible : ∀ result ∈ support ((Observer.handler (.inr query)).run s.oracle),
        ¬ (finish limit enc calls width s query result.2).won := by
      intro result reached event
      rcases event with won | ⟨budget,good,_⟩
      · exact safe won
      · apply active
        refine ⟨budget,?_,safe⟩
        exact Observer.observe_parent enc s.oracle.graph query result.1
          (by rw [← Observer.handler_graph query s.oracle result reached]; exact good)
    change Pr{let result ← (do
      let answer ← (Observer.handler (.inr query)).run s.oracle
      pure (answer.1,finish limit enc calls width s query answer.2))}[result.2.won] ≤ _
    simp only [bind_pure_comp,Functor.map_map,kind,if_neg active,Weighted.hazard]
    calc
      _ ≤ Pr{let _ ← (Observer.handler (.inr query)).run s.oracle}[False] :=
        prEvent_mono_of_support _ _ _ fun result reached event => (impossible result reached event).elim
      _ = 0 := by simp

end CommitGolfCandidate.Chained.Stopped
