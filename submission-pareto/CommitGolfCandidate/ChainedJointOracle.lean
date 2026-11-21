import CommitGolfCandidate.ChainedGraphCache
import CommitGolfCandidate.ChainedGraphSampler
import CommitGolfCandidate.JointOracle238State

/-! Joint lazy sampling retaining the chronological compression graph. -/
namespace CommitGolfCandidate.Chained.Joint
open CommitGolf OracleComp OracleSpec Permutation

structure State where
  graph : Chained.Trace
  trace : Permutation.Trace PermState
  wf : trace.WF
  count : Nat
  size : graph.size+trace.length ≤ count

def State.empty : State := ⟨emptyTrace,[],Trace.WF.nil,0,by simp [emptyTrace]⟩

def State.bump (s : State) : State :=
  { s with count := s.count+1, size := s.size.trans (Nat.le_succ _) }

def State.store (s : State) (input : Input) (reply : Output) (fresh : ∀ i, s.graph.input i ≠ input) : State :=
  ⟨s.graph.append input reply fresh,s.trace,s.wf,s.count+1,by have := s.size; change s.graph.size+1+s.trace.length ≤ s.count+1; omega⟩

def State.forward (s : State) (input output : PermState) (allowed : output ∈ s.trace.fwdAns input) : State :=
  ⟨s.graph,s.trace.stepF input output,s.wf.stepF allowed,s.count+1,by
    have := s.size
    have := Trace.length_stepF_le s.trace input output
    omega⟩

def State.inverse (s : State) (input output : PermState) (allowed : input ∈ s.trace.invAns output) : State :=
  ⟨s.graph,s.trace.stepI input output,s.wf.stepI allowed,s.count+1,by
    have := s.size
    have := Trace.length_stepI_le s.trace input output
    omega⟩

noncomputable def State.toBase (s : State) : JointOracle238.State :=
  ⟨s.graph.cache,s.graph.keys,s.graph.cache_covers,s.trace,s.wf,s.count,
    (Nat.add_le_add_right s.graph.keys_card.le s.trace.length).trans s.size⟩

theorem State.toBase_bump (s : State) : s.bump.toBase = s.toBase.bump := rfl

theorem State.toBase_forward (s : State) (input output : PermState) (allowed : output ∈ s.trace.fwdAns input) :
    (s.forward input output allowed).toBase = s.toBase.forward input output allowed := rfl

theorem State.toBase_inverse (s : State) (input output : PermState) (allowed : input ∈ s.trace.invAns output) :
    (s.inverse input output allowed).toBase = s.toBase.inverse input output allowed := rfl

theorem State.toBase_store (s : State) (input : Input) (reply : Output) (fresh : ∀ i, s.graph.input i ≠ input) :
    (s.store input reply fresh).toBase = s.toBase.store input reply := by
  simp only [toBase,store,JointOracle238.State.store,Chained.Trace.cache_append,Chained.Trace.keys_append]
  rfl

noncomputable def compressionSample (input : CompressionSpec.Domain) : ProbComp (CompressionSpec.Range input) :=
  $ᵗ CompressionSpec.Range input

noncomputable def handler : QueryImpl World (StateT State ProbComp) := by
  classical
  exact fun query s => match query with
    | .inl n => do
        let answer ← (liftM (unifSpec.query n) : ProbComp _)
        pure (answer,s)
    | .inr (.inl input) =>
        if found : ∃ i, s.graph.input i = input then
          pure (s.graph.output (Classical.choose found),s.bump)
        else do
          let reply ← compressionSample input
          pure (reply,s.store input reply (fun i same => found ⟨i,same⟩))
    | .inr (.inr (.inl input)) => do
        let reply ← JointOracle238.sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
        pure (reply.val,s.forward input reply.val reply.property)
    | .inr (.inr (.inr output)) => do
        let reply ← JointOracle238.sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
        pure (reply.val,s.inverse reply.val output reply.property)

theorem handler_coins (n : unifSpec.Domain) (s : State) :
    (handler (.inl n)).run s =
      (do let answer ← (liftM (unifSpec.query n) : ProbComp _); pure (answer,s)) := rfl

theorem handler_project_coins (coins : unifSpec.Domain) (s : State) :
    (do let result ← (handler (.inl coins)).run s; pure (result.1,result.2.toBase)) =
      (JointOracle238.handler (.inl coins)).run s.toBase := by
  rw [handler_coins,JointOracle238.handler_coins]
  simp only [bind_assoc,pure_bind]

theorem handler_project_forward (input : PermState) (s : State) :
    (do let result ← (handler (.inr (.inr (.inl input)))).run s; pure (result.1,result.2.toBase)) =
      (JointOracle238.handler (.inr (.inr (.inl input)))).run s.toBase := by
  change (do
    let result ← (do
      let reply ← JointOracle238.sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
      pure (reply.val,s.forward input reply.val reply.property))
    pure (result.1,result.2.toBase)) = (do
    let reply ← JointOracle238.sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
    pure (reply.val,s.toBase.forward input reply.val reply.property))
  simp only [bind_assoc,pure_bind,State.toBase_forward]

theorem handler_project_inverse (output : PermState) (s : State) :
    (do let result ← (handler (.inr (.inr (.inr output)))).run s; pure (result.1,result.2.toBase)) =
      (JointOracle238.handler (.inr (.inr (.inr output)))).run s.toBase := by
  change (do
    let result ← (do
      let reply ← JointOracle238.sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
      pure (reply.val,s.inverse reply.val output reply.property))
    pure (result.1,result.2.toBase)) = (do
    let reply ← JointOracle238.sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
    pure (reply.val,s.toBase.inverse reply.val output reply.property))
  simp only [bind_assoc,pure_bind,State.toBase_inverse]

end CommitGolfCandidate.Chained.Joint
