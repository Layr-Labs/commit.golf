import CommitGolfCandidate.JointOracleBudget

/-! A joint lazy compression cache and permutation table. The size invariant counts
distinct cached compression inputs and fresh permutation entries together. -/

namespace CommitGolfCandidate.JointOracle241
open CommitGolf OracleComp OracleSpec Permutation

structure State where
  cache : CompressionCache
  keys : Finset CompressionSpec.Domain
  covers : ∀ x, cache x ≠ none → x ∈ keys
  trace : Trace PermState
  wf : trace.WF
  count : Nat
  size : keys.card + trace.length ≤ count

def State.empty : State :=
  ⟨∅, ∅, by intro x h; exact (h rfl).elim, [], Trace.WF.nil, 0, by simp⟩

def State.bump (s : State) : State :=
  { s with count := s.count+1, size := s.size.trans (Nat.le_succ _) }

noncomputable def State.store (s : State) (x : CompressionSpec.Domain) (y : CompressionSpec.Range x) : State := by
  classical
  refine ⟨s.cache.cacheQuery x y, insert x s.keys, ?_, s.trace, s.wf, s.count+1, ?_⟩
  · intro key populated
    by_cases same : key=x
    · exact same ▸ Finset.mem_insert_self _ _
    · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
      exact Finset.mem_insert_of_mem (s.covers key populated)
  · have := Finset.card_insert_le x s.keys
    have := s.size
    omega

def State.forward (s : State) (x y : PermState) (allowed : y ∈ s.trace.fwdAns x) : State := by
  refine ⟨s.cache,s.keys,s.covers,s.trace.stepF x y,s.wf.stepF allowed,s.count+1,?_⟩
  have := Trace.length_stepF_le s.trace x y
  have := s.size
  omega

def State.inverse (s : State) (x y : PermState) (allowed : x ∈ s.trace.invAns y) : State := by
  refine ⟨s.cache,s.keys,s.covers,s.trace.stepI x y,s.wf.stepI allowed,s.count+1,?_⟩
  have := Trace.length_stepI_le s.trace x y
  have := s.size
  omega

noncomputable def sampleSet {α : Type} [Fintype α] (A : Finset α) (hne : A.Nonempty) : ProbComp A := by
  classical
  letI : Nonempty A := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  letI : SampleableType A := SampleableType.ofFintype A
  exact $ᵗ A

noncomputable def handler : QueryImpl World (StateT State ProbComp) := fun query s =>
  match query with
  | .inl n => do
      let answer ← (liftM (unifSpec.query n) : ProbComp _)
      pure (answer,s)
  | .inr (.inl x) =>
      match s.cache x with
      | some y => pure (y,s.bump)
      | none => do
          let y ← $ᵗ CompressionSpec.Range x
          pure (y,s.store x y)
  | .inr (.inr (.inl x)) => do
      let y ← sampleSet (s.trace.fwdAns x) (s.wf.fwdAns_nonempty x)
      pure (y.val,s.forward x y.val y.property)
  | .inr (.inr (.inr y)) => do
      let x ← sampleSet (s.trace.invAns y) (s.wf.invAns_nonempty y)
      pure (x.val,s.inverse x.val y x.property)

def bad (s : State) : Prop :=
  ProjectedCollisionW 238 s.cache ∨ ¬ (TwoPermutationPrototype.Sampling.s3PinCallW 241).badSpec.Good s.trace

theorem handler_coins (n : unifSpec.Domain) (s : State) :
    (handler (.inl n)).run s =
      (do let answer ← (liftM (unifSpec.query n) : ProbComp _); pure (answer,s)) := rfl

theorem handler_count (query : PublicSpec.Domain) (s : State) :
    ∀ result ∈ support ((handler (.inr query)).run s), result.2.count=s.count+1 := by
  rcases query with input | input | output
  · change ∀ result ∈ support (match s.cache input with
      | some answer => pure (answer,s.bump)
      | none => do let answer ← $ᵗ CompressionSpec.Range input; pure (answer,s.store input answer)), _
    split
    · intro result reached
      rw [support_pure,Set.mem_singleton_iff] at reached
      subst result
      rfl
    · intro result reached
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at reached
      obtain ⟨answer,_,rfl⟩ := reached
      rfl
  · intro result reached
    change result ∈ support (do
      let answer ← sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
      pure (answer.val,s.forward input answer.val answer.property)) at reached
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at reached
    obtain ⟨answer,_,rfl⟩ := reached
    rfl
  · intro result reached
    change result ∈ support (do
      let answer ← sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
      pure (answer.val,s.inverse answer.val output answer.property)) at reached
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at reached
    obtain ⟨answer,_,rfl⟩ := reached
    rfl

end CommitGolfCandidate.JointOracle241
