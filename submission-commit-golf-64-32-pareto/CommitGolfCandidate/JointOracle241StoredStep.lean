import CommitGolfCandidate.JointOracle241Probability

namespace CommitGolfCandidate.JointOracle241
open CommitGolf OracleComp OracleSpec Permutation TwoPermutationPrototype.Sampling

def Extends (before after : State) : Prop :=
  (∀ x y, before.cache x = some y → after.cache x = some y) ∧ before.trace <:+ after.trace

theorem Extends.refl (s : State) : Extends s s := ⟨fun _ _ h => h,List.suffix_refl _⟩

theorem Extends.trans {a b c : State} (left : Extends a b) (right : Extends b c) : Extends a c :=
  ⟨fun x y h => right.1 x y (left.1 x y h),left.2.trans right.2⟩

def Stores (s : State) (row : PublicRow) : Prop :=
  match row with
  | .compression x y => s.cache x = some y
  | .permutation x y => ∃ e ∈ s.trace, e.inp=x ∧ e.out=y

theorem Stores.mono {before after : State} (grows : Extends before after) {row : PublicRow}
    (stored : Stores before row) : Stores after row := by
  cases row with
  | compression x y => exact grows.1 x y stored
  | permutation x y =>
    obtain ⟨e,present,input,output⟩ := stored
    exact ⟨e,grows.2.subset present,input,output⟩

theorem store_extends (s : State) (input : CompressionSpec.Domain) (answer : CompressionSpec.Range input)
    (fresh : s.cache input = none) : Extends s (s.store input answer) := by
  refine ⟨?_,List.suffix_refl _⟩
  intro x y present
  change (s.cache.cacheQuery input answer) x = some y
  by_cases same : x=input
  · subst x
    rw [fresh] at present
    contradiction
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    exact present

theorem handler_stores (query : World.Domain) (s : State)
    (result : World.Range query × State) (reached : result ∈ support (handler query s)) :
    Extends s result.2 ∧ ∀ row ∈ queryRows query result.1, Stores result.2 row := by
  classical
  rcases query with coins | input | input | output
  · change result ∈ support (do
      let answer ← (liftM (unifSpec.query coins) : ProbComp _)
      pure (answer,s)) at reached
    obtain ⟨answer,_,same⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure,Set.mem_singleton_iff] at same
    subst result
    exact ⟨Extends.refl s,by intro row present; simp [queryRows] at present⟩
  · change result ∈ support (match s.cache input with
      | some answer => pure (answer,s.bump)
      | none => do let answer ← $ᵗ CompressionSpec.Range input; pure (answer,s.store input answer)) at reached
    cases cached : s.cache input with
    | some answer =>
      simp only [cached,support_pure,Set.mem_singleton_iff] at reached
      subst result
      refine ⟨Extends.refl s,?_⟩
      intro row present
      have same : row = PublicRow.compression input answer := by simpa [queryRows] using present
      subst row
      exact cached
    | none =>
      rw [cached] at reached
      obtain ⟨answer,_,same⟩ := (mem_support_bind_iff _ _ _).mp reached
      simp only [support_pure,Set.mem_singleton_iff] at same
      subst result
      refine ⟨store_extends s input answer cached,?_⟩
      intro row present
      have same : row = PublicRow.compression input answer := by simpa [queryRows] using present
      subst row
      change (s.cache.cacheQuery input answer) input = some answer
      exact QueryCache.cacheQuery_self _ _ _
  · change result ∈ support (do
      let answer ← sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
      pure (answer.val,s.forward input answer.val answer.property)) at reached
    obtain ⟨answer,_,same⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure,Set.mem_singleton_iff] at same
    subst result
    refine ⟨⟨fun _ _ h => h,Trace.suffix_stepF _ _ _⟩,?_⟩
    intro row present
    have same : row = PublicRow.permutation input answer.val := by simpa [queryRows] using present
    subst row
    exact Trace.mem_stepF_of_mem_fwdAns answer.property
  · change result ∈ support (do
      let answer ← sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
      pure (answer.val,s.inverse answer.val output answer.property)) at reached
    obtain ⟨answer,_,same⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure,Set.mem_singleton_iff] at same
    subst result
    refine ⟨⟨fun _ _ h => h,Trace.suffix_stepI _ _ _⟩,?_⟩
    intro row present
    have same : row = PublicRow.permutation answer.val output := by simpa [queryRows] using present
    subst row
    exact Trace.mem_stepI_of_mem_invAns answer.property

end CommitGolfCandidate.JointOracle241
