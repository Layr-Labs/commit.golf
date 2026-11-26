import CommitGolfCandidate.JointOracle241StoredStep

namespace CommitGolfCandidate.JointOracle241
open CommitGolf OracleComp OracleSpec TwoPermutationPrototype.Sampling

theorem run_query {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (s : State) :
    model.run ((liftM (World.query query) : OracleComp World _) >>= next) s =
      handler query s >>= fun result => model.run (next result.1) result.2 := by
  unfold JointOracleBudget.run
  rw [simulateQ_bind,StateT.run_bind]
  simp [model,StateT.run]

theorem run_map {α β : Type} (program : OracleComp World α) (f : α → β) (s : State) :
    model.run (f <$> program) s =
      (fun result => (f result.1,result.2)) <$> model.run program s := by
  simp only [JointOracleBudget.run,simulateQ_map,StateT.run_map]

theorem recorded_stores {α : Type} (program : OracleComp World α) (s : State)
    (result : (α × List PublicRow) × State)
    (reached : result ∈ support (model.run (recordRows program) s)) :
    Extends s result.2 ∧ ∀ row ∈ result.1.2, Stores result.2 row := by
  induction program using OracleComp.inductionOn generalizing s result with
  | pure value =>
    rw [record_rows_pure] at reached
    have runPure : model.run (pure (value,([] : List PublicRow))) s = pure ((value,[]),s) := by
      simp [JointOracleBudget.run]
    rw [runPure,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact ⟨Extends.refl s,by intro row present; contradiction⟩
  | query_bind query next ih =>
    rw [record_rows_query,run_query] at reached
    obtain ⟨⟨answer,middle⟩,called,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
    rw [run_map] at tail
    rw [support_map] at tail
    obtain ⟨⟨⟨value,rows⟩,finish⟩,remaining,same⟩ := tail
    subst result
    obtain ⟨first,headRows⟩ := handler_stores query s (answer,middle) called
    obtain ⟨last,tailRows⟩ := ih answer middle ((value,rows),finish) remaining
    refine ⟨first.trans last,?_⟩
    intro row present
    rcases List.mem_append.mp present with head | tail
    · exact Stores.mono last (headRows row head)
    · exact tailRows row tail

end CommitGolfCandidate.JointOracle241
