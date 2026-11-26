import CommitGolfCandidate.Stage3cGraphRun
import CommitGolfCandidate.CompressionSampling
namespace CommitGolfCandidate.Chained.Replay
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 8192

inductive PublicRow where
  | compression (input : BitVec COMPRESSION_INPUT_LENGTH) (reply : BitVec 256)
  | permutation (input reply : BitVec PERMUTATION_WIDTH)

def queryRows (query : World.Domain) (answer : World.Range query) : List PublicRow :=
  match query with
  | .inl _ => []
  | .inr (.inl input) => [.compression input answer]
  | .inr (.inr (.inl input)) => [.permutation input answer]
  | .inr (.inr (.inr output)) => [.permutation answer output]

def recordRows {α : Type} (program : OracleComp World α) : OracleComp World (α × List PublicRow) :=
  OracleComp.recOn program (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← (liftM (World.query query) : OracleComp World _)
      (fun result => (result.1, queryRows query answer ++ result.2)) <$> next answer)

theorem record_rows_query {α : Type} (query : World.Domain) (next : World.Range query → OracleComp World α) :
    recordRows ((liftM (World.query query) : OracleComp World _) >>= next) =
      (do let answer ← (liftM (World.query query) : OracleComp World _)
          (fun result => (result.1, queryRows query answer ++ result.2)) <$> recordRows (next answer)) := rfl

theorem record_rows_bound {α : Type} (program : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound program budget) : PublicQueryBound (recordRows program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure _ => trivial
  | query_bind query next ih =>
    rw [record_rows_query]
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    refine ⟨bounded.1, fun answer => ?_⟩
    exact (isQueryBound_map_iff _ _ _ _ _).mpr (ih answer _ (bounded.2 answer))

theorem record_rows_pure {α : Type} (value : α) :
    recordRows (pure value : OracleComp World α) = pure (value, []) := rfl

theorem record_rows_bind {α β : Type} (program : OracleComp World α) (next : α → OracleComp World β) :
    recordRows (program >>= next) = (do
      let earlier ← recordRows program
      let later ← recordRows (next earlier.1)
      pure (later.1, earlier.2 ++ later.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [record_rows_pure]
  | query_bind query tail ih =>
    rw [bind_assoc, record_rows_query, record_rows_query]
    simp only [bind_assoc]
    apply bind_congr
    intro answer
    rw [ih]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, List.append_assoc]

theorem record_rows_erase {α : Type} (program : OracleComp World α) :
    Prod.fst <$> recordRows program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [record_rows_pure]
  | query_bind query next ih =>
    rw [record_rows_query, map_bind]
    apply bind_congr
    intro answer
    simpa only [Functor.map_map, Function.comp_def] using ih answer

theorem run_recorded_rows_support {α σ : Type}
    (handler : QueryImpl World (StateT σ ProbComp)) (stored : σ → PublicRow → Prop)
    (step : ∀ query state result, result ∈ support ((handler query).run state) →
      (∀ row, stored state row → stored result.2 row) ∧
      ∀ row ∈ queryRows query result.1, stored result.2 row)
    (program : OracleComp World α) (state : σ) (result : (α × List PublicRow) × σ)
    (reached : result ∈ support ((simulateQ handler (recordRows program)).run state)) :
    (∀ row, stored state row → stored result.2 row) ∧
    ∀ row ∈ result.1.2, stored result.2 row := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
    change result ∈ support ((simulateQ handler (pure (value, []))).run state) at reached
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ before => before, by simp⟩
  | query_bind query next ih =>
    rw [record_rows_query] at reached
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, simulateQ_map, StateT.run_map, mem_support_bind_iff, support_map, Set.mem_image] at reached
    obtain ⟨⟨answer, middle⟩, called, tail, continued, rfl⟩ := reached
    obtain ⟨preserved, head⟩ := step query state (answer, middle) called
    obtain ⟨kept, recorded⟩ := ih answer middle tail continued
    refine ⟨fun row before => kept row (preserved row before), fun row present => ?_⟩
    rcases List.mem_append.mp present with first | later
    · exact kept row (head row first)
    · exact recorded row later

end CommitGolfCandidate.Chained.Replay
