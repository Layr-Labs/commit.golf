import CommitGolfCandidate.JointOracle241State
import CommitGolfCandidate.CompressionSampling

namespace CommitGolfCandidate.JointOracle241
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling
local instance {α : Type} : MeasurableSpace α := ⊤

noncomputable def lazyOut {α : Type} (program : OracleComp World α) (s : State) : ProbComp α :=
  Prod.fst <$> (simulateQ handler program).run s

noncomputable def completedHandler (compression : Compression) :
    QueryImpl World (StateT State ProbComp) := fun query s =>
  match query with
  | .inr (.inl x) => pure (compression x,
      match s.cache x with
      | some _ => s.bump
      | none => s.store x (compression x))
  | .inl n => handler (.inl n) s
  | .inr (.inr (.inl x)) => handler (.inr (.inr (.inl x))) s
  | .inr (.inr (.inr y)) => handler (.inr (.inr (.inr y))) s

noncomputable def completedOut (compression : Compression) {α : Type}
    (program : OracleComp World α) (s : State) : ProbComp α :=
  Prod.fst <$> (simulateQ (completedHandler compression) program).run s

theorem lazyOut_pure {α : Type} (value : α) (s : State) :
    lazyOut (pure value) s = pure value := by simp [lazyOut]

theorem completedOut_pure (compression : Compression) {α : Type} (value : α) (s : State) :
    completedOut compression (pure value) s = pure value := by simp [completedOut]

theorem lazyOut_query {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (s : State) :
    lazyOut ((liftM (World.query query) : OracleComp World _) >>= next) s =
      handler query s >>= fun result => lazyOut (next result.1) result.2 := by
  unfold lazyOut
  rw [simulateQ_bind,StateT.run_bind,map_bind]
  simp [StateT.run]

theorem completedOut_query (compression : Compression) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (s : State) :
    completedOut compression ((liftM (World.query query) : OracleComp World _) >>= next) s =
      completedHandler compression query s >>= fun result => completedOut compression (next result.1) result.2 := by
  unfold completedOut
  rw [simulateQ_bind,StateT.run_bind,map_bind]
  simp [StateT.run]

theorem compression_completion {α : Type} (program : OracleComp World α) (s : State) :
    𝒟[lazyOut program s] =
      𝒟[do let table ← $ᵗ Compression
           completedOut (tableExtending s.cache table) program s] := by
  classical
  induction program using OracleComp.inductionOn generalizing s with
  | pure value =>
    simp only [lazyOut_pure,completedOut_pure]
    exact (OracleComp.evalDist_bind_const ($ᵗ Compression) (pure value)).symm
  | query_bind query next ih =>
    rw [lazyOut_query]
    simp_rw [completedOut_query]
    rcases query with coins | input | input | output
    · simp only [handler,completedHandler,bind_assoc,pure_bind]
      trans 𝒟[do let answer ← (liftM (unifSpec.query coins) : ProbComp _)
                 let table ← $ᵗ Compression
                 completedOut (tableExtending s.cache table) (next answer) s]
      · exact _root_.evalDist_bind_congr _ _ _ (fun answer => ih answer s)
      · exact distribution_bind_comm _ _ _
    · simp only [handler,completedHandler]
      cases cached : s.cache input with
      | some answer =>
        simp only [pure_bind]
        rw [ih answer s.bump]
        apply _root_.evalDist_bind_congr
        intro table
        have reply : tableExtending s.cache table input = answer := by
          change (s.cache input).getD (table input) = answer
          rw [cached]
          rfl
        simp only [reply]
        rfl
      | none =>
        simp only [bind_assoc,pure_bind]
        let continuation : Compression → ProbComp α := fun table =>
          completedOut (tableExtending s.cache table)
            (next (tableExtending s.cache table input))
            (s.store input (tableExtending s.cache table input))
        trans 𝒟[do let answer ← $ᵗ (BitVec COMPRESSION_OUTPUT_LENGTH)
                   let table ← $ᵗ Compression
                   continuation (Function.update table input answer)]
        · apply _root_.evalDist_bind_congr
          intro answer
          rw [ih answer (s.store input answer)]
          apply _root_.evalDist_bind_congr
          intro table
          have updated := tableExtending_update_of_none s.cache table cached answer
          have reply : tableExtending s.cache (Function.update table input answer) input = answer := by
            simp [tableExtending,cached]
          change 𝒟[completedOut (tableExtending (s.cache.cacheQuery input answer) table)
            (next answer) (s.store input answer)] = _
          simp only [continuation,reply,← updated,tableExtending_cacheQuery]
        · exact compression_table_update_bind input continuation
    · simp only [handler,completedHandler,bind_assoc,pure_bind]
      trans 𝒟[do let answer ← sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
                 let table ← $ᵗ Compression
                 completedOut (tableExtending s.cache table) (next answer.val)
                   (s.forward input answer.val answer.property)]
      · exact _root_.evalDist_bind_congr _ _ _ (fun answer => ih answer.val
          (s.forward input answer.val answer.property))
      · exact distribution_bind_comm _ _ _
    · simp only [handler,completedHandler,bind_assoc,pure_bind]
      trans 𝒟[do let answer ← sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
                 let table ← $ᵗ Compression
                 completedOut (tableExtending s.cache table) (next answer.val)
                   (s.inverse answer.val output answer.property)]
      · exact _root_.evalDist_bind_congr _ _ _ (fun answer => ih answer.val
          (s.inverse answer.val output answer.property))
      · exact distribution_bind_comm _ _ _

end CommitGolfCandidate.JointOracle241
