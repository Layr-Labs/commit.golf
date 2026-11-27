import CommitGolfCandidate.ChainedGraphSampler
import CommitGolfCandidate.ChainedGraphCache
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec


theorem handler_cache (p : Perm) (q : World.Domain) (s : Trace) :
    (do let r←(graphHandler p q).run s; pure (r.1,r.2.cache))=(compressionHandler p q).run s.cache := by
  classical
  rcases q with coin | key
  · change (do let r ← (do let a ← (liftM (unifSpec.query coin) : ProbComp _);pure (a,s));pure (r.1,r.2.cache)) =
        (do let a ← (liftM (unifSpec.query coin) : ProbComp _);pure (a,s.cache))
    simp only [bind_assoc,pure_bind]
  rcases key with input | key
  · change (do let r←(if has : ∃ i,s.input i=input then pure (s.output has.choose,s)
                        else do let out←$ᵗ Output; pure (out,s.insert input out has)); pure (r.1,r.2.cache))=
        (randomOracle input).run s.cache
    erw [randomOracle.run_eq]
    by_cases found : ∃ i,s.input i=input
    · erw [dif_pos found,s.cache_of_row found.choose input found.choose_spec];simp
    · erw [dif_neg found,(s.cache_none_iff input).mpr found];simp only [bind_assoc,pure_bind,bind_pure_comp]
      rw [Functor.map_map]
      change (fun a : Output=>(a,(s.insert input a found).cache)) <$> ($ᵗ Output) = (fun a : Output=>(a,s.cache.cacheQuery input a)) <$> ($ᵗ Output)
      apply congrArg (fun f : Output → Output × CompressionCache => f <$> ($ᵗ Output))
      funext a;exact Prod.ext rfl (Trace.cache_append s input a _)
  rcases key with forward | reverse <;> rfl

theorem run_cache (p : Perm) {α : Type} (program : OracleComp World α) (s : Trace) :
    (do let r←(simulateQ (graphHandler p) program).run s; pure (r.1,r.2.cache))=
      compressionRun p program s.cache := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure v => erw [compression_run_pure];rfl
  | query_bind q next ih =>
    have raw : (simulateQ (graphHandler p) ((liftM (World.query q) : OracleComp World _) >>= next)).run s =
        (graphHandler p q).run s >>= fun r => (simulateQ (graphHandler p) (next r.1)).run r.2 := by
      simp [simulateQ_bind,StateT.run_bind]
    erw [raw,compression_run_query_bind p q next s.cache,←handler_cache p q s]
    simp only [bind_assoc,pure_bind]
    congr 1;funext r;exact ih r.1 r.2
end CommitGolfCandidate.Chained
