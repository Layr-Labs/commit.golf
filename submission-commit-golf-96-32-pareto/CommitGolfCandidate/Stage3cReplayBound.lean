import CommitGolfCandidate.Stage3cReplayBridge
import CommitGolfCandidate.Stage3cSecurity
import CommitGolfCandidate.Stage3cPath
namespace CommitGolfCandidate.Chained.Replay
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

def Stored (s : Trace) : PublicRow → Prop
  | .compression x v=>∃ i,s.input i=x ∧ s.output i=v
  | .permutation _ _=>True

def Witness (rows : List PublicRow) : Prop :=
  ∀ s : Trace, (∀ r∈rows,Stored s r) → FinalCollision canonicalEncoding calls width s ∨ ¬Good canonicalEncoding s

theorem witness_mono {a b : List PublicRow} (sub : ∀ r∈a,r∈b) (w : Witness a) : Witness b :=
  fun s stored=>w s (fun r hr=>stored r (sub r hr))

private theorem keep_insert (s : Trace) (x : Input) (v : Output) (missing : ¬∃ j,s.input j=x) (row : PublicRow) :
    Stored s row → Stored (s.insert x v missing) row := by
  cases row with
  | permutation => exact fun _=>trivial
  | compression a b =>
    rintro ⟨i,old,reply⟩
    exact ⟨i.castSucc,by simpa only [Trace.insert,Trace.append,extend,Fin.val_castSucc,dif_pos i.isLt] using old,
      by simpa only [Trace.insert,Trace.append,extend,Fin.val_castSucc,dif_pos i.isLt] using reply⟩

private theorem store_step (p : Perm) (q : World.Domain) (s : Trace) (r : World.Range q × Trace)
    (member : r∈support ((graphHandler p q).run s)) :
    (∀ a,Stored s a→Stored r.2 a) ∧ ∀ a∈queryRows q r.1,Stored r.2 a := by
  classical
  rcases q with coin|x|x|x
  · change r∈support (do let a←(liftM (unifSpec.query coin) : ProbComp _);pure (a,s)) at member
    obtain ⟨a,_,eq⟩:=(mem_support_bind_iff ..).mp member
    erw [support_pure,Set.mem_singleton_iff] at eq;subst r;exact ⟨fun _ h=>h,by simp [queryRows]⟩
  · change r∈support (if seen : ∃ i,s.input i=x then pure (s.output seen.choose,s)
        else do let out←$ᵗ Output;pure (out,s.insert x out seen)) at member
    split at member
    · rename_i seen;erw [support_pure,Set.mem_singleton_iff] at member;subst r
      refine ⟨fun _ h=>h,?_⟩
      intro a ha;simp only [queryRows,List.mem_singleton] at ha;subst a
      exact ⟨seen.choose,seen.choose_spec,rfl⟩
    · rename_i missing
      obtain ⟨out,_,eq⟩:=(mem_support_bind_iff ..).mp member
      erw [support_pure,Set.mem_singleton_iff] at eq;subst r
      refine ⟨keep_insert s x out missing,?_⟩
      intro a ha;simp only [queryRows,List.mem_singleton] at ha;subst a
      refine ⟨Fin.last s.size,?_,?_⟩ <;> simp [Trace.insert,Trace.append,extend] <;> rfl
  · change r∈support (pure (p x,s) : ProbComp _) at member
    erw [support_pure,Set.mem_singleton_iff] at member;subst r
    exact ⟨fun _ h=>h,by simp [queryRows,Stored]⟩
  · change r∈support (pure (p.symm x,s) : ProbComp _) at member
    erw [support_pure,Set.mem_singleton_iff] at member;subst r
    exact ⟨fun _ h=>h,by simp [queryRows,Stored]⟩

theorem trace_witness_bound (p : Perm) {α : Type} (prog : OracleComp World α) (q : Nat) (pos : 1≤q)
    (bounded : PublicQueryBound (recordRows prog) (q+2^32)) :
    Pr{let r←(graphModel canonicalEncoding p).run (recordRows prog) emptyTrace}[Witness r.1.2]≤
      15*(q:ENNReal)/2^124 := by
  apply (prEvent_mono_of_support _ _ _ ?_).trans (Fixed.all_q_reserve p canonicalEncoding _ q pos bounded)
  intro r member w
  exact w r.2 (run_recorded_rows_support (graphHandler p) Stored (store_step p) prog emptyTrace r member).2

private theorem empty_cache : emptyTrace.cache=(∅ : CompressionCache) := by
  apply QueryCache.ext;intro x
  exact (emptyTrace.cache_none_iff x).mpr (fun ⟨i,_⟩=>Fin.elim0 i)

theorem fixed_bound (p : Perm) {α : Type} (prog : OracleComp World α) (q : Nat) (pos : 1≤q)
    (bounded : PublicQueryBound (recordRows prog) (q+2^32)) :
    Pr{let r←(do let H←$ᵗ Compression; fixedOracleRun ⟨H,p⟩ (recordRows prog))}[Witness r.2]≤
      15*(q:ENNReal)/2^124 := by
  let pr:=recordRows prog
  have samples:=(EvalDistEq.of_evalDist_eq (compression_sampling_empty p pr)).prEvent_eq (fun r=>Witness r.2)
  rw [←samples,prEvent_map]
  have projection:=congrArg (fun z : ProbComp ((α×List PublicRow)×CompressionCache) =>
      Pr{let r←z}[Witness r.1.2]) (run_cache p pr emptyTrace)
  rw [empty_cache] at projection
  simp only [bind_pure_comp,prEvent_map,Function.comp_def] at projection
  exact projection.symm.le.trans (trace_witness_bound p prog q pos bounded)

private theorem fraction (q : ENNReal) : 15*q/2^124≤q/2^120 := by
  calc
    _ ≤ 16*q/2^124 := ENNReal.div_le_div_right (mul_le_mul_of_nonneg_right (by norm_num : (15:ENNReal)≤16) zero_le) _
    _ = _ := by
      rw [show (2:ENNReal)^124=16*2^120 by norm_num]
      exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

theorem binding_of_replay (scheme : Scheme) (proof : BindingReplayEvidence scheme Witness (2^32)) :
    scheme.Binding := by
  apply scheme_binding_of_replay_with scheme proof witness_mono
  intro prog q count pos _ room bounded
  have swapped:=distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
    (fun H p=>fixedOracleRun ⟨H,p⟩ (recordRows prog))
  have probabilities:=(EvalDistEq.of_evalDist_eq swapped).prEvent_eq (fun r=>Witness r.2)
  simp only [Oracle.sample,bind_assoc,pure_bind]
  rw [probabilities]
  apply prEvent_bind_le_of_forall_le_of_support;intro p _
  apply (fixed_bound p prog q pos (bounded.mono room)).trans
  exact fraction q
end CommitGolfCandidate.Chained.Replay
