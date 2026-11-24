import CommitGolfCandidate.ChainedRecordedWitness
import CommitGolfCandidate.JointOracle238Sampling
import CommitGolfCandidate.ChainedReplayBudget

/-! Replay evidence is bounded in the same sampled oracle game as binding. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

theorem observer_valid_run {α : Type} (program : OracleComp World α) (s : Observer.State)
    (valid : Observer.Valid s) (result : α × Observer.State)
    (reached : result ∈ support (Observer.run program s)) : Observer.Valid result.2 := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure value =>
    simp only [Observer.run,simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact valid
  | query_bind query next ih =>
    have step : Observer.run ((liftM (World.query query) : OracleComp World _) >>= next) s =
        (Observer.handler query).run s >>= fun answer => Observer.run (next answer.1) answer.2 := by
      simp [Observer.run,simulateQ_bind,StateT.run_bind]
    rw [step] at reached
    obtain ⟨answer,sampled,last⟩ := (mem_support_bind_iff _ _ _).mp reached
    rcases query with coins | publicQuery
    · rw [Observer.handler_coins] at sampled
      simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
      obtain ⟨coin,_,rfl⟩ := sampled
      exact ih coin s valid last
    · exact ih answer.1 answer.2 (Observer.preserves publicQuery s valid answer sampled) last

theorem observer_recorded_stores {α : Type} (program : OracleComp World α) (s : Observer.State)
    (result : (α × List PublicRow) × Observer.State)
    (reached : result ∈ support (Observer.run (recordRows program) s)) :
    ∀ row ∈ result.1.2, JointOracle238.Stores result.2.base row := by
  have projected : (result.1,result.2.base) ∈ support (Observer.sourceRun (recordRows program) s.base) := by
    rw [← Observer.run_project]
    simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff]
    exact ⟨result,reached,rfl⟩
  exact (JointOracle238.recorded_stores program s.base (result.1,result.2.base) projected).2

theorem observer_recorded_failure {α : Type} (enc : Encoding) (program : OracleComp World α)
    (q : Nat) (positive : 1 ≤ q) (bounded : PublicQueryBound (recordRows program) (q+2^32)) :
    Pr{let result ← Observer.run (recordRows program) Observer.State.empty}[
      RecordedFailure enc calls width result.1.2] ≤ 15*(q:ENNReal)/2^124 := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (all_q_reserve enc (recordRows program) q positive bounded)
  intro result reached failure
  exact recorded_failure_bad result.2
    (observer_valid_run _ _ Observer.valid_empty result reached)
    (observer_recorded_stores program _ result reached) failure

theorem observer_sampling_probability {α : Type} (program : OracleComp World α) (event : α → Prop) :
    Pr{let value ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle program)}[event value] =
      Pr{let result ← Observer.run program Observer.State.empty}[event result.1] := by
  have sampled := JointOracle238.joint_sampling_probability program event
  have projection := congrArg (fun computation : ProbComp (α × JointOracle238.State) =>
    Pr{let result ← computation}[event result.1]) (Observer.run_project program Observer.State.empty)
  simp only [bind_pure_comp,Functor.map_map] at projection
  have source : Pr{let value ← JointOracle238.lazyOut program JointOracle238.State.empty}[event value] =
      Pr{let result ← Observer.sourceRun program JointOracle238.State.empty}[event result.1] := by
    simp only [JointOracle238.lazyOut,Observer.sourceRun,prEvent_map]
  have first : Pr{let value ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle program)}[event value] =
      Pr{let value ← JointOracle238.lazyOut program JointOracle238.State.empty}[event value] := by
    simpa only [Oracle.sample,bind_assoc,pure_bind] using sampled
  exact first.trans (source.trans projection.symm)

theorem sampled_recorded_failure {α : Type} (enc : Encoding) (program : OracleComp World α)
    (q : Nat) (positive : 1 ≤ q) (bounded : PublicQueryBound (recordRows program) (q+2^32)) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      RecordedFailure enc calls width result.2] ≤ 15*(q:ENNReal)/2^124 := by
  rw [observer_sampling_probability]
  exact observer_recorded_failure enc program q positive bounded

theorem reserve_target (q : Nat) : 15*(q:ENNReal)/2^124 ≤ (q:ENNReal)/2^120 := by
  have nonnegative : (0:ℝ) ≤ q := by positivity
  have real : 15*(q:ℝ)/2^124 ≤ (q:ℝ)/2^120 := by nlinarith
  have bound := ENNReal.ofReal_le_ofReal real
  simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 2^124),
    ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 2^120),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 15),ENNReal.ofReal_natCast,
    show ENNReal.ofReal (15:ℝ) = 15 from by norm_num,
    show ENNReal.ofReal ((2:ℝ)^124) = (2:ENNReal)^124 from by norm_num,
    show ENNReal.ofReal ((2:ℝ)^120) = (2:ENNReal)^120 from by norm_num] using bound

theorem scheme_binding_of_recorded_replay (scheme : Scheme) (enc : Encoding)
    (spec : BindingReplay scheme (RecordedFailure enc calls width)) : scheme.Binding := by
  apply binding_of_replay scheme spec (fun included evidence => evidence.mono included)
  intro program q budget positive _ replay bounded
  exact (sampled_recorded_failure enc program q positive (bounded.mono replay)).trans (reserve_target q)

end CommitGolfCandidate.Chained
