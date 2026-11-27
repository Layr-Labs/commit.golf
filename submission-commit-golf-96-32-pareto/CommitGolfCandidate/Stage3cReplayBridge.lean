import CommitGolfCandidate.Stage3cRows
set_option Elab.async false
namespace CommitGolfCandidate.Chained.Replay
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem fixed_oracle_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

theorem fixed_oracle_run_map (oracle : Oracle) {α β : Type}
    (f : α → β) (computation : OracleComp World α) :
    fixedOracleRun oracle (f <$> computation) = f <$> fixedOracleRun oracle computation := by
  simp only [fixedOracleRun, oracle_run_map, Functor.map_map]

structure BindingReplayEvidence (scheme : Scheme) (witness : List PublicRow → Prop)
    (overhead : Nat := 2 ^ 32) where
  replay : Scheme.Claim → OracleComp World Unit
  bounded : ∀ claim, PublicQueryBound (replay claim) overhead
  extracts : ∀ oracle claim, scheme.Breaks oracle claim →
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (replay claim))), witness result.2

def replayOption (replay : Scheme.Claim → OracleComp World Unit) : Option Scheme.Claim → OracleComp World Unit
  | none => pure ()
  | some claim => replay claim

def boundedReplay (replay : Scheme.Claim → OracleComp World Unit) (adversary : Scheme.Adversary)
    (budget : Nat) : OracleComp World Unit :=
  limitPublicQueries adversary budget >>= replayOption replay

theorem bounded_replay_queries (scheme : Scheme) {witness : List PublicRow → Prop} {overhead : Nat}
    (spec : BindingReplayEvidence scheme witness overhead)
    (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (recordRows (boundedReplay spec.replay adversary budget)) (budget + overhead) := by
  apply record_rows_bound
  apply public_query_bound_bind (limit_public_bound adversary budget)
  intro limited
  cases limited with
  | none => trivial
  | some claim => exact spec.bounded claim

private theorem replay_dominated (scheme : Scheme) {witness : List PublicRow → Prop} {overhead : Nat}
    (spec : BindingReplayEvidence scheme witness overhead)
    (preserves : ∀ {earlier later}, (∀ row ∈ earlier, row ∈ later) → witness earlier → witness later)
    (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    Pr{let result ← oracle.run adversary}[scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] ≤
      Pr{let result ← fixedOracleRun oracle (recordRows (boundedReplay spec.replay adversary budget))}[
        witness result.2] := by
  classical
  let limited := limitPublicQueries adversary budget
  let start := fixedOracleRun oracle (recordRows limited)
  let good (limited : Option Scheme.Claim) := ∃ claim, limited = some claim ∧ scheme.Breaks oracle claim
  have projected : Prod.fst <$> start = fixedOracleRun oracle limited := by
    rw [← fixed_oracle_run_map, record_rows_erase]
  have prefixWin :
      Pr{let result ← start}[good result.1] =
        Pr{let result ← oracle.run adversary}[scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] := by
    rw [← limit_public_probability oracle adversary budget (scheme.Breaks oracle)]
    have event := congrArg (fun x : ProbComp (Option Scheme.Claim) => Pr{let result ← x}[good result]) projected
    simpa only [prEvent_map, fixedOracleRun, Function.comp_def, good, limited] using event
  rw [← prefixWin]
  unfold boundedReplay
  rw [record_rows_bind, fixed_oracle_run_bind]
  change Pr{let result ← start}[good result.1] ≤ _
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨outcome, trace⟩
  by_cases winning : good outcome
  · obtain ⟨claim, fixed, breaks⟩ := winning
    subst outcome
    have sure :
      Pr{let result ← fixedOracleRun oracle (recordRows (replayOption spec.replay (some claim)) >>= fun next =>
        pure (next.1, trace ++ next.2))}[witness result.2] = 1 := by
      rw [fixed_oracle_run_bind]
      apply prEvent_eq_one_of_forall_mem_support
      intro result reached
      obtain ⟨next, called, same⟩ := (mem_support_bind_iff _ _ _).mp reached
      rw [fixed_oracle_run_pure] at same
      simp only [support_pure, Set.mem_singleton_iff] at same
      subst result
      exact preserves (fun _ present => List.mem_append_right trace present) (spec.extracts oracle claim breaks next called)
    have win : good (some claim) := ⟨claim, rfl, breaks⟩
    simp only [win, ite_true, sure, mul_one, start, limited]
    exact le_rfl
  · simp [winning]

theorem scheme_binding_of_replay_with (scheme : Scheme) {witness : List PublicRow → Prop} {overhead : Nat}
    (spec : BindingReplayEvidence scheme witness overhead)
    (preserves : ∀ {earlier later}, (∀ row ∈ earlier, row ∈ later) → witness earlier → witness later)
    (collisionBound : ∀ (program : OracleComp World Unit) (q calls : Nat),
      1 ≤ q → q ≤ 2 ^ 120 → calls ≤ q + overhead → PublicQueryBound (recordRows program) calls →
      Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
        witness result.2] ≤ (q : ENNReal) / 2 ^ 120) : scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · apply (prEvent_le_one _).trans
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
    simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ budget from Nat.cast_le.mpr large)
  · have small : budget ≤ 2 ^ 120 := by
      change ¬ 2 ^ 120 ≤ budget at large
      omega
    have reduced :
        Pr{let (oracle, claim, calls) ← Scheme.bindingGame adversary}[
          scheme.Breaks oracle claim ∧ calls ≤ budget] ≤
        Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (recordRows (boundedReplay spec.replay adversary budget)))}[
          witness result.2] := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul_of_nonneg_left _ zero_le
      simp only [prEvent_map]
      exact replay_dominated scheme spec preserves oracle adversary budget
    exact reduced.trans (collisionBound (boundedReplay spec.replay adversary budget) budget (budget + overhead)
      positive small le_rfl (bounded_replay_queries scheme spec adversary budget))

end CommitGolfCandidate.Chained.Replay
