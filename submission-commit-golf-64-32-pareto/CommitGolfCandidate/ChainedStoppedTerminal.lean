import CommitGolfCandidate.ChainedStoppedProjection

/-! Terminal leaf/final collisions are covered by the stopped flag or graph failure. -/
namespace CommitGolfCandidate.Chained.Stopped
open CommitGolf OracleComp OracleSpec

theorem valid_run {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    {α : Type} (program : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound program budget) (s : State)
    (valid : (model limit enc calls width small widthBound).valid s known)
    (result : α × State)
    (reached : result ∈ support ((model limit enc calls width small widthBound).run program s)) :
    (model limit enc calls width small widthBound).valid result.2 (known+budget) := by
  let m := model limit enc calls width small widthBound
  induction program using OracleComp.inductionOn generalizing budget known s with
  | pure value =>
    simp only [PredictableSurvival.Model.run,simulateQ_pure,StateT.run_pure,support_pure,
      Set.mem_singleton_iff] at reached
    subst result
    exact ⟨valid.1,valid.2.trans (Nat.le_add_right known budget)⟩
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query)) at bounded
    have step : m.run ((liftM (World.query query) : OracleComp World _) >>= next) s =
        (m.handler query).run s >>= fun answer => m.run (next answer.1) answer.2 := by
      simp [PredictableSurvival.Model.run,simulateQ_bind,StateT.run_bind]
    rw [step] at reached
    obtain ⟨answer,sampled,last⟩ := (mem_support_bind_iff _ _ _).mp reached
    rcases query with coins | publicQuery
    · rw [m.coins] at sampled
      simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at sampled
      obtain ⟨coin,_,rfl⟩ := sampled
      exact ih coin budget known (by simpa only [Oracle.callCost,Nat.sub_zero] using bounded.2 coin) s valid last
    · have positive : 1 ≤ budget := bounded.1
      have current := m.preserves publicQuery s known valid answer sampled
      have terminal := ih answer.1 (budget-1) (known+1) (bounded.2 answer.1) answer.2 current last
      have same : known+1+(budget-1) = known+budget := by omega
      simpa only [same] using terminal

theorem terminal_bad {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (s : State) (core : Core limit enc calls width s) (within : s.oracle.base.count ≤ limit)
    (bad : rawBad enc calls width s.oracle) : s.won ∨ ¬ Good enc s.oracle.graph := by
  classical
  by_cases good : Good enc s.oracle.graph
  · left
    by_contra safe
    have live := core.live within good safe
    rcases bad with leaf | final
    · exact leaf live.2.2.1
    · exact live.2.2.2 final
  · exact Or.inr good

theorem terminal_bound {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    (rateBound : ∀ k, Counters.rate calls k ≤ 8)
    (dense : ∀ k, 2^238 ≤ (Counters.rate calls k)^2*2^(Counters.widths width k))
    (finite : 8*(limit+1) < 2^238) {α : Type} (program : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound program budget) (room : budget ≤ limit) :
    Pr{let result ← (model limit enc calls width small widthBound).run program empty}[
      rawBad enc calls width result.2.oracle] ≤
      (1-ENNReal.ofReal (Real.exp (-((limit+1 : Nat) : ℝ)^2/(2*(2^238-8*((limit+1 : Nat) : ℝ))))))+
        ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (joint_bound small widthBound rateBound dense finite program budget bounded room)
  intro result reached bad
  have valid := valid_run small widthBound program budget 0 bounded empty
    ⟨core_empty limit enc calls width,by decide⟩ result reached
  exact terminal_bad result.2 valid.1 (valid.2.trans (by simpa only [Nat.zero_add] using room)) bad

end CommitGolfCandidate.Chained.Stopped
