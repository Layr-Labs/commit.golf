import CommitGolfCandidate.Stage3cTerminal
import CommitGolfCandidate.ChainedReserve
namespace CommitGolfCandidate.Chained.Fixed
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
theorem valid_run {limit : Nat} {enc : Encoding} (p : Perm)
    (small : 2*limit < 2^256) 
    {α : Type} (program : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound program budget) (s : State)
    (valid : (model limit enc p small).valid s known)
    (result : α × State)
    (reached : result ∈ support ((model limit enc p small).run program s)) :
    (model limit enc p small).valid result.2 (known+budget) := by
  let m := model limit enc p small
  induction program using OracleComp.inductionOn generalizing budget known s with
  | pure value =>
    simp only [PredictableSurvival.Model.run,simulateQ_pure,StateT.run_pure,support_pure,
      Set.mem_singleton_iff] at reached
    subst result
    exact ⟨valid.available.trans (Nat.le_add_right known budget),valid.work,valid.track⟩
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


theorem terminal_bound {l : Nat} (enc : Encoding) (p : Perm) (small : 2*l<2^256) (finite : 16*(l+1)<2^238)
    {α : Type} (prog : OracleComp World α) (bound : PublicQueryBound prog l) :
    Pr{let r←(graphModel enc p).run prog emptyTrace}[FinalCollision enc calls width r.2 ∨ ¬Good enc r.2] ≤
      (1-ENNReal.ofReal (Real.exp (-((l+1:Nat):ℝ)^2/(2*(2^238-16*((l+1:Nat):ℝ))))))+
        ((l*(l-1):Nat):ENNReal)/2^256 := by
  let m:=model l enc p small
  have eqn (ev : Trace→Prop) :
      Pr{let r←m.run prog empty}[ev r.2.trace]=Pr{let r←(graphModel enc p).run prog emptyTrace}[ev r.2] := by
    have e:=congrArg (fun z : ProbComp (α × Trace)=>Pr{let r←z}[ev r.2]) (project_run enc p small prog empty)
    simp only [bind_pure_comp,prEvent_map,Function.comp_def] at e
    exact e
  rw [←eqn (fun t=>FinalCollision enc calls width t ∨ ¬Good enc t)]
  refine (prEvent_mono_of_support _ _ (fun z=>z.2.won ∨ ¬Good enc z.2.trace) ?_).trans ?_
  · intro r member hit
    have v := valid_run p small prog l 0 bound empty (valid_zero l enc) r member
    by_cases good : Good enc r.2.trace
    · left;by_contra safe
      exact (v.track (by simpa only [Nat.zero_add] using v.available) good safe).2 (hit.resolve_right (not_not.mpr good))
    · exact Or.inr good
  · exact (prEvent_or_le _ _ _).trans (add_le_add (stopped_bound enc p small finite prog bound)
      ((eqn (fun t=>¬Good enc t)).le.trans (adaptive_graph_bound enc p prog l bound)))

theorem replay_limits (q : Nat) (bounded : q ≤ 2^121) :
    2*(q+2^32) < 2^256 ∧ 16*(q+2^32+1) < 2^238 := by
  constructor <;> omega

theorem finite_target (q : Nat) (positive : 1 ≤ q) (small : (q:ℝ) ≤ (11/10)*2^120) :
    (1-ENNReal.ofReal (Real.exp (-Reserve.exponent ((q+2^32+1 : Nat) : ℝ))))+
      (((q+2^32 : Nat)*(q+2^32) : Nat) : ENNReal)/2^256 ≤ 15*(q:ENNReal)/2^124 := by
  have qBoundR : (q:ℝ) ≤ 2^121 := by linarith
  have qBound : q ≤ 2^121 := by exact_mod_cast qBoundR
  have finite : 16*(q+2^32+1) < 2^238 := by omega
  have finiteR : (16:ℝ)*((q+2^32+1 : Nat):ℝ) < 2^238 := by exact_mod_cast finite
  have gap : (0:ℝ) < 2^238-16*((q+2^32+1 : Nat):ℝ) := by linarith
  have nonnegative : 0 ≤ 1-Real.exp (-Reserve.exponent ((q+2^32+1 : Nat):ℝ)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ Reserve.exponent ((q+2^32+1 : Nat):ℝ) := by
      unfold Reserve.exponent
      exact div_nonneg (sq_nonneg _) (by positivity)
    linarith
  calc
    _ = ENNReal.ofReal ((1-Real.exp (-Reserve.exponent ((q+2^32+1 : Nat):ℝ)))+
        (((q+2^32 : Nat):ℝ)*((q+2^32 : Nat):ℝ))/2^256) := by
      rw [ENNReal.ofReal_add nonnegative (by positivity),
        ENNReal.ofReal_sub _ (Real.exp_pos _).le,ENNReal.ofReal_one,
        ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast,Nat.cast_mul]
      norm_num
    _ ≤ ENNReal.ofReal ((15/16)*((q:ℝ)/2^120)) :=
      ENNReal.ofReal_le_ofReal (Reserve.joint_margin q positive small)
    _ = _ := by
      rw [show (15/16)*((q:ℝ)/2^120) = 15*(q:ℝ)/2^124 by ring,
        ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_natCast,ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat,ENNReal.ofReal_ofNat]

theorem all_q_reserve {α : Type} (p : Perm) (enc : Encoding) (program : OracleComp World α)
    (q : Nat) (positive : 1 ≤ q) (bounded : PublicQueryBound program (q+2^32)) :
    Pr{let result ← (graphModel enc p).run program emptyTrace}[FinalCollision enc calls width result.2 ∨ ¬Good enc result.2] ≤
      15*(q:ENNReal)/2^124 := by
  by_cases small : (q:ℝ) ≤ (11/10)*2^120
  · have qBoundR : (q:ℝ) ≤ 2^121 := by linarith
    have qBound : q ≤ 2^121 := by exact_mod_cast qBoundR
    have limits := replay_limits q qBound
    have bound := terminal_bound enc p limits.1 limits.2 program bounded
    have numeric : (1-ENNReal.ofReal (Real.exp (-((q+2^32+1 : Nat):ℝ)^2/
        (2*(2^238-16*((q+2^32+1 : Nat):ℝ))))))+
        (((q+2^32 : Nat)*(q+2^32) : Nat):ENNReal)/2^256 ≤ 15*(q:ENNReal)/2^124 := by
      simpa only [Reserve.exponent,neg_div] using finite_target q positive small
    have error : (((q+2^32 : Nat)*(q+2^32-1) : Nat):ENNReal)/2^256 ≤
        (((q+2^32 : Nat)*(q+2^32) : Nat):ENNReal)/2^256 :=
      ENNReal.div_le_div_right (Nat.cast_le.mpr
        (Nat.mul_le_mul_left (q+2^32) (Nat.sub_le (q+2^32) 1))) _
    exact bound.trans ((add_le_add (le_refl _) error).trans numeric)
  · refine (prEvent_le_one _).trans ?_
    have real : (1:ℝ) ≤ 15*(q:ℝ)/2^124 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have bound := ENNReal.ofReal_le_ofReal real
    simpa only [ENNReal.ofReal_one,ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 2^124),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 15),ENNReal.ofReal_natCast,
      show ENNReal.ofReal (15:ℝ) = 15 from by norm_num,
      show ENNReal.ofReal ((2:ℝ)^124) = (2:ENNReal)^124 from by norm_num] using bound

end CommitGolfCandidate.Chained.Fixed
