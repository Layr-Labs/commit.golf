import CommitGolfCandidate.ChainedStoppedTerminal
import CommitGolfCandidate.ChainedReserve
import CommitGolfCandidate.ChainedSchedule

/-! The approved schedule has a 1/16 pointwise reserve, including 32-bit replay. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem observer_terminal_bound {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    (rateBound : ∀ k, Counters.rate calls k ≤ 8)
    (dense : ∀ k, 2^238 ≤ (Counters.rate calls k)^2*2^(Counters.widths width k))
    (finite : 8*(limit+1) < 2^238) {α : Type} (program : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound program budget) (room : budget ≤ limit) :
    Pr{let result ← Observer.run program Observer.State.empty}[Stopped.rawBad enc calls width result.2] ≤
      (1-ENNReal.ofReal (Real.exp (-((limit+1 : Nat) : ℝ)^2/(2*(2^238-8*((limit+1 : Nat) : ℝ))))))+
        ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  have same := congrArg (fun computation : ProbComp (α × Observer.State) =>
    Pr{let result ← computation}[Stopped.rawBad enc calls width result.2])
      (Stopped.run_project (enc := enc) (calls := calls) small widthBound program Stopped.empty)
  simp only [bind_pure_comp,Functor.map_map] at same
  exact same.symm.le.trans
    (Stopped.terminal_bound small widthBound rateBound dense finite program budget bounded room)

theorem schedule_rate : ∀ k, Counters.rate calls k ≤ 8 := by
  intro k
  cases k with
  | none => decide
  | some h => exact calls_bound h

theorem schedule_dense : ∀ k, 2^238 ≤ (Counters.rate calls k)^2*2^(Counters.widths width k) := by
  intro k
  cases k with
  | none => simp [Counters.rate,Counters.widths]
  | some h => exact density h

theorem schedule_width : ∀ h, width h ≤ 256 := fun h => (width_upper h).trans (by decide)

theorem replay_limits (q : Nat) (bounded : q ≤ 2^121) :
    2*(q+2^32) < 2^256 ∧ 8*(q+2^32+1) < 2^238 := by
  constructor <;> omega

theorem finite_target (q : Nat) (positive : 1 ≤ q) (small : (q:ℝ) ≤ (11/10)*2^120) :
    (1-ENNReal.ofReal (Real.exp (-Reserve.exponent ((q+2^32+1 : Nat) : ℝ))))+
      (((q+2^32 : Nat)*(q+2^32) : Nat) : ENNReal)/2^256 ≤ 15*(q:ENNReal)/2^124 := by
  have qBoundR : (q:ℝ) ≤ 2^121 := by linarith
  have qBound : q ≤ 2^121 := by exact_mod_cast qBoundR
  have finite : 8*(q+2^32+1) < 2^238 := by omega
  have finiteR : (8:ℝ)*((q+2^32+1 : Nat):ℝ) < 2^238 := by exact_mod_cast finite
  have gap : (0:ℝ) < 2^238-8*((q+2^32+1 : Nat):ℝ) := by linarith
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

theorem all_q_reserve {α : Type} (enc : Encoding) (program : OracleComp World α)
    (q : Nat) (positive : 1 ≤ q) (bounded : PublicQueryBound program (q+2^32)) :
    Pr{let result ← Observer.run program Observer.State.empty}[Stopped.rawBad enc calls width result.2] ≤
      15*(q:ENNReal)/2^124 := by
  by_cases small : (q:ℝ) ≤ (11/10)*2^120
  · have qBoundR : (q:ℝ) ≤ 2^121 := by linarith
    have qBound : q ≤ 2^121 := by exact_mod_cast qBoundR
    have limits := replay_limits q qBound
    have bound := observer_terminal_bound (enc := enc) limits.1 schedule_width schedule_rate schedule_dense limits.2
      program (q+2^32) bounded (le_refl _)
    have numeric : (1-ENNReal.ofReal (Real.exp (-((q+2^32+1 : Nat):ℝ)^2/
        (2*(2^238-8*((q+2^32+1 : Nat):ℝ))))))+
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

end CommitGolfCandidate.Chained
