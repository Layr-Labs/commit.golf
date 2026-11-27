import CommitGolfCandidate.Stage3cStopped
import CommitGolfCandidate.Stage3cGraphRun
namespace CommitGolfCandidate.Chained.Fixed
open CommitGolf OracleComp OracleSpec

def empty : State := ⟨emptyTrace,fun _=>0,False⟩

theorem no_empty (enc : Encoding) (id : Height × Seed) : ¬Completed enc calls emptyTrace id := by
  rintro ⟨e,_⟩;exact Fin.elim0 (e.row 0)

theorem valid_zero (l : Nat) (enc : Encoding) : Valid l enc empty 0 := by
  refine ⟨le_rfl,by simp [empty,Weighted.work],?_⟩
  intro _ _ _
  constructor
  · funext h
    have no : completedSeeds enc calls emptyTrace h=∅ := by ext x;exact iff_false_intro (no_empty enc (h,x))
    simp [completedCount,no,empty]
  · rintro ⟨h,a,b,_,hit,_⟩;exact no_empty enc (h,a) hit

noncomputable def model (l : Nat) (enc : Encoding) (p : Perm) (small : 2*l<2^256) :
    PredictableSurvival.Model State where
  handler := handler l enc p
  valid := Valid l enc
  bad := State.won
  mass s := Weighted.potential width s.counts
  hazard s q := Weighted.hazard width s.counts (kind l enc s q)
  coins _ _ := rfl
  preserves := preserve p small
  fresh := hazard_bound p small
  mass_step := by
    intro q s known valid safe r reached lastSafe
    change r∈support (do let a←(graphHandler p (.inr q)).run s.trace; pure (a.1,finish l enc s q a.2)) at reached
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at reached
    obtain ⟨a,_,rfl⟩:=reached
    exact Weighted.potential_advance width s.counts (kind l enc s q)

theorem stopped_bound {l : Nat} (enc : Encoding) (p : Perm) (small : 2*l<2^256) (finite : 16*(l+1)<2^238)
    {α : Type} (prog : OracleComp World α) (bound : PublicQueryBound prog l) :
    Pr{let r←(model l enc p small).run prog empty}[r.2.won] ≤
      1-ENNReal.ofReal (Real.exp (-((l+1:Nat):ℝ)^2/(2*(2^238-16*((l+1:Nat):ℝ))))) := by
  have f := Weighted.adaptive_weighted_bound (model l enc p small) calls width State.counts (kind l enc)
    (fun _=>rfl) (fun _ _=>rfl) calls_bound density l (l+1) finite
    (fun q _ _ v _ _ => (forecast small v q).trans (Nat.le_succ l)) prog l 0 bound (by omega) empty (valid_zero l enc) (show ¬False from id)
  have mass : (model l enc p small).mass empty=1 := by simp [model,Weighted.potential,empty,survival]
  rw [mass,div_one] at f
  exact f

theorem project_step (l : Nat) (enc : Encoding) (p : Perm) (q : World.Domain) (s : State) :
    (do let r←(handler l enc p q).run s; pure (r.1,r.2.trace))=(graphHandler p q).run s.trace := by
  cases q with
  | inl n =>
    change (do let r←(do let a←(liftM (unifSpec.query n) : ProbComp _);pure (a,s));pure (r.1,r.2.trace)) =
      (do let a←(liftM (unifSpec.query n) : ProbComp _);pure (a,s.trace))
    simp only [bind_assoc,pure_bind]
  | inr q =>
    change ((graphHandler p (.inr q)).run s.trace >>= fun r => pure (r.1,finish l enc s q r.2)) >>= _ = _
    simp [finish,bind_assoc]

theorem project_run {l : Nat} (enc : Encoding) (p : Perm) (small : 2*l<2^256)
    {α : Type} (prog : OracleComp World α) (s : State) :
    (do let r←(model l enc p small).run prog s;pure (r.1,r.2.trace))=
      (graphModel enc p).run prog s.trace := by
  induction prog using OracleComp.inductionOn generalizing s with
  | pure v => simp [PredictableSurvival.Model.run,GraphBudget.run]
  | query_bind q next ih =>
    have left : (model l enc p small).run ((liftM (World.query q) : OracleComp World _) >>= next) s =
        (handler l enc p q).run s >>= fun r=>(model l enc p small).run (next r.1) r.2 := by
      simp [PredictableSurvival.Model.run,model,simulateQ_bind,StateT.run_bind]
    have right : (graphModel enc p).run ((liftM (World.query q) : OracleComp World _) >>= next) s.trace =
        (graphHandler p q).run s.trace >>= fun r=>(graphModel enc p).run (next r.1) r.2 := by
      simp [GraphBudget.run,graphModel,simulateQ_bind,StateT.run_bind]
    rw [left,right,←project_step l enc p q s]
    simp only [bind_assoc,pure_bind]
    congr 1;funext r;exact ih r.1 r.2
end CommitGolfCandidate.Chained.Fixed
