import CommitGolfCandidate.ReconstructedHidingRetention

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp CommitGolfCandidate.Permutation HidingTape
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048

def allowAnswer (allow : Reply → Reply → Bool) (q : World.Domain) (a : World.Range q) : Bool :=
  match q with
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr (.inl x)) => allow x a
  | .inr (.inr (.inr y)) => allow a y

def checkedQueries {A : Type} (allow : Reply → Reply → Bool) (g : OracleComp World A) :
    Bool → OracleComp World (A × Bool) :=
  OracleComp.recOn g (fun a ok => pure (a,ok)) (fun q _ next ok => do
    let a ← (liftM (World.query q) : OracleComp World _)
    next a (ok && allowAnswer allow q a))

def cleanTrace (allow : Reply → Reply → Bool) (t : Trace Reply) : Prop :=
  ∀ row ∈ t, allow row.inp row.out = true

def fitsPerm (π : Perm) (t : Trace Reply) : Prop := ∀ e ∈ t, π e.inp = e.out

private theorem cons_clean (allow : Reply → Reply → Bool) (e : Entry Reply) (t : Trace Reply) :
    cleanTrace allow (e::t) ↔ cleanTrace allow t ∧ allow e.inp e.out=true := by
  simp only [cleanTrace,List.forall_mem_cons,and_comm]

theorem clean_fwd_iff (allow : Reply → Reply → Bool) (π : Perm) (t : Trace Reply) (known : fitsPerm π t)
    (x : Reply) : cleanTrace allow (t.stepF x (π x)) ↔ cleanTrace allow t ∧ allow x (π x)=true := by
  unfold Trace.stepF
  split
  · rename_i present
    obtain ⟨e,h,inp⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    have img := known e h
    refine ⟨fun safe => ⟨safe,?_⟩,And.left⟩
    rw [←inp,img]
    exact safe e h
  · exact cons_clean _ _ _

theorem clean_inv_iff (allow : Reply → Reply → Bool) (π : Perm) (t : Trace Reply) (known : fitsPerm π t)
    (y : Reply) : cleanTrace allow (t.stepI (π.symm y) y) ↔ cleanTrace allow t ∧ allow (π.symm y) y=true := by
  unfold Trace.stepI
  split
  · rename_i present
    obtain ⟨e,h,out⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    have preimage : π.symm e.out=e.inp := π.symm_apply_eq.mpr (known e h).symm
    refine ⟨fun safe => ⟨safe,?_⟩,And.left⟩
    rw [←out,preimage]
    exact safe e h
  · exact cons_clean _ _ _

private theorem fits_fwd (π : Perm) (t : Trace Reply) (h : fitsPerm π t) (x : Reply) :
    fitsPerm π (t.stepF x (π x)) := by
  unfold Trace.stepF
  split
  · exact h
  · intro e mem
    rcases List.mem_cons.mp mem with rfl|prev
    · rfl
    · exact h _ prev

private theorem fits_inv (π : Perm) (t : Trace Reply) (h : fitsPerm π t) (y : Reply) :
    fitsPerm π (t.stepI (π.symm y) y) := by
  unfold Trace.stepI
  split
  · exact h
  · intro e mem
    rcases List.mem_cons.mp mem with rfl|prev
    · exact π.apply_symm_apply y
    · exact h _ prev

theorem checked_eager {A : Type} (allow : Reply → Reply → Bool) (c : Compression) (π : Perm)
    (g : OracleComp World A) (ev : A → Prop) (s : PState Reply) (start : Bool)
    (known : fitsPerm π s.trace) (initial : (start=true ↔ cleanTrace allow s.trace)) :
    (toStrat c (checkedQueries allow g start)).eager π s (fun a _ => ind (ev a.1 ∧ a.2=true)) =
      (toStrat c g).eager π s (fun a t => ind (ev a ∧ cleanTrace allow t.trace)) := by
  induction g using OracleComp.inductionOn generalizing s start with
  | pure a =>
    change ind (ev a ∧ start=true) = ind (ev a ∧ cleanTrace allow s.trace)
    rw [initial]
  | query_bind q next ih =>
    have expand : checkedQueries allow ((liftM (World.query q) : OracleComp World _) >>= next) start =
        ((liftM (World.query q) : OracleComp World _) >>= fun a => checkedQueries allow (next a) (start && allowAnswer allow q a)) := rfl
    rw [expand]
    rcases q with coins | inp | x | y
    · rw [to_strat_coins,to_strat_coins]
      apply avg_congr
      intro a _
      exact ih a s (start && true) known (by simpa only [Bool.and_true] using initial)
    · rw [to_strat_compress,to_strat_compress]
      exact ih (c inp) s (start && true) known (by simpa only [Bool.and_true] using initial)
    · rw [to_strat_permute,to_strat_permute]
      apply ih (π x) ⟨s.trace.stepF x (π x),s.count+1⟩ _ (fits_fwd π s.trace known x)
      simp only [allowAnswer,Bool.and_eq_true,initial]
      exact (clean_fwd_iff allow π s.trace known x).symm
    · rw [to_strat_inverse,to_strat_inverse]
      apply ih (π.symm y) ⟨s.trace.stepI (π.symm y) y,s.count+1⟩ _ (fits_inv π s.trace known y)
      simp only [allowAnswer,Bool.and_eq_true,initial]
      exact (clean_inv_iff allow π s.trace known y).symm

end CommitGolfCandidate.Reconstruction.HidingTraffic
