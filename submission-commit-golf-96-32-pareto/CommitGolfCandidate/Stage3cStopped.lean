import CommitGolfCandidate.Stage3cPredictionStep
namespace CommitGolfCandidate.Chained.Fixed
open CommitGolf OracleComp OracleSpec

noncomputable def handler (limit : Nat) (enc : Encoding) (p : Perm) :
    QueryImpl World (StateT State ProbComp) := by
  classical
  exact fun q => match q with
    | .inl coins => fun s=>do
      let ans←(liftM (unifSpec.query coins) : ProbComp _)
      pure (ans,s)
    | .inr pub => fun s=> do
      let r←(graphHandler p (.inr pub)).run s.trace
      pure (r.1,finish limit enc s pub r.2)

private theorem skip_seen (l : Nat) (enc : Encoding) (s : State) (x : Input) (e : ∃ j, s.trace.input j=x) :
    kind l enc s (.inl x)=none := by
  classical
  by_cases h : Live l enc s <;> simp [kind,h,e]

private theorem skip_perm (l : Nat) (enc : Encoding) (s : State) (x : PermSpec.Domain) :
    kind l enc s (.inr x)=none := by
  classical
  by_cases h : Live l enc s <;> simp [kind,h]

theorem preserve {l : Nat} {enc : Encoding} (p : Perm) (small : 2*l<2^256)
    (q : PublicSpec.Domain) (s : State) (known : Nat) (valid : Valid l enc s known)
    (r : PublicSpec.Range q × State) (member : r∈support ((handler l enc p (.inr q)).run s)) :
    Valid l enc r.2 (known+1) := by
  classical
  rcases q with x|x|x
  · simp only [handler,graphHandler,StateT.run] at member
    split at member
    · rename_i seen
      simp only [pure_bind,support_pure,Set.mem_singleton_iff] at member;subst r
      exact repeat_valid valid (skip_seen l enc s x seen)
    · rename_i missing
      simp only [bind_assoc,pure_bind,mem_support_bind_iff] at member
      obtain ⟨out,_,e⟩:=member
      rw [support_pure,Set.mem_singleton_iff] at e;subst r
      exact append_valid out missing small valid
  · simp only [handler,graphHandler,StateT.run,pure_bind,support_pure,Set.mem_singleton_iff] at member;subst r
    exact repeat_valid valid (skip_perm l enc s _)
  · simp only [handler,graphHandler,StateT.run,pure_bind,support_pure,Set.mem_singleton_iff] at member;subst r
    exact repeat_valid valid (skip_perm l enc s _)

private theorem skip_safe {l : Nat} {enc} {s : State} {q} {known}
    (v : Valid l enc s known) (safe : ¬s.won) : ¬(finish l enc s q s.trace).won := by
  rintro (win|⟨room,good,hit⟩)
  · exact safe win
  · exact (v.track room.le good safe).2 hit

theorem hazard_bound {l : Nat} {enc : Encoding} (p : Perm) (small : 2*l<2^256)
    (q : PublicSpec.Domain) (s : State) (known : Nat) (v : Valid l enc s known) (safe : ¬s.won) :
    Pr{let r←(handler l enc p (.inr q)).run s}[r.2.won] ≤ Weighted.hazard width s.counts (kind l enc s q) := by
  classical
  rcases q with x|x|x
  · by_cases seen : ∃ j, s.trace.input j=x
    · simp [handler,graphHandler,seen,skip_safe v safe,StateT.run]
    · simp only [handler,graphHandler,dif_neg seen,StateT.run,bind_assoc,pure_bind,bind_pure_comp,prEvent_map]
      by_cases live : Live l enc s
      · exact append_loss seen live small v
      · have none (reply : Output) : ¬(finish l enc s (.inl x) (s.trace.insert x reply seen)).won := by
          rintro (won|⟨room,good,_⟩)
          · exact safe won
          · exact live ⟨room,good_of_append _ _ _ _ _ good,safe⟩
        simp [none]
  · change Pr{let r←(pure (p x,finish l enc s (.inr (.inl x)) s.trace) : ProbComp _)}[r.2.won]≤_
    rw [prEvent_pure,if_neg (skip_safe v safe)];exact zero_le
  · change Pr{let r←(pure (p.symm x,finish l enc s (.inr (.inr x)) s.trace) : ProbComp _)}[r.2.won]≤_
    rw [prEvent_pure,if_neg (skip_safe v safe)];exact zero_le

end CommitGolfCandidate.Chained.Fixed
