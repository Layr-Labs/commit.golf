import CommitGolfCandidate.ChainedCompletionWork
import CommitGolfCandidate.ChainedFinalHazard
import CommitGolfCandidate.ChainedGraphSampler
import CommitGolfCandidate.WeightedAdaptiveSurvival
namespace CommitGolfCandidate.Chained.Fixed
open CommitGolf OracleComp OracleSpec
open scoped BigOperators

structure State where
  trace : Trace
  counts : Height → Nat
  won : Prop

def Live (limit : Nat) (enc : Encoding) (s : State) : Prop :=
  s.trace.size<limit ∧ Good enc s.trace ∧ ¬s.won

noncomputable def kind (limit : Nat) (enc : Encoding) (s : State) (q : PublicSpec.Domain) : Option Height := by
  classical
  exact if Live limit enc s then match q with
    | .inl x => if seen : ∃ j, s.trace.input j=x then none
                else (prediction enc calls s.trace x (fun j e=>seen ⟨j,e⟩)).map Prod.fst
    | .inr _ => none
  else none

noncomputable def finish (limit : Nat) (enc : Encoding) (s : State) (q : PublicSpec.Domain) (t : Trace) : State :=
  ⟨t,Weighted.advance s.counts (kind limit enc s q),
   s.won ∨ (s.trace.size<limit ∧ Good enc t ∧ FinalCollision enc calls width t)⟩

structure Valid (limit : Nat) (enc : Encoding) (s : State) (known : Nat) : Prop where
  available : s.trace.size≤known
  work : Weighted.work calls s.counts≤limit
  track : s.trace.size≤limit → Good enc s.trace → ¬s.won →
      s.counts=completedCount enc calls s.trace ∧ ¬FinalCollision enc calls width s.trace

theorem advance_bump (c : Height → Nat) (opt : Option (Height × Seed)) (j : Height) :
    Weighted.advance c (opt.map Prod.fst) j=c j+bump opt j := by
  rcases opt with _|⟨h,v⟩
  · simp [Weighted.advance,bump]
  · by_cases e : j=h
    · subst j;simp [Weighted.advance,bump]
    · simp [Weighted.advance,bump,e,Ne.symm e]

theorem forecast {limit : Nat} {enc : Encoding} {s : State} {known : Nat}
    (small : 2*limit<2^256) (v : Valid limit enc s known) (q : PublicSpec.Domain) :
    Weighted.work calls (Weighted.advance s.counts (kind limit enc s q))≤limit := by
  classical
  by_cases live : Live limit enc s
  · rcases q with x|p
    · by_cases seen : ∃ j, s.trace.input j=x
      · simpa [kind,live,seen,Weighted.advance] using v.work
      · let fresh := fun j (e : s.trace.input j=x) => seen ⟨j,e⟩
        have exactCounts := (v.track live.1.le live.2.1 live.2.2).1
        have size := live.1
        have bound := predicted_work (calls:=calls) (input:=x) (fresh:=fresh) live.2.1 (by omega)
        simp only [kind,if_pos live,dif_neg seen,Weighted.work,advance_bump,exactCounts]
        exact bound.trans (by omega)
    · simpa [kind,live,Weighted.advance] using v.work
  · simpa [kind,live,Weighted.advance] using v.work
end CommitGolfCandidate.Chained.Fixed
