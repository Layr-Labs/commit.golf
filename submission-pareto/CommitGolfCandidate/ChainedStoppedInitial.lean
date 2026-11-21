import CommitGolfCandidate.ChainedStoppedModel

/-! Empty-state initialization includes one dummy leaf factor of value one. -/
namespace CommitGolfCandidate.Chained.Stopped
open CommitGolf OracleComp OracleSpec

def initialCounts : Counters.Index → Nat
  | none => 1
  | some _ => 0

def empty : State := ⟨Observer.State.empty,initialCounts,False⟩

theorem completed_empty (enc : Encoding) (calls : Height → Nat) (id : Height × Seed) :
    ¬ Completed enc calls emptyTrace id := by
  rintro ⟨evaluation,_⟩
  exact Fin.elim0 (evaluation.row 0)

theorem count_empty (enc : Encoding) (calls : Height → Nat) (h : Height) :
    completedCount enc calls emptyTrace h = 0 := by
  have noSeeds : completedSeeds enc calls emptyTrace h = ∅ := by
    ext seed
    exact iff_false_intro (completed_empty enc calls (h,seed))
  simp only [completedCount,noSeeds,Set.ncard_empty]

theorem core_empty (limit : Nat) (enc : Encoding) (calls width : Height → Nat) :
    Core limit enc calls width empty := by
  refine ⟨Observer.valid_empty,by decide,by decide,?_,?_⟩
  · simp [empty,Counters.work_split,initialCounts,Observer.State.empty,JointOracle238.State.empty]
  · intro within good safe
    refine ⟨?_,by decide,?_,?_⟩
    · intro h
      exact (count_empty enc calls h).symm
    · exact (TwoPermutationPrototype.Sampling.s3PinCallW 238).badSpec.good_nil
    · rintro ⟨h,a,b,_,completed,_⟩
      exact completed_empty enc calls (h,a) completed

theorem empty_potential (width : Height → Nat) :
    Weighted.potential (Counters.widths width) empty.counts = 1 := by
  simp [Weighted.potential,Fintype.prod_option,empty,initialCounts,survival]

theorem from_empty {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    (rateBound : ∀ k, Counters.rate calls k ≤ 8)
    (dense : ∀ k, 2^238 ≤ (Counters.rate calls k)^2*2^(Counters.widths width k))
    (finite : 8*(limit+1) < 2^238) {α : Type} (program : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound program budget) (room : budget ≤ limit) :
    Pr{let result ← (model limit enc calls width small widthBound).run program empty}[result.2.won] ≤
      1-ENNReal.ofReal (Real.exp (-((limit+1 : Nat) : ℝ)^2/(2*(2^238-8*((limit+1 : Nat) : ℝ))))) := by
  simpa only [empty_potential,div_one] using
    adaptive_bound small widthBound rateBound dense finite program budget 0 bounded
      (by simpa only [Nat.zero_add] using room) empty (core_empty limit enc calls width)
      (by decide) (by intro won; exact won)

end CommitGolfCandidate.Chained.Stopped
