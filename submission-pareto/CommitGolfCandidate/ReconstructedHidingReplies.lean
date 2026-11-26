import CommitGolfCandidate.ReconstructedHidingTrace
import CommitGolfCandidate.S3PermBadEvent

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolfCandidate.Permutation
set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

/-- A forward query has a random output, while an inverse query has a random
input. Only the randomly selected side of the new row is counted here. -/
def sampledHits {S : Type} [DecidableEq S] (inputs outputs : Finset S) (e : Entry S) : Prop :=
  match e.dir with
  | .fwd => e.out ∈ outputs
  | .inv => e.inp ∈ inputs

private def sampledSpec {S : Type} [DecidableEq S] (inputs outputs : Finset S) : BadSpec S :=
  ⟨fun _ _ => False, sampledHits inputs outputs⟩

theorem random_replies_le {S A : Type} [Fintype S] [DecidableEq S]
    (inputs outputs : Finset S) (u q : Nat) (hin : inputs.card ≤ u)
    (hout : outputs.card ≤ u) (room : q < Fintype.card S) (strategy : Strat S A)
    (bounded : strategy.QB q) :
    strategy.prob PState.init (fun _ st => ∃ e ∈ st.trace, sampledHits inputs outputs e)
      ≤ (q:ℝ)*u/((Fintype.card S:ℝ)-q) := by
  classical
  let B := sampledSpec inputs outputs
  have small := prob_not_good_le B 0 u q room
    (fun _ _ => ⟨∅,by simp,fun _ h => h.elim⟩)
    (fun _ => ⟨outputs,hout,fun _ h => h⟩)
    (fun _ _ => ⟨∅,by simp,fun _ h => h.elim⟩)
    (fun _ => ⟨inputs,hin,fun _ h => h⟩) strategy
  have step : strategy.prob PState.init (fun _ st => ∃ e ∈ st.trace, sampledHits inputs outputs e)
      ≤ strategy.prob PState.init (fun _ st => ¬ B.Good st.trace ∧ st.count ≤ q) := by
    unfold Strat.prob
    apply Strat.exp_le_exp_of_post (Strat.post_QB bounded PState.init)
    rintro _ st ⟨_,count⟩
    apply ind_mono
    rintro ⟨e,appears,marked⟩
    exact ⟨fun good => good.not_single appears marked,by simpa only [PState.init,Nat.zero_add] using count⟩
  exact step.trans (by simpa only [Nat.cast_zero,mul_zero,zero_add] using small)

theorem random_replies_1600 {A : Type} (inputs outputs : Finset Reply) (u q : Nat)
    (hin : inputs.card ≤ u) (hout : outputs.card ≤ u) (room : q ≤ 2^121)
    (strategy : Strat Reply A) (bounded : strategy.QB q) :
    strategy.prob PState.init (fun _ st => ∃ e ∈ st.trace, sampledHits inputs outputs e)
      ≤ (q:ℝ)*u/2^1599 := by
  have card : Fintype.card Reply = 2^1600 := by
    rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
  have plenty : q < Fintype.card Reply := by rw [card]; omega
  have bound := random_replies_le inputs outputs u q hin hout plenty strategy bounded
  rw [card,Nat.cast_pow,Nat.cast_ofNat] at bound
  refine bound.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
  have limit : (q:ℝ) ≤ 2^121 := by exact_mod_cast room
  linarith


/-- Conditioning on public rows leaves uniform random responses for fresh
requests. Initial rows can be arbitrary, including rows that hit the protected
sets. Only newly created rows are counted. -/
theorem random_replies_after {S A : Type} [Fintype S] [DecidableEq S]
    (start : PState S) (well : start.trace.WF) (counted : start.trace.length ≤ start.count)
    (inputs outputs : Finset S) (u q : Nat) (hin : inputs.card ≤ u) (hout : outputs.card ≤ u)
    (room : start.count+q < Fintype.card S) (strategy : Strat S A) (bounded : strategy.QB q) :
    strategy.prob start (fun _ st => ∃ e ∈ st.trace, e ∉ start.trace ∧ sampledHits inputs outputs e)
      ≤ (q:ℝ)*u/((Fintype.card S:ℝ)-(start.count+q)) := by
  classical
  let B : BadSpec S := ⟨fun _ _ => False, fun e => e ∉ start.trace ∧ sampledHits inputs outputs e⟩
  have good : B.Good start.trace := by
    refine ⟨List.pairwise_of_forall (fun _ _ => fun h => h.elim),?_⟩
    intro e present hab
    exact hab.1 present
  have small := exp_not_good_le B 0 u (start.count+q) room
    (fun _ _ => ⟨∅,by simp,fun _ h => h.elim⟩)
    (fun _ => ⟨outputs,hout,fun _ h => h.2⟩)
    (fun _ _ => ⟨∅,by simp,fun _ h => h.elim⟩)
    (fun _ => ⟨inputs,hin,fun _ h => h.2⟩) strategy start well counted good
  have step : strategy.prob start (fun _ st => ∃ e ∈ st.trace, e ∉ start.trace ∧ sampledHits inputs outputs e)
      ≤ strategy.prob start (fun _ st => ¬ B.Good st.trace ∧ st.count ≤ start.count+q) := by
    unfold Strat.prob
    apply Strat.exp_le_exp_of_post (Strat.post_QB bounded start)
    rintro _ st ⟨_,count⟩
    apply ind_mono
    rintro ⟨e,appears,marked⟩
    exact ⟨fun h => h.not_single appears marked,count⟩
  refine step.trans (small.trans_eq ?_)
  simp [budget]

end CommitGolfCandidate.Reconstruction.HidingTape
