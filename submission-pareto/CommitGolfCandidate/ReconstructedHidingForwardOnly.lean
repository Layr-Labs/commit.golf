import CommitGolfCandidate.ReconstructedHidingMarkedCache
import CommitGolfCandidate.NonceChainView

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp CommitGolfCandidate.Permutation HidingTape TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.NonceChain (mean)
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048

def ForwardOnly {S A : Type} : Strat S A → Prop
  | .done _ => True
  | .fwd _ k => ∀ a, ForwardOnly (k a)
  | .inv _ _ => False
  | .rand _ k => ∀ a, ForwardOnly (k a)

theorem only_bind {S A B : Type} (g : Strat S A) (k : A → Strat S B)
    (first : ForwardOnly g) (next : ∀ a, ForwardOnly (k a)) : ForwardOnly (g.bind k) := by
  induction g with
  | done a => exact next a
  | fwd x f ih => exact fun y => ih y (first y)
  | inv y f ih => exact first.elim
  | rand m f ih => exact fun v => ih v (first v)

theorem only_query_list {I A : Type} (c : Compression) (f : I → OracleComp World A) (xs : List I)
    (each : ∀ x, ForwardOnly (toStrat c (f x))) : ForwardOnly (toStrat c (queryList f xs)) := by
  induction xs with
  | nil => trivial
  | cons x rest ih =>
    rw [queryList,to_strat_bind]
    apply only_bind _ _ (each x)
    intro a
    rw [to_strat_bind]
    exact only_bind _ _ ih (fun _ => trivial)

attribute [local irreducible] queryList List.finRange toStrat

theorem only_digests (c : Compression) (m : Message) (r : CompleteSaltTape) :
    ForwardOnly (toStrat c (queryDigests m r)) := by
  rw [queryDigests,to_strat_bind]
  refine only_bind _ _ ?_ ?_
  · apply only_query_list
    intro i
    unfold querySaltedDigest
    unfold toStrat
    exact fun _ _ => True.intro
  · intro ds; rw [to_strat_pure]; trivial

private theorem mean_unit (f : Unit → ℝ) : mean f = f () := by
  have h : f = fun _ => f () := funext (fun x => by cases x; rfl)
  conv_lhs => rw [h]
  exact avg_const Finset.univ_nonempty _

/-- A computation that makes only forward permutation queries can discover a
fixed protected output only when sampling a new answer. All outputs of the
initial cache are already known to avoid the protected set. -/
theorem forward_output_bound {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (base : Trace S) (well : base.WF) (ys : Finset S) (u Q : Nat) (size : ys.card≤u)
    (cleanBase : ∀ x y, containsPair base x y → y∉ys) (room : Q < Fintype.card S)
    (g : Strat S A) (n : Nat) (limited : g.QB n) (only : ForwardOnly g) (fit : base.length+n≤Q) :
    hitProb (fun _ : Unit => ∅) (fun _ => ys) () g base ≤ (n:ℝ)*(u/((Fintype.card S:ℝ)-Q)) := by
  let ins := fun _ : Unit => (∅ : Finset S)
  let outs := fun _ : Unit => ys
  let D := (Fintype.card S:ℝ)-Q
  have pos : 0<D := sub_pos.mpr (by exact_mod_cast room)
  have nn : 0≤(u:ℝ)/D := div_nonneg (Nat.cast_nonneg _) pos.le
  have aux (m : Nat) (st : Strat S A) (qb : st.QB m) (forward : ForwardOnly st)
      (t : Trace S) (valid : t.WF) (capacity : t.length+m≤Q) :
      tally base ins outs () st t ≤ (m:ℝ)*(u/D) := by
    induction qb generalizing t with
    | done a m => exact mul_nonneg (Nat.cast_nonneg _) nn
    | rand a k m _ ih =>
      apply avg_le (mul_nonneg (Nat.cast_nonneg _) nn)
      exact fun i _ => ih i (forward i) t valid capacity
    | inv y k m hh ih => exact forward.elim
    | fwd x k m _ ih =>
      have many : D ≤ t.freeOut.card := by
        rw [valid.card_freeOut,Nat.cast_sub valid.length_le]
        have hw : (t.length:ℝ)≤Q := by exact_mod_cast (by omega : t.length≤Q)
        dsimp only [D]; linarith
      have pay := forward_payment base t ins outs x u D 0 pos le_rfl many
        (by rw [mean_unit]; exact (ind_neg (Finset.notMem_empty x)).le) (fun _ => size)
        (fun y known => by
          rw [mean_unit]
          exact (ind_neg (fun h => h.elim (Finset.notMem_empty x) (cleanBase x y known))).le)
      rw [mean_unit,zero_add] at pay
      change avg (t.fwdAns x) (fun y => _+_) ≤ _
      rw [avg_add]
      apply (add_le_add pay (avg_le (mul_nonneg (Nat.cast_nonneg _) nn) (fun y allowed =>
        ih y (forward y) (t.stepF x y) (valid.stepF allowed) (by have := Trace.length_stepF_le t x y; omega)))).trans_eq
      push_cast; ring
  exact (hit_le_tally base ins outs () g base (fun e old absent => (absent ⟨e,old,rfl,rfl⟩).elim)).trans
    (aux n g limited only base well fit)

end CommitGolfCandidate.Reconstruction.HidingTraffic
