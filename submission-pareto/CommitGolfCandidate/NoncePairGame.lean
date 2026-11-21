import CommitGolfCandidate.NoncePairReplay
import CommitGolfCandidate.NonceChainGame

/-! A deterministic, time-dependent input transform between permutation replies.
Freshness is bounded separately for its input and output encodings. The public
strategy knows every disclosed prefix and may query in either direction. -/
namespace CommitGolfCandidate.Permutation.NoncePair
open NonceChain Finset
set_option linter.unusedSectionVars false
variable {S K D : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] {n : Nat}

def orbit (π : Equiv.Perm S) (step : Nat → S → S) (x : S) : Nat → S
  | 0 => x
  | j+1 => π (step j (orbit π step x j))

def inputs (step : Nat → S → S) (v : Fin (n+1) → S) : Fin (n+1) → S :=
  fun i => step i.val (v i)

theorem follows_iff (π : Equiv.Perm S) (step : Nat → S → S)
    (start : K → S) (k : K) (z : Fin n → S) :
    follows π (inputs step (vertices start k z)) (vertices start k z) ↔
      z = fun i => orbit π step (start k) (i.val+1) := by
  constructor
  · intro h
    have all (j : Fin (n+1)) : vertices start k z j = orbit π step (start k) j.val := by
      induction j using Fin.induction with
      | zero => rfl
      | succ i ih => exact (h i).symm.trans (congrArg (fun x => π (step i.val x)) ih)
    funext i
    exact all i.succ
  · rintro rfl i
    have one (j : Fin (n+1)) :
        vertices start k (fun i : Fin n => orbit π step (start k) (i.val+1)) j =
          orbit π step (start k) j.val := Fin.cases rfl (fun _ => rfl) j
    change π (step i.val (vertices start k _ i.castSucc)) = vertices start k _ i.succ
    rw [one,one]
    rfl

private theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    mean (fun a => mean (f a)) = mean (fun b => mean (fun a => f a b)) := by
  rw [← mean_prod, ← mean_prod]
  exact mean_equiv (Equiv.prodComm A B) (fun p : B × A => f p.2 p.1)

private theorem exp_mean {A : Type} [Fintype A] {T : Type}
    (g : Strat S T) (s : PState S) (f : A → T → PState S → ℝ) :
    mean (fun a => g.exp s (f a)) = g.exp s (fun b st => mean (fun a => f a b st)) := by
  unfold mean avg
  simp_rw [div_eq_inv_mul, ← Strat.exp_sum, ← Strat.exp_mul_left]

/-- Two applications of the existing hidden-key union bound. The initial
output and final input are harmless extra endpoints, keeping the same key index. -/
private theorem bad_expectation (g : Strat S Bool) {q : Nat} (bounded : g.QB q)
    (input output : Fin (n+1) → K → S)
    (inputInj : ∀ i, Function.Injective (input i))
    (outputInj : ∀ i, Function.Injective (output i)) :
    mean (fun h : Fin (n+1) → K => g.exp PState.init (fun _ st =>
      ind (Bad (fun i => input i (h i)) (fun i => output i (h i)) st.trace))) ≤
      2 * ((n+1 : Nat) : ℝ) * ((q+(n+1) : ℝ) / Fintype.card K) := by
  rw [exp_mean]
  have post := Strat.post_and (g.post_inv PState.init Trace.WF.nil)
    (Strat.post_QB bounded PState.init)
  rw [← g.exp_const (2 * ((n+1 : Nat) : ℝ) * ((q+(n+1) : ℝ) / Fintype.card K))
    PState.init Trace.WF.nil]
  apply Strat.exp_le_exp_of_post post
  intro b st h
  have len : st.trace.length ≤ q := by simpa [PState.init] using h.2.1
  have sizeIn : st.trace.usedIn.card ≤ q := by rw [h.1.1.card_usedIn]; exact len
  have sizeOut : st.trace.usedOut.card ≤ q := by rw [h.1.1.card_usedOut]; exact len
  have one (f : Fin (n+1) → K → S) (inj : ∀ i, Function.Injective (f i))
      (seen : Finset S) (size : seen.card ≤ q) :
      mean (fun h : Fin (n+1) → K => ind (Exposed (fun i => f i (h i)) seen)) ≤
        ((n+1 : Nat) : ℝ) * ((q+(n+1) : ℝ) / Fintype.card K) := by
    have delta := exposed_bound f inj seen
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at delta ⊢
    refine delta.trans ?_
    gcongr
  have union (h : Fin (n+1) → K) :
      ind (Bad (fun i => input i (h i)) (fun i => output i (h i)) st.trace) ≤
        ind (Exposed (fun i => input i (h i)) st.trace.usedIn) +
        ind (Exposed (fun i => output i (h i)) st.trace.usedOut) := by
    by_cases left : Exposed (fun i => input i (h i)) st.trace.usedIn
    · rw [ind_pos left]
      exact (ind_le_one _).trans (le_add_of_nonneg_right (ind_nonneg _))
    · by_cases right : Exposed (fun i => output i (h i)) st.trace.usedOut
      · rw [ind_pos right]
        exact (ind_le_one _).trans (le_add_of_nonneg_left (ind_nonneg _))
      · rw [ind_neg (show ¬Bad (fun i => input i (h i))
            (fun i => output i (h i)) st.trace from fun h => h.elim left right),
          ind_neg left,ind_neg right]
        norm_num
  refine (avg_mono (fun h _ => union h)).trans ?_
  rw [avg_add]
  have a := one input inputInj _ sizeIn
  have b := one output outputInj _ sizeOut
  nlinarith

noncomputable def realProb (split : S ≃ D × K) (start : K → S)
    (step : Nat → S → S) (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun π : Equiv.Perm S => mean fun k : K =>
    (g (fun i => (split (orbit π step (start k) (i.val+1))).1)).eager π PState.init
      (fun b _ => accept b)

noncomputable def idealProb (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun p => (g p).exp PState.init (fun b _ => accept b)

/-- Every permutation and initial key has exactly one output tape, whether
or not the proposed edge list is fresh. This identity does not assume freshness. -/
theorem sum_weight (split : S ≃ D × K) (start : K → S) (step : Nat → S → S)
    (g : (Fin n → D) → Strat S Bool) :
    (Fintype.card S : ℝ)^n * mean (fun p : Fin n → D => mean (fun h : Fin (n+1) → K =>
      weight (g p) (inputs step (fun i => encodeAt split start p i (h i)))
        (fun i => encodeAt split start p i (h i)))) = realProb split start step g := by
  classical
  let F := fun (k : K) (z : Fin n → S) =>
    weight (g (fun i => (split (z i)).1)) (inputs step (vertices start k z)) (vertices start k z)
  have reorder : mean (fun p : Fin n → D => mean (fun h : Fin (n+1) → K =>
        weight (g p) (inputs step (fun i => encodeAt split start p i (h i)))
          (fun i => encodeAt split start p i (h i)))) =
        mean (fun k => mean (F k)) := by
    rw [← mean_prod, ← mean_prod, ← mean_equiv (partition split n) (fun a => F a.1 a.2)]
    apply avg_congr
    rintro ⟨p,h⟩ _
    unfold F
    rw [partition_vertices]
    simp [partition]
  rw [reorder]
  unfold F weight
  simp_rw [follows_iff]
  rw [← avg_mul_left]
  apply Eq.trans _ (mean_swap _)
  apply avg_congr
  intro k _
  rw [mean_swap, ← avg_mul_left]
  apply avg_congr
  intro π _
  unfold mean avg
  simp only [Finset.card_univ,Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [Finset.sum_ite_eq' univ]
  simp [field]

/-- Publicly adaptive event comparison for a transformed permutation path. -/
theorem ideal_le_real (split : S ≃ D × K) (start : K → S)
    (step : Nat → S → S) (startInj : Function.Injective start)
    (inputInj : ∀ (p : Fin n → D) (i : Fin (n+1)),
      Function.Injective (fun k => step i.val (encodeAt split start p i k)))
    (g : (Fin n → D) → Strat S Bool) (q : Nat) (hq : ∀ p, (g p).QB q) :
    idealProb g ≤ realProb split start step g +
      2 * ((n+1 : Nat) : ℝ) * ((q+(n+1) : ℝ) / Fintype.card K) := by
  rw [← sum_weight]
  let err := 2 * ((n+1 : Nat) : ℝ) * ((q+(n+1) : ℝ) / Fintype.card K)
  change mean _ ≤ _ + err
  rw [← avg_mul_left, ← avg_const (Finset.univ_nonempty (α := Fin n → D)) err, ← avg_add]
  apply avg_mono
  intro p _
  let f := encodeAt split start p
  have each (h : Fin (n+1) → K) := path_comparison (g p)
    (inputs step (fun i => f i (h i))) (fun i => f i (h i))
  have avgStep := avg_mono (A := univ) (fun h _ => each h)
  rw [avg_const Finset.univ_nonempty, avg_add, avg_mul_left] at avgStep
  exact avgStep.trans (add_le_add_right (bad_expectation (g p) (hq p)
    (fun i k => step i.val (f i k)) f (inputInj p)
    (encodeAt_injective split start startInj p)) _)

end CommitGolfCandidate.Permutation.NoncePair
