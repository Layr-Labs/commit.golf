import CommitGolfCandidate.LateHidingRun

/-! The commit loop's coins are independent uniform pair words.

`Late.sampleSalts` issues `LENGTH / 2` separate 320-bit draws, one per pair, and
reads the even leaf's salt from bits 0 to 192 and the odd leaf's salt from bits
128 to 320. The two salts of a pair share 64 bits, so the salt tape is not
uniform. Under any fixed oracle, and before any continuation, the draws are
exactly one uniform function from pairs to words, read by `unpackTape`.
The first half follows `LateCoins.sample_salts_uniform` in the machine tree
(independent draws as a uniform function). The bijection with salt tapes that
the 48-byte draw had does not exist here and is gone. -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance saltsDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec

/-- Independent uniform draws along a list are one uniform function on its positions. -/
theorem iid_draws {W α : Type} [SampleableType W] (items : List Nat)
    (next : List W → ProbComp α) :
    𝒟[items.mapM (fun _ => ($ᵗ W : ProbComp W)) >>= next] =
      𝒟[($ᵗ (Fin items.length → W)) >>= fun words => next (List.ofFn words)] := by
  induction items generalizing next with
  | nil =>
    simp only [List.mapM_nil, pure_bind, List.length_nil, List.ofFn_zero]
    exact (OracleComp.evalDist_bind_const _ _).symm
  | cons item rest ih =>
    let split := Fin.consEquiv (fun _ : Fin (rest.length+1) => W)
    have uniform := ((SampleableType.map_uniformSample_evalDistEq_of_bijective
      split.bijective).bind_left (fun words => next (List.ofFn words))).evalDist_eq
    rw [List.length_cons, ← uniform, bind_map_left, SampleableType.uniformSample_prod_eq_bind]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    apply _root_.evalDist_bind_congr
    intro word
    rw [ih (fun words => next (word :: words))]
    congr 1
    apply bind_congr
    intro words
    change next (word :: List.ofFn words) = next (List.ofFn (Fin.cons word words))
    simp [List.ofFn_succ]

abbrev PairIndex := Fin (LENGTH / 2)

private theorem length_even : LENGTH = 2 * (LENGTH / 2) := by decide

/-- Read a salt tape from the pair words, as the commit loop lays them out. -/
def unpackTape (words : PairIndex → Late.PairCoins) (index : Index) : Late.Salt :=
  Late.pairSalts (words ⟨index.val / 2, by
    have inside := index.isLt
    have even := length_even
    omega⟩) (index.val.testBit 0)

/-- The coin requests issued one pair at a time add no public calls and are
ordinary private draws under a fixed oracle. -/
theorem run_draws (oracle : Oracle) {α : Type} (items : List Nat)
    (next : List Late.PairCoins → OracleComp World α) :
    fixedOracleRun oracle (items.mapM (fun _ => Late.drawPair) >>= next) =
      (items.mapM (fun _ => ($ᵗ Late.PairCoins : ProbComp Late.PairCoins)) >>= fun words =>
        fixedOracleRun oracle (next words)) := by
  induction items generalizing next with
  | nil => simp only [List.mapM_nil, pure_bind]
  | cons item rest ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    unfold Late.drawPair
    rw [run_coins_bind]
    apply bind_congr
    intro word
    exact ih _

private theorem draws_uniform {α : Type} (count : Nat) (items : List Nat)
    (size : items.length = count) (next : List Late.PairCoins → ProbComp α) :
    𝒟[items.mapM (fun _ => ($ᵗ Late.PairCoins : ProbComp Late.PairCoins)) >>= next] =
      𝒟[($ᵗ (Fin count → Late.PairCoins)) >>= fun words => next (List.ofFn words)] := by
  subst count
  exact iid_draws items next

attribute [local irreducible] List.range

/-- **RANDOM inside the commit loop.** Under any fixed oracle and before any
continuation, the `LENGTH / 2` per-pair draws of the abstract commitment are
exactly one uniform function from pairs to 320-bit words, read as a salt tape
by `unpackTape`. -/
theorem sample_salts_run (oracle : Oracle) {α : Type}
    (next : Late.SaltTape → OracleComp World α) :
    𝒟[fixedOracleRun oracle (Late.sampleSalts >>= next)] =
      𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        fixedOracleRun oracle (next (unpackTape words))] := by
  unfold Late.sampleSalts
  simp only [bind_assoc, pure_bind]
  rw [run_draws]
  refine (draws_uniform (LENGTH / 2) _ List.length_range _).trans ?_
  have slice (words : PairIndex → Late.PairCoins) :
      (fun index : Index =>
        Late.pairSalts ((List.ofFn words)[index.val / 2]?.getD 0) (index.val.testBit 0)) =
        unpackTape words := by
    funext index
    have bound : index.val / 2 < LENGTH / 2 := by
      have inside := index.isLt
      have even := length_even
      omega
    simp only [unpackTape, List.getElem?_ofFn, dite_eq_left bound, Option.getD_some]
  simp only [slice]

/-- The same statement when the continuation needs no oracle. -/
theorem sample_salts_bind (oracle : Oracle) {α : Type} (next : Late.SaltTape → ProbComp α) :
    𝒟[fixedOracleRun oracle Late.sampleSalts >>= next] =
      𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words => next (unpackTape words)] := by
  have lifted := sample_salts_run oracle (fun salt => (liftM (next salt) : OracleComp World α))
  simpa only [run_bind, run_coins] using lifted

/-- The commit loop's coins, in the instance-free form: equal in distribution to
uniform pair words read as a salt tape, under every fixed oracle. -/
theorem sample_salts_words (oracle : Oracle) :
    fixedOracleRun oracle Late.sampleSalts =ᵈ
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        (pure (unpackTape words) : ProbComp Late.SaltTape)) := by
  have plain := sample_salts_bind oracle (fun salt => (pure salt : ProbComp Late.SaltTape))
  simp only [bind_pure] at plain
  exact EvalDistEq.of_evalDist_eq plain

end CommitGolfCandidate.LateHiding
