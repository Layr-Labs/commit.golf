import CommitGolfCandidate.LateHidingRun

/-! The commit loop's coins are one uniform salt tape.

`Late.sampleSalts` issues `LENGTH / 2` separate 384-bit draws, one per pair, and
reads the even leaf's salt from the low half and the odd leaf's salt from the
high half. Under any fixed oracle, and before any continuation, this is exactly
one uniform draw of the whole per-leaf salt tape: the draws are independent, and
splitting each pair word is a bijection between pair words and salt tapes.
The argument follows the same route as `LateCoins.sample_salts_uniform` in the
machine tree (independent draws as a uniform function, then a bijection); it is
proved here again so that the hiding theorem depends only on `LateModel`. -/
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

/-- The pair word holding the two salts of one pair: odd leaf high, even leaf low. -/
def packTape (salt : Late.SaltTape) (pair : PairIndex) : Late.PairCoins :=
  salt ⟨2 * pair.val + 1, by
    have inside := pair.isLt
    have even := length_even
    omega⟩ ++
  salt ⟨2 * pair.val, by
    have inside := pair.isLt
    have even := length_even
    omega⟩

theorem unpack_pack (salt : Late.SaltTape) : unpackTape (packTape salt) = salt := by
  funext index
  unfold unpackTape packTape Late.pairSalts
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  split
  · rw [BitVec.extractLsb'_append_eq_left]
    congr 1
    apply Fin.ext
    simp_all
    omega
  · rw [BitVec.extractLsb'_append_eq_right]
    congr 1
    apply Fin.ext
    simp_all
    omega

theorem pack_unpack (words : PairIndex → Late.PairCoins) : packTape (unpackTape words) = words := by
  funext pair
  unfold packTape unpackTape Late.pairSalts
  have odd : (2 * pair.val + 1).testBit 0 = true := by
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
    simp
  have even : (2 * pair.val).testBit 0 = false := by
    simp [Nat.testBit_eq_decide_div_mod_eq]
  simp only [odd, even, Bool.false_eq_true, ite_false, ite_true]
  have high : (2 * pair.val + 1) / 2 = pair.val := by omega
  have low : 2 * pair.val / 2 = pair.val := by omega
  simp only [high, low, Fin.eta]
  exact BitVec.extractLsb'_append_extractLsb'

/-- Splitting uniform pair words gives a uniform salt tape. -/
theorem unpack_uniform {α : Type} (next : Late.SaltTape → ProbComp α) :
    𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words => next (unpackTape words)] =
      𝒟[($ᵗ Late.SaltTape) >>= next] := by
  rw [← bind_map_left]
  exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (f := unpackTape) ⟨Function.LeftInverse.injective pack_unpack,
      Function.RightInverse.surjective unpack_pack⟩).bind_left next).evalDist_eq

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
exactly one uniform draw of the complete per-leaf salt tape. -/
theorem sample_salts_run (oracle : Oracle) {α : Type}
    (next : Late.SaltTape → OracleComp World α) :
    𝒟[fixedOracleRun oracle (Late.sampleSalts >>= next)] =
      𝒟[($ᵗ Late.SaltTape) >>= fun salt => fixedOracleRun oracle (next salt)] := by
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
  exact unpack_uniform (fun salt => fixedOracleRun oracle (next salt))

/-- The same statement when the continuation needs no oracle. -/
theorem sample_salts_bind (oracle : Oracle) {α : Type} (next : Late.SaltTape → ProbComp α) :
    𝒟[fixedOracleRun oracle Late.sampleSalts >>= next] = 𝒟[($ᵗ Late.SaltTape) >>= next] := by
  have lifted := sample_salts_run oracle (fun salt => (liftM (next salt) : OracleComp World α))
  simpa only [run_bind, run_coins] using lifted

/-- The commit loop's coins, in the instance-free form: equal in distribution to
one uniform salt tape under every fixed oracle. -/
theorem sample_salts_uniform (oracle : Oracle) :
    fixedOracleRun oracle Late.sampleSalts =ᵈ ($ᵗ Late.SaltTape : ProbComp Late.SaltTape) := by
  have plain := sample_salts_bind oracle (fun salt => (pure salt : ProbComp Late.SaltTape))
  simp only [bind_pure] at plain
  exact EvalDistEq.of_evalDist_eq plain

end CommitGolfCandidate.LateHiding
