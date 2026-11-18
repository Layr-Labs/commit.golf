import CommitGolfCandidate.PairBindingEvenLayout
import CommitGolfCandidate.QuadReplay

/-!
# Pair-heads binding: the even-leaf event

* `even_witness_bad`: an `EvenLeafWitness` in the recorded rows makes the permutation trace bad for
  `evenPinCall` (deterministic extraction, the even analog of `pinned_witness_bad`).
* `fixed_compression_even_leaf_bound_small` (= `even_leaf_small_bound : EvenLeafSmallBound`): for every fixed
  compression function, over the uniform permutation, `Pr[EvenLeafWitness] ≤ q/2^124` (the even analog of
  `fixed_compression_pinned_leaf_bound_small`; the exact union bound is about `q/2^132`).
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100
set_option maxHeartbeats 1100000

private theorem even_trunc_digest (reply : Block) :
    evenPinCall.trunc reply = outputDigest reply := by
  change BitVec.ofNat 256 reply.toNat = reply.extractLsb' 0 256
  apply BitVec.eq_of_toNat_eq
  simp [outputDigest,BitVec.extractLsb',BitVec.toNat_setWidth]

private theorem even_stored_evaluation (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (perm : Block → Block) (i : Index)
    (salt : BitVec 128) (value : CommitGolf.Entry)
    (ha : let a := evenFirstRow perm (entryWords value); PublicRow.permutation a.1 a.2 ∈ rows)
    (hb : let a := evenFirstRow perm (entryWords value)
          let b := evenSecondRow perm i (saltWords salt) a.2 (entryWords value)
          PublicRow.permutation b.1 b.2 ∈ rows) :
    let a := evenFirstRow perm (entryWords value)
    let b := evenSecondRow perm i (saltWords salt) a.2 (entryWords value)
    evenPinCall.Evaluates t (evenInput i salt value) (outputDigest b.2) := by
  let a := evenFirstRow perm (entryWords value)
  let b := evenSecondRow perm i (saltWords salt) a.2 (entryWords value)
  obtain ⟨e,he,ein,eout⟩ := stored a.1 a.2 ha
  obtain ⟨f,hf,fin,fout⟩ := stored b.1 b.2 hb
  have first : e.inp = evenPinCall.enc1 (evenInput i salt value).1 :=
    ein.trans (even_first_eq i salt value)
  refine ⟨e,he,f,hf,first,?_,?_⟩
  · rw [eout,first]
    exact fin.trans (even_second_eq i value a.2 salt)
  · exact (congrArg evenPinCall.trunc fout).trans (even_trunc_digest b.2)

theorem even_witness_bad (t : Trace PermState) (rows : List PublicRow) (stored : PinnedRowsStored rows t)
    (hit : EvenLeafWitness rows) : ¬ evenPinCall.badSpec.Good t := by
  obtain ⟨perm,i,n,m,v,w,a₀,a₁,b₀,b₁,digest,conflict⟩ := hit
  obtain ⟨salt₀,hs₀⟩ := (split_blocks_bijective 64 2 (by decide)).2 n
  obtain ⟨salt₁,hs₁⟩ := (split_blocks_bijective 64 2 (by decide)).2 m
  obtain ⟨value₀,hv₀⟩ := (split_blocks_bijective 64 32 (by decide)).2 v
  obtain ⟨value₁,hv₁⟩ := (split_blocks_bijective 64 32 (by decide)).2 w
  change saltWords salt₀=n at hs₀
  change saltWords salt₁=m at hs₁
  change entryWords value₀=v at hv₀
  change entryWords value₁=w at hv₁
  subst n m v w
  have distinct : value₀ ≠ value₁ := fun h => conflict (congrArg entryWords h)
  have left := even_stored_evaluation t rows stored perm i salt₀ value₀ a₀ b₀
  have right := even_stored_evaluation t rows stored perm i salt₁ value₁ a₁ b₁
  refine evenPinCall.collision_imp_bad (even_input_ne i i salt₀ salt₁ distinct) left ?_
  exact digest.symm ▸ right

/-- The union bound at the even-leaf sizes (`k ≤ 2^1346`, `v ≤ 2^1281`) fits `q/2^124` with the paid replay. -/
theorem even_replay_margin (q calls k v : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (kBound : k ≤ 2^1346) (vBound : v ≤ 2^1281) :
    unionBound (2^1600) k v calls ≤ (q : ℝ)/2^124 := by
  have one : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have limit : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have replayLimit : (calls : ℝ) ≤ (q : ℝ) + 2^31 := by exact_mod_cast replayed
  have nonneg : (0 : ℝ) ≤ calls := by positivity
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have K : (k : ℝ) ≤ 2^1346 := by exact_mod_cast kBound
  have V : (v : ℝ) ≤ 2^1281 := by exact_mod_cast vBound
  have callUpper : (calls : ℝ) ≤ 2^121 := by
    linarith [show (2 : ℝ)^120 + 2^31 ≤ 2^121 by norm_num]
  have denom : (2 : ℝ)^1599 ≤ 2^1600 - (calls : ℝ) := by
    linarith [show (2 : ℝ)^1599 + 2^121 ≤ 2^1600 by norm_num]
  have denomPos : 0 < (2 : ℝ)^1600 - calls :=
    lt_of_lt_of_le (by positivity : 0 < (2 : ℝ)^1599) denom
  have squareBound : (calls : ℝ)^2 ≤ (q : ℝ)*2^122 := by
    let extra : ℝ := 2^31
    have leSum : (calls : ℝ) ≤ q + extra := replayLimit
    have sq := mul_nonneg (sub_nonneg.mpr leSum) (by positivity : 0 ≤ (q : ℝ) + extra + calls)
    have qsq := mul_le_mul_of_nonneg_right limit qNonneg
    have esq : 2*extra^2 ≤ 2^65 := by norm_num [extra]
    have nq := mul_le_mul_of_nonneg_right one (by positivity : (0 : ℝ) ≤ 2^65)
    have slack : (2 : ℝ)^121 + 2^65 ≤ 2^122 := by norm_num
    have pad := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith [sq_nonneg ((q : ℝ) - extra)]
  have linearBound : (calls : ℝ) ≤ (q : ℝ)*2^32 := by
    have scale := mul_le_mul_of_nonneg_right one (by positivity : (0 : ℝ) ≤ 2^31)
    have slack : (1 : ℝ)+2^31 ≤ 2^32 := by norm_num
    have envelope := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith
  have pair : ((calls : ℝ) * ((calls : ℝ)-1)/2) * (k : ℝ) ≤ (calls : ℝ)^2 * 2^1346 := by
    have factor : (calls : ℝ) * ((calls : ℝ)-1)/2 ≤ (calls : ℝ)^2 := by
      nlinarith [sq_nonneg (calls : ℝ)]
    exact (mul_le_mul_of_nonneg_right factor (by positivity : 0 ≤ (k : ℝ))).trans
      (mul_le_mul_of_nonneg_left K (by positivity))
  have tail : (calls : ℝ) * (v : ℝ) ≤ (calls : ℝ) * 2^1281 :=
    mul_le_mul_of_nonneg_left V nonneg
  have pairBound := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ 2^1346)
  have tailBound := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^1281)
  have lower := mul_le_mul_of_nonneg_left denom (by positivity : (0 : ℝ) ≤ (q : ℝ)/2^124)
  have unified : (2 : ℝ)^122*2^1346 + 2^32*2^1281 ≤ 2^1599/2^124 := by norm_num
  have scale := mul_le_mul_of_nonneg_left unified qNonneg
  simp only [unionBound, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_iff₀ denomPos).2
  nlinarith

private theorem even_replayed_event {α : Type} (compress : Compression) (program : OracleComp World α)
    (witness : List PublicRow → Prop) (bad : BadSpec PermState) (q calls : Nat)
    (bounded : PublicQueryBound (recordRows program) calls)
    (extract : ∀ trace rows, PinnedRowsStored rows trace → witness rows → ¬ bad.Good trace)
    (prob : (toStrat compress (recordRows program)).prob PState.init
      (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) ≤ (q : ℝ)/2^124) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      witness result.2] ≤ (q : ENNReal)/2^124 := by
  classical
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have records := pinned_recorded_table compress program PState.init Trace.WF.nil
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have evidence : st.prob PState.init (fun result _ => witness result.2) ≤
      st.prob PState.init (fun _ finish => ¬ bad.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    intro result finish facts hit
    exact ⟨extract finish.trace result.2 facts.1.2 hit, by simpa [PState.init] using facts.2.2⟩
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal (evidence.trans prob)).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- **Even-leaf binding at the small size.** Fixed compression, uniform permutation with inverse queries:
an even-leaf collision among the recorded rows has probability at most `q/2^124`. -/
theorem fixed_compression_even_leaf_bound_small {α : Type}
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      EvenLeafWitness result.2] ≤ (q : ENNReal)/2^124 := by
  refine even_replayed_event compress program EvenLeafWitness evenPinCall.badSpec q calls bounded
    even_witness_bad ?_
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have fits : calls < Fintype.card S3State := by rw [s3_card_state]; omega
  have raw := evenPinCall.prob_bad_le_inv (2^1344) (2^1280) (2^960) (2^1280) (2^1344+2^1281)
    calls fits even_trunc_fiber even_chop_fiber even_pin_fiber even_second_inputs (by norm_num) (by norm_num)
    st calls budget.toIQB
  refine raw.trans ?_
  rw [s3_card_state]
  have margin := even_replay_margin q calls (2^1344+2^1281) (2^1280) positive small replayed (by norm_num)
    (by norm_num)
  norm_num [unionBound] at margin ⊢
  exact margin

/-- **Binding target for the checker lane** (`EvenLeafSmallBound`, PairLeafModel.lean). -/
theorem even_leaf_small_bound : EvenLeafSmallBound :=
  fun compress program q calls positive small replayed bounded =>
    fixed_compression_even_leaf_bound_small compress program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
