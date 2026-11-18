import CommitGolfCandidate.TwoPermutationPinnedReplayProbability

/-! Width-generic leaf collision bound for the pinned two-call leaf hash.

A leaf digest that keeps the low `b` bits of the second permutation reply is
collision resistant in the lazy permutation model with the S3 pinned-call bound
`(Q(Q-1)/2 · k + n·2^896) / (2^1600 - Q)` for `k = 2^(1600-b) + 2^1345 + 2^897`.
`pinned_leaf_probability_width` turns any real margin for that expression into a
bound on `PinnedLeafWitnessW b`; `pinned_margin_width` supplies the margin
`q / 2^124` for every `244 ≤ b`. The packed 240-bit chain uses the same
argument at `b = 240` with the margin `9q/2^124` (TwoPermutationPinnedPeerMargin). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

def truncDigestW (b : Nat) (digest : BitVec 256) : BitVec 256 := BitVec.ofNat 256 (digest.toNat % 2^b)
def leafDigestW (b : Nat) (output : Block) : BitVec 256 := truncDigestW b (outputDigest output)

theorem leaf_digest_eq_width (output : Block) : leafDigest output = leafDigestW 240 output := rfl

def PinnedLeafWitnessW (b : Nat) (rows : List PublicRow) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := pinnedFirstRow perm message₀
    let a₁ := pinnedFirstRow perm message₁
    let b₀ := pinnedSecondRow perm index nonce₀ a₀.2 message₀
    let b₁ := pinnedSecondRow perm index nonce₁ a₁.2 message₁
    PublicRow.permutation a₀.1 a₀.2 ∈ rows ∧ PublicRow.permutation a₁.1 a₁.2 ∈ rows ∧
      PublicRow.permutation b₀.1 b₀.2 ∈ rows ∧ PublicRow.permutation b₁.1 b₁.2 ∈ rows ∧
      leafDigestW b b₀.2 = leafDigestW b b₁.2 ∧ message₀ ≠ message₁

theorem pinned_leaf_witness_width (rows : List PublicRow) (hit : PinnedLeafWitness rows) :
    PinnedLeafWitnessW 240 rows := hit

/-- The pinned two-call hash with its digest cut to the low `b` bits. -/
def s3PinCallW (b : Nat) : PinCall S3State (BitVec 1600) (BitVec 192) (BitVec 704) (BitVec 256)
    (BitVec 448) (BitVec 256) :=
  { s3PinCall with trunc := fun o => BitVec.ofNat 256 (o.toNat % 2^b) }

theorem s3_trunc_width_fiber (b : Nat) (hb : b ≤ 256) (d : BitVec 256) :
    (Finset.univ.filter fun s : S3State => (s3PinCallW b).trunc s = d).card ≤ 2 ^ (1600 - b) := by
  have split : (2 : Nat) ^ 1600 = 2 ^ b * 2 ^ (1600 - b) := by rw [← pow_add]; congr 1; omega
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun s : S3State => (s3PinCallW b).trunc s = d)
    (t := (Finset.univ : Finset (BitVec (1600 - b)))) (fun s => BitVec.ofNat (1600 - b) (s.toNat / 2 ^ b))
    (by intro a _; simp) (by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
      have e1 := congrArg BitVec.toNat (hx.trans hy.symm)
      have e2 := congrArg BitVec.toNat hxy
      have small (s : S3State) : s.toNat % 2^b < 2^256 :=
        lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) hb)
      have quot (s : S3State) : s.toNat / 2^b < 2^(1600-b) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← split]; exact s3_state_lt s
      simp only [s3PinCallW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (small x), Nat.mod_eq_of_lt (small y),
        Nat.mod_eq_of_lt (quot x), Nat.mod_eq_of_lt (quot y)] at e1 e2
      apply BitVec.eq_of_toNat_eq
      rw [← Nat.div_add_mod x.toNat (2^b), ← Nat.div_add_mod y.toNat (2^b), e1, e2])
  rwa [Finset.card_univ, s3_card_bitvec] at h

theorem trunc_digest_width (b : Nat) (hb : b ≤ 256) (reply : Block) :
    (s3PinCallW b).trunc reply = leafDigestW b reply := by
  change BitVec.ofNat 256 (reply.toNat % 2^b) = BitVec.ofNat 256 ((reply.extractLsb' 0 256).toNat % 2^b)
  congr 1
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hb)]

theorem stored_evaluation_width (b : Nat) (hb : b ≤ 256) (layout : PeerLeafLayout) (t : Trace PermState)
    (rows : List PublicRow) (stored : PinnedRowsStored rows t) (perm : Block → Block) (i : Index)
    (salt : BitVec 128) (value : CommitGolf.Entry)
    (ha : let a := pinnedFirstRow perm (entryWords value); PublicRow.permutation a.1 a.2 ∈ rows)
    (hb' : let a := pinnedFirstRow perm (entryWords value)
          let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
          PublicRow.permutation b.1 b.2 ∈ rows) :
    let a := pinnedFirstRow perm (entryWords value)
    let c := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
    (s3PinCallW b).Evaluates t (s3Input (layout.salt i salt,value)) (leafDigestW b c.2) := by
  let leaf := (layout.salt i salt,value)
  let a := pinnedFirstRow perm (entryWords value)
  let c := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
  obtain ⟨e,he,ein,eout⟩ := stored a.1 a.2 ha
  obtain ⟨f,hf,fin,fout⟩ := stored c.1 c.2 hb'
  have first : e.inp = s3PinCall.enc1 (s3Input leaf).1 :=
    ein.trans ((layout.first i value).trans (s3_first_eq leaf))
  refine ⟨e,he,f,hf,first,?_,?_⟩
  · rw [eout,first]
    exact fin.trans ((layout.second i value salt a.2).trans (s3_second_eq leaf a.2))
  · exact (congrArg (s3PinCallW b).trunc fout).trans (trunc_digest_width b hb c.2)

theorem pinned_witness_bad_width (b : Nat) (hb : b ≤ 256) (layout : PeerLeafLayout) (t : Trace PermState)
    (rows : List PublicRow) (stored : PinnedRowsStored rows t)
    (hit : PinnedLeafWitnessW b rows) : ¬ (s3PinCallW b).badSpec.Good t := by
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
  have left := stored_evaluation_width b hb layout t rows stored perm i salt₀ value₀ a₀ b₀
  have right := stored_evaluation_width b hb layout t rows stored perm i salt₁ value₁ a₁ b₁
  refine (s3PinCallW b).collision_imp_bad (s3_input_ne (leaf := (layout.salt i salt₀,value₀))
    (leaf' := (layout.salt i salt₁,value₁)) distinct) left ?_
  exact digest.symm ▸ right

/-- The S3 pinned-call expression at digest width `b`, as a function of the call count. -/
noncomputable def pinnedWidthTerm (b queries : Nat) : ℝ :=
  (((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-b) + 2^1345 + 2^897) + (queries : ℝ)*2^896) /
    (2^1600 - (queries : ℝ))

/-- Any real margin for `pinnedWidthTerm b calls` bounds the `b`-bit leaf collision event. -/
theorem pinned_leaf_probability_width {α : Type} (b : Nat) (hb : b ≤ 256) (layout : PeerLeafLayout)
    (compression : Compression) (program : OracleComp World α) (calls : Nat) (fits : calls < 2^1600)
    (target : ℝ) (margin : pinnedWidthTerm b calls ≤ target)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compression,p⟩ (recordRows program))}[
      PinnedLeafWitnessW b result.2] ≤ ENNReal.ofReal target := by
  classical
  let st := toStrat compression (recordRows program)
  have budget : st.QB calls := to_strat_QB compression bounded
  have records := pinned_recorded_table compression program PState.init Trace.WF.nil
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have evidence : st.prob PState.init (fun result _ => PinnedLeafWitnessW b result.2) ≤
      st.prob PState.init (fun _ finish => ¬ (s3PinCallW b).badSpec.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    intro result finish facts hit
    exact ⟨pinned_witness_bad_width b hb layout finish.trace result.2 facts.1.2 hit,
      by simpa [PState.init] using facts.2.2⟩
  have fitsCard : calls < Fintype.card S3State := by rw [s3_card_state]; exact fits
  have raw := (s3PinCallW b).prob_bad_le_inv (2^(1600-b)) (2^896) (2^1344) (2^896) (2^(1600-b)+2^1345+2^897)
    calls fitsCard (s3_trunc_width_fiber b hb) s3_chop_fiber s3_pin_fiber s3_second_inputs
    (by rw [Nat.add_assoc]; exact Nat.add_le_add_left (by norm_num) _)
    (by rw [Nat.add_assoc]; exact le_trans (by norm_num) (Nat.le_add_left _ _)) st calls budget.toIQB
  have bound : st.prob PState.init (fun _ finish => ¬ (s3PinCallW b).badSpec.Good finish.trace ∧
      finish.count ≤ calls) ≤ target := by
    refine raw.trans (le_of_eq_of_le ?_ margin)
    rw [s3_card_state]
    unfold pinnedWidthTerm
    push_cast
    ring_nf
  rw [perm_sampling_prob]
  exact ENNReal.ofReal_le_ofReal (evidence.trans bound)

/-- For digests of at least 244 bits the leaf term fits in `q/2^124`, leaving the
rest of the `q/2^120` budget to the compression collision event. -/
theorem pinned_margin_width (b q queries : ℕ) (wide : 244 ≤ b) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (count : queries ≤ q + 2^31 + 4) :
    pinnedWidthTerm b queries ≤ (q : ℝ)/2^124 := by
  have qOne : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qUpper : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have nonneg : (0 : ℝ) ≤ queries := by positivity
  have terms : (queries : ℝ) ≤ (q : ℝ) + 2^31 + 4 := by exact_mod_cast count
  have queriesUpper : (queries : ℝ) ≤ 2^121 := by
    have threshold : (2 : ℝ)^120 + 2^31 + 4 ≤ 2^121 := by norm_num
    linarith
  have denominator : (2 : ℝ)^1600 - 2^121 ≤ 2^1600-(queries : ℝ) := by linarith
  have denominatorPos : (0 : ℝ) < 2^1600-(queries : ℝ) := by
    have : (0 : ℝ) < 2^1600 - 2^121 := by norm_num
    linarith
  have fiber : (2 : ℝ)^(1600-b) ≤ 2^1356 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have squareBound : (queries : ℝ)^2 ≤ (q : ℝ)*(2^120 + 2^65) := by
    let extra : ℝ := 2^31+4
    have leSum : (queries : ℝ) ≤ q + extra := by linarith [show extra = (2:ℝ)^31+4 from rfl]
    have sq := mul_le_mul leSum leSum nonneg (by positivity)
    have qsq := mul_le_mul_of_nonneg_right qUpper qNonneg
    have esq : 2*extra*q + extra^2 ≤ q*2^65 := by
      have e1 : 2*extra ≤ 2^33 := by norm_num [extra]
      have e2 : extra^2 ≤ 2^64 := by norm_num [extra]
      nlinarith
    nlinarith
  have linearBound : (queries : ℝ) ≤ (q : ℝ)*2^33 := by
    have extra : (2 : ℝ)^31 + 4 ≤ 2^32 := by norm_num
    nlinarith
  have kBound : (2 : ℝ)^(1600-b) + 2^1345 + 2^897 ≤ 2^1356 + 2^1345 + 2^897 := by linarith
  have pairs : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-b) + 2^1345 + 2^897) ≤
      (queries : ℝ)^2 / 2 * (2^1356 + 2^1345 + 2^897) := by
    have k0 : (0 : ℝ) ≤ 2^(1600-b) + 2^1345 + 2^897 := by positivity
    have : (queries : ℝ) * ((queries : ℝ) - 1) / 2 ≤ (queries : ℝ)^2 / 2 := by nlinarith
    calc _ ≤ (queries : ℝ)^2 / 2 * (2^(1600-b) + 2^1345 + 2^897) := mul_le_mul_of_nonneg_right this k0
      _ ≤ _ := mul_le_mul_of_nonneg_left kBound (by positivity)
  have total : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-b) + 2^1345 + 2^897) + (queries : ℝ)*2^896 ≤
      (q : ℝ) * ((2^120 + 2^65) * (2^1356 + 2^1345 + 2^897) / 2 + 2^929) := by
    have a := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ (2^1356 + 2^1345 + 2^897)/2)
    have c := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^896)
    nlinarith
  have constant : (2^120 + 2^65 : ℝ) * (2^1356 + 2^1345 + 2^897) / 2 + 2^929 ≤ 1 / 2^124 * (2^1600 - 2^121) := by
    norm_num
  unfold pinnedWidthTerm
  rw [div_le_iff₀ denominatorPos]
  have scaled := mul_le_mul_of_nonneg_left constant qNonneg
  have den := mul_le_mul_of_nonneg_left denominator (by positivity : (0 : ℝ) ≤ (q : ℝ)/2^124)
  have eq : (q : ℝ) * (1 / 2^124 * (2^1600 - 2^121)) = (q : ℝ)/2^124 * (2^1600 - 2^121) := by ring
  linarith

/-- The `b`-bit leaf collision event for `244 ≤ b ≤ 256` has probability at most `q/2^124`. -/
theorem pinned_leaf_bound_width {α : Type} (b : Nat) (wide : 244 ≤ b) (hb : b ≤ 256) (layout : PeerLeafLayout)
    (compression : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31) (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compression,p⟩ (recordRows program))}[
      PinnedLeafWitnessW b result.2] ≤ (q : ENNReal)/2^124 := by
  refine (pinned_leaf_probability_width b hb layout compression program calls (by omega) _
    (pinned_margin_width b q calls wide positive small (by omega)) bounded).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  norm_num

end TwoPermutationPrototype.Sampling
