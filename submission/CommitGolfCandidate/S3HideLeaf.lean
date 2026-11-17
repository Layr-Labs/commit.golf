import CommitGolfCandidate.S3HideCount
import CommitGolfCandidate.S3PermBridge
import CommitGolfCandidate.S3LeafProbe
import CommitGolfCandidate.NonceEncoding

/-! Per-leaf replacement for the stage-3 leaf hash, in the contract's oracle world: the
permutation is sampled uniformly, the compression function is fixed, and the adversary's first
stage runs before the nonce is drawn. Replacing the value of a leaf whose nonce stays private
changes any bounded continuation by at most `4 (q1 + q2 + 2) / 2^192`. The proof moves each
event probability to the lazy permutation model and applies its hiding bound. -/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance s3HideLeafDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation

/-! ### Fixed-oracle runs -/

theorem s3_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

theorem s3_run_hash (oracle : Oracle) (salt : BitVec 256) (value : CommitGolf.Entry) {α : Type}
    (next : BitVec 256 → OracleComp World α) :
    fixedOracleRun oracle (s3HashLeaf salt value >>= next) =
      fixedOracleRun oracle (next (s3LeafDigest oracle.permutation salt value)) := by
  have single : fixedOracleRun oracle (s3HashLeaf salt value) =
      pure (s3LeafDigest oracle.permutation salt value) := by
    rw [fixedOracleRun, s3_hash_leaf_run, map_pure]
  rw [s3_run_bind, single, pure_bind]

theorem s3_run_discard (oracle : Oracle) (input : BitVec PERMUTATION_WIDTH) {α : Type}
    (next : OracleComp World α) :
    fixedOracleRun oracle
        ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= fun _ => next) =
      fixedOracleRun oracle next :=
  fixed_oracle_run_public oracle (.inr (.inl input)) (fun _ => next)

theorem s3_hide_leaf_public_bound (salt : BitVec 256) (value : CommitGolf.Entry) :
    PublicQueryBound (s3HashLeaf salt value) 2 := by
  unfold s3HashLeaf
  change 1 ≤ 2 ∧ ∀ first : BitVec PERMUTATION_WIDTH, PublicQueryBound
    ((liftM (World.query (.inr (.inr (.inl (s3Second salt first value))))) :
        OracleComp World (BitVec PERMUTATION_WIDTH)) >>= fun second =>
      pure (BitVec.ofNat 256 second.toNat)) (2 - 1)
  refine ⟨by omega, fun first => ?_⟩
  change 1 ≤ 2 - 1 ∧ ∀ second : BitVec PERMUTATION_WIDTH, PublicQueryBound
    (pure (BitVec.ofNat 256 second.toNat) : OracleComp World (BitVec 256)) (2 - 1 - 1)
  exact ⟨by omega, fun _ => trivial⟩

/-! ### Total variation from event probabilities -/

private theorem le_add_ofReal_of_toReal {a b : ENNReal} {ε : ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hε : 0 ≤ ε) (h : a.toReal ≤ b.toReal + ε) : a ≤ b + ENNReal.ofReal ε := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + ε) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal b.toReal + ENNReal.ofReal ε := ENNReal.ofReal_add ENNReal.toReal_nonneg hε
    _ = b + ENNReal.ofReal ε := by rw [ENNReal.ofReal_toReal hb]

/-- Total variation is the largest event discrepancy. -/
theorem tv_le_of_events {α : Type} (mx my : ProbComp α) (ε : ℝ) (nonneg : 0 ≤ ε)
    (close : ∀ event : α → Prop,
      |(prEvent (event <$> mx)).toReal - (prEvent (event <$> my)).toReal| ≤ ε) :
    measureTVDist mx my ≤ ε := by
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  rw [measureETVDist, MeasureTheory.Measure.etvDist]
  refine iSup_le fun set => ?_
  have left := prEvent_eq_evalDist_of_discrete mx (fun value => value ∈ set.1)
  have right := prEvent_eq_evalDist_of_discrete my (fun value => value ∈ set.1)
  simp only [Set.setOf_mem_eq] at left right
  have bound := abs_sub_le_iff.mp (close (fun value => value ∈ set.1))
  rw [← left, ← right, ENNReal.absDiff_le_iff]
  exact ⟨le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg (by linarith [bound.1]),
    le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg (by linarith [bound.2])⟩

/-! ### The two experiments -/

variable {State α : Type}

/-- Real experiment: the continuation receives the digest of the leaf chosen by the first stage,
hashed with a fresh nonce. -/
def s3RealGame (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α) :
    ProbComp α := do
  let permutation ← $ᵗ Perm
  let state ← fixedOracleRun ⟨compression, permutation⟩ first
  let nonce ← $ᵗ Nonce192
  fixedOracleRun ⟨compression, permutation⟩
    (next state (s3LeafDigest permutation (expandNonce192 nonce) (value state)))

/-- Ideal experiment: the continuation receives a uniform digest. -/
def s3IdealGame (compression : Compression) (first : OracleComp World State)
    (next : State → BitVec 256 → OracleComp World α) : ProbComp α := do
  let permutation ← $ᵗ Perm
  let state ← fixedOracleRun ⟨compression, permutation⟩ first
  let digest ← $ᵗ (BitVec 256)
  fixedOracleRun ⟨compression, permutation⟩ (next state digest)

/-- The real experiment for one nonce, as a single oracle computation. -/
def s3RealComp (first : OracleComp World State) (value : State → CommitGolf.Entry)
    (next : State → BitVec 256 → OracleComp World α) (nonce : Nonce192) : OracleComp World α :=
  first >>= fun state =>
    s3HashLeaf (expandNonce192 nonce) (value state) >>= fun digest => next state digest

/-- The ideal experiment for one digest; the first leaf query is made and its reply dropped. -/
def s3IdealComp (first : OracleComp World State) (value : State → CommitGolf.Entry)
    (next : State → BitVec 256 → OracleComp World α) (digest : BitVec 256) : OracleComp World α :=
  first >>= fun state =>
    (liftM (World.query (.inr (.inr (.inl (s3First (value state)))))) : OracleComp World _) >>=
      fun _ => next state digest

/-- First stage of the lazy-model game: the adversary's prefix and the leaf's two-call input. -/
noncomputable def s3StratFirst (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) : Strat PermState (BitVec 1472 × BitVec 576 × State) :=
  (toStrat compression first).bind fun state =>
    Strat.done ((s3HideInput 0 (value state)).1, (s3HideInput 0 (value state)).2.2, state)

open Classical in
/-- Second stage of the lazy-model game: the continuation, reporting whether the event holds. -/
noncomputable def s3StratNext (compression : Compression)
    (next : State → BitVec 256 → OracleComp World α) (event : α → Prop)
    (state : State) (digest : BitVec 256) : Strat PermState Bool :=
  (toStrat compression (next state digest)).bind fun result => Strat.done (decide (event result))

theorem s3_strat_first_QB (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (budget : Nat) (bounded : PublicQueryBound first budget) :
    (s3StratFirst compression first value).QB budget := by
  have bound := (to_strat_QB compression bounded).bind (fun state =>
    Strat.QB.done ((s3HideInput 0 (value state)).1, (s3HideInput 0 (value state)).2.2, state) 0)
  exact bound

theorem s3_strat_next_QB (compression : Compression)
    (next : State → BitVec 256 → OracleComp World α) (event : α → Prop)
    (state : State) (digest : BitVec 256) (budget : Nat)
    (bounded : PublicQueryBound (next state digest) budget) :
    (s3StratNext compression next event state digest).QB budget := by
  classical
  have bound := (to_strat_QB compression bounded).bind (fun result =>
    Strat.QB.done (decide (event result)) 0)
  exact bound

theorem s3_input_nonce (nonce : Nonce192) (value : CommitGolf.Entry) :
    s3HideInput (expandNonce192 nonce) value = ((s3HideInput 0 value).1, nonce, (s3HideInput 0 value).2.2) := by
  have field : BitVec.ofNat 192 (expandNonce192 nonce).toNat = nonce := by
    apply BitVec.eq_of_toNat_eq
    have bound := nonce.isLt
    simp [expandNonce192] <;> omega
  simp only [s3HideInput, field]

theorem to_strat_hash (compression : Compression) (salt : BitVec 256) (value : CommitGolf.Entry) :
    toStrat compression (s3HashLeaf salt value) = s3TwoCall.eval (s3HideInput salt value) := by
  have left : toStrat compression (s3HashLeaf salt value) =
      Strat.fwd (s3First value) fun first =>
        Strat.fwd (s3Second salt first value) fun second =>
          Strat.done (BitVec.ofNat 256 second.toNat) := rfl
  rw [left, s3First_eq salt value]
  simp only [s3Second_eq]
  rfl

theorem s3_real_strat_prob (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α)
    (event : α → Prop) (nonce : Nonce192) :
    (toStrat compression (s3RealComp first value next nonce)).prob PState.init
        (fun result _ => event result) =
      ((s3StratFirst compression first value).bind fun a =>
        (s3TwoCall.eval (a.1, nonce, a.2.1)).bind
          (s3StratNext compression next event a.2.2)).prob PState.init (fun b _ => b = true) := by
  unfold Strat.prob s3RealComp
  simp only [to_strat_bind, to_strat_hash, s3_input_nonce, s3StratFirst, s3StratNext,
    Strat.exp_bind, Strat.exp, decide_eq_true_eq] <;> rfl

theorem s3_ideal_strat_prob (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α)
    (event : α → Prop) (digest : BitVec 256) :
    (toStrat compression (s3IdealComp first value next digest)).prob PState.init
        (fun result _ => event result) =
      ((s3StratFirst compression first value).bind fun a =>
        Strat.fwd (s3TwoCall.enc1 a.1) fun _ =>
          s3StratNext compression next event a.2.2 digest).prob PState.init
        (fun b _ => b = true) := by
  unfold Strat.prob s3IdealComp
  simp only [to_strat_bind, to_strat_permute, s3StratFirst, s3StratNext,
    Strat.exp_bind, Strat.exp, decide_eq_true_eq, s3First_eq 0] <;> rfl

/-! ### Event probabilities of the two experiments -/

theorem s3_real_game_event (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α)
    (event : α → Prop) :
    prEvent (event <$> s3RealGame compression first value next) =
      ENNReal.ofReal ((s3TwoCall.hidingReal (s3StratFirst compression first value)
        (s3StratNext compression next event)).prob PState.init fun b _ => b = true) := by
  have reordered : 𝒟[s3RealGame compression first value next] =
      𝒟[do let nonce ← $ᵗ Nonce192
           let permutation ← $ᵗ Perm
           fixedOracleRun ⟨compression, permutation⟩ (s3RealComp first value next nonce)] := by
    have inner : ∀ (nonce : Nonce192) (permutation : Perm),
        fixedOracleRun ⟨compression, permutation⟩ (s3RealComp first value next nonce) =
          (fixedOracleRun ⟨compression, permutation⟩ first >>= fun state =>
            fixedOracleRun ⟨compression, permutation⟩
              (next state (s3LeafDigest permutation (expandNonce192 nonce) (value state)))) := by
      intro nonce permutation
      unfold s3RealComp
      rw [s3_run_bind]
      apply bind_congr
      intro state
      exact s3_run_hash ⟨compression, permutation⟩ _ _ _
    unfold s3RealGame
    simp only [inner]
    trans 𝒟[do let permutation ← $ᵗ Perm
                let nonce ← $ᵗ Nonce192
                let state ← fixedOracleRun ⟨compression, permutation⟩ first
                fixedOracleRun ⟨compression, permutation⟩
                  (next state (s3LeafDigest permutation (expandNonce192 nonce) (value state)))]
    · apply _root_.evalDist_bind_congr
      intro permutation
      exact (distribution_bind_comm ($ᵗ Nonce192)
        (fixedOracleRun ⟨compression, permutation⟩ first) _).symm
    · exact distribution_bind_comm ($ᵗ Perm) ($ᵗ Nonce192) _
  rw [(EvalDistEq.of_evalDist_eq reordered).prEvent_eq event]
  rw [prEvent_bind_eq_sum_fintype, TwoCall.hiding_real_avg,
    ← sum_inv_card_mul_ofReal _ fun nonce => Strat.prob_nonneg _ _ _]
  refine Finset.sum_congr rfl fun nonce _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, perm_sampling_prob, s3_real_strat_prob]

theorem s3_ideal_game_event (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α)
    (event : α → Prop) :
    prEvent (event <$> s3IdealGame compression first next) =
      ENNReal.ofReal ((s3TwoCall.hidingIdeal (s3StratFirst compression first value)
        (s3StratNext compression next event)).prob PState.init fun b _ => b = true) := by
  have reordered : 𝒟[s3IdealGame compression first next] =
      𝒟[do let digest ← $ᵗ (BitVec 256)
           let permutation ← $ᵗ Perm
           fixedOracleRun ⟨compression, permutation⟩ (s3IdealComp first value next digest)] := by
    have inner : ∀ (digest : BitVec 256) (permutation : Perm),
        fixedOracleRun ⟨compression, permutation⟩ (s3IdealComp first value next digest) =
          (fixedOracleRun ⟨compression, permutation⟩ first >>= fun state =>
            fixedOracleRun ⟨compression, permutation⟩ (next state digest)) := by
      intro digest permutation
      unfold s3IdealComp
      rw [s3_run_bind]
      apply bind_congr
      intro state
      exact s3_run_discard ⟨compression, permutation⟩ _ _
    unfold s3IdealGame
    simp only [inner]
    trans 𝒟[do let permutation ← $ᵗ Perm
                let digest ← $ᵗ (BitVec 256)
                let state ← fixedOracleRun ⟨compression, permutation⟩ first
                fixedOracleRun ⟨compression, permutation⟩ (next state digest)]
    · apply _root_.evalDist_bind_congr
      intro permutation
      exact (distribution_bind_comm ($ᵗ (BitVec 256))
        (fixedOracleRun ⟨compression, permutation⟩ first) _).symm
    · exact distribution_bind_comm ($ᵗ Perm) ($ᵗ (BitVec 256)) _
  rw [(EvalDistEq.of_evalDist_eq reordered).prEvent_eq event]
  rw [prEvent_bind_eq_sum_fintype, TwoCall.hiding_ideal_avg,
    ← sum_inv_card_mul_ofReal _ fun digest => Strat.prob_nonneg _ _ _]
  refine Finset.sum_congr rfl fun digest _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, perm_sampling_prob, s3_ideal_strat_prob]

/-! ### Distances -/

/-- Real against ideal, for one leaf value. -/
theorem s3_real_ideal_distance (compression : Compression) (first : OracleComp World State)
    (value : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α)
    (firstBudget nextBudget : Nat) (firstBounded : PublicQueryBound first firstBudget)
    (nextBounded : ∀ state digest, PublicQueryBound (next state digest) nextBudget)
    (small : firstBudget + 1 ≤ 2 ^ 1599) :
    measureTVDist (s3RealGame compression first value next) (s3IdealGame compression first next) ≤
      2 * ((firstBudget : ℝ) + 1 + nextBudget) / 2 ^ 192 := by
  apply tv_le_of_events _ _ _ (by positivity)
  intro event
  rw [s3_real_game_event, s3_ideal_game_event compression first value next event,
    ENNReal.toReal_ofReal (Strat.prob_nonneg _ _ _),
    ENNReal.toReal_ofReal (Strat.prob_nonneg _ _ _)]
  exact s3_strat_hiding _ _ firstBudget nextBudget
    (s3_strat_first_QB compression first value firstBudget firstBounded)
    (fun state digest => s3_strat_next_QB compression next event state digest nextBudget
      (nextBounded state digest)) small

theorem s3_leaf_core (compression : Compression) (first : OracleComp World State)
    (left right : State → CommitGolf.Entry) (next : State → BitVec 256 → OracleComp World α)
    (firstBudget nextBudget : Nat) (firstBounded : PublicQueryBound first firstBudget)
    (nextBounded : ∀ state digest, PublicQueryBound (next state digest) nextBudget) :
    measureTVDist (s3RealGame compression first left next)
        (s3RealGame compression first right next) ≤
      4 * ((firstBudget + nextBudget + 2 : Nat) : ℝ) / 2 ^ 192 := by
  simp only [Nat.cast_add, Nat.cast_ofNat]
  by_cases small : firstBudget + 1 ≤ 2 ^ 1599
  · have leftBound := s3_real_ideal_distance compression first left next firstBudget nextBudget
      firstBounded nextBounded small
    have rightBound := s3_real_ideal_distance compression first right next firstBudget nextBudget
      firstBounded nextBounded small
    rw [measureTVDist_comm] at rightBound
    refine ((measureTVDist_triangle _ (s3IdealGame compression first next) _).trans
      (add_le_add leftBound rightBound)).trans ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  · refine (measureTVDist_le_one _ _).trans ?_
    have big : (2 : ℝ) ^ 1599 < (firstBudget : ℝ) + 1 := by exact_mod_cast not_le.mp small
    have step : (2 : ℝ) ^ 192 ≤ 2 ^ 1599 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have nextNonneg : (0 : ℝ) ≤ (nextBudget : ℝ) := Nat.cast_nonneg _
    rw [le_div_iff₀ (by positivity)]
    generalize (2 : ℝ) ^ 192 = small192 at step ⊢
    generalize (2 : ℝ) ^ 1599 = large at step big
    linarith

/-- **Per-leaf replacement, core form.** The leaf is hidden for every first-stage result. -/
theorem s3_leaf_indistinguishable (compression : Compression) {State α : Type}
    (first : OracleComp World State) (left right : State → CommitGolf.Entry)
    (next : State → BitVec 256 → OracleComp World α) (firstBudget nextBudget : Nat)
    (firstBounded : PublicQueryBound first firstBudget)
    (nextBounded : ∀ state digest, PublicQueryBound (next state digest) nextBudget) :
    measureTVDist
      (do let permutation ← $ᵗ Perm
          let state ← fixedOracleRun ⟨compression, permutation⟩ first
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨compression, permutation⟩
            (next state (s3LeafDigest permutation (expandNonce192 nonce) (left state))))
      (do let permutation ← $ᵗ Perm
          let state ← fixedOracleRun ⟨compression, permutation⟩ first
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨compression, permutation⟩
            (next state (s3LeafDigest permutation (expandNonce192 nonce) (right state)))) ≤
      4 * ((firstBudget + nextBudget + 2 : Nat) : ℝ) / 2 ^ 192 :=
  s3_leaf_core compression first left right next firstBudget nextBudget firstBounded nextBounded

/-! ### Guarded form -/

/-- Continuation used to reduce the guarded form to the core form. For a hidden leaf it is the
given continuation (which ignores the nonce); for an opened leaf it ignores the supplied digest
and hashes the common value itself with the spare nonce. -/
def s3Guard (hidden : State → Bool) (common : State → CommitGolf.Entry)
    (next : State → Nonce192 → BitVec 256 → OracleComp World α) (spare : Nonce192)
    (state : State) (digest : BitVec 256) : OracleComp World α :=
  if hidden state then next state 0 digest
  else s3HashLeaf (expandNonce192 spare) (common state) >>= fun actual => next state spare actual

theorem s3_guard_bound (hidden : State → Bool) (common : State → CommitGolf.Entry)
    (next : State → Nonce192 → BitVec 256 → OracleComp World α) (budget : Nat)
    (bounded : ∀ state nonce digest, PublicQueryBound (next state nonce digest) budget)
    (spare : Nonce192) (state : State) (digest : BitVec 256) :
    PublicQueryBound (s3Guard hidden common next spare state digest) (budget + 2) := by
  unfold s3Guard
  split
  · exact (bounded state 0 digest).mono (by omega)
  · exact (public_query_bound_bind (s3_hide_leaf_public_bound _ _)
      (fun actual => bounded state spare actual)).mono (by omega)

theorem s3_guard_dist (compression : Compression) (first : OracleComp World State)
    (hidden : State → Bool) (common value : State → CommitGolf.Entry)
    (same : ∀ state, hidden state = false → value state = common state)
    (next : State → Nonce192 → BitVec 256 → OracleComp World α)
    (blind : ∀ state, hidden state = true → ∀ nonce nonce' digest,
      next state nonce digest = next state nonce' digest) :
    𝒟[do let permutation ← $ᵗ Perm
         let state ← fixedOracleRun ⟨compression, permutation⟩ first
         let nonce ← $ᵗ Nonce192
         fixedOracleRun ⟨compression, permutation⟩
           (next state nonce (s3LeafDigest permutation (expandNonce192 nonce) (value state)))] =
      𝒟[($ᵗ Nonce192) >>= fun spare =>
        s3RealGame compression first value (s3Guard hidden common next spare)] := by
  unfold s3RealGame
  symm
  trans 𝒟[do let permutation ← $ᵗ Perm
              let spare ← $ᵗ Nonce192
              let state ← fixedOracleRun ⟨compression, permutation⟩ first
              let nonce ← $ᵗ Nonce192
              fixedOracleRun ⟨compression, permutation⟩
                (s3Guard hidden common next spare state
                  (s3LeafDigest permutation (expandNonce192 nonce) (value state)))]
  · exact distribution_bind_comm ($ᵗ Nonce192) ($ᵗ Perm) _
  · apply _root_.evalDist_bind_congr
    intro permutation
    trans 𝒟[do let state ← fixedOracleRun ⟨compression, permutation⟩ first
                let spare ← $ᵗ Nonce192
                let nonce ← $ᵗ Nonce192
                fixedOracleRun ⟨compression, permutation⟩
                  (s3Guard hidden common next spare state
                    (s3LeafDigest permutation (expandNonce192 nonce) (value state)))]
    · exact distribution_bind_comm ($ᵗ Nonce192)
        (fixedOracleRun ⟨compression, permutation⟩ first) _
    · apply _root_.evalDist_bind_congr
      intro state
      cases opened : hidden state with
      | true =>
        have step : ∀ spare nonce : Nonce192,
            fixedOracleRun ⟨compression, permutation⟩
                (s3Guard hidden common next spare state
                  (s3LeafDigest permutation (expandNonce192 nonce) (value state))) =
              fixedOracleRun ⟨compression, permutation⟩
                (next state nonce
                  (s3LeafDigest permutation (expandNonce192 nonce) (value state))) := by
          intro spare nonce
          unfold s3Guard
          rw [if_pos opened, blind state opened 0 nonce]
        simp only [step]
        exact OracleComp.evalDist_bind_const _ _
      | false =>
        have step : ∀ spare nonce : Nonce192,
            fixedOracleRun ⟨compression, permutation⟩
                (s3Guard hidden common next spare state
                  (s3LeafDigest permutation (expandNonce192 nonce) (value state))) =
              fixedOracleRun ⟨compression, permutation⟩
                (next state spare
                  (s3LeafDigest permutation (expandNonce192 spare) (value state))) := by
          intro spare nonce
          unfold s3Guard
          rw [if_neg (by simp [opened]), s3_run_hash, same state opened]
        simp only [step]
        apply _root_.evalDist_bind_congr
        intro spare
        exact OracleComp.evalDist_bind_const _ _

/-- **Per-leaf replacement, guarded form.** Whether the coordinate is opened is decided by the
first stage. Opened: both values agree and the continuation may use the nonce. Unopened: the
continuation depends on the leaf only through its digest. -/
theorem s3_leaf_replacement (compression : Compression) {State α : Type}
    (first : OracleComp World State) (hidden : State → Bool)
    (left right : State → CommitGolf.Entry)
    (agree : ∀ state, hidden state = false → left state = right state)
    (next : State → Nonce192 → BitVec 256 → OracleComp World α)
    (blind : ∀ state, hidden state = true → ∀ nonce nonce' digest,
      next state nonce digest = next state nonce' digest)
    (firstBudget nextBudget : Nat)
    (firstBounded : PublicQueryBound first firstBudget)
    (nextBounded : ∀ state nonce digest, PublicQueryBound (next state nonce digest) nextBudget) :
    measureTVDist
      (do let permutation ← $ᵗ Perm
          let state ← fixedOracleRun ⟨compression, permutation⟩ first
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨compression, permutation⟩
            (next state nonce (s3LeafDigest permutation (expandNonce192 nonce) (left state))))
      (do let permutation ← $ᵗ Perm
          let state ← fixedOracleRun ⟨compression, permutation⟩ first
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨compression, permutation⟩
            (next state nonce (s3LeafDigest permutation (expandNonce192 nonce) (right state)))) ≤
      4 * ((firstBudget + nextBudget + 4 : Nat) : ℝ) / 2 ^ 192 := by
  have budget : firstBudget + nextBudget + 4 = firstBudget + (nextBudget + 2) + 2 := by omega
  rw [budget]
  have distance := measureTVDist_bind_left_le_of_forall_le ($ᵗ Nonce192)
    (fun spare => s3RealGame compression first left (s3Guard hidden left next spare))
    (fun spare => s3RealGame compression first right (s3Guard hidden left next spare))
    (by positivity)
    (fun spare => s3_leaf_core compression first left right (s3Guard hidden left next spare)
      firstBudget (nextBudget + 2) firstBounded
      (fun state digest => s3_guard_bound hidden left next nextBudget nextBounded spare state digest))
  simpa only [measureTVDist,
    s3_guard_dist compression first hidden left left (fun _ _ => rfl) next blind,
    s3_guard_dist compression first hidden left right
      (fun state opened => (agree state opened).symm) next blind] using distance

end CommitGolfCandidate
