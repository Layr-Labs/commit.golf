import CommitGolfCandidate.S3PermSingleCall
import CommitGolfCandidate.S3PermBridge
import CommitGolfCandidate.S3LeafLayout
import CommitGolfCandidate.S6Tree
import CommitGolfCandidate.Counting
import CommitGolfCandidate.Model

/-!
# Binding of the group node

The digest of a group of four leaves is one forward call of the 1600-bit permutation on 72 zero
bytes followed by the four leaf digests (1024 bits), truncated to its low 32 bytes. As a
`SingleCall` hash: `enc x = x * 2^576` (the zero bytes are the fixed prefix), `trunc` keeps the low
256 bits. Counts: `2^1344` states per digest, `2^1024` valid inputs.

* `SingleCall.listProbe`, `SingleCall.list_collision_bound`: the single-call hash evaluated on a
  list chosen by an adversary; two evaluated inputs that differ and share a digest appear with
  probability at most the union bound of `S3PermSingleCall`.
* `s6_collision_prob_le`: at these sizes the union bound is at most `(q + e)^2 / 2^256`.
* `s6HashGroup`, `probeGroups`, `s6GroupSearch`, `GroupCollision`: the oracle programs that replay
  group inputs, and the collision event among the replies.
* `s6_group_collision_bound`: the bound in the contract's oracle world, for any fixed compression
  function and a uniform permutation with inverse queries.
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

namespace SingleCall

variable {X D : Type} (H : SingleCall S X D)

theorem evaluates_mono {t t' : Trace S} {x : X} {d : D} (h : t <:+ t')
    (he : H.Evaluates t x d) : H.Evaluates t' x d := by
  obtain ⟨e, he, h1, h2⟩ := he
  exact ⟨e, h.subset he, h1, h2⟩

theorem eval_post (x : X) (s : PState S) (hs : s.trace.WF) :
    (H.eval x).post s fun d s' =>
      s'.trace.WF ∧ s.trace <:+ s'.trace ∧ H.Evaluates s'.trace x d := by
  show (Strat.fwd (H.enc x) _).post s _
  refine Strat.post_fwd hs fun y s1 hwf1 hsuf1 hm1 _ => ?_
  obtain ⟨e, he, h1, h2⟩ := hm1
  exact ⟨hwf1, hsuf1, e, he, h1, by rw [h2]⟩

/-- Evaluate the hash on each input in turn, keeping the input. -/
def listProbe : List X → Strat S (List (X × D))
  | [] => .done []
  | x :: rest => (H.eval x).bind fun d => (listProbe rest).bind fun out => .done ((x, d) :: out)

theorem listProbe_post (items : List X) (s : PState S) (hs : s.trace.WF) :
    (H.listProbe items).post s fun out s' =>
      s'.trace.WF ∧ s.trace <:+ s'.trace ∧ ∀ p ∈ out, H.Evaluates s'.trace p.1 p.2 := by
  induction items generalizing s with
  | nil => exact ⟨hs, List.suffix_refl _, by simp⟩
  | cons x rest ih =>
    show ((H.eval x).bind fun d => (H.listProbe rest).bind fun out => .done ((x, d) :: out)).post
      s _
    refine Strat.post_bind (Strat.post_mono ?_ (H.eval_post x s hs))
    rintro d s1 ⟨hwf1, hsuf1, hev⟩
    refine Strat.post_bind (Strat.post_mono ?_ (ih s1 hwf1))
    rintro out s2 ⟨hwf2, hsuf2, hall⟩
    refine ⟨hwf2, hsuf1.trans hsuf2, fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | h
    · exact H.evaluates_mono hsuf2 hev
    · exact hall p h

theorem listProbe_QB (items : List X) : (H.listProbe items).QB items.length := by
  induction items with
  | nil => exact .done _ _
  | cons x rest ih =>
    have h := Strat.QB.bind (H.eval_QB x) fun d =>
      Strat.QB.bind ih fun out => Strat.QB.done ((x, d) :: out) 0
    exact h.mono (by simp only [List.length_cons]; omega)

/-- Two evaluated inputs that differ and have the same digest. -/
def ListCollision (out : List (X × D)) : Prop :=
  ∃ a ∈ out, ∃ b ∈ out, a.1 ≠ b.1 ∧ a.2 = b.2

/-- **Collision among probed inputs.** The adversary makes at most `q` queries (forward or
inverse) and outputs a list of inputs; the first `e` of them are hashed with one forward query
each. -/
theorem list_collision_bound [Fintype X] [DecidableEq D] (K V q e : ℕ)
    (hQ : q + e < Fintype.card S)
    (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ K)
    (hV : Fintype.card X ≤ V) (A : Strat S (List X)) (hA : A.QB q) :
    (A.bind fun items => H.listProbe (items.take e)).prob PState.init
        (fun out _ => ListCollision out) ≤
      unionBound (Fintype.card S) K V (q + e) := by
  have hQB : (A.bind fun items => H.listProbe (items.take e)).QB (q + e) :=
    Strat.QB.bind hA fun items => (H.listProbe_QB (items.take e)).mono (by
      have := List.length_take_le e items
      omega)
  have hpost : (A.bind fun items => H.listProbe (items.take e)).post PState.init fun out s' =>
      (∀ p ∈ out, H.Evaluates s'.trace p.1 p.2) ∧
        (s'.trace.length ≤ (PState.init : PState S).trace.length + (q + e) ∧
          s'.count ≤ (PState.init : PState S).count + (q + e)) := by
    refine Strat.post_and ?_ (Strat.post_QB hQB PState.init)
    refine Strat.post_bind (Strat.post_mono ?_ (Strat.post_inv A PState.init Trace.WF.nil))
    rintro items s1 ⟨hwf1, -, -⟩
    exact Strat.post_mono (fun out s' h => h.2.2) (H.listProbe_post (items.take e) s1 hwf1)
  refine (Strat.prob_le_prob_of_post hpost ?_).trans
    (prob_not_good_le H.badSpec K V (q + e) hQ ?_ ?_ ?_ ?_ _)
  · rintro out s' ⟨hev, -, hc⟩ ⟨a, ha, b, hb, hne, heq⟩
    refine ⟨(H.not_good_iff _).2 (H.collision_imp_bad hne (hev a ha) ?_),
      by simpa [PState.init] using hc⟩
    rw [heq]
    exact hev b hb
  · intro x old
    exact ⟨univ.filter fun s => H.trunc s = H.trunc old.out, hK _,
      fun y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.2⟩⟩
  · intro x
    exact ⟨∅, Nat.zero_le _, fun y hy => by simp [badSpec] at hy⟩
  · intro y old
    exact ⟨∅, Nat.zero_le _, fun x hx => by simp [badSpec] at hx⟩
  · intro y
    refine ⟨univ.image H.enc, Finset.card_image_le.trans (by simpa using hV), fun x hx => ?_⟩
    obtain ⟨x0, h0⟩ := hx.2
    exact Finset.mem_image.2 ⟨x0, Finset.mem_univ _, h0⟩

end SingleCall

/-! ### The group node as a single-call hash -/

theorem s6_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s6_card_state : Fintype.card S3State = 2 ^ 1600 := s6_card_bitvec _

theorem s6_enc_injective :
    Function.Injective fun x : BitVec 1024 => (BitVec.ofNat 1600 (x.toNat * 2 ^ 576) : S3State) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  apply BitVec.eq_of_toNat_eq
  omega

/-- The group node: 72 zero bytes, then the four leaf digests (1024 bits); the digest is the low
32 bytes of the reply. -/
def s6SingleCall : SingleCall S3State (BitVec 1024) (BitVec 256) where
  enc x := BitVec.ofNat 1600 (x.toNat * 2 ^ 576)
  enc_inj := s6_enc_injective
  trunc o := BitVec.ofNat 256 o.toNat

/-- At most `2^1344` states have a given digest. -/
theorem s6_trunc_fiber (d : BitVec 256) :
    (univ.filter fun s : S3State => s6SingleCall.trunc s = d).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn
    (s := univ.filter fun s : S3State => s6SingleCall.trunc s = d)
    (t := (univ : Finset (BitVec 1344))) (fun s => BitVec.ofNat 1344 (s.toNat / 2 ^ 256))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s6SingleCall, BitVec.toNat_ofNat] at e1 e2
      have hA : a.toNat < 2 ^ 1600 := a.isLt
      have hB : b.toNat < 2 ^ 1600 := b.isLt
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s6_card_bitvec] at h

theorem s6_inputs_card : Fintype.card (BitVec 1024) ≤ 2 ^ 1024 := by
  rw [s6_card_bitvec]

/-- Real-number core: with `N = a 2^256` states, `K ≤ 3a/2` bad answers per older entry,
`u ≤ a/8` bad answers of a single entry and `Q ≤ 2^128` queries, the union bound is at most
`Q^2 / 2^256`. -/
theorem s6_union_core (a K u Q : ℝ) (ha : 1 ≤ a) (hK0 : 0 ≤ K) (hK : K ≤ 3 / 2 * a)
    (hu : u ≤ a / 8) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2 ^ 128) (hQQ : Q ≤ Q ^ 2) :
    (Q * (Q - 1) / 2 * K + Q * u) / (a * 2 ^ 256 - Q) ≤ Q ^ 2 / 2 ^ 256 := by
  have h128 : (2 : ℝ) ^ 128 ≤ 1 / 8 * 2 ^ 256 := by norm_num
  have hbig : (2 : ℝ) ^ 256 ≤ a * 2 ^ 256 := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) 256]
  have hD : 7 / 8 * (a * 2 ^ 256) ≤ a * 2 ^ 256 - Q := by linarith
  have hDpos : 0 < a * 2 ^ 256 - Q := by
    have : (0 : ℝ) < a * 2 ^ 256 := by positivity
    linarith
  rw [div_le_iff₀ hDpos]
  have h1 : Q * (Q - 1) / 2 * K ≤ 3 / 4 * a * Q ^ 2 := by
    have s1 : Q * (Q - 1) / 2 * K ≤ Q ^ 2 / 2 * K :=
      mul_le_mul_of_nonneg_right (by nlinarith) hK0
    have s2 : Q ^ 2 / 2 * K ≤ Q ^ 2 / 2 * (3 / 2 * a) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    linarith
  have h1' : Q * u ≤ 1 / 8 * a * Q ^ 2 := by
    have s1 : Q * u ≤ Q * (a / 8) := mul_le_mul_of_nonneg_left hu hQ0
    have s2 : Q * (a / 8) ≤ Q ^ 2 * (a / 8) :=
      mul_le_mul_of_nonneg_right hQQ (by linarith)
    linarith
  have h2 : Q ^ 2 / 2 ^ 256 * (7 / 8 * (a * 2 ^ 256)) = 7 / 8 * a * Q ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  have h3 : Q ^ 2 / 2 ^ 256 * (7 / 8 * (a * 2 ^ 256)) ≤ Q ^ 2 / 2 ^ 256 * (a * 2 ^ 256 - Q) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  linarith

/-- **The union bound at the group-node sizes**, for `Q ≤ 2^128` queries. -/
theorem s6_union_bound_le (Q : ℕ) (hsmall : Q ≤ 2 ^ 128) :
    unionBound (Fintype.card S3State) (2 ^ 1344) (2 ^ 1024) Q ≤ (Q : ℝ) ^ 2 / 2 ^ 256 := by
  have hcore := s6_union_core ((2 : ℝ) ^ 1344) (((2 ^ 1344 : ℕ) : ℝ)) (((2 ^ 1024 : ℕ) : ℝ))
    (Q : ℝ) (one_le_pow₀ (by norm_num)) (Nat.cast_nonneg _)
    (by
      have h' : (((2 ^ 1344 : ℕ) * 2 : ℕ) : ℝ) ≤ ((3 * 2 ^ 1344 : ℕ) : ℝ) :=
        Nat.cast_le.2 (by norm_num)
      push_cast at h' ⊢
      linarith)
    (by
      have h' : (((2 ^ 1024 : ℕ) * 8 : ℕ) : ℝ) ≤ ((2 ^ 1344 : ℕ) : ℝ) :=
        Nat.cast_le.2 (by norm_num)
      push_cast at h' ⊢
      linarith)
    (Nat.cast_nonneg _) (by exact_mod_cast hsmall)
    (by
      have : Q ≤ Q ^ 2 := by nlinarith
      exact_mod_cast this)
  have hN : (Fintype.card S3State : ℝ) = (2 : ℝ) ^ 1344 * 2 ^ 256 := by
    rw [s6_card_state, ← pow_add]
    norm_num
  unfold unionBound
  rw [hN]
  exact hcore

/-- **Group-node collisions in the lazy permutation model.** An adversary with at most `q`
permutation queries (forward or inverse) outputs group inputs; the first `extra` are hashed with
one forward query each. Two hashed inputs that differ and share a digest appear with probability
at most `(q + extra)^2 / 2^256`. -/
theorem s6_collision_prob_le (A : Strat S3State (List (BitVec 1024))) (q extra : ℕ)
    (hA : A.QB q) (hq : q ≤ 2 ^ 121) (hextra : extra ≤ 2 ^ 26) :
    (A.bind fun items => s6SingleCall.listProbe (items.take extra)).prob PState.init
        (fun out _ => SingleCall.ListCollision out) ≤
      ((q : ℝ) + extra) ^ 2 / 2 ^ 256 := by
  have hsmall : q + extra ≤ 2 ^ 128 := by
    have h1 : (2 : ℕ) ^ 121 + 2 ^ 26 ≤ 2 ^ 128 := by norm_num
    omega
  have hQ : q + extra < Fintype.card S3State := by
    rw [s6_card_state]
    exact lt_of_le_of_lt hsmall (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
  have h := s6SingleCall.list_collision_bound (2 ^ 1344) (2 ^ 1024) q extra hQ s6_trunc_fiber
    s6_inputs_card A hA
  have hu := s6_union_bound_le (q + extra) hsmall
  have hcast : ((q + extra : ℕ) : ℝ) = (q : ℝ) + extra := by push_cast; ring
  rw [hcast] at hu
  exact h.trans hu

theorem s6_strat_bind_assoc {α β γ : Type} (st : Strat S α) (f : α → Strat S β)
    (g : β → Strat S γ) : (st.bind f).bind g = st.bind fun a => (f a).bind g := by
  induction st with
  | done a => rfl
  | fwd x k ih => simp only [Strat.bind, ih]
  | inv y k ih => simp only [Strat.bind, ih]
  | rand n k ih => simp only [Strat.bind, ih]

end CommitGolfCandidate.Permutation

namespace CommitGolfCandidate

open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation

/-! ### Oracle programs: replay of group inputs -/

/-- One forward permutation query on the group window of `x`; the digest is the low 32 bytes of
the reply. -/
def s6HashGroup (x : BitVec 1024) : OracleComp World Digest := do
  let reply ← (liftM (World.query (.inr (.inr (.inl (s6SingleCall.enc x))))) :
    OracleComp World (BitVec PERMUTATION_WIDTH))
  return BitVec.ofNat 256 reply.toNat

theorem s6_hash_group_run (oracle : Oracle) (x : BitVec 1024) :
    oracle.run (s6HashGroup x) =
      pure (BitVec.ofNat 256 (oracle.permutation (s6SingleCall.enc x)).toNat, 1) := by
  unfold s6HashGroup
  erw [oracle_run_public_bind oracle (.inr (.inl (s6SingleCall.enc x)))]
  simp only [oracle_run_pure, pure_bind]
  rfl

theorem s6_hash_group_bound (x : BitVec 1024) : IsTotalQueryBound (s6HashGroup x) 1 := by
  unfold s6HashGroup
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by simp, fun reply => trivial⟩

/-- Replay a list of group inputs, one forward query each. -/
def probeGroups : List (BitVec 1024) → OracleComp World (List (BitVec 1024 × Digest))
  | [] => pure []
  | x :: rest => do
      let digest ← s6HashGroup x
      let replies ← probeGroups rest
      return (x, digest) :: replies

theorem probe_groups_run (oracle : Oracle) (items : List (BitVec 1024)) :
    oracle.run (probeGroups items) =
      pure (items.map fun x => (x, BitVec.ofNat 256 (oracle.permutation (s6SingleCall.enc x)).toNat),
        items.length) := by
  induction items with
  | nil => exact oracle_run_pure _ _
  | cons x rest ih =>
    simp only [probeGroups]
    rw [oracle_run_bind, s6_hash_group_run]
    simp only [pure_bind]
    rw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure, List.map_cons, List.length_cons]
    congr 2
    omega

theorem probe_groups_bound (items : List (BitVec 1024)) :
    IsTotalQueryBound (probeGroups items) items.length := by
  induction items with
  | nil => trivial
  | cons x rest ih =>
    simp only [probeGroups]
    have total : (x :: rest).length = 1 + (rest.length + 0) := by
      simp only [List.length_cons]; omega
    rw [total]
    apply isTotalQueryBound_bind (s6_hash_group_bound _)
    intro digest
    apply isTotalQueryBound_bind ih
    intro replies
    trivial

/-- Run a first stage that outputs the group inputs to replay, then replay at most `extra` of
them. -/
def s6GroupSearch (first : OracleComp World (Option (List (BitVec 1024)))) (extra : Nat) :
    OracleComp World (List (BitVec 1024 × Digest)) :=
  first >>= fun outcome =>
    match outcome with
    | none => pure []
    | some items => probeGroups (items.take extra)

/-- Two replayed group inputs with different digest quadruples and one group digest. -/
def GroupCollision (replies : List (BitVec 1024 × Digest)) : Prop :=
  ∃ a ∈ replies, ∃ b ∈ replies, a.1 ≠ b.1 ∧ a.2 = b.2

/-! ### From the oracle world to the lazy model -/

theorem to_strat_hash_group (compression : Compression) (x : BitVec 1024) :
    toStrat compression (s6HashGroup x) = s6SingleCall.eval x := by
  unfold s6HashGroup
  erw [to_strat_permute]
  rfl

theorem to_strat_probe_groups (compression : Compression) (items : List (BitVec 1024)) :
    toStrat compression (probeGroups items) = s6SingleCall.listProbe items := by
  induction items with
  | nil => rfl
  | cons x rest ih =>
    simp only [probeGroups, SingleCall.listProbe]
    rw [to_strat_bind, to_strat_hash_group]
    congr 1
    funext digest
    rw [to_strat_bind, ih]
    rfl

theorem s6_bound_of_real (budget extra : Nat) :
    ENNReal.ofReal (((budget : ℝ) + extra) ^ 2 / 2 ^ 256) =
      ((budget : ENNReal) + extra) ^ 2 / 2 ^ 256 := by
  have hcast : (budget : ℝ) + extra = ((budget + extra : ℕ) : ℝ) := by push_cast; ring
  have h256 : ENNReal.ofReal ((2 : ℝ) ^ 256) = 2 ^ 256 := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hcast, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast, h256]
  push_cast
  rfl

/-- **Group-node binding.** Any fixed compression function, uniform permutation, inverse queries
allowed: a first stage with at most `budget` public queries followed by the replay of at most
`extra` group inputs produces two replayed inputs that differ and share a group digest with
probability at most `(budget + extra)^2 / 2^256`. -/
theorem s6_group_collision_bound (compression : Compression)
    (first : OracleComp World (Option (List (BitVec 1024)))) (budget extra : Nat)
    (bounded : PublicQueryBound first budget) (small : budget ≤ 2 ^ 121) (short : extra ≤ 2 ^ 26) :
    prEvent (GroupCollision <$> (($ᵗ Perm) >>= fun permutation =>
        fixedOracleRun ⟨compression, permutation⟩ (s6GroupSearch first extra))) ≤
      ((budget : ENNReal) + extra) ^ 2 / 2 ^ 256 := by
  rw [perm_sampling_prob, ← s6_bound_of_real]
  apply ENNReal.ofReal_le_ofReal
  let adversary : Strat S3State (List (BitVec 1024)) :=
    (toStrat compression first).bind fun outcome => Strat.done (outcome.getD [])
  have adversaryBound : adversary.QB budget :=
    (Strat.QB.bind (to_strat_QB compression bounded)
      fun outcome => Strat.QB.done (outcome.getD []) 0).mono (by omega)
  have search : toStrat compression (s6GroupSearch first extra) =
      adversary.bind fun items => s6SingleCall.listProbe (items.take extra) := by
    unfold s6GroupSearch
    refine (to_strat_bind compression first _).trans ?_
    refine Eq.trans ?_ (s6_strat_bind_assoc (toStrat compression first)
      (fun outcome => Strat.done (outcome.getD []))
      (fun items => s6SingleCall.listProbe (items.take extra))).symm
    refine congrArg (Strat.bind (toStrat compression first)) (funext fun outcome => ?_)
    cases outcome with
    | none =>
      have empty : s6SingleCall.listProbe (List.take extra ([] : List (BitVec 1024))) =
          Strat.done [] := by rw [List.take_nil]; rfl
      exact empty.symm
    | some items => exact to_strat_probe_groups compression (items.take extra)
  rw [search]
  refine le_trans ?_ (s6_collision_prob_le adversary budget extra adversaryBound small short)
  exact Strat.exp_mono (fun replies _ => ind_mono id) _ _

end CommitGolfCandidate
