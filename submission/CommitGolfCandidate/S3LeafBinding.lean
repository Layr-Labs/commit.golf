import CommitGolfCandidate.S3LeafGame
import CommitGolfCandidate.S3LeafProbe
import CommitGolfCandidate.S3PermBridge
import CommitGolfCandidate.S6Tree

/-!
# Leaf binding of the leaf hash, in the contract's oracle world

Glue between the lazy-permutation collision bound (`s3_collision_prob_le`, S3LeafGame.lean) and
the eager experiment of the contract (`perm_sampling_prob`, S3PermBridge.lean): for every fixed
compression function and a uniformly sampled permutation with forward and inverse queries, a
first stage with at most `budget` public queries followed by the replay of at most `extra` leaves
produces two replayed leaves with different values and one digest with probability at most
`(budget + 2 extra)^2 / 2^256 + budget / 2^127`.

The last section writes the two windows of a tagged leaf (`expandTagged`) with the salt first:
the first window is `nonce + x 2^128` with `x` = tag and leaf bytes 0..176, the second is
`chaining value + m 2^512` with `m` = leaf bytes 120..256; bits 128..192 of the first window hold
the tag, and the same bits of a group-call window are zero.
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation.Strat

variable {S : Type} {α β γ : Type}

theorem s3_strat_bind_assoc (st : Strat S α) (f : α → Strat S β) (g : β → Strat S γ) :
    (st.bind f).bind g = st.bind fun a => (f a).bind g := by
  induction st with
  | done a => rfl
  | fwd x k ih => simp only [Strat.bind, ih]
  | inv y k ih => simp only [Strat.bind, ih]
  | rand n k ih => simp only [Strat.bind, ih]

end CommitGolfCandidate.Permutation.Strat

namespace CommitGolfCandidate

open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation

/-- The two-call input of a leaf `(salt, value)`: the first window (the low 24 salt bytes, leaf
bytes 0..176), no salt in the second call, leaf bytes 120..256. The top 8 bytes of the salt are
ignored. -/
def s3Input (leaf : BitVec 256 × Entry) : S3LeafInput :=
  (BitVec.ofNat 1600 (leaf.1.toNat % 2 ^ 192 + (leaf.2.toNat % 2 ^ 1408) * 2 ^ 192), (),
    BitVec.ofNat 1088 (leaf.2.toNat / 2 ^ 960))

theorem s3_entry_lt (value : Entry) : value.toNat < 2 ^ 2048 := value.isLt

/-- Every leaf input repeats leaf bytes 120..176 in both calls. -/
theorem s3_input_consistent (leaf : BitVec 256 × Entry) : s3Overlap.Consistent (s3Input leaf) := by
  intro c
  have hvalue := s3_entry_lt leaf.2
  have hc : c.toNat < 2 ^ 512 := c.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [s3Overlap, s3TwoCall, s3Input, BitVec.toNat_ofNat]
  omega

/-- The first window, with literal widths. -/
theorem s3_first_core (salt : BitVec 256) (value : BitVec 2048) :
    (BitVec.ofNat 1600 (salt.toNat % 2 ^ 192 + (value.toNat % 2 ^ 1408) * 2 ^ 192) : S3State) =
      s3TwoCall.enc1
        (BitVec.ofNat 1600 (salt.toNat % 2 ^ 192 + (value.toNat % 2 ^ 1408) * 2 ^ 192)) :=
  rfl

/-- The second window, with literal widths. -/
theorem s3_second_core (reply : S3State) (value : BitVec 2048) :
    (BitVec.ofNat 1600 (reply.toNat / 2 ^ 1088 + value.toNat / 2 ^ 960 * 2 ^ 512) : S3State) =
      s3TwoCall.enc2 ((), s3TwoCall.chop reply, BitVec.ofNat 1088 (value.toNat / 2 ^ 960)) := by
  have hreply : reply.toNat < 2 ^ 1600 := reply.isLt
  have hvalue : value.toNat < 2 ^ 2048 := value.isLt
  have h1 : reply.toNat / 2 ^ 1088 % 2 ^ 512 = reply.toNat / 2 ^ 1088 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hreply))
  have h2 : value.toNat / 2 ^ 960 % 2 ^ 1088 = value.toNat / 2 ^ 960 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hvalue))
  simp only [s3TwoCall, BitVec.toNat_ofNat, h1, h2]

theorem s3_first_eq (leaf : BitVec 256 × Entry) :
    s3First leaf.1 leaf.2 = s3TwoCall.enc1 (s3Input leaf).1 :=
  s3_first_core leaf.1 leaf.2

theorem s3_second_eq (leaf : BitVec 256 × Entry) (reply : S3State) :
    s3Second reply leaf.2 =
      s3TwoCall.enc2 ((s3Input leaf).2.1, s3TwoCall.chop reply, (s3Input leaf).2.2) :=
  s3_second_core reply leaf.2

theorem s3_trunc_eq (reply : S3State) :
    s3TwoCall.trunc reply = BitVec.ofNat 256 reply.toNat := rfl

/-- The digest is the two-call hash of the leaf input. -/
theorem s3_leaf_digest_eq (permutation : Perm) (leaf : BitVec 256 × Entry) :
    s3LeafDigest permutation leaf.1 leaf.2 =
      s3TwoCall.trunc (permutation (s3TwoCall.enc2 ((s3Input leaf).2.1,
        s3TwoCall.chop (permutation (s3TwoCall.enc1 (s3Input leaf).1)), (s3Input leaf).2.2))) := by
  have h1 := s3_first_eq leaf
  have h2 := s3_second_eq leaf (permutation (s3TwoCall.enc1 (s3Input leaf).1))
  unfold s3LeafDigest
  rw [h1, h2]
  rfl

/-- Different leaf values give different two-call inputs, whatever the salts: a value is
determined by its bytes 0..176 and 120..256. -/
theorem s3_input_ne {leaf leaf' : BitVec 256 × Entry} (h : leaf.2 ≠ leaf'.2) :
    s3Input leaf ≠ s3Input leaf' := by
  intro heq
  apply h
  have hvalue := s3_entry_lt leaf.2
  have hvalue' := s3_entry_lt leaf'.2
  have h1 := congrArg (fun p => p.1.toNat) heq
  have h2 := congrArg (fun p => p.2.2.toNat) heq
  simp only [s3Input, BitVec.toNat_ofNat] at h1 h2
  apply BitVec.eq_of_toNat_eq
  omega

/-- The leaf hash program is the two-call evaluation strategy. -/
theorem to_strat_hash_leaf (compression : Compression) (salt : BitVec 256) (value : Entry) :
    toStrat compression (s3HashLeaf salt value) = s3TwoCall.eval (s3Input (salt, value)) := by
  have raw : toStrat compression (s3HashLeaf salt value) =
      Strat.fwd (s3First salt value) fun first =>
        Strat.fwd (s3Second first value) fun second =>
          Strat.done (BitVec.ofNat 256 second.toNat) := by
    unfold s3HashLeaf
    erw [to_strat_permute]
    rfl
  have inner : ∀ first : S3State,
      (Strat.fwd (s3Second first value) fun second =>
        Strat.done (BitVec.ofNat 256 second.toNat) : Strat S3State (BitVec 256)) =
      Strat.fwd (s3TwoCall.enc2 ((s3Input (salt, value)).2.1, s3TwoCall.chop first,
        (s3Input (salt, value)).2.2)) fun second => Strat.done (s3TwoCall.trunc second) :=
    fun first => congrArg (fun input : S3State => Strat.fwd input fun second =>
      Strat.done (s3TwoCall.trunc second)) (s3_second_eq (salt, value) first)
  exact raw.trans (congrArg₂ Strat.fwd (s3_first_eq (salt, value)) (funext inner))

/-- The replay program is the list evaluation strategy. -/
theorem to_strat_probe_leaves (compression : Compression) (items : List (BitVec 256 × Entry)) :
    toStrat compression (probeLeaves items) = s3EvalList s3Input items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [probeLeaves, s3EvalList]
    rw [to_strat_bind, to_strat_hash_leaf]
    congr 1
    funext digest
    rw [to_strat_bind, ih]
    rfl

theorem s3_bound_of_real (budget extra : Nat) :
    ENNReal.ofReal (((budget : ℝ) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ℝ) / 2 ^ 127) =
      ((budget : ENNReal) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ENNReal) / 2 ^ 127 := by
  have hcast : (budget : ℝ) + 2 * extra = ((budget + 2 * extra : ℕ) : ℝ) := by push_cast; ring
  have h256 : ENNReal.ofReal ((2 : ℝ) ^ 256) = 2 ^ 256 := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have h127 : ENNReal.ofReal ((2 : ℝ) ^ 127) = 2 ^ 127 := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hcast, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    h256, h127]
  push_cast
  rfl

/-- **Leaf binding.** Any fixed compression function, uniform permutation, inverse queries
allowed. -/
theorem s3_leaf_collision_bound (compression : Compression)
    (first : OracleComp World (Option (List (BitVec 256 × Entry)))) (budget extra : Nat)
    (bounded : PublicQueryBound first budget) (small : budget ≤ 2 ^ 120) (short : extra ≤ 2 ^ 26) :
    prEvent (LeafCollision <$> (($ᵗ Perm) >>= fun permutation =>
        fixedOracleRun ⟨compression, permutation⟩ (s3LeafSearch first extra))) ≤
      ((budget : ENNReal) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ENNReal) / 2 ^ 127 := by
  rw [perm_sampling_prob, ← s3_bound_of_real]
  apply ENNReal.ofReal_le_ofReal
  let adversary : Strat S3State (List (BitVec 256 × Entry)) :=
    (toStrat compression first).bind fun outcome => Strat.done (outcome.getD [])
  have adversaryBound : adversary.QB budget :=
    (Strat.QB.bind (to_strat_QB compression bounded)
      fun outcome => Strat.QB.done (outcome.getD []) 0).mono (by omega)
  have search : toStrat compression (s3LeafSearch first extra) =
      adversary.bind fun items => s3EvalList s3Input (items.take extra) := by
    unfold s3LeafSearch
    refine (to_strat_bind compression first _).trans ?_
    refine Eq.trans ?_ (Strat.s3_strat_bind_assoc (toStrat compression first)
      (fun outcome => Strat.done (outcome.getD []))
      (fun items => s3EvalList s3Input (items.take extra))).symm
    refine congrArg (Strat.bind (toStrat compression first)) (funext fun outcome => ?_)
    cases outcome with
    | none =>
      have empty : s3EvalList s3Input (List.take extra ([] : List (BitVec 256 × Entry))) =
          Strat.done [] := by rw [List.take_nil]; rfl
      exact empty.symm
    | some items => exact to_strat_probe_leaves compression (items.take extra)
  rw [search]
  refine le_trans ?_ (s3_collision_prob_le s3Input s3_input_consistent adversary budget extra
    adversaryBound small short)
  refine Strat.exp_mono (fun replies _ => ind_mono ?_) _ _
  rintro ⟨a, ha, b, hb, hne, heq⟩
  exact ⟨a, ha, b, hb, s3_input_ne hne, heq⟩

/-! ### Tagged leaves, salt first -/

/-- The first-call part of a tagged leaf after its nonce: the tag, then leaf bytes 0..176. -/
def s5LeafX (index : Index) (value : Entry) : BitVec 1472 :=
  BitVec.ofNat 1472 (s6Tag index + (value.toNat % 2 ^ 1408) * 2 ^ 64)

/-- The second message part of a leaf: leaf bytes 120..256. -/
def s5LeafM (value : Entry) : BitVec 1088 := BitVec.ofNat 1088 (value.toNat / 2 ^ 960)

theorem s5_index_lt (index : Index) : index.val < 2 ^ 24 := index.isLt

/-- The low 64 bits of `s5LeafX` are the tag. -/
theorem s5_leaf_x_tag (index : Index) (value : Entry) :
    (s5LeafX index value).toNat % 2 ^ 64 = s6Tag index := by
  have hi := s5_index_lt index
  have hvalue := s3_entry_lt value
  simp only [s5LeafX, s6Tag, BitVec.toNat_ofNat]
  omega

/-- Leaves with different indices have different `s5LeafX`. -/
theorem s5_leaf_x_index {index index' : Index} {value value' : Entry}
    (h : s5LeafX index value = s5LeafX index' value') : index = index' := by
  have e := congrArg (fun x : BitVec 1472 => x.toNat % 2 ^ 64) h
  simp only [s5_leaf_x_tag, s6Tag] at e
  exact Fin.ext (by omega)

/-- The first window of a tagged leaf: the nonce, then `s5LeafX`. -/
theorem s5_first_window (index : Index) (nonce : BitVec 128) (value : Entry) :
    s3First (expandTagged index nonce) value =
      BitVec.ofNat 1600 (nonce.toNat + (s5LeafX index value).toNat * 2 ^ 128) := by
  have hi := s5_index_lt index
  have hn := nonce.isLt
  have hvalue := s3_entry_lt value
  apply BitVec.eq_of_toNat_eq
  simp only [s3First, expandTagged, s6Tag, s5LeafX, BitVec.toNat_ofNat, PERMUTATION_WIDTH]
  omega

/-- The second window of a leaf: the chaining value of the first reply, then `s5LeafM`. -/
theorem s5_second_window (reply : S3State) (value : Entry) :
    s3Second reply value =
      BitVec.ofNat 1600 ((s3TwoCall.chop reply).toNat + (s5LeafM value).toNat * 2 ^ 512) :=
  s3_second_core reply value

/-- Bits 128..192 of the first window of a tagged leaf hold its tag. -/
theorem s5_first_tag (index : Index) (nonce : BitVec 128) (value : Entry) :
    (s3First (expandTagged index nonce) value).toNat / 2 ^ 128 % 2 ^ 64 = s6Tag index := by
  have hi := s5_index_lt index
  have hn := nonce.isLt
  have hvalue := s3_entry_lt value
  simp only [s3First, expandTagged, s6Tag, BitVec.toNat_ofNat, PERMUTATION_WIDTH]
  omega

/-- Bits 128..192 of a group-call window (72 zero bytes, then four digests) are zero. -/
theorem s6_group_input_tag (d0 d1 d2 d3 : BitVec 256) :
    (s6GroupInput d0 d1 d2 d3).toNat / 2 ^ 128 % 2 ^ 64 = 0 := by
  simp only [s6GroupInput, BitVec.toNat_ofNat, PERMUTATION_WIDTH]
  omega

end CommitGolfCandidate
