import CommitGolfCandidate.QuadReplay
import CommitGolfCandidate.TaggedPinnedBitLayout
import CommitGolfCandidate.S3Leaf

/-!
# Leaf binding of the K1 leaf (both kinds)

`k1_peer_leaf_layout : PeerLeafLayout`: a pinned leaf collision (two different leaf values at one
position with one digest, all four calls in the replayed table) has probability at most
`q / 2^123` for every fixed compression, `q / 2^124` per leaf kind.

* Salt-first leaves (rank ≠ 0) are the stage-3 pinned two-call hash `s3PinCall` of the record:
  the first window is `v[0..200)`, the second `salt ‖ tag ‖ reply[112..200) ‖ v[168..256)`, so the
  record's peer salt becomes `0^64 ‖ tag ‖ salt` (salt in the low 128 bits).
* A leaves (rank 0) are a second pinned two-call hash `aPinCall` on the same 1600-bit state: the
  first-call input is `v[56..256)`; the pinned part of a first-call state is its bytes `0..72`
  (`v[56..128)`); the chaining value of a reply is its words 18, 19, 21..24 (bytes 144..160 and
  168..200, 384 bits); the second call encodes `(salt ‖ tag, chaining value, pinned part, v[0..56))`
  in the window `reply[144..160) ‖ tag ‖ reply[168..200) ‖ v[0..128) ‖ salt`.
  Counts: digest, chaining and pin fibres are all within `2^1344` (each one fixes 256 bits of
  the state), second-call inputs per chaining slot `2^(192+576+448) = 2^1216`.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling Finset
open TwoPermutationPrototype.RV64
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2100

/-! ### Arithmetic of bit windows -/

private theorem k1_append_nat {a b : Nat} (high : BitVec a) (low : BitVec b) :
    (high ++ low).toNat = high.toNat * 2^b + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

private theorem k1_extract_nat {w : Nat} (x : BitVec w) (start len : Nat) :
    (x.extractLsb' start len).toNat = x.toNat / 2^start % 2^len := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem k1_trunc_digest (reply : Block) :
    s3PinCall.trunc reply = outputDigest reply := by
  change BitVec.ofNat 256 reply.toNat = reply.extractLsb' 0 256
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, k1_extract_nat]
  simp

/-! ### Salt-first leaves: the record's stage-3 layout -/

/-- Peer salt of a salt-first leaf: its 192 low bits are `tag ‖ salt` with the salt lowest. -/
def k1PeerSalt (index : Index) (salt : BitVec 128) : BitVec 256 :=
  (0#64) ++ (pinnedPositionTag index ++ salt)

theorem k1_first_sf (index : Index) (value : Entry) (kind : isAHead index = false) :
    packBuffer (pinnedFirstInput index (entryWords value)) = s3First value := by
  have layout := pinned_pack_first_input_sf (fun _ => value) index kind
  change packBuffer (pinnedFirstInput index (entryWords value)) = value.extractLsb' 0 1600 at layout
  rw [layout]
  apply BitVec.eq_of_toNat_eq
  rw [k1_extract_nat]
  simp [s3First, PERMUTATION_WIDTH]

private theorem k1_add_backwards (salt reply value : Nat) : value + (reply + salt) = salt + reply + value := by
  omega

private theorem k1_top_toNat (high low : Nat) (x : BitVec (high+low)) :
    (x.extractLsb' low high).toNat = x.toNat / 2^low := by
  have fits : x.toNat / 2^low < 2^high := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rw [← Nat.pow_add]
    exact x.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

private theorem k1_padded_nat {w h : Nat} (x : BitVec w) :
    ((0#h) ++ x).toNat % 2^w = x.toNat := by
  rw [k1_append_nat]
  simp only [BitVec.toNat_zero,zero_mul,zero_add,Nat.mod_eq_of_lt x.isLt]

private theorem k1_from_own_nat {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  exact Nat.mod_eq_of_lt x.isLt

private theorem k1_three_windows {h m l : Nat} (high : BitVec h) (mid : BitVec m) (low : BitVec l) :
    high ++ (mid ++ low) = BitVec.ofNat (h+(m+l))
      (low.toNat+mid.toNat*2^l+high.toNat*2^(m+l)) := by
  refine (k1_from_own_nat (high ++ (mid ++ low))).symm.trans ?_
  apply congrArg (BitVec.ofNat _)
  rw [k1_append_nat,k1_append_nat]
  exact k1_add_backwards _ _ _

private theorem k1_assembled_second (value : BitVec 2048) (reply : BitVec 1600) (salt : BitVec 192) :
    value.extractLsb' 1344 704 ++ (reply.extractLsb' 896 704 ++ salt) =
      s3Second ((0#64) ++ salt) reply value := by
  refine (k1_three_windows (value.extractLsb' 1344 704) (reply.extractLsb' 896 704) salt).trans ?_
  unfold s3Second
  apply congrArg (BitVec.ofNat 1600)
  rw [k1_top_toNat 704 1344 value,k1_top_toNat 704 896 reply,k1_padded_nat,show (704 : Nat) + 192 = 896 by decide]
  rfl

theorem k1_second_sf (index : Index) (value : Entry) (nonce : BitVec 128) (reply : Block)
    (kind : isAHead index = false) :
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (entryWords value)) =
      s3Second (k1PeerSalt index nonce) reply value :=
  (pinned_pack_second_input_sf (fun _ => value) index reply nonce kind).trans
    (k1_assembled_second value reply (pinnedPositionTag index ++ nonce))

def k1SaltFirstLayout : SaltFirstPeerLayout where
  salt := k1PeerSalt
  first := k1_first_sf
  second := k1_second_sf

/-! ### A leaves: a second pinned two-call hash -/

/-- Chaining value of a reply in an A window: reply bytes `144..160` and `168..200`. -/
def aChop (o : S3State) : BitVec 128 × BitVec 256 := (o.extractLsb' 1152 128, o.extractLsb' 1344 256)

/-- Pinned part of an A first-call state: its bytes `0..72` (message bytes `56..128`). -/
def aPin (s : S3State) : BitVec 576 := s.extractLsb' 0 576

/-- The A second window `reply[144..160) ‖ tag ‖ reply[168..200) ‖ v[0..56) ‖ v[56..128) ‖ salt`
(low bytes first) for the prefix `(tag, salt)`, chaining value `(low, high)`, pinned part `p` and
message bytes `m = v[0..56)`. -/
def aEnc2 (i : (BitVec 64 × BitVec 128) × (BitVec 128 × BitVec 256) × BitVec 576 × BitVec 448) : S3State :=
  i.1.2 ++ ((i.2.2.1 ++ i.2.2.2) ++ (i.2.1.2 ++ (i.1.1 ++ i.2.1.1)))

theorem a_enc2_injective : Function.Injective aEnc2 := by
  rintro ⟨⟨t, s⟩, ⟨l, h⟩, p, m⟩ ⟨⟨t', s'⟩, ⟨l', h'⟩, p', m'⟩ same
  have e : (s ++ ((p ++ m) ++ (h ++ (t ++ l)))).toNat = (s' ++ ((p' ++ m') ++ (h' ++ (t' ++ l')))).toNat :=
    congrArg BitVec.toNat same
  simp only [k1_append_nat] at e
  simp only [Nat.reduceAdd] at e
  have := t.isLt; have := s.isLt; have := l.isLt; have := h.isLt; have := p.isLt; have := m.isLt
  have := t'.isLt; have := s'.isLt; have := l'.isLt; have := h'.isLt; have := p'.isLt; have := m'.isLt
  have el : l.toNat = l'.toNat := by omega
  have et : t.toNat = t'.toNat := by omega
  have eh : h.toNat = h'.toNat := by omega
  have em : m.toNat = m'.toNat := by omega
  have ep : p.toNat = p'.toNat := by omega
  have es : s.toNat = s'.toNat := by omega
  rw [BitVec.eq_of_toNat_eq el, BitVec.eq_of_toNat_eq et, BitVec.eq_of_toNat_eq eh,
    BitVec.eq_of_toNat_eq em, BitVec.eq_of_toNat_eq ep, BitVec.eq_of_toNat_eq es]

/-- The A leaf hash as a pinned two-call hash. A leaf input is
`(first window v[56..256), (tag, salt), v[0..56))`. -/
def aPinCall : PinCall S3State (BitVec 1600) (BitVec 64 × BitVec 128) (BitVec 128 × BitVec 256) (BitVec 576)
    (BitVec 448) (BitVec 256) where
  enc1 x := x
  enc1_inj := fun _ _ same => same
  pin := aPin
  chop := aChop
  enc2 := aEnc2
  enc2_inj := a_enc2_injective
  trunc := s3PinCall.trunc

/-- The pinned two-call input of an A leaf with value `value` and second-call prefix `r`. -/
def aInput (r : BitVec 64 × BitVec 128) (value : Entry) : BitVec 1600 × (BitVec 64 × BitVec 128) × BitVec 448 :=
  (value.extractLsb' 448 1600, r, value.extractLsb' 0 448)

theorem a_input_ne {r r' : BitVec 64 × BitVec 128} {value value' : Entry} (different : value ≠ value') :
    aInput r value ≠ aInput r' value' := by
  intro same
  apply different
  have hv := s3_entry_lt value
  have hv' := s3_entry_lt value'
  have h1 := congrArg (fun p => p.1.toNat) same
  have h2 := congrArg (fun p => p.2.2.toNat) same
  simp only [aInput, k1_extract_nat, pow_zero, Nat.div_one] at h1 h2
  apply BitVec.eq_of_toNat_eq
  omega

/-- Message bytes `0..128` are `v[0..56)` below the pinned part `v[56..128)` of the first window. -/
theorem a_value_split (value : Entry) :
    value.extractLsb' 0 1024 = aPin (value.extractLsb' 448 1600) ++ value.extractLsb' 0 448 := by
  apply BitVec.eq_of_toNat_eq
  have hv := s3_entry_lt value
  show (value.extractLsb' 0 1024).toNat = (aPin (value.extractLsb' 448 1600) ++ value.extractLsb' 0 448).toNat
  rw [k1_append_nat]
  simp only [aPin, k1_extract_nat, pow_zero, Nat.div_one]
  omega

theorem a_first_eq (index : Index) (value : Entry) (kind : isAHead index = true) :
    packBuffer (pinnedFirstInput index (entryWords value)) = aPinCall.enc1 (value.extractLsb' 448 1600) :=
  pinned_pack_first_input_a (fun _ => value) index kind

theorem a_second_eq (index : Index) (value : Entry) (nonce : BitVec 128) (reply : Block)
    (kind : isAHead index = true) :
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (entryWords value)) =
      aPinCall.enc2 ((pinnedPositionTag index, nonce), aPinCall.chop reply,
        aPinCall.pin (aPinCall.enc1 (value.extractLsb' 448 1600)), value.extractLsb' 0 448) := by
  refine (pinned_pack_second_input_a (fun _ => value) index reply nonce kind).trans ?_
  show nonce ++ (value.extractLsb' 0 1024 ++
    (reply.extractLsb' 1344 256 ++ (pinnedPositionTag index ++ reply.extractLsb' 1152 128))) = _
  rw [a_value_split]
  rfl

/-! ### Counts of the A instance -/

theorem a_chop_fiber (c : BitVec 128 × BitVec 256) :
    (univ.filter fun s : S3State => aPinCall.chop s = c).card ≤ 2^1344 := by
  refine (Finset.card_le_card ?_).trans (s3_pin_fiber c.2)
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  rw [← hs]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 256 (s.toNat / 2^1344)).toNat = (s.extractLsb' 1344 256).toNat
  rw [BitVec.toNat_ofNat, k1_extract_nat]

theorem a_pin_fiber (p : BitVec 576) :
    (univ.filter fun s : S3State => aPinCall.pin s = p).card ≤ 2^1344 := by
  refine (Finset.card_le_card ?_).trans (s3_trunc_fiber (p.extractLsb' 0 256))
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  rw [← hs]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 256 s.toNat).toNat = ((s.extractLsb' 0 576).extractLsb' 0 256).toNat
  simp only [BitVec.toNat_ofNat, k1_extract_nat, pow_zero, Nat.div_one]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 256 ≤ 576))]

theorem a_second_inputs :
    Fintype.card (BitVec 64 × BitVec 128) * Fintype.card (BitVec 576) * Fintype.card (BitVec 448) ≤ 2^1216 := by
  rw [Fintype.card_prod, s3_card_bitvec, s3_card_bitvec, s3_card_bitvec, s3_card_bitvec, ← pow_add, ← pow_add,
    ← pow_add]

/-! ### Extraction: an A leaf collision is a bad event of `aPinCall` -/

private theorem a_stored_evaluation (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (perm : Block → Block) (i : Index) (kind : isAHead i = true)
    (salt : BitVec 128) (value : CommitGolf.Entry)
    (ha : let a := pinnedFirstRow perm i (entryWords value); PublicRow.permutation a.1 a.2 ∈ rows)
    (hb : let a := pinnedFirstRow perm i (entryWords value)
          let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
          PublicRow.permutation b.1 b.2 ∈ rows) :
    let a := pinnedFirstRow perm i (entryWords value)
    let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
    aPinCall.Evaluates t (aInput (pinnedPositionTag i, salt) value) (outputDigest b.2) := by
  let a := pinnedFirstRow perm i (entryWords value)
  let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
  obtain ⟨e,he,ein,eout⟩ := stored a.1 a.2 ha
  obtain ⟨f,hf,fin,fout⟩ := stored b.1 b.2 hb
  have first : e.inp = aPinCall.enc1 (aInput (pinnedPositionTag i, salt) value).1 :=
    ein.trans (a_first_eq i value kind)
  refine ⟨e,he,f,hf,first,?_,?_⟩
  · rw [eout,first]
    exact fin.trans (a_second_eq i value salt a.2 kind)
  · exact (congrArg s3PinCall.trunc fout).trans (k1_trunc_digest b.2)

theorem pinned_witness_bad_a (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (hit : PinnedLeafWitnessOf true rows) : ¬ aPinCall.badSpec.Good t := by
  obtain ⟨perm,i,n,m,v,w,kind,a₀,a₁,b₀,b₁,digest,conflict⟩ := hit
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
  have left := a_stored_evaluation t rows stored perm i kind salt₀ value₀ a₀ b₀
  have right := a_stored_evaluation t rows stored perm i kind salt₁ value₁ a₁ b₁
  refine aPinCall.collision_imp_bad (a_input_ne (r := (pinnedPositionTag i, salt₀))
    (r' := (pinnedPositionTag i, salt₁)) distinct) left ?_
  exact digest.symm ▸ right

/-! ### The probability bounds -/

theorem fixed_compression_pinned_leaf_bound_a {α : Type}
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitnessOf true result.2] ≤ (q : ENNReal)/2^124 := by
  refine fixed_compression_witness_bound compress program (PinnedLeafWitnessOf true) aPinCall.badSpec q calls
    bounded pinned_witness_bad_a ?_
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have fits : calls < Fintype.card S3State := by rw [s3_card_state]; omega
  have raw := aPinCall.prob_bad_le_inv (2^1344) (2^1344) (2^1344) (2^1216) (2^1346)
    calls fits s3_trunc_fiber a_chop_fiber a_pin_fiber a_second_inputs (by norm_num) (by norm_num)
    st calls budget.toIQB
  refine raw.trans ?_
  rw [s3_card_state]
  have margin := replay_extra_margin q calls (2^1346) (2^1216) positive small replayed (by norm_num) (by norm_num)
  norm_num [unionBound] at margin ⊢
  exact margin

theorem k1_pinned_leaf_bound {α : Type}
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitness result.2] ≤ (q : ENNReal)/2^123 := by
  let execution := (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))
  change Pr{let result ← execution}[PinnedLeafWitness result.2] ≤ _
  have split := prEvent_mono execution (fun result => PinnedLeafWitness result.2)
    (fun result => PinnedLeafWitnessOf false result.2 ∨ PinnedLeafWitnessOf true result.2)
    (fun _ hit => pinned_leaf_witness_split hit)
  refine split.trans ((prEvent_or_le execution (fun result => PinnedLeafWitnessOf false result.2)
    (fun result => PinnedLeafWitnessOf true result.2)).trans ?_)
  have sf := fixed_compression_pinned_leaf_bound_sf k1SaltFirstLayout compress program q calls positive small
    replayed bounded
  have a := fixed_compression_pinned_leaf_bound_a compress program q calls positive small replayed bounded
  refine (add_le_add sf a).trans_eq ?_
  rw [← ENNReal.add_div, ← two_mul,
    show (2 : ENNReal)^124 = 2 * 2^123 by rw [show (124 : Nat) = 1+123 by decide, pow_add]; norm_num]
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

/-- Leaf binding of the K1 leaf, both kinds. -/
theorem k1_peer_leaf_layout : PeerLeafLayout :=
  ⟨fun compress program q calls positive small replayed bounded =>
    k1_pinned_leaf_bound compress program q calls positive small replayed bounded⟩

/-- The pinned replay bound (compression witnesses and K1 leaf collisions) from a leaf layout. -/
theorem pinned_replay_bound_of_k1_layout (layout : PeerLeafLayout) : PinnedReplayBound := by
  intro program q calls positive small replayed bounded
  unfold PinnedReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans_eq (event_budget_sum q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress,perm⟩ (recordRows program)))
    simp only [Oracle.sample,bind_assoc,pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small replayed bounded
  · simp only [Oracle.sample,bind_assoc,pure_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      (layout.bound compress program q calls positive small replayed bounded).trans ?_
    exact ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _

/-- The K1 pinned replay bound. -/
theorem k1_pinned_replay_bound : PinnedReplayBound :=
  pinned_replay_bound_of_k1_layout k1_peer_leaf_layout

end TwoPermutationPrototype.Sampling
