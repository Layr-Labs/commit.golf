import CommitGolfCandidate.PairLeafModel
import CommitGolfCandidate.QuartetFinalSharp
import CommitGolfCandidate.QuartetOldFrame

/-!
# Pair-heads hiding: the leaf-shape seeds

The pinned hiding stack (TaggedPinned*, TwoPermutationPinned*, Quartet*) sees the leaf shape only through three
functions: the second-call address `pinnedPrivateSecond`, the first-call address `pinnedFirstAddress` and the digest
tape `pinnedFullLeafDigests`. This module redefines the first two parity-wise in namespace
`TwoPermutationPrototype.Sampling.Quartet.PairH` (where they shadow the originals; the third is replaced by the
frozen `pairFullLeafDigests`) and proves every fact the stack uses about them:

* the word-0 tag `pairPositionTag` of each second call, injective over all leaves (even and odd tags differ);
* salt injectivity of the second-call address (hence the fresh-guess bounds of TaggedPinnedObserver);
* the second-call address depends on the first reply only through its top 1344 bits;
* a second-call address never lies in the quartet node domain (its word 0 is a nonzero tag);
* the digest formula `pairFullLeafDigests p m s i = outputDigest (p (second i (p (first m i)) m_i s_i)))`.

The Planning-level declarations of TaggedPinnedPlanning are copied here unchanged on top of these seeds.
-/

namespace TwoPermutationPrototype.Sampling.Quartet.PairH
open CommitGolf OracleComp MeasureTheory TwoPermutationPrototype.RV64 CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

/-! ## Seeds and their API -/

/-- Word-0 tag of the second call of leaf `index`. -/
def pairPositionTag (index : Index) : BitVec 64 :=
  if index.val % 2 = 0 then evenPositionTag index else pinnedPositionTag index

theorem pair_tag_even {index : Index} (even : index.val % 2 = 0) : pairPositionTag index = evenPositionTag index := by
  unfold pairPositionTag
  exact if_pos even

theorem pair_tag_odd {index : Index} (odd : ¬ index.val % 2 = 0) : pairPositionTag index = pinnedPositionTag index := by
  unfold pairPositionTag
  exact if_neg odd

theorem pair_position_tag_injective : Function.Injective pairPositionTag := by
  intro i j same
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
  · rw [pair_tag_even hi, pair_tag_even hj] at same
    exact even_position_tag_injective same
  · rw [pair_tag_even hi, pair_tag_odd hj] at same
    exact absurd same (even_tag_ne_pinned_tag i j)
  · rw [pair_tag_odd hi, pair_tag_even hj] at same
    exact absurd same.symm (even_tag_ne_pinned_tag j i)
  · rw [pair_tag_odd hi, pair_tag_odd hj] at same
    exact pinned_position_tag_injective same

theorem pair_position_tag_ne_zero (index : Index) : pairPositionTag index ≠ 0 := by
  have range : index.val < 2^24 := index.isLt
  intro zero
  have numerical := congrArg BitVec.toNat zero
  by_cases even : index.val % 2 = 0
  · rw [pair_tag_even even] at numerical
    have fits : 4048 + 256 * index.val < 2^64 := by omega
    simp only [evenPositionTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at numerical
    simp at numerical
  · rw [pair_tag_odd even] at numerical
    have fits : 4152 + 256 * index.val < 2^64 := by omega
    simp only [pinnedPositionTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at numerical
    simp at numerical

/-- Second-call address of leaf `i` (even shape at even positions, pinned shape at odd ones). -/
def pinnedPrivateSecond (i : Index) (reply : Block) (message : Words 32) (salt : BitVec 128) : Block :=
  if i.val % 2 = 0 then packBuffer (evenSecondInput i (saltWords salt) (replyWords reply) message)
  else packBuffer (pinnedSecondInput i (saltWords salt) (replyWords reply) message)

theorem pair_private_even {i : Index} (even : i.val % 2 = 0) (reply : Block) (message : Words 32)
    (salt : BitVec 128) :
    pinnedPrivateSecond i reply message salt = packBuffer (evenSecondInput i (saltWords salt) (replyWords reply) message) := by
  unfold pinnedPrivateSecond
  exact if_pos even

theorem pair_private_odd {i : Index} (odd : ¬ i.val % 2 = 0) (reply : Block) (message : Words 32)
    (salt : BitVec 128) :
    pinnedPrivateSecond i reply message salt = packBuffer (pinnedSecondInput i (saltWords salt) (replyWords reply) message) := by
  unfold pinnedPrivateSecond
  exact if_neg odd

theorem pair_second_tag (i : Index) (reply : Block) (message : Words 32) (salt : BitVec 128) :
    (pinnedPrivateSecond i reply message salt).extractLsb' 0 64 = pairPositionTag i := by
  by_cases even : i.val % 2 = 0
  · rw [pair_private_even even, pair_tag_even even]
    exact even_second_tag i (saltWords salt) reply message
  · rw [pair_private_odd even, pair_tag_odd even]
    exact pinned_second_tag i (saltWords salt) reply message

private theorem pair_salt_words_injective : Function.Injective saltWords := by
  intro left right same
  have low := congrFun same (0 : Fin 2)
  have high := congrFun same (1 : Fin 2)
  change left.extractLsb' 0 64 = right.extractLsb' 0 64 at low
  change left.extractLsb' 64 64 = right.extractLsb' 64 64 at high
  have reconstruct (value : BitVec 128) :
      value.extractLsb' 64 64 ++ value.extractLsb' 0 64 = value :=
    BitVec.extractLsb'_append_extractLsb'
  calc
    left = _ := (reconstruct left).symm
    _ = right.extractLsb' 64 64 ++ right.extractLsb' 0 64 := by rw [low, high]
    _ = right := reconstruct right

theorem pair_private_second_injective (i : Index) (reply : Block) (message : Words 32) :
    Function.Injective (pinnedPrivateSecond i reply message) := by
  intro a b same
  by_cases even : i.val % 2 = 0
  · rw [pair_private_even even, pair_private_even even] at same
    exact pair_salt_words_injective (even_second_input_nonce_injective i reply message same)
  · rw [pair_private_odd even, pair_private_odd even] at same
    exact pair_salt_words_injective (pinned_second_input_nonce_injective i reply message same)

theorem pair_private_second_site (i j : Index) (reply reply' : Block) (message message' : Words 32)
    (salt salt' : BitVec 128) (same : pinnedPrivateSecond i reply message salt = pinnedPrivateSecond j reply' message' salt') :
    i = j :=
  pair_position_tag_injective ((pair_second_tag i reply message salt).symm.trans
    ((congrArg (fun address : Block => address.extractLsb' 0 64) same).trans (pair_second_tag j reply' message' salt')))

private theorem even_chaining_high (index : Index) (nonce : Words 2) (tail : BitVec 1344)
    (low₀ low₁ : BitVec 256) (message : Words 32) :
    evenSecondInput index nonce (replyWords (tail ++ low₀)) message =
      evenSecondInput index nonce (replyWords (tail ++ low₁)) message := by
  funext i
  unfold evenSecondInput
  split
  · rfl
  split
  · let start := 64 * (i.val + 19)
    change (tail ++ low₀).extractLsb' start 64 = (tail ++ low₁).extractLsb' start 64
    have inTail : 256 ≤ start := by dsimp [start]; omega
    exact (BitVec.extractLsb'_append_eq_of_le inTail).trans
      (BitVec.extractLsb'_append_eq_of_le inTail).symm
  · rfl

theorem pair_chaining_preserved (index : Index) (nonce : BitVec 128) (tail : BitVec 1344)
    (low₀ low₁ : BitVec 256) (message : Words 32) :
    pinnedPrivateSecond index (tail ++ low₀) message nonce = pinnedPrivateSecond index (tail ++ low₁) message nonce := by
  by_cases even : index.val % 2 = 0
  · have e0 := pair_private_even even (tail ++ low₀) message nonce
    have e1 := pair_private_even even (tail ++ low₁) message nonce
    exact e0.trans ((congrArg packBuffer
      (even_chaining_high index (saltWords nonce) tail low₀ low₁ message)).trans e1.symm)
  · have e0 := pair_private_odd even (tail ++ low₀) message nonce
    have e1 := pair_private_odd even (tail ++ low₁) message nonce
    exact e0.trans ((congrArg packBuffer
      (pinned_chaining_preserved index (saltWords nonce) tail low₀ low₁ message)).trans e1.symm)

theorem quad_domain_disjoint_private (index : Index) (salt : BitVec 128) (first : Block) (entry : Words 32) :
    pinnedPrivateSecond index first entry salt ∉ quadDomain := by
  rintro ⟨payload, hit⟩
  have zero : (quadEncode payload).extractLsb' 0 64 = 0 := by
    change (payload ++ (0 : BitVec 576)).extractLsb' 0 64 = 0
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 576)]
    decide
  have hit' : quadNodeCall.enc payload = pinnedPrivateSecond index first entry salt := hit
  change (quadNodeCall.enc payload).extractLsb' 0 64 = 0 at zero
  rw [hit'] at zero
  exact pair_position_tag_ne_zero index ((pair_second_tag index first entry salt).symm.trans zero)

/-! ## Fresh-guess bounds (TaggedPinnedObserver, re-proved on the pair seeds) -/

theorem pinned_fixed_salt_guess_le (i : Index) (reply : Block) (message : Words 32) (guess : Block) :
    Pr{let salt ← $ᵗ BitVec 128}[pinnedPrivateSecond i reply message salt = guess] ≤
      (1 : ENNReal)/2^128 := by
  let : MeasurableSpace (BitVec 128) := ⊤
  let event : Set (BitVec 128) := {salt | pinnedPrivateSecond i reply message salt = guess}
  have unique : Function.Injective (pinnedPrivateSecond i reply message) :=
    pair_private_second_injective i reply message
  have size : event.encard ≤ (1 : ℕ∞) := by
    by_cases hit : ∃ salt, pinnedPrivateSecond i reply message salt = guess
    · obtain ⟨key, fits⟩ := hit
      have subset : event ⊆ {key} := fun salt equal => Set.mem_singleton_iff.mpr (unique (equal.trans fits.symm))
      exact (Set.encard_mono subset).trans (by simp)
    · have empty : event = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun salt equal => hit ⟨salt, equal⟩)
      simp [empty]
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Nat.cast_one, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] using
    SampleableType.evalDist_uniformSample_le_of_encard_le event 1 size

noncomputable local instance pairSeedsFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

section Tape
variable {I : Type} [Fintype I] [DecidableEq I]

theorem pinned_fixed_address_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : I → Block) (message : I → Words 32) (guess : Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ i, pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = guess] ≤
      (1 : ENNReal)/2^128 := by
  classical
  let event (i : I) (nonce : I → BitVec 128) := pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = guess
  let selected (i : I) := pairPositionTag (position i) = guess.extractLsb' 0 64
  have implied (i : I) (nonce : I → BitVec 128) (hit : event i nonce) : selected i :=
    (pair_second_tag (position i) (reply i) (message i) (nonce i)).symm.trans
      (congrArg (fun address : Block => address.extractLsb' 0 64) hit)
  by_cases someTag : ∃ i, selected i
  · obtain ⟨j, chosen⟩ := someTag
    refine (prEvent_mono ($ᵗ (I → BitVec 128)) (p := fun nonce => ∃ i, event i nonce)
      (q := event j) ?_).trans ?_
    · rintro nonce ⟨i, hit⟩
      have same := different (pair_position_tag_injective ((implied i nonce hit).trans chosen.symm))
      exact same ▸ hit
    · have sampler := (uniform_tape_coordinate j (fun salt : BitVec 128 => pure salt)).prEvent_eq
        (fun salt => pinnedPrivateSecond (position j) (reply j) (message j) salt = guess)
      rw [bind_pure_comp, prEvent_map, bind_pure] at sampler
      exact sampler.le.trans (pinned_fixed_salt_guess_le (position j) (reply j) (message j) guess)
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun nonce _ ⟨i, hit⟩ => someTag ⟨i, implied i nonce hit⟩)]
    exact zero_le

theorem pinned_known_address_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : I → Block) (message : I → Words 32) (known : List Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ address ∈ known, ∃ i,
      pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = address] ≤
      (known.length : ENNReal)/2^128 := by
  simpa only [mul_one_div] using prEvent_list_le known ($ᵗ (I → BitVec 128))
    (fun guess nonce => ∃ i, pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = guess)
    (1/2^128) (fun guess _ => pinned_fixed_address_hit_le position different reply message guess)

theorem pinned_reused_output_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : I → Block) (message : I → Words 32)
    (latent : Block → Option (BitVec 1344))
    (unique : ∀ a b hi, latent a = some hi → latent b = some hi → a = b)
    (digest : I → BitVec 256) (guess : Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ i,
      (latent (pinnedPrivateSecond (position i) (reply i) (message i) (nonce i))).map
        (fun hi => (hi ++ digest i : Block)) = some guess] ≤ (1 : ENNReal)/2^128 := by
  classical
  let event (nonce : I → BitVec 128) := ∃ i,
    (latent (pinnedPrivateSecond (position i) (reply i) (message i) (nonce i))).map
      (fun hi => (hi ++ digest i : Block)) = some guess
  have tailHit (nonce : I → BitVec 128) : event nonce → ∃ i,
      latent (pinnedPrivateSecond (position i) (reply i) (message i) (nonce i)) =
        some (pinnedOutputTail guess) := by
    rintro ⟨i, found⟩
    let address := pinnedPrivateSecond (position i) (reply i) (message i) (nonce i)
    change (latent address).map (fun hi => (hi ++ digest i : Block)) = some guess at found
    cases eq : latent address with
    | none => simp [eq] at found
    | some hi =>
      have foundEq : (some (hi ++ digest i) : Option Block) = some guess := by
        rw [eq] at found
        exact found
      have output : (hi ++ digest i : Block) = guess := Option.some.inj foundEq
      have split : pinnedOutputTail (hi ++ digest i) = hi := BitVec.extractLsb'_append_eq_left
      exact ⟨i, eq.trans (congrArg Option.some (split.symm.trans (congrArg pinnedOutputTail output)))⟩
  by_cases present : ∃ address, latent address = some (pinnedOutputTail guess)
  · obtain ⟨address, known⟩ := present
    refine (prEvent_mono ($ᵗ (I → BitVec 128)) (p := event)
      (q := fun nonce => ∃ i, pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = address)
      ?_).trans (pinned_fixed_address_hit_le position different reply message address)
    intro nonce hit
    obtain ⟨i, found⟩ := tailHit nonce hit
    exact ⟨i, unique _ _ _ found known⟩
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun nonce _ hit => by
          obtain ⟨i, found⟩ := tailHit nonce hit
          exact present ⟨_, found⟩)]
    exact zero_le

end Tape

/-! ## Planning (TaggedPinnedPlanning, on the pair seeds) -/

/-- First-call address of leaf `index` (value bytes 56..256 at even positions, 0..200 at odd ones). -/
def pinnedFirstAddress (message : Message) (index : Index) : Block :=
  if index.val % 2 = 0 then packBuffer (evenFirstInput (messageWords message index))
  else packBuffer (pinnedFirstInput (messageWords message index))

def pinnedSecondFromHigh (index : Index) (message : Message) (nonce : BitVec 128)
    (upper : BitVec 1344) : Block :=
  pinnedPrivateSecond index (upper ++ (0 : BitVec 256)) (messageWords message index) nonce

theorem pinned_address_from_first_high (index : Index) (message : Message) (nonce : BitVec 128)
    (reply : Block) :
    pinnedPrivateSecond index reply (messageWords message index) nonce =
      pinnedSecondFromHigh index message nonce (pinnedOutputTail reply) := by
  have whole : pinnedOutputTail reply ++ pinnedOutputDigest reply = reply :=
    BitVec.extractLsb'_append_extractLsb'
  have chain := pair_chaining_preserved index nonce (pinnedOutputTail reply) (pinnedOutputDigest reply) 0
    (messageWords message index)
  exact (congrArg (fun first => pinnedPrivateSecond index first (messageWords message index) nonce) whole).symm.trans chain

def pinnedFirstAddresses (left right : Message) : List Block :=
  (List.finRange LENGTH).map (pinnedFirstAddress left) ++
    (List.finRange LENGTH).map (pinnedFirstAddress right)

theorem pinned_first_addresses_length (left right : Message) :
    (pinnedFirstAddresses left right).length = 2 * LENGTH := by
  simp [pinnedFirstAddresses, two_mul]

theorem pinned_first_address_mem (left right : Message) (which : Bool) (i : Index) :
    pinnedFirstAddress (if which then right else left) i ∈ pinnedFirstAddresses left right := by
  cases which <;> simp [pinnedFirstAddresses]

def pinnedPublicAddress (message : Message) (upper : Block → BitVec 1344) (index : Index)
    (nonce : BitVec 128) : Block :=
  pinnedSecondFromHigh index message nonce (upper (pinnedFirstAddress message index))

theorem pinned_public_addresses_site (m m' : Message) (hi hi' : Block → BitVec 1344)
    (i j : Index) (nonce nonce' : BitVec 128)
    (same : pinnedPublicAddress m hi i nonce = pinnedPublicAddress m' hi' j nonce') :
    i = j :=
  pair_private_second_site i j _ _ _ _ nonce nonce' same

noncomputable def pinnedOpenedAddresses (positions : Positions) (message : Message) (upper : Block → BitVec 1344)
    (salts : OpenedSalts positions) : List Block :=
  positions.toList.map (fun i => pinnedPublicAddress message upper i (publicOpenedSalts salts i))

theorem pinned_opened_addresses_length (positions : Positions) (message : Message)
    (upper : Block → BitVec 1344) (salts : OpenedSalts positions) :
    (pinnedOpenedAddresses positions message upper salts).length = positions.card := by
  simp [pinnedOpenedAddresses]

theorem pinned_opened_addresses_agree (positions : Positions) (left right : Message)
    (upper : Block → BitVec 1344) (salts : OpenedSalts positions)
    (agree : ∀ i ∈ positions, left i = right i) :
    pinnedOpenedAddresses positions left upper salts = pinnedOpenedAddresses positions right upper salts := by
  unfold pinnedOpenedAddresses
  apply List.map_congr_left
  intro i included
  have words : messageWords left i = messageWords right i :=
    congrArg (fun entry : Entry => fun word : Fin 32 => entry.extractLsb' (64 * word.val) 64)
      (agree i (Finset.mem_toList.mp included))
  simp only [pinnedPublicAddress, pinnedSecondFromHigh, pinnedFirstAddress, words]

theorem pinned_hidden_from_opened {positions : Positions} (message openedMessage : Message)
    (upper : Block → BitVec 1344) (salts : OpenedSalts positions)
    (i : Index) (hidden : i ∉ positions) (nonce : BitVec 128) :
    pinnedPublicAddress message upper i nonce ∉ pinnedOpenedAddresses positions openedMessage upper salts := by
  intro seen
  obtain ⟨j, present, same⟩ := List.mem_map.mp seen
  have equal := pinned_public_addresses_site _ _ _ _ _ _ _ _ same
  exact hidden (equal ▸ Finset.mem_toList.mp present)

/-- The pair digest tape reads the second call of the first call. -/
theorem pair_full_leaf_digest_formula (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape)
    (i : Index) :
    pairFullLeafDigests p message salts i =
      outputDigest (p.forward (pinnedPrivateSecond i (p.forward (pinnedFirstAddress message i))
        (messageWords message i) (salts i))) := by
  have first : ∀ i : Index, pinnedFirstAddress message i = if i.val % 2 = 0 then
      packBuffer (evenFirstInput (messageWords message i)) else packBuffer (pinnedFirstInput (messageWords message i)) :=
    fun _ => rfl
  change pairLeafDigest p.forward i (saltWords (salts i)) (messageWords message i) = _
  by_cases even : i.val % 2 = 0
  · rw [pair_leaf_even _ _ _ _ even, pair_private_even even, first, if_pos even]
    rfl
  · rw [pair_leaf_odd _ _ _ _ (by omega), pair_private_odd even, first, if_neg even]
    rfl

theorem pinned_leaf_digest_from_high (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) (upper : Block → BitVec 1344) (i : Index)
    (agree : upper (pinnedFirstAddress message i) = pinnedOutputTail (p.forward (pinnedFirstAddress message i))) :
    pairFullLeafDigests p message salts i =
      outputDigest (p.forward (pinnedPublicAddress message upper i (salts i))) := by
  let first := p.forward (pinnedFirstAddress message i)
  have formula := pinned_address_from_first_high i message (salts i) first
  rw [pair_full_leaf_digest_formula]
  exact congrArg (fun addr => outputDigest (p.forward addr))
    (formula.trans (congrArg (pinnedSecondFromHigh i message (salts i)) agree.symm))

end TwoPermutationPrototype.Sampling.Quartet.PairH
