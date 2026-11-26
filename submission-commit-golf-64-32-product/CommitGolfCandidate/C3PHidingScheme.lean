import CommitGolfCandidate.C3PLeafModel
import CommitGolfCandidate.MirrorHidingScheme

/-! # Hiding for the paired 3c1p leaf

The machine side proves `C3PTranscriptRefines packedSubmission.scheme Hybrid.builder`: the honest
commitment and proof are `c3pHonestView` of a uniform `CompleteSaltTape`. This module turns that
into the contract's hiding bound.

The paired leaf is a `Mirror.MirrorLayout` (`c3pLayout`): even leaves keep their tag in word 21
and their salt in words 23 and 24, odd leaves keep their tag in word 2 and their salt in words 0
and 1, and in both layouts the other layout's salt words hold entry words (`c3p_salt_foreign`).
An even reply splits into its top 256 bits and the rest, an odd reply into its low 256 bits and
the rest. `c3pHonestView` is `Mirror.mirrorView c3pLayout` (`c3p_view_eq`), so the theorem is
`Mirror.scheme_hiding_of_mirror_transcript`.

What the mirrored layout costs against the unpaired leaf is in the `MirrorHiding*` modules: a
query can name one leaf of each side (`Mirror.fixed_reference_hit_le`), and honest inputs of
different sides can coincide (`Mirror.hidden_inputs_repeat_le`,
`Mirror.opened_hidden_coincide_le`). The distance is at most
`4t(2/2^128 + 2^24/2^1344) + 2·2^24(t + 2^24)/2^1600 + 4·2^48/2^256`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option autoImplicit false

/-- The layout of a position: `false` for even leaves, `true` for odd leaves. -/
def c3pSide (index : Index) : Bool := !decide (c3pEven index)

/-- The tag word of each layout: word 21 for even leaves, word 2 for odd leaves. -/
def c3pTagField (odd : Bool) (input : Block) : BitVec 64 :=
  if odd then input.extractLsb' (64 * 2) 64 else input.extractLsb' (64 * 21) 64

/-- The salt words of each layout: words 23 and 24 for even leaves, words 0 and 1 for odd ones. -/
def c3pSaltField (odd : Bool) (input : Block) : BitVec 128 :=
  if odd then input.extractLsb' (64 * 1) 64 ++ input.extractLsb' (64 * 0) 64
  else input.extractLsb' (64 * 24) 64 ++ input.extractLsb' (64 * 23) 64

/-- An even reply: its top 256 bits are the digest. -/
def c3pEvenSplit : Block ≃ BitVec 256 × BitVec 1344 where
  toFun reply := (c3pEvenDigest reply, reply.extractLsb' 0 1344)
  invFun pair := pair.1 ++ pair.2
  left_inv reply := by
    change reply.extractLsb' 1344 256 ++ reply.extractLsb' 0 1344 = reply
    exact BitVec.extractLsb'_append_extractLsb'
  right_inv pair := by
    obtain ⟨digest, tail⟩ := pair
    change ((digest ++ tail).extractLsb' 1344 256, (digest ++ tail).extractLsb' 0 1344) = (digest, tail)
    rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

/-- An odd reply: its low 256 bits are the digest. -/
def c3pOddSplit : Block ≃ BitVec 256 × BitVec 1344 where
  toFun reply := (outputDigest reply, reply.extractLsb' 256 1344)
  invFun pair := pair.2 ++ pair.1
  left_inv reply := by
    change reply.extractLsb' 256 1344 ++ reply.extractLsb' 0 256 = reply
    exact BitVec.extractLsb'_append_extractLsb'
  right_inv pair := by
    obtain ⟨digest, tail⟩ := pair
    change ((tail ++ digest).extractLsb' 0 256, (tail ++ digest).extractLsb' 256 1344) = (digest, tail)
    rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

def c3pSplit (index : Index) : Block ≃ BitVec 256 × BitVec 1344 :=
  if c3pEven index then c3pEvenSplit else c3pOddSplit

theorem c3p_split_digest (index : Index) (reply : Block) :
    (c3pSplit index reply).1 = c3pDigestWindow index reply := by
  unfold c3pSplit c3pDigestWindow
  split <;> rfl

theorem c3p_side_even {index : Index} (even : c3pEven index) : c3pSide index = false := by
  simp [c3pSide, even]

theorem c3p_side_odd {index : Index} (odd : ¬ c3pEven index) : c3pSide index = true := by
  simp [c3pSide, odd]

theorem c3p_salt_words (salt : BitVec 128) :
    saltWords salt (1 : Fin 2) ++ saltWords salt (0 : Fin 2) = salt := by
  change salt.extractLsb' 64 64 ++ salt.extractLsb' 0 64 = salt
  exact BitVec.extractLsb'_append_extractLsb'

/-! ### The windows of a packed input, by words -/

theorem c3p_tag_field_even_words (words : Words 25) :
    c3pTagField false (packBuffer words) = words ⟨21, by decide⟩ :=
  packed_word words ⟨21, by decide⟩

theorem c3p_tag_field_odd_words (words : Words 25) :
    c3pTagField true (packBuffer words) = words ⟨2, by decide⟩ :=
  packed_word words ⟨2, by decide⟩

theorem c3p_salt_field_even_words (words : Words 25) :
    c3pSaltField false (packBuffer words) = words ⟨24, by decide⟩ ++ words ⟨23, by decide⟩ :=
  congrArg₂ (fun high low : BitVec 64 => high ++ low) (packed_word words ⟨24, by decide⟩)
    (packed_word words ⟨23, by decide⟩)

theorem c3p_salt_field_odd_words (words : Words 25) :
    c3pSaltField true (packBuffer words) = words ⟨1, by decide⟩ ++ words ⟨0, by decide⟩ :=
  congrArg₂ (fun high low : BitVec 64 => high ++ low) (packed_word words ⟨1, by decide⟩)
    (packed_word words ⟨0, by decide⟩)

/-! ### The words of the two layouts -/

theorem c3p_even_tag_word (compress : Compression) (index : Index) (even : c3pEven index)
    (nonce : Words 2) (v : Words 32) :
    c3pPermWords compress index nonce v ⟨21, by decide⟩ = c3pTag index := by
  simp only [c3pPermWords, even, ite_true, c3pEvenWords, show ¬ (21 < 17) by decide,
    show ¬ (21 < 21) by decide, dite_false]

theorem c3p_odd_tag_word (compress : Compression) (index : Index) (odd : ¬ c3pEven index)
    (nonce : Words 2) (v : Words 32) :
    c3pPermWords compress index nonce v ⟨2, by decide⟩ = c3pTag index := by
  simp only [c3pPermWords, odd, ite_false, c3pOddWords, show ¬ (2 < 2) by decide, dite_false, ite_true]

theorem c3p_even_salt_words (compress : Compression) (index : Index) (even : c3pEven index)
    (nonce : Words 2) (v : Words 32) :
    c3pPermWords compress index nonce v ⟨24, by decide⟩ = nonce 1 ∧
      c3pPermWords compress index nonce v ⟨23, by decide⟩ = nonce 0 := by
  constructor
  · simp only [c3pPermWords, even, ite_true, c3pEvenWords, show ¬ (24 < 17) by decide,
      show ¬ (24 < 21) by decide, show ¬ (24 = 21) by decide, show ¬ (24 = 22) by decide,
      dite_false, ite_false]
    rfl
  · simp only [c3pPermWords, even, ite_true, c3pEvenWords, show ¬ (23 < 17) by decide,
      show ¬ (23 < 21) by decide, show ¬ (23 = 21) by decide, show ¬ (23 = 22) by decide,
      dite_false, ite_false]
    rfl

theorem c3p_odd_salt_words (compress : Compression) (index : Index) (odd : ¬ c3pEven index)
    (nonce : Words 2) (v : Words 32) :
    c3pPermWords compress index nonce v ⟨1, by decide⟩ = nonce 1 ∧
      c3pPermWords compress index nonce v ⟨0, by decide⟩ = nonce 0 := by
  constructor
  · simp only [c3pPermWords, odd, ite_false, c3pOddWords, show (1 < 2) by decide, dite_true]
    rfl
  · simp only [c3pPermWords, odd, ite_false, c3pOddWords, show (0 < 2) by decide, dite_true]
    rfl

/-- In an even input the odd layout's salt words hold entry words 8 and 7. -/
theorem c3p_even_other_words (compress : Compression) (index : Index) (even : c3pEven index)
    (nonce : Words 2) (v : Words 32) :
    c3pPermWords compress index nonce v ⟨1, by decide⟩ = v ⟨8, by decide⟩ ∧
      c3pPermWords compress index nonce v ⟨0, by decide⟩ = v ⟨7, by decide⟩ := by
  constructor
  · simp only [c3pPermWords, even, ite_true, c3pEvenWords, show (1 < 17) by decide, dite_true]
  · simp only [c3pPermWords, even, ite_true, c3pEvenWords, show (0 < 17) by decide, dite_true]

/-- In an odd input the even layout's salt words hold entry words 24 and 23. -/
theorem c3p_odd_other_words (compress : Compression) (index : Index) (odd : ¬ c3pEven index)
    (nonce : Words 2) (v : Words 32) :
    c3pPermWords compress index nonce v ⟨24, by decide⟩ = v ⟨24, by decide⟩ ∧
      c3pPermWords compress index nonce v ⟨23, by decide⟩ = v ⟨23, by decide⟩ := by
  constructor
  · simp only [c3pPermWords, odd, ite_false, c3pOddWords, show ¬ (24 < 2) by decide,
      show ¬ (24 = 2) by decide, show ¬ (24 = 3) by decide, show ¬ (24 < 8) by decide,
      dite_false, ite_false]
  · simp only [c3pPermWords, odd, ite_false, c3pOddWords, show ¬ (23 < 2) by decide,
      show ¬ (23 = 2) by decide, show ¬ (23 = 3) by decide, show ¬ (23 < 8) by decide,
      dite_false, ite_false]

/-! ### The laws of the layout -/

theorem c3p_tag_input (compress : Compression) (index : Index) (message : Words 32) (salt : BitVec 128) :
    c3pTagField (c3pSide index) (c3pPermInput compress index (saltWords salt) message) = c3pTag index := by
  by_cases even : c3pEven index
  · rw [c3p_side_even even]
    exact (c3p_tag_field_even_words _).trans (c3p_even_tag_word compress index even _ _)
  · rw [c3p_side_odd even]
    exact (c3p_tag_field_odd_words _).trans (c3p_odd_tag_word compress index even _ _)

theorem c3p_salt_input (compress : Compression) (index : Index) (message : Words 32) (salt : BitVec 128) :
    c3pSaltField (c3pSide index) (c3pPermInput compress index (saltWords salt) message) = salt := by
  by_cases even : c3pEven index
  · obtain ⟨high, low⟩ := c3p_even_salt_words compress index even (saltWords salt) message
    rw [c3p_side_even even]
    refine (c3p_salt_field_even_words _).trans ?_
    rw [high, low]
    exact c3p_salt_words salt
  · obtain ⟨high, low⟩ := c3p_odd_salt_words compress index even (saltWords salt) message
    rw [c3p_side_odd even]
    refine (c3p_salt_field_odd_words _).trans ?_
    rw [high, low]
    exact c3p_salt_words salt

theorem c3p_salt_foreign (compress : Compression) (index : Index) (message : Words 32)
    (salt salt' : BitVec 128) :
    c3pSaltField (!c3pSide index) (c3pPermInput compress index (saltWords salt) message) =
      c3pSaltField (!c3pSide index) (c3pPermInput compress index (saltWords salt') message) := by
  by_cases even : c3pEven index
  · obtain ⟨high, low⟩ := c3p_even_other_words compress index even (saltWords salt) message
    obtain ⟨high', low'⟩ := c3p_even_other_words compress index even (saltWords salt') message
    rw [c3p_side_even even, Bool.not_false]
    refine (c3p_salt_field_odd_words _).trans ((c3p_salt_field_odd_words _).trans ?_).symm
    rw [high, low, high', low']
  · obtain ⟨high, low⟩ := c3p_odd_other_words compress index even (saltWords salt) message
    obtain ⟨high', low'⟩ := c3p_odd_other_words compress index even (saltWords salt') message
    rw [c3p_side_odd even, Bool.not_true]
    refine (c3p_salt_field_even_words _).trans ((c3p_salt_field_even_words _).trans ?_).symm
    rw [high, low, high', low']

/-- The paired 3c1p leaf as a mirrored layout. -/
def c3pLayout : Mirror.MirrorLayout where
  input compress index message salt := c3pPermInput compress index (saltWords salt) message
  side := c3pSide
  tagField := c3pTagField
  tag := c3pTag
  saltField := c3pSaltField
  split := c3pSplit
  tag_injective := fun _ _ _ same => c3p_tag_injective same
  tag_input := c3p_tag_input
  salt_input := c3p_salt_input
  salt_foreign := c3p_salt_foreign

/-- The honest view of the paired leaf is the view of its layout. -/
theorem c3p_view_eq (build : TranscriptBuilder) :
    c3pHonestView build = Mirror.mirrorView c3pLayout build := by
  have digests (compress : Compression) (p : BiPermutation Block) (message : Message)
      (salts : CompleteSaltTape) :
      c3pFullLeafDigests compress p message salts =
        Mirror.fullLeafDigests c3pLayout compress p message salts := by
    funext index
    exact (c3p_split_digest index _).symm
  funext compress p message positions salts
  unfold c3pHonestView Mirror.mirrorView
  rw [digests]

/-- **The contract's hiding clause for the paired 3c1p transcript.** -/
theorem scheme_hiding_of_c3p_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : C3PTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply Mirror.scheme_hiding_of_mirror_transcript c3pLayout scheme build
  rw [← c3p_view_eq]
  exact refines

end TwoPermutationPrototype.Sampling
