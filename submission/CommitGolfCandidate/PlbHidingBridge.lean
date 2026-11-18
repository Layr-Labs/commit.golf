import CommitGolfCandidate.TwoPermutationOpeningTranscript
import CommitGolfCandidate.OverlapInputs
import CommitGolfCandidate.PermLean.HidingSwap

/-! # Hiding with the overlap leaf

The overlap leaf of position `i` with salt `s` and value words `m`: `X = 0^8 ‖ m[0..192)` (unsalted,
untagged), `W = tag(i) ‖ P(X)[168..200) ‖ s ‖ m[112..256)`, digest `P(W)[0..32)`.

The proof is the swap coupling of `PermLean/HidingSwap.lean` (`HSwap.scheme_hiding_digest`). Its
remaining hypotheses are discharged here against the reference transcript of this tree:

* the salt layout `plbSaltLayout`: tags `secondTag i = 4152 + 256 i` in word 0 of `W` (word 0 of `X`
  is zero, which is no tag), the salt in words 5..6 of `W`, the swapped positions are the unopened
  positions where the two messages differ;
* uniform 128-bit salts over `2^24` positions (`sampleCompleteSaltTape`);
* the view `plbView`: the reference transcript `transcriptBuilder false` over the leaf digests. It
  reads salts of opened positions only and second-call outputs only through their 32-byte digests;
* the honest law: `PlbTranscriptRefines`, the overlap-leaf version of `TranscriptRefines`, which
  `plb_transcript_refines` derives from the verified opener (`OpeningABI`) and the commit-side
  refinement `PlbCommitTranscript` (the record's `CommitTranscript` with the overlap-leaf digests).

`plb_scheme_hiding` is the hiding field of the certificate. -/

/-! ## The overlap-leaf reference transcript -/

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 (packBuffer replyWords)
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

local instance plbBridgeDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

/-- `X = 0^8 ‖ m[0..192)`. -/
def plbFirstInput (message : Words 32) : Block := packBuffer (Overlap.firstInput message)

/-- `W = tag(index) ‖ P(X)[168..200) ‖ salt ‖ m[112..256)`. -/
def plbSecondInput (index : Index) (message : Words 32) (salt : BitVec 128) (firstReply : Block) : Block :=
  packBuffer (Overlap.secondInput index.val (saltWords salt) (replyWords firstReply) message)

/-- The overlap-leaf digests of a message under a permutation and a salt tape. -/
def plbLeafDigests (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i =>
    let first := p.forward (plbFirstInput (messageWords message i))
    outputDigest (p.forward (plbSecondInput i (messageWords message i) (salts i) first))

theorem plb_leaf_digests_apply (σ : Perm) (message : Message) (salts : CompleteSaltTape) (i : Index) :
    plbLeafDigests (BiPermutation.equiv Block σ) message salts i =
      outputDigest (σ (packBuffer (Overlap.secondInput i.val (saltWords (salts i))
        (replyWords (σ (packBuffer (Overlap.firstInput (messageWords message i))))) (messageWords message i)))) :=
  rfl

def plbHonestView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun i => salts i.val) (plbLeafDigests p message salts)

/-- The overlap-leaf version of `TranscriptRefines`: commit then open is, for every fixed oracle,
a uniform salt tape followed by the reference transcript over the overlap-leaf digests. -/
def PlbTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          pure (plbHonestView build oracle.compression (BiPermutation.equiv Block oracle.permutation)
            message positions salts))

end TwoPermutationPrototype.Sampling

/-! ## The commit-side refinement and the opener -/

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp

local instance plbOpeningDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

/-- The record's `CommitTranscript` with the overlap-leaf digests. -/
structure PlbCommitTranscript (s : Submission) where
  trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*s.sizes.trapdoor)
  distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
    (do let salts ← sampleCompleteSaltTape
        let leaves := plbLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts
        pure (transcriptHeap false oracle.compression leaves 1, trapdoorOf oracle message salts))
  nonce : ∀ oracle message salts index,
    trapdoorSalt (s := s) (trapdoorOf oracle message salts) index = salts index
  heap : ∀ oracle message salts node, 0 < node → node < 2*LENGTH →
    trapdoorHeap (s := s) (trapdoorOf oracle message salts) node =
      transcriptHeap false oracle.compression
        (plbLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) node

/-- The verified opener composed with the commit-side refinement gives the overlap-leaf
transcript law. -/
theorem plb_transcript_refines (s : Submission) (abi : OpeningABI s)
    (committed : PlbCommitTranscript s) : PlbTranscriptRefines s.scheme (transcriptBuilder false) := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((committed.distribution oracle message).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro salts
  rw [scheme_open_bytes s abi, pure_bind, fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (committed.trapdoorOf oracle message salts) positions
    oracle.compression (plbLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
    salts (committed.heap oracle message salts) (committed.nonce oracle message salts)
  rw [proof]
  rfl

/-- The real commitment RNG returns one packed tape: `CommitTranscript.ofPacked` for the
overlap leaf. -/
noncomputable def PlbCommitTranscript.ofPacked (s : Submission)
    (trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*s.sizes.trapdoor))
    (distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let packed ← $ᵗ BitVec (128 * LENGTH)
          let salts := splitBlocks 128 LENGTH packed
          let leaves := plbLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts
          pure (transcriptHeap false oracle.compression leaves 1, trapdoorOf oracle message salts)))
    (nonce : ∀ oracle message salts index,
      trapdoorSalt (s := s) (trapdoorOf oracle message salts) index = salts index)
    (heap : ∀ oracle message salts node, 0 < node → node < 2*LENGTH →
      trapdoorHeap (s := s) (trapdoorOf oracle message salts) node =
        transcriptHeap false oracle.compression
          (plbLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) node) :
    PlbCommitTranscript s :=
  ⟨trapdoorOf, fun oracle message =>
    (distribution oracle message).trans
      (packed_salt_tape_uniform (fun salts => pure
        (transcriptHeap false oracle.compression
          (plbLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) 1,
         trapdoorOf oracle message salts))), nonce, heap⟩

end TwoPermutationPrototype.Opening

/-! ## The swap-coupling instance -/

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 (packBuffer replyWords)

/-- The position whose second-call tag is `t`, if `t` is one. -/
def plbTagPosition (t : BitVec 64) : Option Index :=
  if h : 4152 ≤ t.toNat ∧ (t.toNat - 4152) % 256 = 0 ∧ (t.toNat - 4152) / 256 < LENGTH then
    some ⟨(t.toNat - 4152) / 256, h.2.2⟩
  else none

theorem plb_tag_position (j : Index) : plbTagPosition (secondTag j.val) = some j := by
  have small : j.val < 2 ^ 24 := by
    have := j.isLt
    simpa [LENGTH, LOG_LENGTH] using this
  have value : (secondTag j.val).toNat = 4152 + 256 * j.val := by
    rw [second_tag_address, BitVec.toNat_ofNat]
    omega
  have quotient : (4152 + 256 * j.val - 4152) / 256 = j.val := by omega
  have condition : 4152 ≤ (secondTag j.val).toNat ∧ ((secondTag j.val).toNat - 4152) % 256 = 0 ∧
      ((secondTag j.val).toNat - 4152) / 256 < LENGTH := by
    rw [value, quotient]
    exact ⟨by omega, by omega, j.isLt⟩
  unfold plbTagPosition
  rw [dite_eq_left_of_eq_true (eq_true condition)]
  congr 1
  apply Fin.ext
  show ((secondTag j.val).toNat - 4152) / 256 = j.val
  rw [value, quotient]

theorem plb_tag_position_zero : plbTagPosition 0 = none := by
  unfold plbTagPosition
  simp

theorem plb_first_tag (message : Words 32) : (plbFirstInput message).extractLsb' 0 64 = 0 := by
  have packed := packed_word (Overlap.firstInput message) ⟨0, by decide⟩
  change (packBuffer _).extractLsb' (64 * (⟨0, by decide⟩ : Fin 25).val) 64 = 0
  rw [packed]
  simp [Overlap.firstInput]

theorem plb_second_tag (index : Index) (message : Words 32) (salt : BitVec 128) (firstReply : Block) :
    (plbSecondInput index message salt firstReply).extractLsb' 0 64 = secondTag index.val := by
  have packed := packed_word (Overlap.secondInput index.val (saltWords salt) (replyWords firstReply) message)
    ⟨0, by decide⟩
  change (packBuffer _).extractLsb' (64 * (⟨0, by decide⟩ : Fin 25).val) 64 = _
  rw [packed]
  simp [Overlap.secondInput]

theorem plb_second_salt (index : Index) (message : Words 32) (salt : BitVec 128) (firstReply : Block) :
    (plbSecondInput index message salt firstReply).extractLsb' 320 128 = salt := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  let i : Fin 25 := ⟨5 + bit / 64, by omega⟩
  have packed := packed_word (Overlap.secondInput index.val (saltWords salt) (replyWords firstReply) message) i
  have notZero : 5 + bit / 64 ≠ 0 := by omega
  have notLink : ¬ 5 + bit / 64 < 5 := by omega
  have isSalt : 5 + bit / 64 < 7 := by omega
  have word : (plbSecondInput index message salt firstReply).extractLsb' (64 * (5 + bit / 64)) 64 =
      salt.extractLsb' (64 * (bit / 64)) 64 := by
    change (packBuffer _).extractLsb' (64 * i.val) 64 = _
    rw [packed]
    simp [Overlap.secondInput, saltWords, i, notZero, notLink, isSalt]
  have eq := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) word
  have lhs : 64 * (5 + bit / 64) + bit % 64 = 320 + bit := by omega
  have rhs : 64 * (bit / 64) + bit % 64 = bit := by omega
  simpa [show bit % 64 < 64 by omega, inside, lhs, rhs] using eq

/-- The message of world `b`. -/
def plbChosen {St : Type} {k : Nat} (c : Hiding.HidingChallenge St k) (b : Bool) : Message :=
  if b then c.message₁ else c.message₀

theorem plb_chosen_agree {St : Type} {k : Nat} (c : Hiding.HidingChallenge St k) (j : Index)
    (outside : ¬ (j ∉ c.positions ∧ c.message₀ j ≠ c.message₁ j)) :
    messageWords (plbChosen c false) j = messageWords (plbChosen c true) j := by
  have same : c.message₀ j = c.message₁ j := by
    by_cases opened : j ∈ c.positions
    · exact congrFun c.agree ⟨j, opened⟩
    · by_contra different
      exact outside ⟨opened, different⟩
  funext word
  show (c.message₀ j).extractLsb' (64 * word.val) 64 = (c.message₁ j).extractLsb' (64 * word.val) 64
  rw [same]

/-- **The overlap-leaf salt layout.** -/
def plbSaltLayout (St : Type) (k : Nat) :
    HSwap.SaltLayout (Hiding.HidingChallenge St k) Index (BitVec 128) where
  tag x := plbTagPosition (x.extractLsb' 0 64)
  X c b j := plbFirstInput (messageWords (plbChosen c b) j)
  W c b j u y := plbSecondInput j (messageWords (plbChosen c b) j) u y
  saltOf x := x.extractLsb' 320 128
  swapSet c := Finset.univ.filter fun j => j ∉ c.positions ∧ c.message₀ j ≠ c.message₁ j
  tag_X c b j := by
    show plbTagPosition ((plbFirstInput _).extractLsb' 0 64) = none
    rw [plb_first_tag, plb_tag_position_zero]
  tag_W c b j u y := by
    show plbTagPosition ((plbSecondInput _ _ _ _).extractLsb' 0 64) = some j
    rw [plb_second_tag, plb_tag_position]
  saltOf_W c b j u y := plb_second_salt _ _ _ _
  agree c j outside := by
    have same := plb_chosen_agree c j (by simpa using outside)
    exact ⟨by rw [same], fun u y => by rw [same]⟩

/-- The honest view: the reference transcript over the digests of the second-call outputs. -/
def plbView (St : Type) (k : Nat) (compress : Compression) (c : Hiding.HidingChallenge St k)
    (salts : Index → BitVec 128) (outputs : Index → HSwap.PWord) : Commitment × Proof :=
  transcriptBuilder false compress c.positions (fun i => salts i.val) (fun j => outputDigest (outputs j))

theorem plb_view_salts (St : Type) (k : Nat) (compress : Compression) (c : Hiding.HidingChallenge St k)
    (salts salts' : Index → BitVec 128) (outputs : Index → HSwap.PWord)
    (same : ∀ j, j ∉ (plbSaltLayout St k).swapSet c → salts j = salts' j) :
    plbView St k compress c salts outputs = plbView St k compress c salts' outputs := by
  have opened : (fun i : {i // i ∈ c.positions} => salts i.val) = fun i => salts' i.val := by
    funext i
    apply same
    intro swapped
    have member : i.val ∈ (Finset.univ.filter fun j : Index => j ∉ c.positions ∧ c.message₀ j ≠ c.message₁ j) :=
      swapped
    exact (Finset.mem_filter.mp member).2.1 i.property
  unfold plbView
  rw [opened]

theorem plb_view_digest (St : Type) (k : Nat) (compress : Compression) (c : Hiding.HidingChallenge St k)
    (salts : Index → BitVec 128) (outputs outputs' : Index → HSwap.PWord)
    (same : ∀ j, HSwap.digestOf (outputs j) = HSwap.digestOf (outputs' j)) :
    plbView St k compress c salts outputs = plbView St k compress c salts outputs' := by
  have digests : (fun j => outputDigest (outputs j)) = fun j => outputDigest (outputs' j) :=
    funext same
  unfold plbView
  rw [digests]

theorem plb_salt_uniform (salts : CompleteSaltTape) :
    Pr{let x ← sampleCompleteSaltTape}[x = salts] =
      Pr{let x ← sampleCompleteSaltTape}[x = fun _ => 0] :=
  @HSwap.uniform_point_eq CompleteSaltTape completeSaltSampler salts (fun _ => 0)

theorem plb_index_card : Fintype.card Index ≤ 2 ^ 24 := by
  simp [LENGTH, LOG_LENGTH]

/-- The honest law of the swap coupling, from the overlap-leaf transcript law. -/
theorem plb_honest_law (scheme : Scheme) (refines : PlbTranscriptRefines scheme (transcriptBuilder false))
    (St : Type) (k : Nat) (C : Compression) (σ : Perm) (b : Bool) (c : Hiding.HidingChallenge St k)
    (q : Commitment × Proof → Prop) :
    Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (HSwap.honest scheme b c)}[q v] =
      Pr{let v ← (sampleCompleteSaltTape >>= fun s =>
        pure (plbView St k C c s fun j => σ (HSwap.wpt (plbSaltLayout St k).toLeaf c s σ b j)))}[q v] := by
  rw [← fixed_run_eq_simulate]
  exact (refines ⟨C, σ⟩ (if b then c.message₁ else c.message₀) c.positions).prEvent_eq q

/-- Hiding from the overlap-leaf transcript law. -/
theorem plb_scheme_hiding_of_transcript (scheme : Scheme)
    (refines : PlbTranscriptRefines scheme (transcriptBuilder false)) : scheme.Hiding HIDING_ERROR :=
  HSwap.scheme_hiding_digest scheme (Fintype.card_bitVec 128) plb_index_card sampleCompleteSaltTape
    (Pr{let x ← sampleCompleteSaltTape}[x = fun _ => 0]) plb_salt_uniform plbSaltLayout plbView
    plb_view_salts plb_view_digest (plb_honest_law scheme refines)

end TwoPermutationPrototype.Sampling

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

/-- **Hiding with the overlap leaf**: the certificate's hiding field from the verified opener and
the commit-side refinement. -/
theorem plb_scheme_hiding (s : Submission) (abi : OpeningABI s) (committed : PlbCommitTranscript s) :
    s.scheme.Hiding HIDING_ERROR :=
  plb_scheme_hiding_of_transcript s.scheme (plb_transcript_refines s abi committed)

end TwoPermutationPrototype.Opening
