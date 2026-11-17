import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingLeafReplacement
import CommitGolfCandidate.S3HideLeaf

/-! Replace one message coordinate in the complete reference game. The uniform
permutation is sampled for the whole game, the first stage runs inside the step,
and the other salts are sampled first; the isolated nonce is still fresh and
private. The step itself is the per-leaf permutation lemma `s3_leaf_replacement`
(S3HideLeaf.lean). -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingCoordinateDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

/-- Resampling one coordinate of a uniform function preserves its distribution,
also for randomized continuations. Stated generically to avoid expanding the
challenge's enormous finite salt space during elaboration. -/
theorem uniform_coordinate_bind {D R α : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    𝒟[do let values ← $ᵗ (D → R)
         let value ← $ᵗ R
         next (Function.update values index value)] =
    𝒟[do let values ← $ᵗ (D → R); next values] := by
  have marginal : 𝒟[do let value ← $ᵗ R
                        let values ← $ᵗ (D → R)
                        pure (Function.update values index value)] = 𝒟[$ᵗ (D → R)] := by
    simpa only [bind_pure] using evalDist_uniformSample_bind_update_map
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index (fun values : D → R => values)
  trans 𝒟[do let value ← $ᵗ R
              let values ← $ᵗ (D → R)
              next (Function.update values index value)]
  · exact distribution_bind_comm _ _ _
  · trans 𝒟[(do let value ← $ᵗ R
                let values ← $ᵗ (D → R)
                pure (Function.update values index value)) >>= next]
    · simp only [bind_assoc, pure_bind]
    · rw [evalDist_bind_of_discrete, marginal, ← evalDist_bind_of_discrete]

def observeTranscript {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  let transcript := referenceTranscript oracle.compression oracle.permutation message salt positions
  fixedOracleRun oracle (observe transcript.1 transcript.2)

/-- The observer on a transcript whose leaves are all hashed through the oracle. -/
def observeFull {α : Type} (message : Message) (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let transcript ← queryFullTranscript message salt positions
  observe transcript.1 transcript.2

def observeExcept {α : Type} (message : Message) (salt : Index → Digest) (positions : Positions)
    (hidden : Index) (observe : Commitment → Proof → OracleComp World α) (digest : Digest) :
    OracleComp World α := do
  let transcript ← queryTranscriptExcept message salt positions hidden digest
  observe transcript.1 transcript.2

attribute [local irreducible] queryFullTranscript queryTranscriptExcept

theorem observe_full_bound {α : Type} (message : Message) (salt : Index → Digest)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    PublicQueryBound (observeFull message salt positions observe) ((3*LENGTH-1) + budget) :=
  public_query_bound_bind (query_full_transcript_bound message salt positions)
    (fun transcript => bounded transcript.1 transcript.2)

theorem observe_except_bound {α : Type} (message : Message) (salt : Index → Digest)
    (positions : Positions) (hidden : Index) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (digest : Digest) :
    PublicQueryBound (observeExcept message salt positions hidden observe digest)
      ((3*LENGTH-1) + budget) :=
  public_query_bound_bind (query_transcript_except_bound message salt positions hidden digest)
    (fun transcript => bounded transcript.1 transcript.2)

theorem observe_full_reference {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) :
    fixedOracleRun oracle (observeFull message salt positions observe) =
      observeTranscript oracle message salt positions observe := by
  rw [observeFull, fixed_oracle_run_bind, query_full_transcript_reference, pure_bind]
  rfl

theorem observe_except_reference {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions) (hidden : Index) (unopened : hidden ∉ positions)
    (observe : Commitment → Proof → OracleComp World α) (value : Entry) (fresh : Digest) :
    fixedOracleRun oracle
      (observeExcept message salt positions hidden observe (s3LeafDigest oracle.permutation fresh value)) =
      observeTranscript oracle (Function.update message hidden value)
        (Function.update salt hidden fresh) positions observe := by
  rw [observeExcept, fixed_oracle_run_bind, query_transcript_hidden_update oracle message salt positions hidden unopened,
    pure_bind]
  rfl

section game

variable {State Output : Type} {openingSize : Nat}

/-- The reference game with a challenge-dependent committed message. -/
def hidingGame (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) : ProbComp Output := do
  let compression ← $ᵗ Compression
  let permutation ← $ᵗ Perm
  let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
  let salt ← $ᵗ (Index → Nonce192)
  observeTranscript ⟨compression, permutation⟩ (message challenge) (expandNonceVector salt)
    challenge.positions (adversary.observe challenge.aux)

/-- The second stage after coordinate `index` has been isolated. Opened: recompute
the whole transcript with the isolated nonce. Unopened: use only the leaf digest. -/
def coordinateNext (adversary : Hiding.HidingAdversary State Output openingSize)
    (base : Hiding.HidingChallenge State openingSize → Message) (index : Index)
    (salt : Index → Digest) (challenge : Hiding.HidingChallenge State openingSize)
    (nonce : Nonce192) (digest : Digest) : OracleComp World Output :=
  if index ∈ challenge.positions then
    observeFull (base challenge) (Function.update salt index (expandNonce192 nonce))
      challenge.positions (adversary.observe challenge.aux)
  else
    observeExcept (base challenge) salt challenge.positions index
      (adversary.observe challenge.aux) digest

theorem coordinate_next_bound (adversary : Hiding.HidingAdversary State Output openingSize)
    (budget : Nat)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (base : Hiding.HidingChallenge State openingSize → Message) (index : Index)
    (salt : Index → Digest) (challenge : Hiding.HidingChallenge State openingSize)
    (nonce : Nonce192) (digest : Digest) :
    PublicQueryBound (coordinateNext adversary base index salt challenge nonce digest)
      ((3*LENGTH-1) + budget) := by
  unfold coordinateNext
  split
  · exact observe_full_bound _ _ _ _ budget (observeBound challenge.aux)
  · exact observe_except_bound _ _ _ _ _ budget (observeBound challenge.aux) digest

theorem coordinate_next_run (adversary : Hiding.HidingAdversary State Output openingSize)
    (base : Hiding.HidingChallenge State openingSize → Message) (index : Index)
    (compression : Compression) (permutation : Perm) (salt : Index → Nonce192)
    (challenge : Hiding.HidingChallenge State openingSize) (nonce : Nonce192) (value : Entry)
    (agree : index ∈ challenge.positions → value = base challenge index) :
    fixedOracleRun ⟨compression, permutation⟩
      (coordinateNext adversary base index (expandNonceVector salt) challenge nonce
        (s3LeafDigest permutation (expandNonce192 nonce) value)) =
      observeTranscript ⟨compression, permutation⟩ (Function.update (base challenge) index value)
        (expandNonceVector (Function.update salt index nonce)) challenge.positions
        (adversary.observe challenge.aux) := by
  rw [expand_nonce_vector_update]
  unfold coordinateNext
  split
  · rename_i opened
    rw [agree opened, Function.update_eq_self, observe_full_reference]
  · rename_i unopened
    exact observe_except_reference ⟨compression, permutation⟩ (base challenge)
      (expandNonceVector salt) challenge.positions index unopened _ value _

/-- The game with coordinate `index` isolated, in the shape of `s3_leaf_replacement`
under the outer draws of the compression function and the other nonces. -/
def coordinateGame (adversary : Hiding.HidingAdversary State Output openingSize)
    (base : Hiding.HidingChallenge State openingSize → Message) (index : Index)
    (value : Hiding.HidingChallenge State openingSize → Entry) : ProbComp Output := do
  let compression ← $ᵗ Compression
  let salt ← $ᵗ (Index → Nonce192)
  let permutation ← $ᵗ Perm
  let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
  let nonce ← $ᵗ Nonce192
  fixedOracleRun ⟨compression, permutation⟩
    (coordinateNext adversary base index (expandNonceVector salt) challenge nonce
      (s3LeafDigest permutation (expandNonce192 nonce) (value challenge)))

theorem hiding_game_coordinate (adversary : Hiding.HidingAdversary State Output openingSize)
    (base : Hiding.HidingChallenge State openingSize → Message) (index : Index)
    (value : Hiding.HidingChallenge State openingSize → Entry)
    (agree : ∀ challenge, index ∈ challenge.positions → value challenge = base challenge index) :
    𝒟[hidingGame adversary fun challenge => Function.update (base challenge) index (value challenge)] =
      𝒟[coordinateGame adversary base index value] := by
  unfold hidingGame coordinateGame
  apply _root_.evalDist_bind_congr
  intro compression
  trans 𝒟[do let permutation ← $ᵗ Perm
              let salt ← $ᵗ (Index → Nonce192)
              let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
              let nonce ← $ᵗ Nonce192
              fixedOracleRun ⟨compression, permutation⟩
                (coordinateNext adversary base index (expandNonceVector salt) challenge nonce
                  (s3LeafDigest permutation (expandNonce192 nonce) (value challenge)))]
  · apply _root_.evalDist_bind_congr
    intro permutation
    trans 𝒟[do let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
                let salt ← $ᵗ (Index → Nonce192)
                let nonce ← $ᵗ Nonce192
                fixedOracleRun ⟨compression, permutation⟩
                  (coordinateNext adversary base index (expandNonceVector salt) challenge nonce
                    (s3LeafDigest permutation (expandNonce192 nonce) (value challenge)))]
    · apply _root_.evalDist_bind_congr
      intro challenge
      refine Eq.trans (uniform_coordinate_bind index (fun salt =>
        observeTranscript ⟨compression, permutation⟩
          (Function.update (base challenge) index (value challenge)) (expandNonceVector salt)
          challenge.positions (adversary.observe challenge.aux))).symm ?_
      apply _root_.evalDist_bind_congr
      intro salt
      apply _root_.evalDist_bind_congr
      intro nonce
      rw [coordinate_next_run adversary base index compression permutation salt challenge nonce
        (value challenge) (agree challenge)]
    · exact (distribution_bind_comm _ _ _).symm
  · exact (distribution_bind_comm _ _ _).symm

/-- One hybrid step: changing coordinate `index` of the committed message, where
both values agree with `base` whenever the first stage opens that coordinate. -/
theorem hiding_coordinate_distance
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (base : Hiding.HidingChallenge State openingSize → Message) (index : Index)
    (left right : Hiding.HidingChallenge State openingSize → Entry)
    (agreeLeft : ∀ challenge, index ∈ challenge.positions → left challenge = base challenge index)
    (agreeRight : ∀ challenge, index ∈ challenge.positions → right challenge = base challenge index) :
    measureTVDist
      (hidingGame adversary fun challenge => Function.update (base challenge) index (left challenge))
      (hidingGame adversary fun challenge => Function.update (base challenge) index (right challenge)) ≤
      4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192 := by
  have distance : measureTVDist (coordinateGame adversary base index left)
      (coordinateGame adversary base index right) ≤
      4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192 := by
    unfold coordinateGame
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro compression
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro salt
    exact s3_leaf_replacement compression adversary.choose
      (fun challenge => decide (index ∉ challenge.positions)) left right
      (fun challenge opened => by
        have member : index ∈ challenge.positions := by simpa using opened
        rw [agreeLeft challenge member, agreeRight challenge member])
      (coordinateNext adversary base index (expandNonceVector salt))
      (fun challenge unopened nonce nonce' digest => by
        have absent : index ∉ challenge.positions := by simpa using unopened
        simp only [coordinateNext, if_neg absent])
      budget ((3*LENGTH-1) + budget) chooseBound
      (fun challenge nonce digest =>
        coordinate_next_bound adversary budget observeBound base index _ challenge nonce digest)
  simpa only [measureTVDist, hiding_game_coordinate adversary base index left agreeLeft,
    hiding_game_coordinate adversary base index right agreeRight] using distance

end game

end CommitGolfCandidate
