import CommitGolfCandidate.Probability
import CommitGolfCandidate.S5HideQuery

/-! The reference hiding game with uniform nonces, and the observer stage in two forms: on the
transcript formula (`observeTranscript`) and on the transcript computed through the oracle
(`observeFull`). -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingCoordinateDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

def observeTranscript {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  let transcript := referenceTranscript oracle.compression oracle.permutation message salt positions
  fixedOracleRun oracle (observe transcript.1 transcript.2)

/-- The observer on a transcript whose leaves, group nodes and internal nodes are all computed
through the oracle. -/
def observeFull {α : Type} (message : Message) (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let transcript ← queryFullTranscript message salt positions
  observe transcript.1 transcript.2

theorem observe_full_bound {α : Type} (message : Message) (salt : Index → Digest)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    PublicQueryBound (observeFull message salt positions observe) ((2^25 + 2^23) + budget) :=
  public_query_bound_bind (query_full_transcript_bound message salt positions)
    (fun transcript => bounded transcript.1 transcript.2)

theorem observe_full_reference {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) :
    fixedOracleRun oracle (observeFull message salt positions observe) =
      observeTranscript oracle message salt positions observe := by
  rw [observeFull, fixed_oracle_run_bind, query_full_transcript_reference, pure_bind]
  rfl

section game

variable {State Output : Type} {openingSize : Nat}

/-- The reference game with a challenge-dependent committed message and uniform nonces. -/
def hidingGame (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) : ProbComp Output := do
  let compression ← $ᵗ Compression
  let permutation ← $ᵗ Perm
  let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
  let nonce ← $ᵗ (Index → Nonce128)
  observeTranscript ⟨compression, permutation⟩ (message challenge) (expandTaggedVector nonce)
    challenge.positions (adversary.observe challenge.aux)

end game

end CommitGolfCandidate
