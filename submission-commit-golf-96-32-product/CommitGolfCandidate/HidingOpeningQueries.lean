import CommitGolfCandidate.HidingHeapQueries

/-! An oracle continuation producing exactly the public root and opening bytes.
This deliberately loose query bound is for the security reduction only; submitted
machine cycles and proof-size claims continue to use the existing exact proofs. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

def queryList {α β : Type} (query : α → OracleComp World β) : List α → OracleComp World (List β)
  | [] => pure []
  | head :: tail => do
      let value ← query head
      let values ← queryList query tail
      pure (value :: values)

theorem query_list_bound {α β : Type} (query : α → OracleComp World β)
    (budget : Nat) (bounded : ∀ input, PublicQueryBound (query input) budget) (inputs : List α) :
    PublicQueryBound (queryList query inputs) (inputs.length*budget) := by
  induction inputs with
  | nil => trivial
  | cons head tail ih =>
    have rest (value : β) := public_query_bound_bind ih
      (fun values => (show PublicQueryBound (pure (value :: values) : OracleComp World _) 0 from trivial))
    have result := public_query_bound_bind (bounded head) rest
    simpa only [queryList, List.length_cons, Nat.add_zero, Nat.add_mul, Nat.one_mul,
      Nat.add_comm] using result

theorem query_list_reference (oracle : Oracle) {α β : Type}
    (query : α → OracleComp World β) (values : α → β) (inputs : List α)
    (correct : ∀ input ∈ inputs, fixedOracleRun oracle (query input) = pure (values input)) :
    fixedOracleRun oracle (queryList query inputs) = pure (inputs.map values) := by
  induction inputs with
  | nil => exact fixed_oracle_run_pure _ _
  | cons head tail ih =>
    rw [queryList, fixed_oracle_run_bind, correct head List.mem_cons_self, pure_bind]
    rw [fixed_oracle_run_bind, ih (fun input member => correct input (List.mem_cons_of_mem _ member)), pure_bind]
    exact fixed_oracle_run_pure _ _

def queryOpeningDigest (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) (ordinal part : Nat) : OracleComp World Digest :=
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  if part = 0 then pure (salt index)
  else heap (((LENGTH+index.val)/2^(part-1)) ^^^ 1)

def queryOpening (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) : OracleComp World Proof :=
  queryList (fun offset => do
    let digest ← queryOpeningDigest heap salt positions (offset/800) ((offset%800)/32)
    pure (digest.extractLsb' (8*(offset%32)) 8)) (List.range (800*positions.card))

theorem query_opening_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (queryOpening heap salt positions) (800*positions.card*budget) := by
  have digestBound (ordinal part : Nat) :
      PublicQueryBound (queryOpeningDigest heap salt positions ordinal part) budget := by
    unfold queryOpeningDigest
    split
    · trivial
    · exact bounded _
  have bytes (offset : Nat) := public_query_bound_bind (digestBound (offset/800) ((offset%800)/32))
    (fun digest => (show PublicQueryBound
      (pure (digest.extractLsb' (8*(offset%32)) 8) : OracleComp World _) 0 from trivial))
  simpa only [queryOpening, List.length_range, Nat.add_zero] using
    query_list_bound _ (budget+0) bytes (List.range (800*positions.card))

theorem query_opening_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2*LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryOpening heap salt positions) =
      pure (referenceOpening values salt positions) := by
  unfold queryOpening referenceOpening
  apply query_list_reference
  intro offset member
  rw [fixed_oracle_run_bind]
  have part : (offset%800)/32 < 25 := by omega
  let index : Index := ⟨openingIndex positions (offset/800), opening_index_bound positions (offset/800)⟩
  have digest : fixedOracleRun oracle
      (queryOpeningDigest heap salt positions (offset/800) ((offset%800)/32)) =
      pure (referenceOpeningDigest values salt positions (offset/800) ((offset%800)/32)) := by
    unfold queryOpeningDigest referenceOpeningDigest
    split
    · exact fixed_oracle_run_pure _ _
    · have level : (offset%800)/32-1 < LOG_LENGTH := by change _ < 24; omega
      have valid := opening_sibling_bounds index _ level
      exact correct _ valid.1 valid.2
  rw [digest, pure_bind]
  exact fixed_oracle_run_pure _ _

/-- Compute the root and the exact opening proof from a common oracle. -/
def queryTranscript (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) : OracleComp World (Commitment × Proof) := do
  let root ← heap 1
  let proof ← queryOpening heap salt positions
  pure (root, proof)

theorem query_transcript_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (queryTranscript heap salt positions) ((1+800*positions.card)*budget) := by
  have rest (root : Commitment) := public_query_bound_bind (query_opening_bound heap budget bounded salt positions)
    (fun proof => (show PublicQueryBound (pure (root, proof) : OracleComp World _) 0 from trivial))
  have result := public_query_bound_bind (bounded 1) rest
  simpa only [queryTranscript, Nat.add_zero, Nat.add_mul, Nat.one_mul] using result

theorem query_transcript_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2*LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryTranscript heap salt positions) =
      pure (values 1, referenceOpening values salt positions) := by
  rw [queryTranscript, fixed_oracle_run_bind, correct 1 (by decide) (by decide), pure_bind]
  rw [fixed_oracle_run_bind, query_opening_reference oracle heap values correct salt positions, pure_bind]
  exact fixed_oracle_run_pure _ _

end CommitGolfCandidate
