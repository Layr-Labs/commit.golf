import CommitGolfCandidate.HidingHeapQueries

/-! An oracle continuation producing exactly the public root and opening bytes
for both normal openings (`k ≠ 128`) and level-7 cap-table openings (`k = 128`).
This deliberately loose query bound is for the security reduction only; submitted
machine cycles and proof-size claims continue to use the exact machine proofs. -/
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
    PublicQueryBound (queryList query inputs) (inputs.length * budget) := by
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

def queryOpeningDigestAt (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) (offset : Nat) : OracleComp World Digest :=
  if positions.card = BATCH then
    if offset < 73728 then
      let ordinal := offset / 576
      let part := (offset % 576) / 32
      let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
      if part = 0 then pure (salt index)
      else heap (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1)
    else
      heap (128 + (offset - 73728) / 32)
  else
    let ordinal := offset / 800
    let part := (offset % 800) / 32
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    if part = 0 then pure (salt index)
    else heap (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1)

def queryOpening (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) : OracleComp World Proof :=
  queryList (fun offset => do
    let digest ← queryOpeningDigestAt heap salt positions offset
    pure (digest.extractLsb' (8 * (offset % 32)) 8)) (List.range (openingProofBytes positions.card))

theorem query_opening_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (queryOpening heap salt positions) (800 * positions.card * budget) := by
  have digestBound (offset : Nat) :
      PublicQueryBound (queryOpeningDigestAt heap salt positions offset) budget := by
    unfold queryOpeningDigestAt
    split
    · split
      · dsimp only
        split
        · trivial
        · exact bounded _
      · exact bounded _
    · dsimp only
      split
      · trivial
      · exact bounded _
  have bytes (offset : Nat) := public_query_bound_bind (digestBound offset)
    (fun digest => (show PublicQueryBound
      (pure (digest.extractLsb' (8 * (offset % 32)) 8) : OracleComp World _) 0 from trivial))
  have exactBound : PublicQueryBound (queryOpening heap salt positions)
      (openingProofBytes positions.card * budget) := by
    simpa only [queryOpening, List.length_range, Nat.add_zero] using
      query_list_bound _ (budget + 0) bytes (List.range (openingProofBytes positions.card))
  exact exactBound.mono (Nat.mul_le_mul_right budget (opening_proof_bytes_le positions.card))

theorem query_opening_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2 * LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryOpening heap salt positions) =
      pure (referenceOpening values salt positions) := by
  unfold queryOpening referenceOpening
  apply query_list_reference
  intro offset member
  have below : offset < openingProofBytes positions.card := List.mem_range.mp member
  rw [fixed_oracle_run_bind]
  have digest : fixedOracleRun oracle (queryOpeningDigestAt heap salt positions offset) =
      pure (referenceOpeningDigestAt values salt positions offset) := by
    unfold queryOpeningDigestAt referenceOpeningDigestAt
    by_cases batch : positions.card = BATCH
    · rw [if_pos batch, if_pos batch]
      have belowCap : offset < 77824 := by
        simp only [openingProofBytes, if_pos batch] at below; exact below
      by_cases inRecs : offset < 73728
      · rw [if_pos inRecs, if_pos inRecs]
        dsimp only
        by_cases zero : (offset % 576) / 32 = 0
        · rw [if_pos zero, if_pos zero]; exact fixed_oracle_run_pure _ _
        · rw [if_neg zero, if_neg zero]
          have level : (offset % 576) / 32 - 1 < LOG_LENGTH := by change _ < 24; omega
          have valid := opening_sibling_bounds
            ⟨openingIndex positions (offset / 576), opening_index_bound positions (offset / 576)⟩
            _ level
          exact correct _ valid.1 valid.2
      · rw [if_neg inRecs, if_neg inRecs]
        exact correct (128 + (offset - 73728) / 32) (by omega)
          (by change 128 + (offset - 73728) / 32 < 2 * 16777216; omega)
    · rw [if_neg batch, if_neg batch]
      dsimp only
      by_cases zero : (offset % 800) / 32 = 0
      · rw [if_pos zero, if_pos zero]; exact fixed_oracle_run_pure _ _
      · rw [if_neg zero, if_neg zero]
        have level : (offset % 800) / 32 - 1 < LOG_LENGTH := by change _ < 24; omega
        have valid := opening_sibling_bounds
          ⟨openingIndex positions (offset / 800), opening_index_bound positions (offset / 800)⟩
          _ level
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
    PublicQueryBound (queryTranscript heap salt positions) ((1 + 800 * positions.card) * budget) := by
  have rest (root : Commitment) := public_query_bound_bind (query_opening_bound heap budget bounded salt positions)
    (fun proof => (show PublicQueryBound (pure (root, proof) : OracleComp World _) 0 from trivial))
  have result := public_query_bound_bind (bounded 1) rest
  simpa only [queryTranscript, Nat.add_zero, Nat.add_mul, Nat.one_mul] using result

theorem query_transcript_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2 * LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryTranscript heap salt positions) =
      pure (values 1, referenceOpening values salt positions) := by
  rw [queryTranscript, fixed_oracle_run_bind, correct 1 (by decide) (by decide), pure_bind]
  rw [fixed_oracle_run_bind, query_opening_reference oracle heap values correct salt positions, pure_bind]
  exact fixed_oracle_run_pure _ _

end CommitGolfCandidate
