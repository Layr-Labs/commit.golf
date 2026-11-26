import CommitGolfCandidate.HidingHeapQueries

/-! An oracle continuation producing exactly the public root and opening bytes
for both normal openings (`k ≠ 128`, 784 B/pos) and level-7 cap-table openings
(`k = 128`, 75,776 B). -/
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

def queryOpeningByte (heap : Nat → OracleComp World Digest) (salt : Index → Salt)
    (positions : Positions) (offset : Nat) : OracleComp World (BitVec 8) :=
  if positions.card = BATCH then
    if offset < 71680 then
      let ordinal := offset / 560
      let rem := offset % 560
      let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
      if rem < 16 then
        pure ((salt index).extractLsb' (8 * rem) 8)
      else do
        let level := (rem - 16) / 32
        let digest ← heap (((LENGTH + index.val) / 2 ^ level) ^^^ 1)
        pure (digest.extractLsb' (8 * ((rem - 16) % 32)) 8)
    else do
      let digest ← heap (128 + (offset - 71680) / 32)
      pure (digest.extractLsb' (8 * ((offset - 71680) % 32)) 8)
  else
    let ordinal := offset / 784
    let rem := offset % 784
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    if rem < 16 then
      pure ((salt index).extractLsb' (8 * rem) 8)
    else do
      let level := (rem - 16) / 32
      let digest ← heap (((LENGTH + index.val) / 2 ^ level) ^^^ 1)
      pure (digest.extractLsb' (8 * ((rem - 16) % 32)) 8)

def queryOpening (heap : Nat → OracleComp World Digest) (salt : Index → Salt)
    (positions : Positions) : OracleComp World Proof :=
  queryList (queryOpeningByte heap salt positions) (List.range (openingProofBytes positions.card))

theorem query_opening_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Salt) (positions : Positions) :
    PublicQueryBound (queryOpening heap salt positions) (784 * positions.card * budget) := by
  have byteBound (offset : Nat) :
      PublicQueryBound (queryOpeningByte heap salt positions offset) budget := by
    unfold queryOpeningByte
    split
    · split
      · dsimp only
        split
        · trivial
        · rw [← Nat.add_zero budget]
          exact public_query_bound_bind (bounded _) (fun _ => trivial)
      · rw [← Nat.add_zero budget]
        exact public_query_bound_bind (bounded _) (fun _ => trivial)
    · dsimp only
      split
      · trivial
      · rw [← Nat.add_zero budget]
        exact public_query_bound_bind (bounded _) (fun _ => trivial)
  have exactBound : PublicQueryBound (queryOpening heap salt positions)
      (openingProofBytes positions.card * budget) := by
    simpa only [queryOpening, List.length_range] using
      query_list_bound _ budget byteBound (List.range (openingProofBytes positions.card))
  exact exactBound.mono (Nat.mul_le_mul_right budget (opening_proof_bytes_le positions.card))

theorem query_opening_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2 * LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Salt) (positions : Positions) :
    fixedOracleRun oracle (queryOpening heap salt positions) =
      pure (referenceOpening values salt positions) := by
  unfold queryOpening referenceOpening
  apply query_list_reference
  intro offset member
  have below : offset < openingProofBytes positions.card := List.mem_range.mp member
  unfold queryOpeningByte referenceOpeningByte
  by_cases batch : positions.card = BATCH
  · rw [if_pos batch, if_pos batch]
    have belowCap : offset < 75776 := by
      simp only [openingProofBytes, if_pos batch] at below; exact below
    by_cases inRecs : offset < 71680
    · rw [if_pos inRecs, if_pos inRecs]
      dsimp only
      split
      · exact fixed_oracle_run_pure _ _
      · rename_i notSalt
        have level : (offset % 560 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
        let index : Index := ⟨openingIndex positions (offset / 560), opening_index_bound positions (offset / 560)⟩
        have valid := opening_sibling_bounds index ((offset % 560 - 16) / 32) level
        rw [fixed_oracle_run_bind, correct _ valid.1 valid.2, pure_bind]
        exact fixed_oracle_run_pure _ _
    · rw [if_neg inRecs, if_neg inRecs]
      rw [fixed_oracle_run_bind, correct (128 + (offset - 71680) / 32) (by omega)
        (by change 128 + (offset - 71680) / 32 < 2 * 16777216; omega), pure_bind]
      exact fixed_oracle_run_pure _ _
  · rw [if_neg batch, if_neg batch]
    dsimp only
    split
    · exact fixed_oracle_run_pure _ _
    · rename_i notSalt
      have level : (offset % 784 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
      let index : Index := ⟨openingIndex positions (offset / 784), opening_index_bound positions (offset / 784)⟩
      have valid := opening_sibling_bounds index ((offset % 784 - 16) / 32) level
      rw [fixed_oracle_run_bind, correct _ valid.1 valid.2, pure_bind]
      exact fixed_oracle_run_pure _ _

/-- Compute the root and the exact opening proof from a common oracle. -/
def queryTranscript (heap : Nat → OracleComp World Digest) (salt : Index → Salt)
    (positions : Positions) : OracleComp World (Commitment × Proof) := do
  let root ← heap 1
  let proof ← queryOpening heap salt positions
  pure (root, proof)

theorem query_transcript_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Salt) (positions : Positions) :
    PublicQueryBound (queryTranscript heap salt positions) ((1 + 784 * positions.card) * budget) := by
  have rest (root : Commitment) := public_query_bound_bind (query_opening_bound heap budget bounded salt positions)
    (fun proof => (show PublicQueryBound (pure (root, proof) : OracleComp World _) 0 from trivial))
  have result := public_query_bound_bind (bounded 1) rest
  simpa only [queryTranscript, Nat.add_zero, Nat.add_mul, Nat.one_mul] using result

theorem query_transcript_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2 * LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Salt) (positions : Positions) :
    fixedOracleRun oracle (queryTranscript heap salt positions) =
      pure (values 1, referenceOpening values salt positions) := by
  rw [queryTranscript, fixed_oracle_run_bind, correct 1 (by decide) (by decide), pure_bind]
  rw [fixed_oracle_run_bind, query_opening_reference oracle heap values correct salt positions, pure_bind]
  exact fixed_oracle_run_pure _ _

end CommitGolfCandidate
