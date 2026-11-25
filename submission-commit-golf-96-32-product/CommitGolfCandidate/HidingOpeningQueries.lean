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

/-- The digest containing proof byte `offset`, matching `referenceProofDigest`. -/
def queryProofDigest (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) (offset : Nat) : OracleComp World Digest :=
  if offset < 4096 then heap (128+offset/32)
  else queryOpeningDigest heap salt positions ((offset-4096)/576) (((offset-4096)%576)/32)

def queryOpening (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) : OracleComp World Proof :=
  queryList (fun offset => do
    let digest ← queryProofDigest heap salt positions offset
    pure (digest.extractLsb' (8*(offset%32)) 8)) (List.range (4096+576*positions.card))

theorem query_opening_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (queryOpening heap salt positions) ((4096+576*positions.card)*budget) := by
  have digestBound (offset : Nat) :
      PublicQueryBound (queryProofDigest heap salt positions offset) budget := by
    unfold queryProofDigest queryOpeningDigest
    split
    · exact bounded _
    · split
      · trivial
      · exact bounded _
  have bytes (offset : Nat) := public_query_bound_bind (digestBound offset)
    (fun digest => (show PublicQueryBound
      (pure (digest.extractLsb' (8*(offset%32)) 8) : OracleComp World _) 0 from trivial))
  simpa only [queryOpening, List.length_range, Nat.add_zero] using
    query_list_bound _ (budget+0) bytes (List.range (4096+576*positions.card))

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
  have below := List.mem_range.mp member
  rw [fixed_oracle_run_bind]
  have digest : fixedOracleRun oracle (queryProofDigest heap salt positions offset) =
      pure (referenceProofDigest values salt positions offset) := by
    unfold queryProofDigest referenceProofDigest
    split
    · exact correct _ (by omega) (by change 128+offset/32 < 2*16777216; omega)
    · let index : Index := ⟨openingIndex positions ((offset-4096)/576),
        opening_index_bound positions ((offset-4096)/576)⟩
      unfold queryOpeningDigest referenceOpeningDigest
      split
      · exact fixed_oracle_run_pure _ _
      · have level : ((offset-4096)%576)/32-1 < 17 := by omega
        have valid := opening_cap_sibling_bounds index _ level
        exact correct _ (Nat.lt_of_le_of_lt (Nat.zero_le _) valid.1) valid.2
  rw [digest, pure_bind]
  exact fixed_oracle_run_pure _ _

/-- The commitment as an oracle program: read the 128 cap nodes, then the 64-call chain. -/
def queryCap (heap : Nat → OracleComp World Digest) : OracleComp World Digest := do
  let cap ← queryList heap ((List.range 128).map (128 + ·))
  hashBlocks (capBlocks fun node => cap.getD node 0) 0

theorem query_cap_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget) :
    PublicQueryBound (queryCap heap) (128*budget+64) := by
  have nodes := query_list_bound heap budget bounded ((List.range 128).map (128 + ·))
  simp only [List.length_map, List.length_range] at nodes
  have chain (cap : List Digest) := hash_blocks_bound (capBlocks fun node => cap.getD node 0) 0
  simp only [capBlocks, List.length_map, List.length_range] at chain
  exact public_query_bound_bind nodes chain

theorem query_cap_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2*LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node)) :
    fixedOracleRun oracle (queryCap heap) = pure (capRoot oracle.compression (referenceCap values)) := by
  unfold queryCap
  rw [fixed_oracle_run_bind, query_list_reference oracle heap values _ (by
    intro node member
    obtain ⟨m, inside, rfl⟩ := List.mem_map.mp member
    have := List.mem_range.mp inside
    exact correct _ (by omega) (by change 128+m < 2*16777216; omega)), pure_bind]
  have chained := fixed_hash_blocks oracle
    (capBlocks fun node => (((List.range 128).map (128 + ·)).map values).getD node 0) 0 pure
  simp only [bind_pure, fixed_oracle_run_pure] at chained
  rw [chained]
  refine congrArg pure ?_
  change capRoot oracle.compression _ = _
  apply cap_congr
  intro node inside
  have small : node < 128 := inside
  simp [referenceCap, small, List.getD_eq_getElem?_getD]

/-- Compute the cap-chain commitment and the exact opening proof from a common oracle. -/
def queryTranscript (heap : Nat → OracleComp World Digest) (salt : Index → Digest)
    (positions : Positions) : OracleComp World (Commitment × Proof) := do
  let root ← queryCap heap
  let proof ← queryOpening heap salt positions
  pure (root, proof)

theorem query_transcript_bound (heap : Nat → OracleComp World Digest) (budget : Nat)
    (bounded : ∀ node, PublicQueryBound (heap node) budget)
    (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (queryTranscript heap salt positions)
      ((4224+576*positions.card)*budget+64) := by
  have rest (root : Commitment) := public_query_bound_bind (query_opening_bound heap budget bounded salt positions)
    (fun proof => (show PublicQueryBound (pure (root, proof) : OracleComp World _) 0 from trivial))
  have result := public_query_bound_bind (query_cap_bound heap budget bounded) rest
  exact result.mono (le_of_eq (by ring))

theorem query_transcript_reference (oracle : Oracle) (heap : Nat → OracleComp World Digest)
    (values : Nat → Digest)
    (correct : ∀ node, 0 < node → node < 2*LENGTH →
      fixedOracleRun oracle (heap node) = pure (values node))
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryTranscript heap salt positions) =
      pure (capRoot oracle.compression (referenceCap values), referenceOpening values salt positions) := by
  rw [queryTranscript, fixed_oracle_run_bind, query_cap_reference oracle heap values correct, pure_bind]
  rw [fixed_oracle_run_bind, query_opening_reference oracle heap values correct salt positions, pure_bind]
  exact fixed_oracle_run_pure _ _

end CommitGolfCandidate
