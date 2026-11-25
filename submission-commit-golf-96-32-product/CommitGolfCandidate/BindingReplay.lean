import CommitGolfCandidate.BindingMachine

/-! Replay the two conflicting records through the actual public oracle interface.
The reduction pays for every compression call; it never reads the compression
function directly or assumes a free verification oracle. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- Replay a salted leaf chain and retain the inputs actually queried. -/
def replayChain : Digest → List LeafBlock → OracleComp World (Digest × List (BitVec COMPRESSION_INPUT_LENGTH))
  | state, [] => pure (state, [])
  | state, block :: rest => do
      let input := leafInput state block
      let next ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayChain next rest
      return (root, input :: inputs)

/-- Replay a bottom-up authentication path, retaining its compression inputs. -/
def replayPath : Digest → List (Bool × Digest) → OracleComp World (Digest × List (BitVec COMPRESSION_INPUT_LENGTH))
  | node, [] => pure (node, [])
  | node, (right, sibling) :: rest => do
      let input := if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node))
      let next ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayPath next rest
      return (root, input :: inputs)

theorem replay_chain_run (oracle : Oracle) (state : Digest) (blocks : List LeafBlock) :
    oracle.run (replayChain state blocks) =
      pure ((blocks.foldl (absorb oracle.compression) state,
        chainInputs oracle.compression state blocks), blocks.length) := by
  induction blocks generalizing state with
  | nil => exact oracle_run_pure _ _
  | cons block rest ih =>
    simp only [replayChain]
    erw [oracle_run_public_bind oracle (.inl (leafInput state block))]
    erw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure]
    simp [Oracle.answer, chainInputs, absorb, Nat.add_comm]
    exact ⟨rfl, rfl⟩

theorem replay_path_run (oracle : Oracle) (node : Digest) (path : List (Bool × Digest)) :
    oracle.run (replayPath node path) =
      pure ((climb oracle.compression node path,
        pathInputs oracle.compression node path), path.length) := by
  induction path generalizing node with
  | nil => exact oracle_run_pure _ _
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [replayPath]
    erw [oracle_run_public_bind oracle (.inl (if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node))))]
    erw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure]
    cases right <;> simp [Oracle.answer, pathInputs, climb, combine, Nat.add_comm] <;> exact ⟨rfl, rfl⟩

/-- Replay the 64-call chain over a supplied cap. -/
def replayCap (input : CheckInput) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let (_, capInputs) ← replayChain 0 (capBlocks (recordCap input))
  return capInputs

theorem replay_cap_run (oracle : Oracle) (input : CheckInput) :
    oracle.run (replayCap input) =
      pure (chainInputs oracle.compression 0 (capBlocks (recordCap input)), 64) := by
  simp only [replayCap, oracle_run_bind, replay_chain_run, pure_bind, oracle_run_pure,
    capBlocks_length, CAP_PAIRS, Nat.add_zero]

/-- The leaf chain and the path of one parsed record. -/
def replayLeafPath (input : CheckInput) (ordinal : Nat) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let (leaf, leafInputs) ← replayChain (recordSalt input ordinal) (leafBlocks (recordValue input ordinal))
  let (_, treeInputs) ← replayPath leaf (recordPath (recordIndex input ordinal) (recordSibling input ordinal))
  return leafInputs ++ treeInputs

theorem replay_leaf_path_run (oracle : Oracle) (input : CheckInput) (ordinal : Nat) :
    oracle.run (replayLeafPath input ordinal) =
      pure (openingInputs oracle.compression (recordSalt input ordinal) (recordValue input ordinal)
        (recordPath (recordIndex input ordinal) (recordSibling input ordinal)), 21) := by
  simp only [replayLeafPath, oracle_run_bind, replay_chain_run,
    bind_pure_comp, oracle_run_map, replay_path_run, map_pure]
  simp only [openingInputs, leafDigest_eq_fold, leafBlocks,
    List.length_map, List.length_range, record_path_length, PATH_LEVELS]

/-- Exactly the 85 public calls needed to reconstruct one parsed record up to the
commitment: 4 leaf calls, 17 path calls and the 64-call cap chain. -/
def replayRecord (input : CheckInput) (ordinal : Nat) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let opening ← replayLeafPath input ordinal
  let capInputs ← replayCap input
  return opening ++ capInputs

theorem replay_record_run (oracle : Oracle) (input : CheckInput) (ordinal : Nat) :
    oracle.run (replayRecord input ordinal) = pure (recordInputs oracle.compression input ordinal, 85) := by
  simp only [replayRecord, oracle_run_bind, replay_leaf_path_run, replay_cap_run, pure_bind,
    oracle_run_pure, recordInputs, capOpeningInputs]

/-- This choice depends only on the adversary's claim, not on oracle answers.
Classical choice is allowed here because the binding adversary is unrestricted
in local computation; all public oracle queries remain explicitly counted. -/
noncomputable def selectedRecords (claim : Scheme.Claim) : Nat × Nat := by
  classical
  exact if conflicting : claim.Conflicting then
    let left := Classical.choose (conflicting_records_exist claim conflicting)
    (left, Classical.choose (Classical.choose_spec (conflicting_records_exist claim conflicting)))
  else (0, 0)

theorem selected_records_conflict (claim : Scheme.Claim) (conflicting : claim.Conflicting) :
    ConflictingRecords claim (selectedRecords claim).1 (selectedRecords claim).2 := by
  classical
  simp only [selectedRecords, dif_pos conflicting]
  exact Classical.choose_spec (Classical.choose_spec (conflicting_records_exist claim conflicting))

/-- Replay both selected records. Even a nonconflicting claim costs exactly 170
queries, making the reduction's overhead independent of the adversary's output. -/
noncomputable def replayClaim (claim : Scheme.Claim) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let left ← replayRecord (claimLeft claim) (selectedRecords claim).1
  let right ← replayRecord (claimRight claim) (selectedRecords claim).2
  return left ++ right

noncomputable def claimInputs (compress : Compression) (claim : Scheme.Claim) : List (BitVec COMPRESSION_INPUT_LENGTH) :=
  recordInputs compress (claimLeft claim) (selectedRecords claim).1 ++
    recordInputs compress (claimRight claim) (selectedRecords claim).2

theorem replay_claim_run (oracle : Oracle) (claim : Scheme.Claim) :
    oracle.run (replayClaim claim) = pure (claimInputs oracle.compression claim, 170) := by
  simp only [replayClaim, oracle_run_bind, replay_record_run, pure_bind,
    oracle_run_pure, claimInputs]

/-- A collision is between distinct queried inputs, not merely a repeated query. -/
def HasCompressionCollision (compress : Compression) (inputs : List (BitVec COMPRESSION_INPUT_LENGTH)) : Prop :=
  ∃ input ∈ inputs, ∃ input' ∈ inputs, input ≠ input' ∧ compress input = compress input'

theorem breaks_replay_collision (oracle : Oracle) (claim : Scheme.Claim)
    (breaks : submission.scheme.Breaks oracle claim) :
    HasCompressionCollision oracle.compression (claimInputs oracle.compression claim) := by
  obtain ⟨input, member, input', member', collision⟩ := binding_claim_collision oracle claim
    (selectedRecords claim).1 (selectedRecords claim).2
    (selected_records_conflict claim breaks.1) breaks.2.1 breaks.2.2
  exact ⟨input, List.mem_append_left _ member, input', List.mem_append_right _ member', collision⟩

/-- The binding reduction runs the original adversary, then spends 170 calls
replaying its selected records. -/
noncomputable def bindingExtractor (adversary : Scheme.Adversary) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let claim ← adversary
  replayClaim claim

theorem binding_extractor_run (oracle : Oracle) (adversary : Scheme.Adversary) :
    oracle.run (bindingExtractor adversary) =
      (fun result => (claimInputs oracle.compression result.1, result.2 + 170)) <$>
        oracle.run adversary := by
  simp only [bindingExtractor, oracle_run_bind, replay_claim_run, pure_bind,
    map_eq_bind_pure_comp]
  rfl

/-- The replay bounds hold structurally for every possible sequence of replies,
not only for replies consistent with a fixed oracle table. -/
theorem replay_chain_query_bound (state : Digest) (blocks : List LeafBlock) :
    IsTotalQueryBound (replayChain state blocks) blocks.length := by
  induction blocks generalizing state with
  | nil => trivial
  | cons block rest ih =>
    simp only [replayChain, bind_pure_comp]
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl ((leafInput state block))))) :
      OracleComp World Digest) >>= _) (rest.length + 1)
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun next => ?_⟩
    simpa only [Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using ih next

theorem replay_path_query_bound (node : Digest) (path : List (Bool × Digest)) :
    IsTotalQueryBound (replayPath node path) path.length := by
  induction path generalizing node with
  | nil => trivial
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [replayPath, bind_pure_comp]
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl
      (if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node)))))) : OracleComp World Digest) >>= _)
      (rest.length + 1)
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun next => ?_⟩
    simpa only [Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using ih next

theorem replay_leaf_path_query_bound (input : CheckInput) (ordinal : Nat) :
    IsTotalQueryBound (replayLeafPath input ordinal) 21 := by
  unfold replayLeafPath
  change IsTotalQueryBound (_ >>= _) (4 + 17)
  apply isTotalQueryBound_bind
  · simpa only [leafBlocks, List.length_map, List.length_range] using
      replay_chain_query_bound (recordSalt input ordinal) (leafBlocks (recordValue input ordinal))
  · intro result
    simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    simpa only [record_path_length, IsTotalQueryBound] using replay_path_query_bound result.1
      (recordPath (recordIndex input ordinal) (recordSibling input ordinal))

theorem replay_cap_query_bound (input : CheckInput) : IsTotalQueryBound (replayCap input) 64 := by
  unfold replayCap
  change IsTotalQueryBound (_ >>= _) (64 + 0)
  apply isTotalQueryBound_bind
  · simpa only [capBlocks_length] using replay_chain_query_bound 0 (capBlocks (recordCap input))
  · intro result
    trivial

theorem replay_record_query_bound (input : CheckInput) (ordinal : Nat) :
    IsTotalQueryBound (replayRecord input ordinal) 85 := by
  unfold replayRecord
  change IsTotalQueryBound (_ >>= _) (21 + 64)
  apply isTotalQueryBound_bind (replay_leaf_path_query_bound _ _)
  intro opening
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using replay_cap_query_bound input

theorem replay_claim_query_bound (claim : Scheme.Claim) :
    IsTotalQueryBound (replayClaim claim) 170 := by
  unfold replayClaim
  change IsTotalQueryBound (_ >>= _) (85 + 85)
  apply isTotalQueryBound_bind (replay_record_query_bound _ _)
  intro left
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    replay_record_query_bound (claimRight claim) (selectedRecords claim).2

end CommitGolfCandidate
