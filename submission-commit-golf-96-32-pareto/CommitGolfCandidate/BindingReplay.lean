import CommitGolfCandidate.BindingMachine

/-! Replay the two conflicting records through the actual public oracle interface.
For normal proofs (`k ≠ 128`) replay uses 28 compression calls per record; for cap-table
proofs (`k = 128`) replay first reconstructs the 7 upper cap-tree siblings (120 calls)
and then replays the 28-call tagged-salt leaf-and-path sequence (148 calls total). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec

/-- Replay a tail leaf chain and retain the inputs actually queried. -/
def replayChain : Digest → List LeafBlock → OracleComp World (Digest × List (BitVec COMPRESSION_INPUT_LENGTH))
  | state, [] => pure (state, [])
  | state, block :: rest => do
      let input := leafInput state block
      let next ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayChain next rest
      return (root, input :: inputs)

/-- Replay Call 0 and the three tail blocks of one tagged salted leaf. -/
def replayLeaf (index : Index) (salt : Salt) (value : Entry) :
    OracleComp World (Digest × List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let init := leafInitInput index salt value
  let d0 ← (liftM (World.query (.inr (.inl init))) : OracleComp World Digest)
  let (leaf, tailInputs) ← replayChain d0 (leafTailBlocks value)
  return (leaf, init :: tailInputs)

/-- Replay a bottom-up authentication path, retaining its compression inputs. -/
def replayPath : Digest → List (Bool × Digest) → OracleComp World (Digest × List (BitVec COMPRESSION_INPUT_LENGTH))
  | node, [] => pure (node, [])
  | node, (right, sibling) :: rest => do
      let input := if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node))
      let next ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayPath next rest
      return (root, input :: inputs)

/-- Replay the binary subtree of `referenceHeap compress 128 cap` rooted at `node`
with `height` levels above the 128 leaves at slots `128..255`. Uses `2 ^ height - 1` calls. -/
def replayCapNode (cap : Nat → Digest) : Nat → Nat → OracleComp World Digest
  | 0, node => pure (cap (node - 128))
  | height + 1, node => do
      let left ← replayCapNode cap height (2 * node)
      let right ← replayCapNode cap height (2 * node + 1)
      let out ← (liftM (World.query (.inr (.inl (padInput (right ++ left))))) : OracleComp World Digest)
      pure out

def replayCapUpperLevel (cap : Nat → Digest) (index : Index) (h : Nat) :
    OracleComp World (Bool × Digest) := do
  let sibling ← replayCapNode cap h (((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1)
  return (index.val.testBit (17 + h), sibling)

/-- Replay all 7 upper siblings of a cap-mode record (heights 0..6, 120 calls total). -/
def replayCapUpper (cap : Nat → Digest) (index : Index) :
    OracleComp World (Fin 7 → Bool × Digest) := do
  let s0 ← replayCapUpperLevel cap index 0
  let s1 ← replayCapUpperLevel cap index 1
  let s2 ← replayCapUpperLevel cap index 2
  let s3 ← replayCapUpperLevel cap index 3
  let s4 ← replayCapUpperLevel cap index 4
  let s5 ← replayCapUpperLevel cap index 5
  let s6 ← replayCapUpperLevel cap index 6
  return fun k =>
    match k.val with
    | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | _ => s6

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

theorem replay_leaf_run (oracle : Oracle) (index : Index) (salt : Salt) (value : Entry) :
    oracle.run (replayLeaf index salt value) =
      pure ((leafDigest oracle.compression index salt value,
        leafChainInputs oracle.compression index salt value), 4) := by
  simp only [replayLeaf]
  erw [oracle_run_public_bind oracle (.inl (leafInitInput index salt value))]
  erw [oracle_run_bind, replay_chain_run]
  simp only [pure_bind, oracle_run_pure, leafTailBlocks, List.length_cons, List.length_nil]
  rfl

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

theorem replay_cap_node_run (oracle : Oracle) (cap : Nat → Digest) (height node : Nat)
    (lo : 128 ≤ 2 ^ height * node) (hi : 2 ^ height * (node + 1) ≤ 256) :
    oracle.run (replayCapNode cap height node) =
      pure (referenceHeap oracle.compression 128 cap node, 2 ^ height - 1) := by
  induction height generalizing node with
  | zero =>
    rw [replayCapNode, oracle_run_pure]
    have hLeaf : referenceHeap oracle.compression 128 cap node = cap (node - 128) := by
      have h := reference_heap_leaf oracle.compression 128 cap (node - 128) (by simp at lo hi; omega)
      rw [show 128 + (node - 128) = node by simp at lo hi; omega] at h
      exact h
    rw [hLeaf]; rfl
  | succ height ih =>
    have hPow : 2 ^ (height + 1) = 2 * 2 ^ height := by rw [Nat.pow_succ]; omega
    have pos1 : 1 ≤ 2 ^ height := Nat.one_le_two_pow
    have hNodePos : 0 < node := by
      by_contra h0; have : node = 0 := by omega
      subst node; simp at lo
    have hNodeLt : node < 128 := by
      rw [hPow, Nat.mul_comm 2, Nat.mul_assoc] at hi
      have := Nat.mul_le_mul_right (2 * (node + 1)) pos1
      omega
    have leftLo : 128 ≤ 2 ^ height * (2 * node) := by rw [hPow] at lo; linarith
    have leftHi : 2 ^ height * (2 * node + 1) ≤ 256 := by rw [hPow] at hi; nlinarith
    have rightLo : 128 ≤ 2 ^ height * (2 * node + 1) := by rw [hPow] at lo; nlinarith
    have rightHi : 2 ^ height * (2 * node + 1 + 1) ≤ 256 := by rw [hPow] at hi; linarith
    simp only [replayCapNode]
    erw [oracle_run_bind, ih (2 * node) leftLo leftHi]
    simp only [pure_bind]
    erw [oracle_run_bind, ih (2 * node + 1) rightLo rightHi]
    simp only [pure_bind]
    erw [oracle_run_public_bind oracle (.inl (padInput _))]
    erw [oracle_run_pure]
    simp only [pure_bind, Oracle.answer]
    have hRef := (reference_heap_parent oracle.compression 128 cap node hNodePos hNodeLt).symm
    change pure (combine oracle.compression _ _, (2 ^ height - 1) + ((2 ^ height - 1) + (1 + 0))) = _
    rw [hRef]
    congr 2; omega

private theorem cap_sibling_node_bounds (index : Index) (h : Nat) (hh : h < 7) :
    128 ≤ 2 ^ h * (((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1) ∧
    2 ^ h * ((((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1) + 1) ≤ 256 := by
  have hlt : index.val < 2 ^ 24 := index.isLt
  have hq : index.val / 2 ^ 17 < 128 := by omega
  let x := (128 + index.val / 2 ^ 17) / 2 ^ h
  have hEvenPow : 2 ^ (7 - h) % 2 = 0 := by
    have : 7 - h = (6 - h) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have hpow : 2 ^ h * 2 ^ (7 - h) = 128 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have xLo : 2 ^ (7 - h) ≤ x :=
    (Nat.le_div_iff_mul_le (by positivity)).mpr (by rw [Nat.mul_comm, hpow]; omega)
  have xHi : x < 2 * 2 ^ (7 - h) :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by
      have : 2 * 2 ^ (7 - h) * 2 ^ h = 256 := by
        rw [Nat.mul_assoc, Nat.mul_comm (2 ^ (7 - h)), hpow]
      omega)
  have sxBounds : 2 ^ (7 - h) ≤ x ^^^ 1 ∧ (x ^^^ 1) + 1 ≤ 2 * 2 ^ (7 - h) := by
    by_cases even : x % 2 = 0
    · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]; omega
    · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]; omega
  constructor
  · calc 128 = 2 ^ h * 2 ^ (7 - h) := hpow.symm
      _ ≤ 2 ^ h * (x ^^^ 1) := Nat.mul_le_mul_left _ sxBounds.1
  · calc 2 ^ h * ((x ^^^ 1) + 1) ≤ 2 ^ h * (2 * 2 ^ (7 - h)) := Nat.mul_le_mul_left _ sxBounds.2
      _ = 2 * (2 ^ h * 2 ^ (7 - h)) := by ring
      _ = 256 := by rw [hpow]

theorem replay_cap_upper_level_run (oracle : Oracle) (cap : Nat → Digest)
    (index : Index) (h : Nat) (hh : h < 7) :
    oracle.run (replayCapUpperLevel cap index h) =
      pure ((index.val.testBit (17 + h),
        referenceHeap oracle.compression 128 cap (((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1)),
        2 ^ h - 1) := by
  have bounds := cap_sibling_node_bounds index h hh
  simp only [replayCapUpperLevel, oracle_run_bind, replay_cap_node_run oracle cap h _ bounds.1 bounds.2,
    pure_bind, oracle_run_pure, Nat.add_zero]

theorem replay_cap_upper_run (oracle : Oracle) (cap : Nat → Digest) (index : Index) :
    oracle.run (replayCapUpper cap index) =
      pure (fun k : Fin 7 => (index.val.testBit (17 + k.val),
        referenceHeap oracle.compression 128 cap (((128 + index.val / 2 ^ 17) / 2 ^ k.val) ^^^ 1)),
        120) := by
  simp only [replayCapUpper, oracle_run_bind,
    replay_cap_upper_level_run oracle cap index 0 (by decide),
    replay_cap_upper_level_run oracle cap index 1 (by decide),
    replay_cap_upper_level_run oracle cap index 2 (by decide),
    replay_cap_upper_level_run oracle cap index 3 (by decide),
    replay_cap_upper_level_run oracle cap index 4 (by decide),
    replay_cap_upper_level_run oracle cap index 5 (by decide),
    replay_cap_upper_level_run oracle cap index 6 (by decide),
    pure_bind, oracle_run_pure]
  congr 1
  refine Prod.ext ?_ ?_
  · funext ⟨k, hk⟩
    interval_cases k <;> rfl
  · norm_num

/-- Exact query cost of replaying one record (`148` in cap mode, `28` in normal mode). -/
def replayRecordCost (input : CheckInput) : Nat :=
  if input.positions.card = BATCH then 148 else 28

theorem replay_record_cost_le (input : CheckInput) : replayRecordCost input ≤ 148 := by
  unfold replayRecordCost; split <;> decide

/-- Replay one parsed record through the public oracle interface. -/
def replayRecord (input : CheckInput) (ordinal : Nat) :
    OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let (leaf, leafInputs) ← replayLeaf (recordIndex input ordinal) (recordSalt input ordinal) (recordValue input ordinal)
  if input.positions.card = BATCH then
    let upper ← replayCapUpper (recordCap input) (recordIndex input ordinal)
    let lower := (List.range 17).map fun level =>
      ((recordIndex input ordinal).val.testBit level,
        readBuffer (submission.initialState .check input)
          (submission.layout.proof + 560 * ordinal + 16 + 32 * level) 32)
    let (_, treeInputs) ← replayPath leaf (lower ++ List.ofFn upper)
    return leafInputs ++ treeInputs
  else
    let siblings := fun level =>
      readBuffer (submission.initialState .check input)
        (submission.layout.proof + 784 * ordinal + 16 + 32 * level) 32
    let (_, treeInputs) ← replayPath leaf (recordPath (recordIndex input ordinal) siblings)
    return leafInputs ++ treeInputs

private theorem range_24_split_replay :
    List.range 24 = List.range 17 ++ (List.range 7).map (· + 17) := by
  decide

theorem replay_record_run (oracle : Oracle) (input : CheckInput) (ordinal : Nat) :
    oracle.run (replayRecord input ordinal) =
      pure (recordInputs oracle.compression input ordinal, replayRecordCost input) := by
  unfold replayRecord replayRecordCost
  rw [oracle_run_bind, replay_leaf_run, pure_bind]
  dsimp only
  by_cases batch : input.positions.card = BATCH
  · simp only [if_pos batch]
    erw [oracle_run_bind, replay_cap_upper_run]
    simp only [pure_bind]
    erw [oracle_run_bind, replay_path_run]
    simp only [pure_bind, oracle_run_pure]
    have pathEq :
        ((List.range 17).map fun level =>
          ((recordIndex input ordinal).val.testBit level,
            (readBuffer (submission.initialState .check input)
              (submission.layout.proof + 560 * ordinal + 16 + 32 * level) 32 : Digest))) ++
        List.ofFn (fun k : Fin 7 =>
          ((recordIndex input ordinal).val.testBit (17 + k.val),
            referenceHeap oracle.compression 128 (recordCap input)
              (((128 + (recordIndex input ordinal).val / 2 ^ 17) / 2 ^ k.val) ^^^ 1))) =
        recordPath (recordIndex input ordinal) (recordSibling oracle.compression input ordinal) := by
      unfold recordPath recordPathPrefix
      rw [range_24_split_replay, List.map_append, List.map_map]
      refine congrArg₂ List.append ?_ ?_
      · apply List.map_congr_left
        intro level hmem
        have hlt : level < 17 := List.mem_range.mp hmem
        simp only [recordSibling, if_pos batch, if_pos hlt]
      · apply List.ext_getElem
        · simp
        · intro k hk1 hk2
          have hk : k < 7 := by simp at hk1; exact hk1
          simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply,
            recordSibling, if_pos batch, if_neg (show ¬ (k + 17 < 17) by omega),
            Nat.add_sub_cancel, Nat.add_comm 17 k]
    erw [pathEq]
    simp only [recordInputs, openingInputs, record_path_length]
  · simp only [if_neg batch]
    erw [oracle_run_bind, replay_path_run]
    simp only [pure_bind, oracle_run_pure]
    have pathEq :
        recordPath (recordIndex input ordinal) (fun level =>
          (readBuffer (submission.initialState .check input)
            (submission.layout.proof + 784 * ordinal + 16 + 32 * level) 32 : Digest)) =
        recordPath (recordIndex input ordinal) (recordSibling oracle.compression input ordinal) := by
      unfold recordPath recordPathPrefix
      apply List.map_congr_left
      intro level _
      simp only [recordSibling, if_neg batch]
    erw [pathEq]
    simp only [recordInputs, openingInputs, record_path_length]

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

/-- Replay both selected records (at most 296 calls total). -/
noncomputable def replayClaim (claim : Scheme.Claim) :
    OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let left ← replayRecord (claimLeft claim) (selectedRecords claim).1
  let right ← replayRecord (claimRight claim) (selectedRecords claim).2
  return left ++ right

def replayClaimCost (claim : Scheme.Claim) : Nat :=
  replayRecordCost (claimLeft claim) + replayRecordCost (claimRight claim)

theorem replay_claim_cost_le (claim : Scheme.Claim) : replayClaimCost claim ≤ 296 := by
  unfold replayClaimCost
  have h1 := replay_record_cost_le (claimLeft claim)
  have h2 := replay_record_cost_le (claimRight claim)
  omega

noncomputable def claimInputs (compress : Compression) (claim : Scheme.Claim) :
    List (BitVec COMPRESSION_INPUT_LENGTH) :=
  recordInputs compress (claimLeft claim) (selectedRecords claim).1 ++
    recordInputs compress (claimRight claim) (selectedRecords claim).2

theorem replay_claim_run (oracle : Oracle) (claim : Scheme.Claim) :
    oracle.run (replayClaim claim) =
      pure (claimInputs oracle.compression claim, replayClaimCost claim) := by
  simp only [replayClaim, oracle_run_bind, replay_record_run, pure_bind,
    oracle_run_pure, claimInputs, replayClaimCost, Nat.add_zero]

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

/-- The binding reduction runs the original adversary, then replays its selected records. -/
noncomputable def bindingExtractor (adversary : Scheme.Adversary) :
    OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let claim ← adversary
  replayClaim claim

theorem binding_extractor_run (oracle : Oracle) (adversary : Scheme.Adversary) :
    oracle.run (bindingExtractor adversary) =
      (fun result => (claimInputs oracle.compression result.1, result.2 + replayClaimCost result.1)) <$>
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

theorem replay_leaf_query_bound (index : Index) (salt : Salt) (value : Entry) :
    IsTotalQueryBound (replayLeaf index salt value) 4 := by
  simp only [replayLeaf, bind_pure_comp]
  change IsTotalQueryBound ((liftM (World.query (.inr (.inl (leafInitInput index salt value)))) :
    OracleComp World Digest) >>= _) (3 + 1)
  erw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun d0 => ?_⟩
  have hq := replay_chain_query_bound d0 (leafTailBlocks value)
  have hlen : (leafTailBlocks value).length = 3 := by simp [leafTailBlocks]
  rw [hlen] at hq
  simpa only [Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using hq

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

theorem replay_cap_node_query_bound (cap : Nat → Digest) (height node : Nat) :
    IsTotalQueryBound (replayCapNode cap height node) (2 ^ height - 1) := by
  induction height generalizing node with
  | zero => trivial
  | succ height ih =>
    unfold replayCapNode
    have eqPow : 2 ^ (height + 1) - 1 = (2 ^ height - 1) + ((2 ^ height - 1) + 1) := by
      have pos : 1 ≤ 2 ^ height := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    rw [eqPow]
    apply isTotalQueryBound_bind (ih (2 * node))
    intro left
    apply isTotalQueryBound_bind (ih (2 * node + 1))
    intro right
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl (padInput (right ++ left))))) :
      OracleComp World Digest) >>= pure) 1
    erw [isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => trivial⟩

theorem replay_cap_upper_level_query_bound (cap : Nat → Digest) (index : Index) (h : Nat) :
    IsTotalQueryBound (replayCapUpperLevel cap index h) (2 ^ h - 1) := by
  unfold replayCapUpperLevel
  simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  exact replay_cap_node_query_bound cap h _

theorem replay_cap_upper_query_bound (cap : Nat → Digest) (index : Index) :
    IsTotalQueryBound (replayCapUpper cap index) 120 := by
  unfold replayCapUpper
  change IsTotalQueryBound (_ >>= _) (0 + (1 + (3 + (7 + (15 + (31 + (63 + 0)))))))
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 0); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 1); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 2); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 3); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 4); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 5); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 6); intro _
  trivial

theorem replay_record_query_bound (input : CheckInput) (ordinal : Nat) :
    IsTotalQueryBound (replayRecord input ordinal) (replayRecordCost input) := by
  unfold replayRecord replayRecordCost
  by_cases batch : input.positions.card = BATCH
  · simp only [if_pos batch]
    change IsTotalQueryBound (_ >>= _) (4 + (120 + 24))
    apply isTotalQueryBound_bind (replay_leaf_query_bound _ _ _)
    intro result
    apply isTotalQueryBound_bind (replay_cap_upper_query_bound (recordCap input) (recordIndex input ordinal))
    intro upper
    simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    let p : List (Bool × Digest) :=
      ((List.range 17).map fun level =>
        ((recordIndex input ordinal).val.testBit level,
          (readBuffer (submission.initialState .check input)
            (submission.layout.proof + 560 * ordinal + 16 + 32 * level) 32 : Digest))) ++
      List.ofFn upper
    have lenEq : p.length = 24 := by simp [p]
    have hq := replay_path_query_bound result.1 p
    rw [lenEq] at hq
    exact hq
  · simp only [if_neg batch]
    change IsTotalQueryBound (_ >>= _) (4 + 24)
    apply isTotalQueryBound_bind (replay_leaf_query_bound _ _ _)
    intro result
    simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    simpa only [record_path_length, IsTotalQueryBound] using replay_path_query_bound result.1
      (recordPath (recordIndex input ordinal) _)

theorem replay_claim_query_bound (claim : Scheme.Claim) :
    IsTotalQueryBound (replayClaim claim) (replayClaimCost claim) := by
  unfold replayClaim replayClaimCost
  apply isTotalQueryBound_bind (replay_record_query_bound _ _)
  intro left
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    replay_record_query_bound (claimRight claim) (selectedRecords claim).2

end CommitGolfCandidate
