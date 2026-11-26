import CommitGolfCandidate.Model

/-! Deterministic collision extraction for the submitted 16-byte tagged-salt construction. -/
namespace CommitGolfCandidate
open CommitGolf

private theorem append_injective {left right left' right' : Digest}
    (h : right ++ left = right' ++ left') : left = left' ∧ right = right' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun x : BitVec 512 => x.extractLsb' 0 256) h
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun x : BitVec 512 => x.extractLsb' 256 256) h

/-- Inputs made by the tail leaf chain, in execution order. -/
def chainInputs (compress : Compression) : Digest → List LeafBlock → List (BitVec COMPRESSION_INPUT_LENGTH)
  | _, [] => []
  | state, block :: rest =>
      leafInput state block :: chainInputs compress (absorb compress state block) rest

/-- Different starting digests or equal-length block sequences with the same final digest
produce a collision among the inputs of the two executions. -/
theorem collision_of_chain_eq (compress : Compression)
    (state state' : Digest) (blocks blocks' : List LeafBlock)
    (sameLength : blocks.length = blocks'.length)
    (different : state ≠ state' ∨ blocks ≠ blocks')
    (sameDigest : blocks.foldl (absorb compress) state =
      blocks'.foldl (absorb compress) state') :
    ∃ input ∈ chainInputs compress state blocks,
      ∃ input' ∈ chainInputs compress state' blocks',
        input ≠ input' ∧ compress input = compress input' := by
  induction blocks generalizing state state' blocks' with
  | nil =>
    cases blocks' with
    | nil => simp_all
    | cons block rest => simp at sameLength
  | cons block rest ih =>
    cases blocks' with
    | nil => simp at sameLength
    | cons block' rest' =>
      by_cases inputsEqual : leafInput state block = leafInput state' block'
      · obtain ⟨rfl, rfl⟩ := leafInput_injective inputsEqual
        have tailsDifferent : rest ≠ rest' := by
          intro h
          subst rest'
          simp at different
        obtain ⟨input, hInput, input', hInput', hCollision⟩ :=
          ih _ _ rest' (by simpa using sameLength) (Or.inr tailsDifferent) sameDigest
        exact ⟨input, List.mem_cons_of_mem _ hInput, input',
          List.mem_cons_of_mem _ hInput', hCollision⟩
      · by_cases nextEqual : absorb compress state block = absorb compress state' block'
        · exact ⟨_, List.mem_cons_self .., _, List.mem_cons_self .., inputsEqual, nextEqual⟩
        · obtain ⟨input, hInput, input', hInput', hCollision⟩ :=
            ih _ _ rest' (by simpa using sameLength) (Or.inl nextEqual) sameDigest
          exact ⟨input, List.mem_cons_of_mem _ hInput, input',
            List.mem_cons_of_mem _ hInput', hCollision⟩

/-- Compression inputs of a bottom-up authentication path. -/
def pathInputs (compress : Compression) : Digest → List (Bool × Digest) → List (BitVec COMPRESSION_INPUT_LENGTH)
  | _, [] => []
  | node, (right, sibling) :: rest =>
      let input := if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node))
      input :: pathInputs compress (compress input) rest

/-- Conflicting leaf digests at the same position that verify against one root
produce a compression collision on the two authentication paths. -/
theorem collision_of_climb_eq (compress : Compression)
    (leaf leaf' : Digest) (path path' : List (Bool × Digest))
    (samePosition : path.map Prod.fst = path'.map Prod.fst)
    (different : leaf ≠ leaf')
    (sameRoot : climb compress leaf path = climb compress leaf' path') :
    ∃ input ∈ pathInputs compress leaf path,
      ∃ input' ∈ pathInputs compress leaf' path',
        input ≠ input' ∧ compress input = compress input' := by
  induction path generalizing leaf leaf' path' with
  | nil =>
    cases path' with
    | nil => exact different sameRoot |>.elim
    | cons head rest => simp at samePosition
  | cons head rest ih =>
    cases path' with
    | nil => simp at samePosition
    | cons head' rest' =>
      rcases head with ⟨right, sibling⟩
      rcases head' with ⟨right', sibling'⟩
      simp only [List.map_cons, List.cons.injEq] at samePosition
      obtain ⟨rfl, tailsEqual⟩ := samePosition
      let input : BitVec COMPRESSION_INPUT_LENGTH := if right then (padInput (leaf ++ sibling)) else (padInput (sibling ++ leaf))
      let input' : BitVec COMPRESSION_INPUT_LENGTH := if right then (padInput (leaf' ++ sibling')) else (padInput (sibling' ++ leaf'))
      have inputsDifferent : input ≠ input' := by
        intro h
        cases right <;> simp only [input, input', if_true, Bool.false_eq_true, if_false] at h
        · exact different (append_injective (padInput_injective h)).1
        · exact different (append_injective (padInput_injective h)).2
      have tailRoots : climb compress (compress input) rest =
          climb compress (compress input') rest' := by
        cases right <;> simpa [climb, combine, input, input'] using sameRoot
      by_cases nextEqual : compress input = compress input'
      · exact ⟨_, List.mem_cons_self .., _, List.mem_cons_self .., inputsDifferent, nextEqual⟩
      · obtain ⟨x, hx, y, hy, hCollision⟩ :=
          ih _ _ rest' tailsEqual nextEqual tailRoots
        exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hCollision⟩

/-- The 72-byte head together with the three 64-byte tail blocks uniquely determine the 256-byte leaf entry. -/
theorem leaf_head_and_tail_injective (value value' : Entry)
    (headEq : value.extractLsb' 0 576 = value'.extractLsb' 0 576)
    (tailEq : leafTailBlocks value = leafTailBlocks value') :
    value = value' := by
  have hblocks :
      [value.extractLsb' 512 512, value.extractLsb' 1024 512, value.extractLsb' 1536 512] =
      [value'.extractLsb' 512 512, value'.extractLsb' 1024 512, value'.extractLsb' 1536 512] := by
    simpa [leafTailBlocks, List.range_succ] using tailEq
  have b1 : value.extractLsb' 512 512 = value'.extractLsb' 512 512 := (List.cons.inj hblocks).1
  have b2 : value.extractLsb' 1024 512 = value'.extractLsb' 1024 512 := (List.cons.inj (List.cons.inj hblocks).2).1
  have b3 : value.extractLsb' 1536 512 = value'.extractLsb' 1536 512 :=
    (List.cons.inj (List.cons.inj (List.cons.inj hblocks).2).2).1
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  change bit < 2048 at hbit
  by_cases h0 : bit < 512
  · have := congrArg (fun x : BitVec 576 => x.getLsbD bit) headEq
    simpa [BitVec.getLsbD_extractLsb', show bit < 576 by omega] using this
  · by_cases h1 : bit < 1024
    · have := congrArg (fun x : LeafBlock => x.getLsbD (bit - 512)) b1
      simpa [BitVec.getLsbD_extractLsb', show bit - 512 < 512 by omega, show 512 + (bit - 512) = bit by omega] using this
    · by_cases h2 : bit < 1536
      · have := congrArg (fun x : LeafBlock => x.getLsbD (bit - 1024)) b2
        simpa [BitVec.getLsbD_extractLsb', show bit - 1024 < 512 by omega, show 1024 + (bit - 1024) = bit by omega] using this
      · have := congrArg (fun x : LeafBlock => x.getLsbD (bit - 1536)) b3
        simpa [BitVec.getLsbD_extractLsb', show bit - 1536 < 512 by omega, show 1536 + (bit - 1536) = bit by omega] using this

/-- The four compression inputs of one position-tagged salted leaf evaluation. -/
def leafChainInputs (compress : Compression) (index : Index) (salt : Salt) (value : Entry) :
    List (BitVec COMPRESSION_INPUT_LENGTH) :=
  let init := leafInitInput index salt value
  init :: chainInputs compress (compress init) (leafTailBlocks value)

theorem leafDigest_eq_tail_fold (compress : Compression) (index : Index) (salt : Salt) (value : Entry) :
    leafDigest compress index salt value =
      (leafTailBlocks value).foldl (absorb compress) (compress (leafInitInput index salt value)) := rfl

/-- All compression inputs needed to verify one position (4 leaf + 24 path = 28). -/
def openingInputs (compress : Compression) (index : Index) (salt : Salt) (value : Entry)
    (path : List (Bool × Digest)) : List (BitVec COMPRESSION_INPUT_LENGTH) :=
  leafChainInputs compress index salt value ++
    pathInputs compress (leafDigest compress index salt value) path

theorem chainInputs_length (compress : Compression) (state : Digest) (blocks : List LeafBlock) :
    (chainInputs compress state blocks).length = blocks.length := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih => simp only [chainInputs, List.length_cons, ih]

theorem pathInputs_length (compress : Compression) (node : Digest)
    (path : List (Bool × Digest)) : (pathInputs compress node path).length = path.length := by
  induction path generalizing node with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [pathInputs, List.length_cons]
    exact congrArg (fun n : Nat => n + 1) (ih _)

theorem openingInputs_length (compress : Compression) (index : Index) (salt : Salt) (value : Entry)
    (path : List (Bool × Digest)) :
    (openingInputs compress index salt value path).length = 4 + path.length := by
  unfold openingInputs leafChainInputs
  rw [List.length_append, List.length_cons, pathInputs_length]
  have hlen : (chainInputs compress (compress (leafInitInput index salt value)) (leafTailBlocks value)).length =
      (leafTailBlocks value).length :=
    chainInputs_length compress (compress (leafInitInput index salt value)) (leafTailBlocks value)
  rw [hlen]
  simp [leafTailBlocks]

/-- Two different opened values at the same position and root force a compression collision. -/
theorem collision_of_openings_eq (compress : Compression) (index : Index)
    (salt salt' : Salt) (value value' : Entry) (path path' : List (Bool × Digest))
    (samePosition : path.map Prod.fst = path'.map Prod.fst)
    (different : value ≠ value')
    (sameRoot : climb compress (leafDigest compress index salt value) path =
      climb compress (leafDigest compress index salt' value') path') :
    ∃ input ∈ openingInputs compress index salt value path,
      ∃ input' ∈ openingInputs compress index salt' value' path',
        input ≠ input' ∧ compress input = compress input' := by
  by_cases leavesEqual : leafDigest compress index salt value = leafDigest compress index salt' value'
  · let init := leafInitInput index salt value
    let init' := leafInitInput index salt' value'
    by_cases stepDiff : compress init ≠ compress init' ∨ leafTailBlocks value ≠ leafTailBlocks value'
    · obtain ⟨x, hx, y, hy, collision⟩ := collision_of_chain_eq compress (compress init) (compress init')
        (leafTailBlocks value) (leafTailBlocks value') (by simp [leafTailBlocks])
        stepDiff (by simpa only [leafDigest_eq_tail_fold] using leavesEqual)
      exact ⟨x, List.mem_append_left _ (List.mem_cons_of_mem _ hx),
        y, List.mem_append_left _ (List.mem_cons_of_mem _ hy), collision⟩
    · push Not at stepDiff
      have initNeq : init ≠ init' := by
        intro eq
        have headEq : value.extractLsb' 0 576 = value'.extractLsb' 0 576 := by
          have h := congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => x.extractLsb' 192 576) eq
          simpa only [init, init', leafInitInput_head] using h
        exact different (leaf_head_and_tail_injective value value' headEq stepDiff.2)
      exact ⟨init, List.mem_append_left _ (List.mem_cons_self ..),
        init', List.mem_append_left _ (List.mem_cons_self ..), initNeq, stepDiff.1⟩
  · obtain ⟨x, hx, y, hy, collision⟩ := collision_of_climb_eq compress _ _ path path'
      samePosition leavesEqual sameRoot
    exact ⟨x, List.mem_append_right _ hx, y, List.mem_append_right _ hy, collision⟩

end CommitGolfCandidate
