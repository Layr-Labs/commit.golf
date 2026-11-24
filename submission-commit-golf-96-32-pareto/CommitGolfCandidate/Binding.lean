import CommitGolfCandidate.Model

/-! Deterministic collision extraction for the submitted construction. These lemmas
identify actual compression inputs; the random-oracle probability bound and machine
refinement are separate obligations. -/
namespace CommitGolfCandidate
open CommitGolf

private theorem append_injective {left right left' right' : Digest}
    (h : right ++ left = right' ++ left') : left = left' ∧ right = right' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun x : BitVec 512 => x.extractLsb' 0 256) h
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun x : BitVec 512 => x.extractLsb' 256 256) h

/-- Inputs made by the salted leaf chain, in execution order. -/
def chainInputs (compress : Compression) : Digest → List Digest → List (BitVec COMPRESSION_INPUT_LENGTH)
  | _, [] => []
  | state, block :: rest =>
      ((padInput (block ++ state))) :: chainInputs compress (combine compress state block) rest

/-- Different salts or equal-length block sequences with the same final digest
produce a collision among the inputs of the two executions. -/
theorem collision_of_chain_eq (compress : Compression)
    (state state' : Digest) (blocks blocks' : List Digest)
    (sameLength : blocks.length = blocks'.length)
    (different : state ≠ state' ∨ blocks ≠ blocks')
    (sameDigest : blocks.foldl (combine compress) state =
      blocks'.foldl (combine compress) state') :
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
      by_cases inputsEqual : (padInput (block ++ state)) = (padInput (block' ++ state'))
      · obtain ⟨rfl, rfl⟩ := append_injective (padInput_injective inputsEqual)
        have tailsDifferent : rest ≠ rest' := by
          intro h
          subst rest'
          simp at different
        obtain ⟨input, hInput, input', hInput', hCollision⟩ :=
          ih _ _ rest' (by simpa using sameLength) (Or.inr tailsDifferent) sameDigest
        exact ⟨input, List.mem_cons_of_mem _ hInput, input',
          List.mem_cons_of_mem _ hInput', hCollision⟩
      · by_cases nextEqual : combine compress state block = combine compress state' block'
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


/-- The eight blocks absorbed by the leaf routine, in little-endian order. -/
def leafBlocks (value : Entry) : List Digest :=
  (List.range 8).map fun block => value.extractLsb' (256 * block) 256

theorem leafBlocks_injective : Function.Injective leafBlocks := by
  intro value value' h
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have blockBound : bit / 256 < 8 := by
    change bit < 2048 at hbit
    omega
  have blockEqual := List.map_inj_left.mp h (bit / 256) (List.mem_range.mpr blockBound)
  have bitEqual := congrArg (fun block : Digest => block.getLsbD (bit % 256)) blockEqual
  have offset : 256 * (bit / 256) + bit % 256 = bit := by omega
  simpa [BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 256), offset] using bitEqual

theorem leafDigest_eq_fold (compress : Compression) (salt : Digest) (value : Entry) :
    leafDigest compress salt value = (leafBlocks value).foldl (combine compress) salt := by
  simp [leafDigest, leafBlocks, List.foldl_map]

/-- All compression inputs needed to verify one position. -/
def openingInputs (compress : Compression) (salt : Digest) (value : Entry)
    (path : List (Bool × Digest)) : List (BitVec COMPRESSION_INPUT_LENGTH) :=
  chainInputs compress salt (leafBlocks value) ++
    pathInputs compress (leafDigest compress salt value) path

theorem chainInputs_length (compress : Compression) (state : Digest) (blocks : List Digest) :
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

/-- A collision extractor need only replay eight leaf calls and one per tree level
for each of the two conflicting positions, independently of the opening batch size. -/
theorem openingInputs_length (compress : Compression) (salt : Digest) (value : Entry)
    (path : List (Bool × Digest)) :
    (openingInputs compress salt value path).length = 8 + path.length := by
  simp [openingInputs, chainInputs_length, pathInputs_length, leafBlocks]

/-- Two different opened values at the same position and root force a collision.
This covers collisions inside the salted leaf chain as well as in the tree path. -/
theorem collision_of_openings_eq (compress : Compression)
    (salt salt' : Digest) (value value' : Entry) (path path' : List (Bool × Digest))
    (samePosition : path.map Prod.fst = path'.map Prod.fst)
    (different : value ≠ value')
    (sameRoot : climb compress (leafDigest compress salt value) path =
      climb compress (leafDigest compress salt' value') path') :
    ∃ input ∈ openingInputs compress salt value path,
      ∃ input' ∈ openingInputs compress salt' value' path',
        input ≠ input' ∧ compress input = compress input' := by
  by_cases leavesEqual : leafDigest compress salt value = leafDigest compress salt' value'
  · have blocksDifferent : leafBlocks value ≠ leafBlocks value' :=
      fun h => different (leafBlocks_injective h)
    obtain ⟨x, hx, y, hy, collision⟩ := collision_of_chain_eq compress salt salt'
      (leafBlocks value) (leafBlocks value') (by simp [leafBlocks])
      (Or.inr blocksDifferent) (by simpa only [leafDigest_eq_fold] using leavesEqual)
    exact ⟨x, List.mem_append_left _ hx, y, List.mem_append_left _ hy, collision⟩
  · obtain ⟨x, hx, y, hy, collision⟩ := collision_of_climb_eq compress _ _ path path'
      samePosition leavesEqual sameRoot
    exact ⟨x, List.mem_append_right _ hx, y, List.mem_append_right _ hy, collision⟩

end CommitGolfCandidate
