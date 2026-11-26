import CommitGolfCandidate.Programs

/-! Pure reference functions for the machine's byte ordering and Merkle construction.
The compression function is an explicit argument, so correctness can be stated for
all oracle realizations. These definitions are not a substitute for machine refinement. -/
namespace CommitGolfCandidate
open CommitGolf

abbrev Digest := BitVec 256

/-- The first buffer half is the low half of the little-endian oracle input. -/
def combine (compress : Compression) (left right : Digest) : Digest :=
  compress ((padInput (right ++ left)))

/-- A leaf absorbs 512 message bits per call. -/
abbrev LeafBlock := BitVec 512

/-- One leaf call: the chaining value occupies the low 256 bits (first 32 bytes in memory),
followed by the 64-byte message block. No padding is involved. -/
def leafInput (state : Digest) (block : LeafBlock) : BitVec COMPRESSION_INPUT_LENGTH :=
  block ++ state

def absorb (compress : Compression) (state : Digest) (block : LeafBlock) : Digest :=
  compress (leafInput state block)

@[simp] theorem leafInput_digest (state : Digest) (block : LeafBlock) :
    (leafInput state block).extractLsb' 0 256 = state :=
  BitVec.extractLsb'_append_eq_right

@[simp] theorem leafInput_block (state : Digest) (block : LeafBlock) :
    (leafInput state block).extractLsb' 256 512 = block :=
  BitVec.extractLsb'_append_eq_left

theorem leafInput_injective {state state' : Digest} {block block' : LeafBlock}
    (same : leafInput state block = leafInput state' block') : state = state' ∧ block = block' := by
  constructor
  · simpa only [leafInput_digest] using
      congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => x.extractLsb' 0 256) same
  · simpa only [leafInput_block] using
      congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => x.extractLsb' 256 512) same

def leafDigest (compress : Compression) (salt : Digest) (value : Entry) : Digest :=
  (List.range 4).foldl
    (fun state block => absorb compress state (value.extractLsb' (512 * block) 512)) salt

/-- A 24-byte salt as the initial leaf state `salt | 0^64`: the salt occupies the low
192 bits (the first 24 bytes in memory) and the high word is zero. -/
def saltState (salt : BitVec 192) : Digest := (0 : BitVec 64) ++ salt

@[simp] theorem saltState_low (salt : BitVec 192) : (saltState salt).extractLsb' 0 192 = salt :=
  BitVec.extractLsb'_append_eq_right

theorem saltState_injective {salt salt' : BitVec 192} (same : saltState salt = saltState salt') :
    salt = salt' := by
  simpa only [saltState_low] using congrArg (fun x : Digest => x.extractLsb' 0 192) same

/-- Number of cap pairs and levels authenticated per record, for the 2^24-leaf vector. -/
abbrev CAP_PAIRS : Nat := 64
abbrev PATH_LEVELS : Nat := 17

/-- Two adjacent cap digests as one 512-bit block; the even node is the low half,
so the chain input in memory reads `[state | cap (2k) | cap (2k+1)]`. -/
def capBlock (cap : Nat → Digest) (pair : Nat) : LeafBlock := cap (2*pair+1) ++ cap (2*pair)

def capBlocks (cap : Nat → Digest) : List LeafBlock := (List.range CAP_PAIRS).map (capBlock cap)

/-- The commitment: a 96-byte chain over the 64 cap pairs, starting from the zero state. -/
def capRoot (compress : Compression) (cap : Nat → Digest) : Digest :=
  (capBlocks cap).foldl (absorb compress) 0

theorem capBlock_injective {cap cap' : Nat → Digest} {pair : Nat}
    (same : capBlock cap pair = capBlock cap' pair) :
    cap (2*pair) = cap' (2*pair) ∧ cap (2*pair+1) = cap' (2*pair+1) := by
  constructor
  · simpa only [capBlock, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun x : LeafBlock => x.extractLsb' 0 256) same
  · simpa only [capBlock, BitVec.extractLsb'_append_eq_left] using
      congrArg (fun x : LeafBlock => x.extractLsb' 256 256) same

/-- Different cap entries give different block lists. -/
theorem capBlocks_ne_of_ne {cap cap' : Nat → Digest} {node : Nat} (inside : node < 2*CAP_PAIRS)
    (different : cap node ≠ cap' node) : capBlocks cap ≠ capBlocks cap' := by
  intro same
  have pairEq := List.map_inj_left.mp same (node/2) (List.mem_range.mpr (by omega))
  have halves := capBlock_injective pairEq
  rcases Nat.mod_two_eq_zero_or_one node with even | odd
  · exact different (by have h := halves.1; rwa [show 2*(node/2) = node by omega] at h)
  · exact different (by have h := halves.2; rwa [show 2*(node/2)+1 = node by omega] at h)

def parentLayer (compress : Compression) : List Digest → List Digest
  | left :: right :: rest => combine compress left right :: parentLayer compress rest
  | _ => []

def layers (compress : Compression) : Nat → List Digest → List (List Digest)
  | 0, leaves => [leaves]
  | depth + 1, leaves => leaves :: layers compress depth (parentLayer compress leaves)

def digestBytes (digest : Digest) : List Byte :=
  List.ofFn fun i : Fin 32 => digest.extractLsb' (8*i) 8

def referenceProof (tree : List (List Digest)) (depth index : Nat) (salt : Digest) : Proof :=
  digestBytes salt ++ ((List.range depth).flatMap fun level =>
    digestBytes ((tree[level]?.getD [])[(index / 2^level) ^^^ 1]?.getD 0))

theorem digestBytes_length (digest : Digest) : (digestBytes digest).length = 32 := by
  simp [digestBytes]

theorem referenceProof_length (tree : List (List Digest)) (depth index : Nat) (salt : Digest) :
    (referenceProof tree depth index salt).length = 32 * (depth + 1) := by
  simp [referenceProof, digestBytes_length, List.length_flatMap, List.sum_replicate]
  omega

/-- Indexed trees make the root reconstruction invariant independent of memory layout. -/
inductive Tree : Nat → Type where
  | leaf (digest : Digest) : Tree 0
  | node {depth : Nat} (left right : Tree depth) : Tree (depth + 1)

inductive Path : Nat → Type where
  | here : Path 0
  | left {depth : Nat} (rest : Path depth) : Path (depth + 1)
  | right {depth : Nat} (rest : Path depth) : Path (depth + 1)

def Tree.root (compress : Compression) : {depth : Nat} → Tree depth → Digest
  | _, .leaf digest => digest
  | _, .node left right => combine compress (left.root compress) (right.root compress)

def Tree.value : {depth : Nat} → Tree depth → Path depth → Digest
  | _, .leaf digest, .here => digest
  | _, .node left _, .left rest => left.value rest
  | _, .node _ right, .right rest => right.value rest

/-- Bottom-up siblings, tagged true when the current node is the right child. -/
def Tree.opening (compress : Compression) : {depth : Nat} → Tree depth → Path depth →
    List (Bool × Digest)
  | _, .leaf _, .here => []
  | _, .node left right, .left rest => left.opening compress rest ++ [(false, right.root compress)]
  | _, .node left right, .right rest => right.opening compress rest ++ [(true, left.root compress)]

def climb (compress : Compression) (leaf : Digest) (path : List (Bool × Digest)) : Digest :=
  path.foldl (fun node (right, sibling) =>
    if right then combine compress sibling node else combine compress node sibling) leaf

theorem reconstruct_root (compress : Compression) {depth : Nat} (tree : Tree depth)
    (path : Path depth) : climb compress (tree.value path) (tree.opening compress path) =
      tree.root compress := by
  induction tree with
  | leaf digest => cases path; rfl
  | node left right ihLeft ihRight =>
    cases path with
    | left rest => simpa [Tree.value, Tree.opening, Tree.root, climb, List.foldl_append] using
        (congrArg (fun digest => combine compress digest (right.root compress)) (ihLeft rest))
    | right rest => simpa [Tree.value, Tree.opening, Tree.root, climb, List.foldl_append] using
        (congrArg (fun digest => combine compress (left.root compress) digest) (ihRight rest))

end CommitGolfCandidate
