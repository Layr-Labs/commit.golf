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

def leafDigest (compress : Compression) (salt : Digest) (value : Entry) : Digest :=
  (List.range 8).foldl
    (fun state block => combine compress state (value.extractLsb' (256 * block) 256)) salt

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
    (referenceProof tree depth index salt).length = openingBytes depth := by
  simp [referenceProof, digestBytes_length, openingBytes, List.length_flatMap, List.sum_replicate]
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
