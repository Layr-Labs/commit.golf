import CommitGolfCandidate.Programs
import CommitGolfCandidate.Cut

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


/-- One climbing step from a node at `height`: the parent (at `height+1`) is stored in cut form. -/
def climbStep (compress : Compression) (height : Nat) (digest : Digest) (step : Bool × Digest) : Digest :=
  cut (height+1) (if step.1 then combine compress step.2 digest else combine compress digest step.2)

/-- Climb from a node at `height` along a path, storing every computed ancestor in cut form. -/
def climbAt (compress : Compression) : Nat → Digest → List (Bool × Digest) → Digest
  | _, digest, [] => digest
  | height, digest, step :: rest => climbAt compress (height+1) (climbStep compress height digest step) rest

@[simp] theorem climbAt_nil (compress : Compression) (height : Nat) (digest : Digest) :
    climbAt compress height digest [] = digest := rfl

theorem climbAt_cons (compress : Compression) (height : Nat) (digest : Digest) (step : Bool × Digest)
    (rest : List (Bool × Digest)) :
    climbAt compress height digest (step :: rest) =
      climbAt compress (height+1) (climbStep compress height digest step) rest := rfl

theorem climbAt_append (compress : Compression) (height : Nat) (digest : Digest)
    (first second : List (Bool × Digest)) :
    climbAt compress height digest (first ++ second) =
      climbAt compress (height + first.length) (climbAt compress height digest first) second := by
  induction first generalizing height digest with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.cons_append, climbAt_cons, ih, List.length_cons]
    congr 1; omega

/-- Above height 17 nothing is cut, so climbing there is the plain `climb`. -/
theorem climbAt_eq_climb (compress : Compression) (height : Nat) (above : 17 ≤ height)
    (digest : Digest) (path : List (Bool × Digest)) :
    climbAt compress height digest path = climb compress digest path := by
  induction path generalizing height digest with
  | nil => rfl
  | cons step rest ih =>
    rw [climbAt_cons, ih (height+1) (by omega)]
    unfold climb climbStep
    rw [cut_of_not (by unfold CutHeight; omega)]
    rcases step with ⟨right, sibling⟩
    rfl

end CommitGolfCandidate
