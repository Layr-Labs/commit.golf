import CommitGolfCandidate.Programs

/-! Pure reference functions for the machine's byte ordering and Merkle construction.
The compression function is an explicit argument, so correctness can be stated for
all oracle realizations. These definitions are not a substitute for machine refinement. -/
namespace CommitGolfCandidate
open CommitGolf

abbrev Digest := BitVec 256

/-- Private 128-bit per-leaf salt. -/
abbrev Salt := BitVec 128

/-- Unique 64-bit leaf-slot tag `4072 + 256 * index.val`, matching `slot_i = message - 24 + 256*i`. -/
def leafTag (index : Index) : BitVec 64 :=
  BitVec.ofNat 64 (4072 + 256 * index.val)

theorem leafTag_toNat (index : Index) : (leafTag index).toNat = 4072 + 256 * index.val := by
  have hi : index.val < 2^24 := index.isLt
  unfold leafTag
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem leafTag_injective : Function.Injective leafTag := by
  intro i j same
  have h := congrArg BitVec.toNat same
  rw [leafTag_toNat, leafTag_toNat] at h
  exact Fin.ext (by omega)

/-- Recover the unique leaf index encoded by a 64-bit tag word, if any. -/
def tagIndexOfWord (tag : BitVec 64) : Option Index :=
  let t := tag.toNat
  if h : 4072 ≤ t ∧ (t - 4072) % 256 = 0 ∧ (t - 4072) / 256 < LENGTH then
    some ⟨(t - 4072) / 256, h.2.2⟩
  else none

theorem tagIndexOfWord_leafTag (index : Index) : tagIndexOfWord (leafTag index) = some index := by
  have hi : index.val < LENGTH := index.isLt
  have hnat : (leafTag index).toNat = 4072 + 256 * index.val := leafTag_toNat index
  have cond : 4072 ≤ (leafTag index).toNat ∧
      ((leafTag index).toNat - 4072) % 256 = 0 ∧
      ((leafTag index).toNat - 4072) / 256 < LENGTH := by
    rw [hnat]
    refine ⟨by omega, by omega, ?_⟩
    simpa [show (4072 + 256 * index.val - 4072) / 256 = index.val by omega] using hi
  unfold tagIndexOfWord
  dsimp only
  rw [dif_pos cond]
  congr 1
  apply Fin.ext
  dsimp only
  rw [hnat]
  omega

/-- The first buffer half is the low half of the little-endian oracle input. -/
def combine (compress : Compression) (left right : Digest) : Digest :=
  compress ((padInput (right ++ left)))

/-- Tail leaf calls absorb 512 message bits per call. -/
abbrev LeafBlock := BitVec 512

/-- Tail leaf call input: the chaining value occupies the low 256 bits (first 32 bytes in memory),
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

/-- Initial leaf call input: 16-byte salt (bits 0..127), 8-byte leaf tag (bits 128..191),
and the first 72 message bytes (bits 192..767). Total 768 bits = 96 bytes. -/
def leafInitInput (index : Index) (salt : Salt) (value : Entry) : BitVec COMPRESSION_INPUT_LENGTH :=
  (value.extractLsb' 0 576 ++ leafTag index) ++ salt

@[simp] theorem leafInitInput_salt (index : Index) (salt : Salt) (value : Entry) :
    (leafInitInput index salt value).extractLsb' 0 128 = salt :=
  BitVec.extractLsb'_append_eq_right

@[simp] theorem leafInitInput_tag (index : Index) (salt : Salt) (value : Entry) :
    (leafInitInput index salt value).extractLsb' 128 64 = leafTag index :=
  (BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128)).trans
    BitVec.extractLsb'_append_eq_right

@[simp] theorem leafInitInput_head (index : Index) (salt : Salt) (value : Entry) :
    (leafInitInput index salt value).extractLsb' 192 576 = value.extractLsb' 0 576 :=
  (BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 192)).trans
    BitVec.extractLsb'_append_eq_left

theorem leafInitInput_injective {i i' : Index} {s s' : Salt} {v v' : Entry}
    (same : leafInitInput i s v = leafInitInput i' s' v') :
    i = i' ∧ s = s' ∧ v.extractLsb' 0 576 = v'.extractLsb' 0 576 := by
  refine ⟨?_, ?_, ?_⟩
  · apply leafTag_injective
    simpa only [leafInitInput_tag] using
      congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => x.extractLsb' 128 64) same
  · simpa only [leafInitInput_salt] using
      congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => x.extractLsb' 0 128) same
  · simpa only [leafInitInput_head] using
      congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => x.extractLsb' 192 576) same

/-- Extract the leaf index encoded in bits 128..191 of a 768-bit compression input. -/
def tagIndex (input : BitVec COMPRESSION_INPUT_LENGTH) : Option Index :=
  tagIndexOfWord (input.extractLsb' 128 64)

@[simp] theorem tagIndex_leafInitInput (index : Index) (salt : Salt) (value : Entry) :
    tagIndex (leafInitInput index salt value) = some index := by
  unfold tagIndex
  rw [leafInitInput_tag]
  exact tagIndexOfWord_leafTag index

/-- The three 512-bit message blocks absorbed after Call 0 (bytes 64..256 of the leaf). -/
def leafTailBlocks (value : Entry) : List LeafBlock :=
  (List.range 3).map fun block => value.extractLsb' (512 * (block + 1)) 512

/-- Three tail calls starting from the Call-0 digest. -/
def leafDigestFromInit (compress : Compression) (init : Digest) (value : Entry) : Digest :=
  (leafTailBlocks value).foldl (absorb compress) init

/-- Full four-call salted, position-tagged leaf digest. -/
def leafDigest (compress : Compression) (index : Index) (salt : Salt) (value : Entry) : Digest :=
  leafDigestFromInit compress (compress (leafInitInput index salt value)) value

def parentLayer (compress : Compression) : List Digest → List Digest
  | left :: right :: rest => combine compress left right :: parentLayer compress rest
  | _ => []

def layers (compress : Compression) : Nat → List Digest → List (List Digest)
  | 0, leaves => [leaves]
  | depth + 1, leaves => leaves :: layers compress depth (parentLayer compress leaves)

def digestBytes (digest : Digest) : List Byte :=
  List.ofFn fun i : Fin 32 => digest.extractLsb' (8*i) 8

def saltBytes (salt : Salt) : List Byte :=
  List.ofFn fun i : Fin 16 => salt.extractLsb' (8*i) 8

def referenceProof (tree : List (List Digest)) (depth index : Nat) (salt : Salt) : Proof :=
  saltBytes salt ++ ((List.range depth).flatMap fun level =>
    digestBytes ((tree[level]?.getD [])[(index / 2^level) ^^^ 1]?.getD 0))

theorem digestBytes_length (digest : Digest) : (digestBytes digest).length = 32 := by
  simp [digestBytes]

theorem saltBytes_length (salt : Salt) : (saltBytes salt).length = 16 := by
  simp [saltBytes]

theorem referenceProof_length (tree : List (List Digest)) (depth index : Nat) (salt : Salt) :
    (referenceProof tree depth index salt).length = openingBytes depth := by
  simp [referenceProof, saltBytes_length, digestBytes_length, openingBytes, List.length_flatMap,
    List.sum_replicate]
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
