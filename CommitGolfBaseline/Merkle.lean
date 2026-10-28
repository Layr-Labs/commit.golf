import CommitGolf

/-! # Baseline: the Merkle commitment scheme of [CY24, §18.1]

The textbook binary Merkle tree, without salts (Remark 18.1.3) and without path pruning.

```
                 rt                    level 24 (the commitment)
               /    \
             ·        ·                ...
            / \      / \
           C   ·    ·   ·              level 1:  C(m[0], m[1]), C(m[2], m[3]), …
          / \
       m[0] m[1]  m[2] m[3] …          level 0:  the 2 ^ 24 entries themselves
```

- **Leaves** are the raw entries; each **internal node** is the compression `C(L, R)` of its two
  children (see `compress`).
- **Opening** a position means giving its 24 sibling digests, from the leaf up (its *copath*).
  A proof concatenates the copaths of the opened positions, in increasing order of position.
- **Checking** recomputes the root from each claimed value and its copath, and accepts if every
  recomputed root equals `rt`.

Score: `BATCH × LOG_LENGTH × DIGEST_BYTES = 100 × 24 × 32 = 76800` bytes, checked with
`BATCH × LOG_LENGTH = 2400` permutation calls.

This file defines the scheme; `CommitGolfTests` runs it on small trees. `MerkleProof/` proves
`Certificate merkle 76800 2400` (`merkle_certificate`), the sanity check of the statements. -/

namespace CommitGolf.Baseline
open OracleComp OracleSpec

/-! ### Encoding digests as bytes -/

/-- A node of the tree: 256 bits, like an entry and a commitment. -/
abbrev Digest := BitVec DIGEST_BITS

/-- The 32 bytes of a digest, least significant first. -/
def Digest.toBytes (digest : Digest) : List Byte :=
  List.ofFn fun k : Fin DIGEST_BYTES => digest.extractLsb' (8 * k) 8

/-- Inverse of `Digest.toBytes` on lists of `DIGEST_BYTES` bytes. -/
def Digest.ofBytes (bytes : List Byte) : Digest :=
  BitVec.ofNat DIGEST_BITS (bytes.foldr (fun byte acc => 256 * acc + byte.toNat) 0)

/-! ### The compression function -/

/-- `C(L, R)`, one forward call to `π`.

The input state holds `L ‖ R` in its low 512 bits (`R` lowest) and zeros in its high 1088 bits; the
output is the low 256 bits of `π` of that state. -/
def compress (left right : Digest) : OracleComp PermSpec Digest := do
  let output : State ← (PermSpec.query (Sum.inl ((left ++ right).setWidth WIDTH)) :)
  return output.setWidth DIGEST_BITS

/-! ### Trees as lists of layers

These functions are generic in the number of leaves, so the tests can run them on small trees. -/

/-- Hash adjacent pairs `(d₀, d₁), (d₂, d₃), …`: the layer above. -/
def parentLayer : List Digest → OracleComp PermSpec (List Digest)
  | left :: right :: rest => do
      let parent ← compress left right
      let parents ← parentLayer rest
      return parent :: parents
  | _ => return []

/-- All layers of the tree over `2 ^ depth` leaves, from the leaves (first) to the root (last). -/
def layers : (depth : Nat) → List Digest → OracleComp PermSpec (List (List Digest))
  | 0, leaves => return [leaves]
  | depth + 1, leaves => do
      let parents ← parentLayer leaves
      let above ← layers depth parents
      return leaves :: above

/-- The root: the only digest of the last layer (or zero for a malformed tree). -/
def rootOf (tree : List (List Digest)) : Digest :=
  ((tree.getLast?.getD []).head?).getD 0

/-- The copath of leaf `index`: at each level from the leaves up to just below the root, the
sibling of the node on the path from the leaf to the root. At level `k` that node has index
`index >>> k`, and its sibling `(index >>> k) ^^^ 1` (flip the last bit). -/
def copath (tree : List (List Digest)) (depth index : Nat) : List Digest :=
  (List.range depth).map fun level =>
    ((tree.getD level []).getD ((index >>> level) ^^^ 1) 0)

/-- Recompute the root from leaf `index`'s value and its copath. At level `k`, the current node is
a left child when bit `k` of `index` is `0`, a right child otherwise. -/
def climb (index : Nat) (leaf : Digest) (siblings : List Digest) :
    OracleComp PermSpec Digest :=
  (siblings.zipIdx).foldlM (fun node (sibling, level) =>
    if (index >>> level) % 2 = 0 then compress node sibling else compress sibling node) leaf

/-! ### The scheme -/

/-- The opened positions in increasing order. Proofs list the copaths in this order. -/
def ordered (positions : Positions) : List positions :=
  positions.attach.sort (· ≤ ·)

/-- The Merkle commitment scheme.

- `commit`: build the whole tree (`2 ^ 24 - 1` calls); the root is the commitment and the tree is
  the opening trapdoor.
- `opening`: read off the copaths from the stored tree (no calls).
- `check`: reject unless the proof has exactly `|I| × 24` digests; split it into one copath per
  position; climb each to a root (24 calls each); accept when all roots equal `rt`. -/
def merkle : Scheme where
  Trapdoor := List (List Digest)
  commit message := do
    let tree ← liftM (layers LOG_LENGTH (List.ofFn message))
    return (rootOf tree, tree)
  opening tree positions :=
    return (ordered positions).flatMap fun i =>
      (copath tree LOG_LENGTH i.1.1).flatMap Digest.toBytes
  check root positions values proof := do
    let paths := (proof.toChunks DIGEST_BYTES).map Digest.ofBytes |>.toChunks LOG_LENGTH
    if proof.length ≠ positions.card * LOG_LENGTH * DIGEST_BYTES then return false
    let roots ← ((ordered positions).zip paths).mapM fun (i, siblings) =>
      climb i.1.1 (values i) siblings
    return roots.all (· == root)

end CommitGolf.Baseline
