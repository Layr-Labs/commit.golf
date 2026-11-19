import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.QuadNonceSpec

/-! Shared interface for the two-level 4-ary permutation bottom ("quad2" design).

Tree: leaves are the unchanged pinned leaf digests. Level 1: quad nodes
`quadValue g = quad (quadGroupLeaves leaves g)` for `g < LENGTH/4` (exactly the quad nodes of
`TwoPermutationQuadSpec`). Level 2: quad2 nodes `quad (quad2Group h)` over four consecutive quad
nodes `4h … 4h+3`, for `h < LENGTH/16`, with the same function `quad` (domain D2: 72 zero bytes,
then four 32-byte children). The heap has the quad2 nodes at indices `[LENGTH/16, LENGTH/8)` and
the 240-bit projected compression nodes at `[1, LENGTH/16)`. Above height 4 the heap is the same
binary heap as before, so the frontier footer is unchanged.

Proof record per opened position (570 bytes): salt (16) ++ three other leaf digests of the quad
group in rotation order `r+1, r+2, r+3 (mod 4)`, `r = index % 4` (3 × 32) ++ three other quad nodes
of the quad2 group in rotation order `s+1, s+2, s+3 (mod 4)`, `s = (index / 4) % 4` (3 × 32) ++
the quad2 sibling (32, untruncated) ++ the binary siblings at heights 5..15 (11 × 30). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

/-- Level-1 node `g` (a quad node over leaves `4g … 4g+3`). -/
def quadValue (quad : QuadFunction) (leaves : DigestTape) (g : Nat) : BitVec 256 :=
  quad (quadGroupLeaves leaves g)

/-- Children of level-2 node `h`: quad nodes `4h … 4h+3`. -/
def quad2Group (quad : QuadFunction) (leaves : DigestTape) (h : Nat) : Fin 4 → BitVec 256 :=
  fun k => quadValue quad leaves (4 * h + k.val)

def quad2Heap (compress : Compression) (quad : QuadFunction) (leaves : DigestTape) : Nat → BitVec 256 :=
  referenceHeap (projectInternal true compress) (LENGTH / 16) (fun h => quad (quad2Group quad leaves h))

/-- Slot of the `j`-th other quad node in the record: `s+1, s+2, s+3 (mod 4)`, `s = (index/4) % 4`. -/
def quad2RotSlot (index : Index) (j : Nat) : Fin 4 :=
  ⟨((index.val / 4) % 4 + j + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- Level-1 node index of the `j`-th other quad node of the quad2 group containing `index`. -/
def quad2Neighbour (index : Index) (j : Nat) : Nat := 4 * (index.val / 16) + (quad2RotSlot index j).val

def quad2LowerRecord (heap : Nat → BitVec 256) (quad : QuadFunction) (leaves : DigestTape)
    (index : Index) (salt : BitVec 128) : List Byte :=
  saltBytes salt ++
  (List.range 3).flatMap (fun j => digestBytes (quadLeaf leaves index (quadRotSlot index j))) ++
  (List.range 3).flatMap (fun j => digestBytes (quadValue quad leaves (quad2Neighbour index j))) ++
  proofDigestBytes false (heap (((LENGTH + index.val) / 16) ^^^ 1)) ++
  (List.range 11).flatMap fun j =>
    proofDigestBytes true (heap (((LENGTH + index.val) / 2 ^ (j + 5)) ^^^ 1))

def quad2TranscriptBuilder : QuadTranscriptBuilder :=
  fun compress quad positions salts leaves =>
    let heap := quad2Heap compress quad leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let path := ordered.flatMap (fun index => quad2LowerRecord heap quad leaves index.val (salts index))
    let footer := frontierProof true heap (ordered.map (capGroup ∘ Subtype.val))
    (heap 1, path ++ footer)

theorem quad2_lower_record_length (heap : Nat → BitVec 256) (quad : QuadFunction) (leaves : DigestTape)
    (index : Index) (salt : BitVec 128) : (quad2LowerRecord heap quad leaves index salt).length = 570 := by
  unfold quad2LowerRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, proof_digest_length]
  simp [digestBytes, List.range_succ]

theorem quad2_heap_node (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (h : Nat) (inside : h < LENGTH / 16) :
    quad2Heap compress quad leaves (LENGTH / 16 + h) = quad (quad2Group quad leaves h) := by
  unfold quad2Heap
  rw [referenceHeap]
  have notBranch : ¬ (0 < LENGTH / 16 + h ∧ LENGTH / 16 + h < LENGTH / 16) := by omega
  have leafRange : LENGTH / 16 ≤ LENGTH / 16 + h ∧ LENGTH / 16 + h < 2 * (LENGTH / 16) := by omega
  simp only [notBranch, leafRange, dite_false, if_true, and_self, Nat.add_sub_cancel_left]

theorem quad2_heap_parent (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (branch : node < LENGTH / 16) :
    quad2Heap compress quad leaves node =
      projectInternal true compress
        (quad2Heap compress quad leaves (2 * node + 1) ++ quad2Heap compress quad leaves (2 * node)) := by
  unfold quad2Heap
  exact reference_heap_parent _ _ _ _ positive branch

/-! ### Trapdoor layout (interface between the commit image and the opening image)
Byte offsets from the trapdoor base:
* `[0, 2^26)`: heap, node `k ∈ [1, LENGTH/8)` at `32 k` (quad2 nodes at `k ∈ [LENGTH/16, LENGTH/8)`);
  `[2^26, 2^26 + 168)` absorbs the overflow of the last (ascending) quad2-node write.
* leaf groups and salts exactly as in `TwoPermutationQuadSpec` (`QUAD_GROUP_BASE`, `QUAD_SALT_BASE`).
* quad groups from `QUAD2_GROUP_BASE = QUAD_SALT_BASE + 2^28 + 3·4096 - 72` (so `QUAD2_GROUP_BASE + 72 =
  0x7C004000` is one `lui`; the NonceChain generator's last replies end below offset 0x7C003018): group `h` at `QUAD2_GROUP_BASE + 368 h`, 72 zero bytes (never written),
  then quad-node slots `k = 0..3` at `+72 + 32 k` (each quad node's reply writes 200 bytes from its
  slot; the last slot's write ends exactly at the next group).
* `QUAD2_TRAPDOOR_BYTES = QUAD2_GROUP_BASE + 368 · LENGTH/16 + 72` (72 bytes of padding).
Layout: message 4096, commitment 4294971392, trapdoor 4294971424, indices = trapdoor + QUAD2_TRAPDOOR_BYTES,
values = indices + 2^27 + 64, proof = values + 2^32. Proof capacity `570 · 2^24 + 7680`. -/
def QUAD2_GROUP_BASE : Nat := QUAD_SALT_BASE + 16 * LENGTH + 3 * 4096 - 72
def quad2SlotOffset (g : Nat) : Nat := QUAD2_GROUP_BASE + 368 * (g / 4) + 72 + 32 * (g % 4)
def QUAD2_TRAPDOOR_BYTES : Nat := QUAD2_GROUP_BASE + 368 * (LENGTH / 16) + 72
def QUAD2_PROOF_CAPACITY : Nat := 570 * 2 ^ 24 + 7680

theorem quad2_group_base_value : QUAD2_GROUP_BASE = 0x7C003FB8 := rfl
theorem quad2_trapdoor_bytes_value : QUAD2_TRAPDOOR_BYTES = 2466267136 := rfl
theorem quad2_proof_capacity_value : QUAD2_PROOF_CAPACITY = 9563020800 := rfl

theorem quad2_groups_after_salts : QUAD_SALT_BASE + 16 * LENGTH ≤ QUAD2_GROUP_BASE := by decide

def quad2TrapdoorQuad {n : Nat} (trapdoor : BitVec n) (g : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (8 * quad2SlotOffset g) 256

def quad2PublicQuads (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  quadValue (quadFunction oracle.permutation) (quadPublicLeaves oracle message salts)

def quad2PublicTree (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  quad2Heap oracle.compression (quadFunction oracle.permutation) (quadPublicLeaves oracle message salts)

/-- What the commit side delivers to the opening side (quad2 + NonceChain). -/
structure Quad2NonceCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → Key → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          pure (quad2PublicTree oracle message (actualNonces oracle.permutation k) 1, trapdoor oracle message k))
  nonce : ∀ oracle message k index,
    quadTrapdoorSalt (trapdoor oracle message k) index = actualNonces oracle.permutation k index
  leaf : ∀ oracle message k index,
    quadTrapdoorLeaf (trapdoor oracle message k) index =
      quadPublicLeaves oracle message (actualNonces oracle.permutation k) index
  quad : ∀ oracle message k g, g < LENGTH / 4 →
    quad2TrapdoorQuad (trapdoor oracle message k) g =
      quad2PublicQuads oracle message (actualNonces oracle.permutation k) g
  heap : ∀ oracle message k node, 0 < node → node < LENGTH / 8 →
    quadTrapdoorHeap (trapdoor oracle message k) node =
      quad2PublicTree oracle message (actualNonces oracle.permutation k) node

/-- The builder reads the quad node function only on the honest level-1 and level-2 inputs. -/
def Quad2BuildLocal (build : QuadTranscriptBuilder) : Prop :=
  ∀ (compress : Compression) (quad quad' : QuadFunction) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape),
    (∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g)) →
    (∀ h, h < LENGTH / 16 → quad (quad2Group quad leaves h) = quad' (quad2Group quad leaves h)) →
      build compress quad positions salts leaves = build compress quad' positions salts leaves

theorem quad_value_congr (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g))
    (g : Nat) (inside : g < LENGTH / 4) : quadValue quad leaves g = quadValue quad' leaves g :=
  same g inside

theorem quad2_group_congr (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g))
    (h : Nat) (inside : h < LENGTH / 16) : quad2Group quad leaves h = quad2Group quad' leaves h := by
  funext k
  exact same _ (by have := k.isLt; have : LENGTH = 16777216 := rfl; omega)

theorem quad2_heap_congr (compress : Compression) (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g))
    (same2 : ∀ h, h < LENGTH / 16 → quad (quad2Group quad leaves h) = quad' (quad2Group quad leaves h)) :
    quad2Heap compress quad leaves = quad2Heap compress quad' leaves := by
  unfold quad2Heap
  funext node
  apply reference_heap_congr
  intro h inside
  rw [same2 h inside, quad2_group_congr quad quad' leaves same h inside]

theorem quad2_transcript_builder_local : Quad2BuildLocal quad2TranscriptBuilder := by
  intro compress quad quad' positions salts leaves same same2
  have heap := quad2_heap_congr compress quad quad' leaves same same2
  unfold quad2TranscriptBuilder
  dsimp only
  rw [heap]
  congr 2
  apply List.flatMap_congr
  intro index _
  unfold quad2LowerRecord
  congr 2
  congr 1
  apply List.flatMap_congr
  intro j _
  have := index.val.isLt
  have hL : LENGTH = 16777216 := rfl
  rw [quadValue, quadValue, same _ (by unfold quad2Neighbour; have := (quad2RotSlot index.val j).isLt; omega)]

end TwoPermutationPrototype.Sampling
