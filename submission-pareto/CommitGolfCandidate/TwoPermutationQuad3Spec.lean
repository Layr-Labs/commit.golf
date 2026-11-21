import CommitGolfCandidate.TwoPermutationQuad2Spec

/-! Shared interface for the three-level 4-ary permutation bottom ("quad3" design).

Tree: leaves (unchanged) -> level 1 quad nodes `quadValue g`, `g < LENGTH/4` -> level 2 nodes
`quad2Value h = quad (quad2Group h)`, `h < LENGTH/16` -> level 3 nodes `quad (quad3Group m)` over
four consecutive level-2 nodes, `m < LENGTH/64`, all with the same quad function (domain D2).
The heap has the level-3 nodes at indices `[LENGTH/64, LENGTH/32)` and the 240-bit projected
compression nodes at `[1, LENGTH/64)`. Above height 6 the heap is the same binary heap as before,
so the frontier footer is unchanged.

Proof record per opened position (606 bytes): salt (16) ++ three leaf neighbours (rotation by
`index % 4`) ++ three level-1 neighbours (rotation by `(index/4) % 4`) ++ three level-2 neighbours
(rotation by `(index/16) % 4`) (3 × 3 × 32) ++ the level-3 sibling (32, untruncated) ++ the binary
siblings at heights 7..15 (9 × 30). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp
open CommitGolfCandidate.Permutation.NoncePair (Key actualNonces)

/-- Level-2 node `h`. -/
def quad2Value (quad : QuadFunction) (leaves : DigestTape) (h : Nat) : BitVec 256 :=
  quad (quad2Group quad leaves h)

/-- Children of level-3 node `m`: level-2 nodes `4m … 4m+3`. -/
def quad3Group (quad : QuadFunction) (leaves : DigestTape) (m : Nat) : Fin 4 → BitVec 256 :=
  fun k => quad2Value quad leaves (4 * m + k.val)

def quad3Heap (compress : Compression) (quad : QuadFunction) (leaves : DigestTape) : Nat → BitVec 256 :=
  referenceHeap (projectInternal true compress) (LENGTH / 64) (fun m => quad (quad3Group quad leaves m))

/-- Slot of the `j`-th other level-2 node in the record: `u+1, u+2, u+3 (mod 4)`, `u = (index/16) % 4`. -/
def quad3RotSlot (index : Index) (j : Nat) : Fin 4 :=
  ⟨((index.val / 16) % 4 + j + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- Level-2 node index of the `j`-th other level-2 node of the level-3 group containing `index`. -/
def quad3Neighbour (index : Index) (j : Nat) : Nat := 4 * (index.val / 64) + (quad3RotSlot index j).val

def quad3LowerRecord (heap : Nat → BitVec 256) (quad : QuadFunction) (leaves : DigestTape)
    (index : Index) (salt : BitVec 128) : List Byte :=
  saltBytes salt ++
  (List.range 3).flatMap (fun j => digestBytes (quadLeaf leaves index (quadRotSlot index j))) ++
  (List.range 3).flatMap (fun j => digestBytes (quadValue quad leaves (quad2Neighbour index j))) ++
  (List.range 3).flatMap (fun j => digestBytes (quad2Value quad leaves (quad3Neighbour index j))) ++
  proofDigestBytes false (heap (((LENGTH + index.val) / 64) ^^^ 1)) ++
  (List.range 9).flatMap fun j =>
    proofDigestBytes true (heap (((LENGTH + index.val) / 2 ^ (j + 7)) ^^^ 1))

def quad3TranscriptBuilder : QuadTranscriptBuilder :=
  fun compress quad positions salts leaves =>
    let heap := quad3Heap compress quad leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let path := ordered.flatMap (fun index => quad3LowerRecord heap quad leaves index.val (salts index))
    let footer := frontierProof true heap (ordered.map (capGroup ∘ Subtype.val))
    (heap 1, path ++ footer)

theorem quad3_lower_record_length (heap : Nat → BitVec 256) (quad : QuadFunction) (leaves : DigestTape)
    (index : Index) (salt : BitVec 128) : (quad3LowerRecord heap quad leaves index salt).length = 606 := by
  unfold quad3LowerRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, proof_digest_length]
  simp [digestBytes, List.range_succ]

theorem quad3_heap_node (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (m : Nat) (inside : m < LENGTH / 64) :
    quad3Heap compress quad leaves (LENGTH / 64 + m) = quad (quad3Group quad leaves m) := by
  unfold quad3Heap
  rw [referenceHeap]
  have notBranch : ¬ (0 < LENGTH / 64 + m ∧ LENGTH / 64 + m < LENGTH / 64) := by omega
  have leafRange : LENGTH / 64 ≤ LENGTH / 64 + m ∧ LENGTH / 64 + m < 2 * (LENGTH / 64) := by omega
  simp only [notBranch, leafRange, dite_false, if_true, and_self, Nat.add_sub_cancel_left]

theorem quad3_heap_parent (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (branch : node < LENGTH / 64) :
    quad3Heap compress quad leaves node =
      projectInternal true compress
        (quad3Heap compress quad leaves (2 * node + 1) ++ quad3Heap compress quad leaves (2 * node)) := by
  unfold quad3Heap
  exact reference_heap_parent _ _ _ _ positive branch

/-! ### Trapdoor layout (interface between the commit image and the opening image)
As in `TwoPermutationQuad2Spec` (same trapdoor size `QUAD2_TRAPDOOR_BYTES`, same buffer layout),
except:
* `[0, 2^24)`: heap, node `k ∈ [1, LENGTH/32)` at `32 k` (level-3 nodes at `k ∈ [LENGTH/64, LENGTH/32)`);
  `[2^24, 2^24 + 168)` absorbs the overflow of the last (ascending) level-3 write.
* level-2 groups (holding level-2 nodes) from `QUAD3_GROUP_BASE = 2^25 + 4096 - 72` (inside the
  space the old heap used; `QUAD3_GROUP_BASE + 72 = 0x02001000` is one `lui`): group `m` at
  `QUAD3_GROUP_BASE + 368 m`, 72 zero bytes (never written), then slots `k = 0..3` at `+72 + 32 k`.
  The last group ends at `2^25 + 4024 + 368 · 2^18 < QUAD_GROUP_BASE`.
* level-1 groups (holding level-1 nodes) stay at `QUAD2_GROUP_BASE`.
Proof capacity `606 · 2^24 + 7680`. -/
def QUAD3_GROUP_BASE : Nat := 2 ^ 25 + 4096 - 72
def quad3SlotOffset (h : Nat) : Nat := QUAD3_GROUP_BASE + 368 * (h / 4) + 72 + 32 * (h % 4)
def QUAD3_PROOF_CAPACITY : Nat := 606 * 2 ^ 24 + 7680

theorem quad3_proof_capacity_value : QUAD3_PROOF_CAPACITY = 10167000576 := rfl
theorem quad3_groups_inside : 2 ^ 24 + 168 ≤ QUAD3_GROUP_BASE ∧
    QUAD3_GROUP_BASE + 368 * (LENGTH / 64) ≤ QUAD_GROUP_BASE := by decide

def quad3TrapdoorQuad2 {n : Nat} (trapdoor : BitVec n) (h : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (8 * quad3SlotOffset h) 256

def quad3PublicQuad2s (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  quad2Value (quadFunction oracle.permutation) (quadPublicLeaves oracle message salts)

def quad3PublicTree (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  quad3Heap oracle.compression (quadFunction oracle.permutation) (quadPublicLeaves oracle message salts)

/-- What the commit side delivers to the opening side (quad3 + NonceChain). -/
structure Quad3NonceCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → Key → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          pure (quad3PublicTree oracle message (actualNonces oracle.permutation k) 1, trapdoor oracle message k))
  nonce : ∀ oracle message k index,
    quadTrapdoorSalt (trapdoor oracle message k) index = actualNonces oracle.permutation k index
  leaf : ∀ oracle message k index,
    quadTrapdoorLeaf (trapdoor oracle message k) index =
      quadPublicLeaves oracle message (actualNonces oracle.permutation k) index
  quad : ∀ oracle message k g, g < LENGTH / 4 →
    quad2TrapdoorQuad (trapdoor oracle message k) g =
      quad2PublicQuads oracle message (actualNonces oracle.permutation k) g
  quad2 : ∀ oracle message k h, h < LENGTH / 16 →
    quad3TrapdoorQuad2 (trapdoor oracle message k) h =
      quad3PublicQuad2s oracle message (actualNonces oracle.permutation k) h
  heap : ∀ oracle message k node, 0 < node → node < LENGTH / 32 →
    quadTrapdoorHeap (trapdoor oracle message k) node =
      quad3PublicTree oracle message (actualNonces oracle.permutation k) node

/-- The builder reads the quad node function only on the honest level-1, 2 and 3 inputs. -/
def Quad3BuildLocal (build : QuadTranscriptBuilder) : Prop :=
  ∀ (compress : Compression) (quad quad' : QuadFunction) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape),
    (∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g)) →
    (∀ h, h < LENGTH / 16 → quad (quad2Group quad leaves h) = quad' (quad2Group quad leaves h)) →
    (∀ m, m < LENGTH / 64 → quad (quad3Group quad leaves m) = quad' (quad3Group quad leaves m)) →
      build compress quad positions salts leaves = build compress quad' positions salts leaves

theorem quad2_value_congr (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g))
    (same2 : ∀ h, h < LENGTH / 16 → quad (quad2Group quad leaves h) = quad' (quad2Group quad leaves h))
    (h : Nat) (inside : h < LENGTH / 16) : quad2Value quad leaves h = quad2Value quad' leaves h := by
  unfold quad2Value
  rw [same2 h inside, quad2_group_congr quad quad' leaves same h inside]

theorem quad3_group_congr (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g))
    (same2 : ∀ h, h < LENGTH / 16 → quad (quad2Group quad leaves h) = quad' (quad2Group quad leaves h))
    (m : Nat) (inside : m < LENGTH / 64) : quad3Group quad leaves m = quad3Group quad' leaves m := by
  funext k
  exact quad2_value_congr quad quad' leaves same same2 _
    (by have := k.isLt; have : LENGTH = 16777216 := rfl; omega)

theorem quad3_heap_congr (compress : Compression) (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g))
    (same2 : ∀ h, h < LENGTH / 16 → quad (quad2Group quad leaves h) = quad' (quad2Group quad leaves h))
    (same3 : ∀ m, m < LENGTH / 64 → quad (quad3Group quad leaves m) = quad' (quad3Group quad leaves m)) :
    quad3Heap compress quad leaves = quad3Heap compress quad' leaves := by
  unfold quad3Heap
  funext node
  apply reference_heap_congr
  intro m inside
  rw [same3 m inside, quad3_group_congr quad quad' leaves same same2 m inside]

theorem quad3_transcript_builder_local : Quad3BuildLocal quad3TranscriptBuilder := by
  intro compress quad quad' positions salts leaves same same2 same3
  have heap := quad3_heap_congr compress quad quad' leaves same same2 same3
  unfold quad3TranscriptBuilder
  dsimp only
  rw [heap]
  congr 2
  apply List.flatMap_congr
  intro index _
  have := index.val.isLt
  have hL : LENGTH = 16777216 := rfl
  unfold quad3LowerRecord
  congr 2
  congr 1
  · congr 1
    apply List.flatMap_congr
    intro j _
    rw [quadValue, quadValue, same _ (by unfold quad2Neighbour; have := (quad2RotSlot index.val j).isLt; omega)]
  · apply List.flatMap_congr
    intro j _
    rw [quad2_value_congr quad quad' leaves same same2 _
      (by unfold quad3Neighbour; have := (quad3RotSlot index.val j).isLt; omega)]

end TwoPermutationPrototype.Sampling
