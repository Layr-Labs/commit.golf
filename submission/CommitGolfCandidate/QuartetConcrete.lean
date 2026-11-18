import CommitGolfCandidate.QuartetFinal
import CommitGolfCandidate.QuartetOldFrame
import CommitGolfCandidate.QuartetOpeningSchedule

namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf CommitGolfCandidate
local instance QuartetConcreteLocalInstance1 {α : Type} : MeasurableSpace α := ⊤

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048

def leafAt (leaves : DigestTape) (i : Nat) : BitVec 256 :=
  if inside : i < LENGTH then leaves ⟨i,inside⟩ else 0

/-- Little-endian readBuffer puts the highest-address child in the highest bits. -/
def quartetPayload (leaves : DigestTape) (group : Nat) : BitVec 1024 :=
  leafAt leaves (4*group+3) ++ leafAt leaves (4*group+2) ++
    leafAt leaves (4*group+1) ++ leafAt leaves (4*group)

/-- A complete binary heap with leaves at `leafCount ..< 2 leafCount` whose parent at node `n` keeps
`keep n` of the compression of its children (the right child in the high half). -/
def keptHeap (keep : Nat → BitVec 256 → BitVec 256) (compress : Compression) (leafCount : Nat)
    (leaf : Nat → BitVec 256) (node : Nat) : BitVec 256 :=
  if branch : 0 < node ∧ node < leafCount then
    keep node (compress (keptHeap keep compress leafCount leaf (2*node+1) ++
      keptHeap keep compress leafCount leaf (2*node)))
  else if leafCount ≤ node ∧ node < 2*leafCount then leaf (node - leafCount)
  else 0
termination_by 2*leafCount - node
decreasing_by all_goals omega

theorem kept_heap_parent (keep : Nat → BitVec 256 → BitVec 256) (compress : Compression) (leafCount : Nat)
    (leaf : Nat → BitVec 256) (node : Nat) (positive : 0 < node) (below : node < leafCount) :
    keptHeap keep compress leafCount leaf node =
      keep node (compress (keptHeap keep compress leafCount leaf (2*node+1) ++
        keptHeap keep compress leafCount leaf (2*node))) := by
  rw [keptHeap, dif_pos ⟨positive, below⟩]

theorem kept_heap_leaf (keep : Nat → BitVec 256 → BitVec 256) (compress : Compression) (leafCount : Nat)
    (leaf : Nat → BitVec 256) (index : Nat) (inside : index < leafCount) :
    keptHeap keep compress leafCount leaf (leafCount + index) = leaf index := by
  rw [keptHeap, dif_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem kept_heap_congr (keep : Nat → BitVec 256 → BitVec 256) (compress : Compression) (leafCount : Nat)
    (leaf leaf' : Nat → BitVec 256) (same : ∀ g < leafCount, leaf g = leaf' g) (node : Nat) :
    keptHeap keep compress leafCount leaf node = keptHeap keep compress leafCount leaf' node := by
  conv_lhs => rw [keptHeap]
  conv_rhs => rw [keptHeap]
  by_cases branch : 0 < node ∧ node < leafCount
  · rw [dif_pos branch, dif_pos branch,
      kept_heap_congr keep compress leafCount leaf leaf' same (2*node+1),
      kept_heap_congr keep compress leafCount leaf leaf' same (2*node)]
  · rw [dif_neg branch, dif_neg branch]
    by_cases low : leafCount ≤ node ∧ node < 2*leafCount
    · rw [if_pos low, if_pos low]
      exact same _ (by omega)
    · rw [if_neg low, if_neg low]
termination_by 2*leafCount - node
decreasing_by all_goals omega

/-- The upper tree over the 2^22 group nodes `quads` (heap nodes `2^22 + g`); the parent at heap node
`0 < n < 2^22` keeps `nodeKeep n` of the compression of its children. -/
def upperHeapFrom (quads : Nat → BitVec 256) (compress : Compression) : Nat → BitVec 256 :=
  keptHeap nodeKeep compress 4194304 quads

theorem upper_heap_from_parent (quads : Nat → BitVec 256) (compress : Compression) (node : Nat)
    (positive : 0 < node) (below : node < 4194304) :
    upperHeapFrom quads compress node =
      nodeKeep node (compress (upperHeapFrom quads compress (2*node+1) ++ upperHeapFrom quads compress (2*node))) :=
  kept_heap_parent nodeKeep compress 4194304 quads node positive below

theorem upper_heap_from_group (quads : Nat → BitVec 256) (compress : Compression) (group : Nat)
    (inside : group < 4194304) :
    upperHeapFrom quads compress (4194304 + group) = quads group :=
  kept_heap_leaf nodeKeep compress 4194304 quads group inside

/-- The upper tree depends on the group nodes only below `2^22`. -/
theorem upper_heap_from_congr (quads quads' : Nat → BitVec 256) (same : ∀ g < 4194304, quads g = quads' g)
    (compress : Compression) (node : Nat) :
    upperHeapFrom quads compress node = upperHeapFrom quads' compress node :=
  kept_heap_congr nodeKeep compress 4194304 quads quads' same node

/-- The honest upper tree: group `g`'s node is `lookup g` of its payload. -/
def upperHeap (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) : Nat → BitVec 256 :=
  upperHeapFrom (fun g => lookup g (quartetPayload leaves g)) compress

theorem upper_heap_parent (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (node : Nat) (positive : 0 < node) (below : node < 4194304) :
    upperHeap lookup compress leaves node =
      nodeKeep node (compress (upperHeap lookup compress leaves (2*node+1) ++ upperHeap lookup compress leaves (2*node))) :=
  upper_heap_from_parent _ compress node positive below

theorem upper_heap_leaf (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (group : Nat) (inside : group < 4194304) :
    upperHeap lookup compress leaves (4194304 + group) = lookup group (quartetPayload leaves group) :=
  upper_heap_from_group _ compress group inside

/-! ### Proof bytes: 238-bit nodes packed eight to 238 bytes -/

/-- A 30-byte slot: the low 238 bits of `x` with two carried bits in bits `238, 239`
(the 30 little-endian bytes of `x mod 2^238 + 2^238 carry`). -/
def packedSlot (x : BitVec 256) (carry : BitVec 2) : List Byte :=
  proofDigestBytes true ((0 : BitVec 16) ++ (carry ++ x.extractLsb' 0 238))

/-- Eight 238-bit nodes in 238 bytes: slots `k = 0..6` carry node `k` and bits `224+2k, 225+2k` of
node 7, then node 7's low 224 bits in 28 bytes. -/
def packEight (nodes : List (BitVec 256)) : List Byte :=
  let last := nodes.getD 7 0
  (List.range 7).flatMap (fun k => packedSlot (nodes.getD k 0) (last.extractLsb' (224 + 2*k) 2)) ++
    (digestBytes last).take 28

/-- A list of 238-bit nodes: full groups of eight as `packEight`, a trailing partial group as
30-byte slots with zero carried bits. -/
def packNodes (nodes : List (BitVec 256)) : List Byte :=
  if 8 ≤ nodes.length then packEight (nodes.take 8) ++ packNodes (nodes.drop 8)
  else nodes.flatMap (fun x => packedSlot x 0)
termination_by nodes.length
decreasing_by simp only [List.length_drop]; omega

theorem packed_slot_length (x : BitVec 256) (carry : BitVec 2) : (packedSlot x carry).length = 30 := by
  unfold packedSlot
  rw [proof_digest_length]
  rfl

theorem pack_eight_length (nodes : List (BitVec 256)) : (packEight nodes).length = 238 := by
  unfold packEight digestBytes
  simp only [List.length_append, List.length_flatMap, packed_slot_length, List.length_take, List.length_ofFn]
  decide

theorem pack_nodes_length (nodes : List (BitVec 256)) :
    (packNodes nodes).length + 2 * (nodes.length / 8) = 30 * nodes.length := by
  rw [packNodes]
  split
  · next long =>
    have rest := pack_nodes_length (nodes.drop 8)
    rw [List.length_drop] at rest
    rw [List.length_append, pack_eight_length]
    omega
  · next short =>
    have small : nodes.length / 8 = 0 := by omega
    rw [small, List.length_flatMap]
    simp only [packed_slot_length, List.map_const', List.sum_replicate, smul_eq_mul]
    omega
termination_by nodes.length
decreasing_by simp only [List.length_drop]; omega

/-- One opening record: the salt, the three sibling leaf digests, the path siblings at `l = 0, 1`
(the sibling group node and the level-21 sibling, 32 bytes each), `l = 2..5` (30 bytes each), and the
eight 238-bit siblings at `l = 6..13` packed in 238 bytes. -/
def openingRecord (leaves : DigestTape) (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) : Proof :=
  saltBytes salt ++
    ([1, 2, 3] : List Nat).flatMap (fun j => digestBytes (leafAt leaves (index.val ^^^ j))) ++
    (List.range 6).flatMap (fun level =>
      proofDigestBytes (2 ≤ level) (heap ((((4194304 + index.val/4) / 2^level)) ^^^ 1))) ++
    packEight ((List.range 8).map (fun k => heap ((((4194304 + index.val/4) / 2^(6+k))) ^^^ 1)))

/-- The cap frontier (the record's depth-first order) as packed 238-bit nodes. -/
def frontierProof238 (heap : Nat → BitVec 256) (groups : List Nat) : Proof :=
  if groups.isEmpty then [] else packNodes ((capFrontierNodes groups 1 8).map heap)

def builder : QuartetBuilder :=
  fun lookup compress positions salts leaves =>
    let heap := upperHeap lookup compress leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let records := ordered.flatMap (fun i => openingRecord leaves heap i.val (salts i))
    (heap 1, records ++ frontierProof238 heap (ordered.map (capGroup ∘ Subtype.val)))

/-- `builder` with the 2^22 group nodes supplied directly. -/
def builderFrom (quads : Nat → BitVec 256) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) : Commitment × Proof :=
  let heap := upperHeapFrom quads compress
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let records := ordered.flatMap (fun i => openingRecord leaves heap i.val (salts i))
  (heap 1, records ++ frontierProof238 heap (ordered.map (capGroup ∘ Subtype.val)))

theorem builder_eq_from (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) :
    builder lookup compress positions salts leaves =
      builderFrom (fun g => lookup g (quartetPayload leaves g)) compress positions salts leaves := rfl

theorem builder_from_congr (quads quads' : Nat → BitVec 256) (same : ∀ g < 4194304, quads g = quads' g)
    (compress : Compression) (positions : Positions) (salts : OpenedSalts positions) (leaves : DigestTape) :
    builderFrom quads compress positions salts leaves = builderFrom quads' compress positions salts leaves := by
  have heap : upperHeapFrom quads compress = upperHeapFrom quads' compress :=
    funext (upper_heap_from_congr quads quads' same compress)
  unfold builderFrom
  rw [heap]

theorem opening_record_length (leaves : DigestTape) (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) :
    (openingRecord leaves heap index salt).length = 534 := by
  unfold openingRecord saltBytes digestBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, pack_eight_length,
    proof_digest_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  decide

theorem frontier_proof238_bound (heap : Nat → BitVec 256) (groups : List Nat) :
    (frontierProof238 heap groups).length ≤ 3808 := by
  unfold frontierProof238
  split
  · simp
  · have count := (cap_frontier_length groups 1 8).trans_le (production_boundary_bound (capMarkTree groups 1 8))
    have size := pack_nodes_length ((capFrontierNodes groups 1 8).map heap)
    rw [List.length_map] at size
    omega

theorem transcript_128 (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (count : positions.card = 128) :
    (builder lookup compress positions salts leaves).2.length ≤ 72160 := by
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let heap := upperHeap lookup compress leaves
  have boundary := frontier_proof238_bound heap (ordered.map (capGroup ∘ Subtype.val))
  have cardinal : ordered.length = 128 := by simp [ordered, count]
  change ((ordered.flatMap (fun i => openingRecord leaves heap i.val (salts i))) ++
    frontierProof238 heap (ordered.map (capGroup ∘ Subtype.val))).length ≤ _
  simp only [List.length_append, List.length_flatMap]
  simp [Function.comp_def, opening_record_length, cardinal] at boundary ⊢
  omega

theorem abstract_reference_hiding {State Output : Type} {k : Nat}
    (attacker : Hiding.HidingAdversary State Output k) (compress : Compression)
    (budget : Nat) (bounded : Hiding.QueryBound attacker budget) :
    measureTVDist (viewReference attacker builder compress false) (viewReference attacker builder compress true)
      ≤ min 1 (((budget : ℝ) + 1) / 2^120) :=
  final_reference_hiding global_frame attacker builder compress budget bounded

theorem concrete_hiding_of_refinement (scheme : Scheme) (refines : QuartetRefines scheme builder) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2^120)) :=
  scheme_hiding_of_transcript scheme builder refines abstract_reference_hiding

end TwoPermutationPrototype.Sampling.Quartet
