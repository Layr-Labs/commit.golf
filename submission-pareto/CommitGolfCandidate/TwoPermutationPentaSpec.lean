import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.QuadNonceSpec

/-! Shared interface for the full 5-ary permutation tree ("penta" design).

Leaves are the unchanged pinned two-permutation leaf digests (256 bits). Every internal node is one
permutation call on `pentaInput c = 0^320 || c0 || c1 || c2 || c3 || c4` (low bits first: 40 zero
bytes, then five 32-byte children); the node is the low 256 bits of the reply. Domain D5 = blocks
whose low 320 bits are zero. Level 0 has `LENGTH` nodes (the leaves). Levels `k < PENTA_LOW = 3`
group five children: level-`k+1` node `j` is over level-`k` nodes `5j … 5j+4`. The levels above are
binary: node `j` is the penta node with children `0, 0, 0, c(2j), c(2j+1)` (slots 3 and 4). Nodes
beyond `pentaCount k` count as 0 (ragged last groups). Level 21 has one node, the root
(= the commitment). No compression function is used.

Donor record per opened position `i` (1432 bytes): salt (16) ++ `virtIndex i` (8) ++ for each level `k = 0 … 20`, the four
other slots of the group above `i` in rotation order `r+1, …, r+4 (mod 5)`, `r = hybridSlot i k`
(4 × 32 each). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

/-- Levels `k < PENTA_LOW` and `k ≥ PENTA_HIGH` group five children, level `QUAD_LEVEL` groups four
(slots 1-4) and the levels from `BIN_LOW` up to `PENTA_HIGH` are binary (slots 3 and 4). -/
def PENTA_LOW : Nat := 6
def QUAD_LEVEL : Nat := 6
def BIN_LOW : Nat := 7
def PENTA_HIGH : Nat := 7
def PENTA_LEVELS : Nat := 11

/-- Whether level-`k` nodes are grouped in fives. -/
def pentaLevel (k : Nat) : Prop := k < PENTA_LOW ∨ PENTA_HIGH ≤ k

instance (k : Nat) : Decidable (pentaLevel k) := by unfold pentaLevel; infer_instance

/-- Children per level-`k+1` node. -/
def radix (k : Nat) : Nat := if pentaLevel k then 5 else if k = QUAD_LEVEL then 4 else 2
/-- First occupied slot of a level-`k` group (`5 - radix k`). -/
def slotBase (k : Nat) : Nat := if pentaLevel k then 0 else if k = QUAD_LEVEL then 1 else 3

theorem radix_low (k : Nat) (h : k < PENTA_LOW) : radix k = 5 := by
  unfold radix pentaLevel; rw [if_pos (Or.inl h)]
theorem radix_quad : radix QUAD_LEVEL = 4 := by decide
theorem radix_mid (k : Nat) (h1 : BIN_LOW ≤ k) (h2 : k < PENTA_HIGH) : radix k = 2 := by
  unfold radix pentaLevel; rw [if_neg (by unfold PENTA_LOW PENTA_HIGH BIN_LOW at *; omega),
    if_neg (by unfold QUAD_LEVEL BIN_LOW at *; omega)]
theorem radix_high (k : Nat) (h : PENTA_HIGH ≤ k) : radix k = 5 := by
  unfold radix pentaLevel; rw [if_pos (Or.inr h)]
theorem slot_base_low (k : Nat) (h : k < PENTA_LOW) : slotBase k = 0 := by
  unfold slotBase pentaLevel; rw [if_pos (Or.inl h)]
theorem slot_base_quad : slotBase QUAD_LEVEL = 1 := by decide
theorem slot_base_mid (k : Nat) (h1 : BIN_LOW ≤ k) (h2 : k < PENTA_HIGH) : slotBase k = 3 := by
  unfold slotBase pentaLevel; rw [if_neg (by unfold PENTA_LOW PENTA_HIGH BIN_LOW at *; omega),
    if_neg (by unfold QUAD_LEVEL BIN_LOW at *; omega)]
theorem slot_base_high (k : Nat) (h : PENTA_HIGH ≤ k) : slotBase k = 0 := by
  unfold slotBase pentaLevel; rw [if_pos (Or.inr h)]

theorem radix_pos (k : Nat) : 0 < radix k := by unfold radix; split_ifs <;> omega
theorem slot_base_add (k : Nat) : slotBase k + radix k = 5 := by unfold slotBase radix; split_ifs <;> rfl

/-- Nodes at level `k` (see `penta_count_values`). -/
def pentaCount : Nat → Nat
  | 0 => LENGTH
  | k + 1 => (pentaCount k + radix k - 1) / radix k

theorem penta_count_values :
    (List.range 12).map pentaCount =
      [16777216, 3355444, 671089, 134218, 26844, 5369, 1074, 269, 54, 11, 3, 1] := by decide

/-- Permutation block of a 5-ary node: low 320 bits zero, then child 0, 1, 2, 3, 4. -/
def pentaInput (c : Fin 5 → BitVec 256) : Block :=
  ((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) ++ (0#320)

abbrev PentaFunction := (Fin 5 → BitVec 256) → BitVec 256

def pentaFunction (perm : Block → Block) : PentaFunction :=
  fun c => (perm (pentaInput c)).extractLsb' 0 256

/-- Level-`k` node held by slot `t` of group `g` (meaningful when `slotBase k ≤ t`). -/
def childIndex (k g : Nat) (t : Fin 5) : Nat := radix k * g + (t.val - slotBase k)

/-- Node `j` of level `k` (0 beyond `pentaCount k`). -/
def pentaNode (penta : PentaFunction) (leaves : DigestTape) : Nat → Nat → BitVec 256
  | 0, j => if h : j < LENGTH then leaves ⟨j, h⟩ else 0
  | k + 1, j => if j < pentaCount (k + 1) then
      penta (fun t => if slotBase k ≤ t.val then pentaNode penta leaves k (childIndex k j t) else 0) else 0

/-- The five slots of level-`k` group `j` (the children of level-`k+1` node `j`). -/
def pentaGroup (penta : PentaFunction) (leaves : DigestTape) (k j : Nat) : Fin 5 → BitVec 256 :=
  fun t => if slotBase k ≤ t.val then pentaNode penta leaves k (childIndex k j t) else 0

theorem penta_node_succ (penta : PentaFunction) (leaves : DigestTape) (k j : Nat)
    (inside : j < pentaCount (k + 1)) :
    pentaNode penta leaves (k + 1) j = penta (pentaGroup penta leaves k j) := by
  rw [pentaNode, if_pos inside]
  rfl

/-- Unfolding of a non-leaf node in terms of its group. -/
theorem penta_node_succ_or (penta : PentaFunction) (leaves : DigestTape) (k j : Nat) :
    pentaNode penta leaves (k + 1) j =
      if j < pentaCount (k + 1) then penta (pentaGroup penta leaves k j) else 0 := by
  rw [pentaNode]; rfl

def pentaRoot (penta : PentaFunction) (leaves : DigestTape) : BitVec 256 :=
  pentaNode penta leaves PENTA_LEVELS 0

/-- Product of the radices below level `k`: the level-`k` node above position `i` is `i / placeValue k`. -/
def placeValue : Nat → Nat
  | 0 => 1
  | k + 1 => placeValue k * radix k

/-- Slot of position `index`'s level-`k` node inside its group. -/
def hybridSlot (index k : Nat) : Nat := slotBase k + index / placeValue k % radix k

theorem hybrid_slot_lt (index k : Nat) : hybridSlot index k < 5 := by
  have := Nat.mod_lt (index / placeValue k) (radix_pos k)
  have := slot_base_add k
  unfold hybridSlot; omega

/-- Base-5 number whose digits are the slots of levels `k, k+1, …, k+n-1`. -/
def virtFrom (index : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => hybridSlot index k + 5 * virtFrom index (k + 1) n

/-- The slots as base-5 digits: the donor checker walks levels with `v % 5`, `v / 5`. -/
def virtIndex (index : Nat) : Nat := virtFrom index 0 PENTA_LEVELS

theorem virt_from_digit (index : Nat) :
    ∀ j k n, j < n → virtFrom index k n / 5 ^ j % 5 = hybridSlot index (k + j) := by
  intro j
  induction j with
  | zero =>
    intro k n lt
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hybrid_slot_lt index k
    simp only [virtFrom, pow_zero, Nat.div_one, Nat.add_zero]
    omega
  | succ j ih =>
    intro k n lt
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hybrid_slot_lt index k
    have step : virtFrom index k (n + 1) / 5 ^ (j + 1) = virtFrom index (k + 1) n / 5 ^ j := by
      rw [virtFrom, pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      omega
    rw [step, ih (k + 1) n (by omega), show k + 1 + j = k + (j + 1) by omega]

theorem virt_index_digit (index k : Nat) (lt : k < PENTA_LEVELS) :
    virtIndex index / 5 ^ k % 5 = hybridSlot index k := by
  have h := virt_from_digit index k 0 PENTA_LEVELS lt
  rw [Nat.zero_add] at h
  exact h

theorem virt_index_lt (index : Nat) : virtIndex index < 5 ^ PENTA_LEVELS := by
  have gen : ∀ k n, virtFrom index k n < 5 ^ n := by
    intro k n
    induction n generalizing k with
    | zero => simp [virtFrom]
    | succ n ih =>
      have := hybrid_slot_lt index k
      have := ih (k + 1)
      simp only [virtFrom, pow_succ]
      omega
  exact gen 0 _

theorem place_div_lt_count (i : Nat) (inside : i < LENGTH) : ∀ k, i / placeValue k < pentaCount k
  | 0 => by simpa [pentaCount, placeValue] using inside
  | k+1 => by
    have ih := place_div_lt_count i inside k
    rw [placeValue, ← Nat.div_div_eq_div_mul]
    show i/placeValue k/radix k < (pentaCount k+radix k-1)/radix k
    unfold radix; split_ifs <;> omega

theorem place_root (i : Nat) (inside : i < LENGTH) : i / placeValue PENTA_LEVELS = 0 := by
  have : placeValue PENTA_LEVELS = 39062500 := by decide
  rw [this]; apply Nat.div_eq_of_lt; change i < 16777216 at inside; omega

/-- The record's own node sits in its group at `hybridSlot`. -/
theorem group_own (penta : PentaFunction) (leaves : DigestTape) (i k : Nat) :
    pentaGroup penta leaves k (i / placeValue (k+1)) ⟨hybridSlot i k, hybrid_slot_lt i k⟩ =
      pentaNode penta leaves k (i / placeValue k) := by
  unfold pentaGroup childIndex hybridSlot
  simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
  congr 1
  rw [placeValue, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod (i / placeValue k) (radix k)

/-- Slot of the `j`-th (`j < 4`) other child at level `k` in a donor record. -/
def pentaRot (index : Index) (k j : Nat) : Fin 5 :=
  ⟨(hybridSlot index.val k + j + 1) % 5, Nat.mod_lt _ (by decide)⟩

/-- Little-endian bytes of a doubleword. -/
def wordBytes (w : BitVec 64) : List Byte := List.ofFn fun i : Fin 8 => w.extractLsb' (8 * i.val) 8

/-- Donor record: the salt, the virtual index, then for every level the four other slots of the
record's group. -/
def pentaRecord (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) : List Byte :=
  saltBytes salt ++ wordBytes (BitVec.ofNat 64 (virtIndex index.val)) ++
  (List.range PENTA_LEVELS).flatMap fun k =>
    (List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))

abbrev PentaTranscriptBuilder :=
  PentaFunction → (positions : Positions) → OpenedSalts positions → DigestTape → Commitment × Proof

def pentaTranscriptBuilder : PentaTranscriptBuilder :=
  fun penta positions salts leaves =>
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    (pentaRoot penta leaves, ordered.flatMap (fun index => pentaRecord penta leaves index.val (salts index)))

theorem penta_record_length (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    (pentaRecord penta leaves index salt).length = 1432 := by
  have inner : ∀ k, ((List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))).length = 128 := by
    intro k
    simp only [List.length_flatMap, digestBytes, List.length_ofFn, List.map_const', List.length_range,
      List.sum_replicate, smul_eq_mul]
  unfold pentaRecord saltBytes wordBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, inner, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul, PENTA_LEVELS]

/-- Honest view: same leaf digests as 8d2a211; every internal node queries the same permutation. -/
def pentaHonestView (build : PentaTranscriptBuilder) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build (pentaFunction p.forward) positions (fun index => salts index.val) (pinnedFullLeafDigests p message salts)

/-- Executable commit-and-open transcript = penta honest view with nonce-chain salts. -/
def PentaNonceTranscriptRefines (scheme : Scheme) (build : PentaTranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let k ← $ᵗ Key
          pure (pentaHonestView build (BiPermutation.equiv Block oracle.permutation)
            message positions (actualNonces oracle.permutation k)))

/-- The builder reads the node function only on the honest inputs of levels `1 … PENTA_LEVELS`. -/
def PentaBuildLocal (build : PentaTranscriptBuilder) : Prop :=
  ∀ (penta penta' : PentaFunction) (positions : Positions) (salts : OpenedSalts positions) (leaves : DigestTape),
    (∀ k j, k < PENTA_LEVELS → j < pentaCount (k + 1) →
      penta (pentaGroup penta leaves k j) = penta' (pentaGroup penta leaves k j)) →
      build penta positions salts leaves = build penta' positions salts leaves

/-- Groups agree when the nodes of their level agree. -/
theorem penta_group_of_nodes (f g : PentaFunction) (leaves : DigestTape) (k j : Nat)
    (same : ∀ i, pentaNode f leaves k i = pentaNode g leaves k i) :
    pentaGroup f leaves k j = pentaGroup g leaves k j := by
  funext t
  unfold pentaGroup
  split <;> simp [same]

theorem penta_node_congr (penta penta' : PentaFunction) (leaves : DigestTape)
    (same : ∀ k j, k < PENTA_LEVELS → j < pentaCount (k + 1) →
      penta (pentaGroup penta leaves k j) = penta' (pentaGroup penta leaves k j)) :
    ∀ k, k ≤ PENTA_LEVELS → ∀ j, pentaNode penta leaves k j = pentaNode penta' leaves k j := by
  intro k
  induction k with
  | zero => intro _ j; rfl
  | succ k ih =>
    intro le j
    rw [penta_node_succ_or, penta_node_succ_or]
    split_ifs with inside
    · have children := penta_group_of_nodes penta penta' leaves k j (fun i => ih (by omega) i)
      rw [same k j (by omega) inside, children]
    · rfl

theorem penta_transcript_builder_local : PentaBuildLocal pentaTranscriptBuilder := by
  intro penta penta' positions salts leaves same
  have nodes := penta_node_congr penta penta' leaves same
  have root : pentaRoot penta leaves = pentaRoot penta' leaves := nodes _ le_rfl _
  have record : ∀ index salt, pentaRecord penta leaves index salt = pentaRecord penta' leaves index salt := by
    intro index salt
    unfold pentaRecord
    congr 1
    apply List.flatMap_congr
    intro k member
    apply List.flatMap_congr
    intro j _
    rw [penta_group_of_nodes penta penta' leaves k _ (nodes k (le_of_lt (List.mem_range.mp member)))]
  simp only [pentaTranscriptBuilder, root, record]

/-! ### Trapdoor layout (interface between the commit image and the opening image)
Byte offsets from the trapdoor base (the trapdoor size, salts and buffer layout are exactly those
of the quad base: size `QUAD_TRAPDOOR_BYTES = 2080378880`, salts at `QUAD_SALT_BASE + 16 i`):
* level-`k` groups (`k = 0 … 21`) from `pentaGroupBase k` (each `+ 40` is 4096-aligned, one `lui`):
  group `g` at `pentaGroupBase k + 368 g`, 40 zero bytes, then slots `t = 0 … 4` at `+40 + 32 t`;
  level-`k` node `j` sits in slot `slotBase k + j % radix k` of group `j / radix k`
  (`pentaSlotOffset k j`); slots 0-2 of binary groups are never written. Level 0 holds
  the leaf digests (each leaf's 200-byte second reply is written from its slot). Writes are ascending
  within a level, so each 200-byte reply only overwrites later slots of its own group or ends by the
  next group.
* ragged slots (slots of nodes `j ≥ pentaCount k` in the last level-`k` group, `k ≤ 20`) are zero in
  the trapdoor: the commit clears them after the level is written.
* all groups end below `QUAD_SALT_BASE - 176`.
Layout: message 4096, commitment 4294971392, trapdoor 4294971424, indices 6375350304,
values 6509568096, proof 10804535392 (as in the quad base); proof capacity `2456 · LENGTH`. -/
def pentaGroupBase : Nat → Nat
  | 0 => 4056 | 1 => 1234812888 | 2 => 1481781208 | 3 => 1531178968 | 4 => 1541058520
  | 5 => 1543036888 | 6 => 1543434200 | 7 => 1543536600 | 8 => 1543557080 | 9 => 1543561176
  | 10 => 1543565272 | _ => 1543569368

/-- Byte offset of slot `t` of level-`k` group `g`. -/
def pentaGroupSlotOffset (k g t : Nat) : Nat := pentaGroupBase k + 368 * g + 40 + 32 * t

/-- Level-`k` node `j` sits in slot `slotBase k + j % radix k` of group `j / radix k`. -/
def pentaSlotOffset (k j : Nat) : Nat := pentaGroupSlotOffset k (j / radix k) (slotBase k + j % radix k)

def PENTA_PROOF_CAPACITY : Nat := 2456 * LENGTH

theorem penta_proof_capacity_value : PENTA_PROOF_CAPACITY = 41204842496 := rfl

/-- Consecutive level regions do not overlap, and all lie below the salt area. -/
theorem penta_levels_separate :
    (∀ k, k < 10 → pentaGroupBase k + 368 * pentaCount (k + 1) ≤ pentaGroupBase (k + 1)) ∧
    pentaGroupBase 10 + 368 ≤ QUAD_SALT_BASE - 176 := by
  refine ⟨?_, by decide⟩
  intro k lt
  interval_cases k <;> decide

def pentaTrapdoorNode {n : Nat} (trapdoor : BitVec n) (k j : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (8 * pentaSlotOffset k j) 256

def pentaTrapdoorSlot {n : Nat} (trapdoor : BitVec n) (k g t : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (8 * pentaGroupSlotOffset k g t) 256

def pentaPublicNodes (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Nat → BitVec 256 :=
  pentaNode (pentaFunction oracle.permutation) (quadPublicLeaves oracle message salts)

/-- What the commit side delivers to the opening side (penta + NonceChain). -/
structure PentaNonceCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → Key → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          pure (pentaPublicNodes oracle message (actualNonces oracle.permutation k) PENTA_LEVELS 0,
            trapdoor oracle message k))
  nonce : ∀ oracle message k index,
    quadTrapdoorSalt (trapdoor oracle message k) index = actualNonces oracle.permutation k index
  /-- Every slot of every used group of levels `0 … PENTA_LEVELS - 1` (nodes, unused binary
  slots and ragged slots, the latter two zero). -/
  slot : ∀ oracle message k level g (t : Fin 5), level < PENTA_LEVELS → g < pentaCount (level + 1) →
    pentaTrapdoorSlot (trapdoor oracle message k) level g t.val =
      pentaGroup (pentaFunction oracle.permutation) (quadPublicLeaves oracle message
        (actualNonces oracle.permutation k)) level g t

end TwoPermutationPrototype.Sampling
