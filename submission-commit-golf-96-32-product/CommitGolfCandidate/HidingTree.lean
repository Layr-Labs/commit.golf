import CommitGolfCandidate.HeapModel
import CommitGolfCandidate.CompressionSampling

/-! A memory-independent description of the honest Merkle tree. The hiding proof
can reason about salted leaves and their ancestors; machine refinement must still
identify the emitted root and proof with this tree. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- The complete binary heap, with leaves at slots `leafCount` through
`2*leafCount-1`. Slot zero and out-of-range slots are unused. -/
def referenceHeap (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (node : Nat) : Digest :=
  if branch : 0 < node ∧ node < leafCount then
    combine compress (referenceHeap compress leafCount leaf (2*node))
      (referenceHeap compress leafCount leaf (2*node+1))
  else if leafCount ≤ node ∧ node < 2*leafCount then leaf (node-leafCount)
  else 0
termination_by 2*leafCount-node
decreasing_by all_goals omega

theorem reference_heap_parent (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (node : Nat) (positive : 0 < node) (below : node < leafCount) :
    referenceHeap compress leafCount leaf node =
      combine compress (referenceHeap compress leafCount leaf (2*node))
        (referenceHeap compress leafCount leaf (2*node+1)) := by
  rw [referenceHeap, dif_pos ⟨positive, below⟩]

theorem reference_heap_leaf (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (index : Nat) (inside : index < leafCount) :
    referenceHeap compress leafCount leaf (leafCount+index) = leaf index := by
  rw [referenceHeap, dif_neg (by omega), if_pos (by omega)]
  congr 1
  omega

/-- Parent consistency and leaf contents uniquely determine every used heap slot.
No injectivity or random-oracle property of compression is required. -/
theorem heap_eq_reference (compress : Compression) (leafCount : Nat)
    (leaf heap : Nat → Digest)
    (parents : ∀ node, 0 < node → node < leafCount →
      heap node = combine compress (heap (2*node)) (heap (2*node+1)))
    (leaves : ∀ index, index < leafCount → heap (leafCount+index) = leaf index)
    (node : Nat) (positive : 0 < node) (inside : node < 2*leafCount) :
    heap node = referenceHeap compress leafCount leaf node := by
  by_cases branch : node < leafCount
  · rw [parents node positive branch, reference_heap_parent _ _ _ _ positive branch]
    congr 1
    · exact heap_eq_reference compress leafCount leaf heap parents leaves (2*node)
        (by omega) (by omega)
    · exact heap_eq_reference compress leafCount leaf heap parents leaves (2*node+1)
        (by omega) (by omega)
  · have index : node-leafCount < leafCount := by omega
    have address : leafCount+(node-leafCount) = node := by omega
    rw [← address, leaves _ index, reference_heap_leaf _ _ _ _ index]
termination_by 2*leafCount-node
decreasing_by all_goals omega

/-- The mathematical heap for this submission, using exactly its four-block
salted leaf hash and the same compression function for all internal nodes. -/
def saltedHeap (compress : Compression) (message : Message) (salt : Index → Digest) :
    Nat → Digest :=
  referenceHeap compress LENGTH fun index =>
    if inside : index < LENGTH then
      leafDigest compress (salt ⟨index, inside⟩) (message ⟨index, inside⟩)
    else 0

theorem salted_heap_leaf (compress : Compression) (message : Message)
    (salt : Index → Digest) (index : Index) :
    saltedHeap compress message salt (LENGTH+index.val) =
      leafDigest compress (salt index) (message index) := by
  rw [saltedHeap, reference_heap_leaf _ _ _ _ index.isLt, dif_pos index.isLt]

/-- Every sibling read by a valid authentication path is a used heap slot. -/
theorem heap_sibling_bounds (leafCount node : Nat) (positive : 2 ≤ node)
    (inside : node < 2*leafCount) : 0 < node ^^^ 1 ∧ node ^^^ 1 < 2*leafCount := by
  by_cases even : node%2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    omega
  · have odd : node%2 = 1 := by omega
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr odd)]
    omega

theorem opening_sibling_bounds (index : Index) (level : Nat) (inside : level < LOG_LENGTH) :
    0 < ((LENGTH+index.val)/2^level) ^^^ 1 ∧
      ((LENGTH+index.val)/2^level) ^^^ 1 < 2*LENGTH := by
  have indexBound := index.isLt
  have powerPositive : 0 < 2^level := by positivity
  have powerBound : 2^(level+1) ≤ LENGTH :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have doubled : 2^(level+1) = 2*2^level := by rw [Nat.pow_succ]; omega
  have lower : 2 ≤ (LENGTH+index.val)/2^level := by
    rw [doubled] at powerBound
    exact (Nat.le_div_iff_mul_le powerPositive).mpr (by omega)
  have upper : (LENGTH+index.val)/2^level < 2*LENGTH :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact heap_sibling_bounds LENGTH _ lower upper

/-- Heap consistency above a cap level `low` and the leaf contents determine every
slot above `low`; nodes at or below `low` need not be parent-consistent. -/
theorem heap_eq_reference_above (compress : Compression) (leafCount low : Nat)
    (leaf heap : Nat → Digest)
    (parents : ∀ node, low < node → node < leafCount →
      heap node = combine compress (heap (2*node)) (heap (2*node+1)))
    (leaves : ∀ index, index < leafCount → heap (leafCount+index) = leaf index) :
    ∀ measure node, 2*leafCount-node ≤ measure → low < node → node < 2*leafCount →
      heap node = referenceHeap compress leafCount leaf node := by
  intro measure
  induction measure with
  | zero => intro node bounded above inside; omega
  | succ measure ih =>
    intro node bounded above inside
    by_cases branch : node < leafCount
    · rw [parents node above branch, reference_heap_parent _ _ _ _ (by omega) branch]
      congr 1
      · exact ih (2*node) (by omega) (by omega) (by omega)
      · exact ih (2*node+1) (by omega) (by omega) (by omega)
    · have index : node-leafCount < leafCount := by omega
      have address : leafCount+(node-leafCount) = node := by omega
      rw [← address, leaves _ index, reference_heap_leaf _ _ _ _ index]

/-- The 17 siblings of an opened record lie strictly above the cap level 127. -/
theorem opening_cap_sibling_bounds (index : Index) (level : Nat) (inside : level < 17) :
    127 < ((LENGTH+index.val)/2^level) ^^^ 1 ∧
      ((LENGTH+index.val)/2^level) ^^^ 1 < 2*LENGTH := by
  have indexBound := index.isLt
  have powerPositive : 0 < 2^level := by positivity
  have powerBound : 2^level ≤ 2^16 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at powerBound
  have lower : 256 ≤ (LENGTH+index.val)/2^level := by
    apply (Nat.le_div_iff_mul_le powerPositive).mpr
    change 256 * 2^level ≤ 16777216 + index.val
    omega
  have upper : (LENGTH+index.val)/2^level < 2*LENGTH :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have bounds := heap_sibling_bounds LENGTH _ (by omega) upper
  refine ⟨?_, bounds.2⟩
  by_cases even : ((LENGTH+index.val)/2^level) % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

theorem fixed_oracle_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

theorem fixed_oracle_run_map (oracle : Oracle) {α β : Type}
    (f : α → β) (computation : OracleComp World α) :
    fixedOracleRun oracle (f <$> computation) = f <$> fixedOracleRun oracle computation := by
  simp only [fixedOracleRun, oracle_run_map, Functor.map_map]

/-- The sorted-position lookup (same definition as the machine's `openingIndex`). -/
def hidingRecordIndex (positions : Positions) (ordinal : Nat) : Nat :=
  if present : ordinal < positions.card then
    ((positions.sort (· ≤ ·))[ordinal]'(by simpa using present)).val
  else 0

theorem hiding_record_index_bound (positions : Positions) (ordinal : Nat) :
    hidingRecordIndex positions ordinal < LENGTH := by
  unfold hidingRecordIndex
  split
  · exact Fin.isLt _
  · decide

/-- The committed cap: heap slots 128..255, clamped to zero beyond the cap. -/
def referenceCap (heap : Nat → Digest) (node : Nat) : Digest :=
  if node < 128 then heap (128+node) else 0

/-- Proof byte `offset`: the 4096-byte cap (node `offset/32`, heap slot `128+offset/32`),
then one 568-byte record per opened position: the 24 salt bytes (the low bytes of the
leaf's initial state digest), followed by 17 sibling digests. -/
def referenceProofByte (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (offset : Nat) : Byte :=
  if offset < 4096 then (heap (128+offset/32)).extractLsb' (8*(offset%32)) 8
  else
    let index : Index := ⟨hidingRecordIndex positions ((offset-4096)/568),
      hiding_record_index_bound positions ((offset-4096)/568)⟩
    let part := (offset-4096)%568
    if part < 24 then (salt index).extractLsb' (8*part) 8
    else (heap (((LENGTH+index.val)/2^((part-24)/32)) ^^^ 1)).extractLsb' (8*((part-24)%32)) 8

/-- Exact little-endian proof bytes, in the ABI's sorted position order. -/
def referenceOpening (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : Proof :=
  (List.range (4096+568*positions.card)).map (referenceProofByte heap salt positions)

theorem reference_opening_length (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) :
    (referenceOpening heap salt positions).length = 4096+568*positions.card := by
  simp only [referenceOpening, List.length_map, List.length_range]

/-- Public transcript of the mathematical salted tree for one fixed salt vector:
the chain over the 128 cap nodes and the serialized cap-and-records proof. -/
def referenceTranscript (compress : Compression) (message : Message)
    (salt : Index → Digest) (positions : Positions) : Commitment × Proof :=
  let heap := saltedHeap compress message salt
  (capRoot compress (referenceCap heap), referenceOpening heap salt positions)

end CommitGolfCandidate
