import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Identify the commitment and every transmitted proof byte with the salted
reference tree. This removes machine memory from the remaining privacy argument,
without replacing the machine-derived scheme being certified. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The heap constructed by the machine is the unique reference heap for its
message and retained salts, on every slot above the cap level (heap slots 128 and up).
Slots below the cap are never committed to and need not be consistent. -/
theorem committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160+32*index.val) 32 = salt index)
    (node : Nat) (above : 127 < node) (inside : node < 2*LENGTH) :
    heapDigest state 4294971424 node = saltedHeap oracle.compression message salt node := by
  apply heap_eq_reference_above oracle.compression LENGTH 127 _ _ correct.2.1 _ (2*LENGTH) node
    (by omega) above inside
  intro index below
  have leaf := correct.2.2 ⟨index, below⟩
  rw [salts] at leaf
  simpa only [dif_pos below] using leaf

/-- The committed cap: heap slots 128..255, clamped to zero beyond the cap. -/
def referenceCap (heap : Nat → Digest) (node : Nat) : Digest :=
  if node < 128 then heap (128+node) else 0

/-- The commitment is the 64-call chain over the reference cap. -/
theorem committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160+32*index.val) 32 = salt index) :
    readBuffer state submission.layout.commitment 32 =
      capRoot oracle.compression (referenceCap (saltedHeap oracle.compression message salt)) := by
  refine correct.1.trans ?_
  apply congrArg (capRoot oracle.compression)
  funext node
  unfold heapCap referenceCap
  split
  · exact committed_heap_reference oracle message state correct salt salts (128+node)
      (by omega) (by change 128+node < 2*16777216; omega)
  · rfl

/-- An opening record contains its leaf's salt followed by its 17 siblings.
`part = 0` selects the salt; parts 1 through 17 select siblings. -/
def referenceOpeningDigest (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (ordinal part : Nat) : Digest :=
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  if part = 0 then salt index
  else heap (((LENGTH+index.val)/2^(part-1)) ^^^ 1)

/-- The digest containing proof byte `offset`: the 4096-byte cap (node `offset/32`,
heap slot `128+offset/32`), then one 576-byte record per opened position. -/
def referenceProofDigest (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (offset : Nat) : Digest :=
  if offset < 4096 then heap (128+offset/32)
  else referenceOpeningDigest heap salt positions ((offset-4096)/576) (((offset-4096)%576)/32)

/-- Exact little-endian proof bytes, in the ABI's sorted position order. -/
def referenceOpening (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : Proof :=
  (List.range (4096+576*positions.card)).map fun offset =>
    (referenceProofDigest heap salt positions offset).extractLsb' (8*(offset%32)) 8

theorem reference_opening_length (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) :
    (referenceOpening heap salt positions).length = 4096+576*positions.card := by
  simp only [referenceOpening, List.length_map, List.length_range]

theorem opening_reference_cap (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160+32*index.val) 32 = salt index)
    (positions : Positions) (node : Nat) (inside : node < 128) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state (submission.layout.proof+32*node) 32 =
      saltedHeap oracle.compression message salt (128+node) := by
  dsimp only
  rw [(opening_output_records state positions).1 node inside]
  exact committed_heap_reference oracle message state correct salt salts (128+node)
    (by omega) (by change 128+node < 2*16777216; omega)

theorem opening_reference_digest (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160+32*index.val) 32 = salt index)
    (positions : Positions) (ordinal part : Nat)
    (present : ordinal < positions.card) (inside : part < 18) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state
      (submission.layout.proof+4096+576*ordinal+32*part) 32 =
    referenceOpeningDigest (saltedHeap oracle.compression message salt) salt positions ordinal part := by
  dsimp only
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  have records := (opening_output_records state positions).2 ordinal present
  by_cases zero : part = 0
  · subst part
    simpa only [referenceOpeningDigest, if_pos rfl, ite_true, Nat.mul_zero, Nat.add_zero]
      using records.1.trans (salts index)
  · have level : part-1 < 17 := by omega
    have address : submission.layout.proof+4096+576*ordinal+32*part =
        submission.layout.proof+4096+576*ordinal+32+32*(part-1) := by omega
    rw [address, records.2 (part-1) level]
    simp only [referenceOpeningDigest, if_neg zero]
    have bounds := opening_cap_sibling_bounds index (part-1) level
    exact committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2

/-- All bytes emitted by the actual opening image equal the reference proof.
The proof covers arbitrary opening sets, including the empty set. -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160+32*index.val) 32 = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (saltedHeap oracle.compression message salt) salt positions := by
  dsimp only
  rw [Submission.readProof, opening_result_succeeded, if_pos rfl, opening_result_length]
  unfold referenceOpening
  apply List.map_congr_left
  intro offset present
  have below := List.mem_range.mp present
  by_cases cap : offset < 4096
  · have node : offset/32 < 128 := by omega
    have address : submission.layout.proof+32*(offset/32)+offset%32 =
        submission.layout.proof+offset := by omega
    have digest := opening_reference_cap oracle message state correct salt salts positions
      (offset/32) node
    simp only [referenceProofDigest, if_pos cap]
    rw [← digest, read_buffer_byte _ _ 32 (offset%32) (by omega), address]
  · have ordinal : (offset-4096)/576 < positions.card :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    have part : ((offset-4096)%576)/32 < 18 := by omega
    have address : submission.layout.proof+4096+576*((offset-4096)/576)+
        32*(((offset-4096)%576)/32)+offset%32 = submission.layout.proof+offset := by omega
    have digest := opening_reference_digest oracle message state correct salt salts positions
      ((offset-4096)/576) (((offset-4096)%576)/32) ordinal part
    simp only [referenceProofDigest, if_neg cap]
    rw [← digest, read_buffer_byte _ _ 32 (offset%32) (by omega), address]

end CommitGolfCandidate
