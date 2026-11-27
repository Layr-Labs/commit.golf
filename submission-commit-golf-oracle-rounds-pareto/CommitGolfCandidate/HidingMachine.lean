import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Identify the commitment and every transmitted proof byte with the salted
reference tree. This removes machine memory from the remaining privacy argument,
without replacing the machine-derived scheme being certified. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The heap constructed by the machine is the unique reference heap for its
message and retained salts, on every used slot. -/
theorem committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5368713248+32*index.val) 32 = salt index)
    (node : Nat) (positive : 0 < node) (inside : node < 2*LENGTH) :
    heapDigest state 4294971424 node = saltedHeap oracle.compression message salt node := by
  apply heap_eq_reference oracle.compression LENGTH _ _ correct.2.1 _ node positive inside
  intro index below
  have leaf := correct.2.2 ⟨index, below⟩
  rw [salts] at leaf
  simpa only [dif_pos below] using leaf

theorem committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5368713248+32*index.val) 32 = salt index) :
    readBuffer state submission.layout.commitment 32 =
      saltedHeap oracle.compression message salt 1 :=
  correct.1.trans (committed_heap_reference oracle message state correct salt salts
    1 (by decide) (by decide))

/-- An opening record contains its leaf's salt followed by its 24 siblings.
`part = 0` selects the salt; parts 1 through 24 select siblings. -/
def referenceOpeningDigest (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (ordinal part : Nat) : Digest :=
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  if part = 0 then salt index
  else heap (((LENGTH+index.val)/2^(part-1)) ^^^ 1)

/-- Exact little-endian proof bytes, in the ABI's sorted position order. -/
def referenceOpening (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : Proof :=
  (List.range (800*positions.card)).map fun offset =>
    (referenceOpeningDigest heap salt positions (offset/800) ((offset%800)/32)).extractLsb'
      (8*(offset%32)) 8

theorem reference_opening_length (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : (referenceOpening heap salt positions).length = 800*positions.card := by
  simp only [referenceOpening, List.length_map, List.length_range]

theorem opening_reference_digest (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5368713248+32*index.val) 32 = salt index)
    (positions : Positions) (ordinal part : Nat)
    (present : ordinal < positions.card) (inside : part < 25) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state
      (submission.layout.proof+800*ordinal+32*part) 32 =
    referenceOpeningDigest (saltedHeap oracle.compression message salt) salt positions ordinal part := by
  dsimp only
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  have records := opening_output_records state positions ordinal present
  by_cases zero : part = 0
  · subst part
    simpa only [referenceOpeningDigest, if_pos rfl, ite_true, Nat.mul_zero, Nat.add_zero]
      using records.1.trans (salts index)
  · have level : part-1 < LOG_LENGTH := by change part-1 < 24; omega
    have address : submission.layout.proof+800*ordinal+32*part =
        submission.layout.proof+800*ordinal+32+32*(part-1) := by omega
    rw [address, records.2 (part-1) level]
    simp only [referenceOpeningDigest, if_neg zero]
    have bounds := opening_sibling_bounds index (part-1) level
    exact committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2

/-- All bytes emitted by the actual opening image equal the reference proof.
The proof covers arbitrary opening sets, including the empty set. -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5368713248+32*index.val) 32 = salt index)
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
  have ordinal : offset/800 < positions.card := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have part : (offset%800)/32 < 25 := by omega
  have address : submission.layout.proof+800*(offset/800)+32*((offset%800)/32)+offset%32 =
      submission.layout.proof+offset := by omega
  have digest := opening_reference_digest oracle message state correct salt salts positions
    (offset/800) ((offset%800)/32) ordinal part
  rw [← digest, read_buffer_byte _ _ 32 (offset%32) (by omega), address]

end CommitGolfCandidate
