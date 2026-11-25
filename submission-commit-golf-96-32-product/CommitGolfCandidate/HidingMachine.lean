import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Identify the commitment and every transmitted proof byte with the salted
reference tree, covering both normal openings (`k ≠ 128`) and level-7 cap-table
openings (`k = 128`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The heap constructed by the machine is the unique reference heap for its
message and retained salts, on every used slot. -/
theorem committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160 + 32 * index.val) 32 = salt index)
    (node : Nat) (positive : 0 < node) (inside : node < 2 * LENGTH) :
    heapDigest state 4294971424 node = saltedHeap oracle.compression message salt node := by
  apply heap_eq_reference oracle.compression LENGTH _ _ correct.2.1 _ node positive inside
  intro index below
  have leaf := correct.2.2 ⟨index, below⟩
  rw [salts] at leaf
  simpa only [dif_pos below] using leaf

theorem committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160 + 32 * index.val) 32 = salt index) :
    readBuffer state submission.layout.commitment 32 =
      saltedHeap oracle.compression message salt 1 :=
  correct.1.trans (committed_heap_reference oracle message state correct salt salts
    1 (by decide) (by decide))

/-- The 32-byte digest containing byte `offset` of the opening proof.
For `k = BATCH`, bytes `0..73727` hold 128 records of `(salt, 17 siblings)` and bytes
`73728..77823` hold the 128 level-7 cap digests `heap[128..255]`.
For `k ≠ BATCH`, bytes `0..800*k - 1` hold `k` records of `(salt, 24 siblings)`. -/
def referenceOpeningDigestAt (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (offset : Nat) : Digest :=
  if positions.card = BATCH then
    if offset < 73728 then
      let ordinal := offset / 576
      let part := (offset % 576) / 32
      let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
      if part = 0 then salt index
      else heap (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1)
    else
      heap (128 + (offset - 73728) / 32)
  else
    let ordinal := offset / 800
    let part := (offset % 800) / 32
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    if part = 0 then salt index
    else heap (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1)

/-- Exact little-endian proof bytes, in the ABI's sorted position order. -/
def referenceOpening (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : Proof :=
  (List.range (openingProofBytes positions.card)).map fun offset =>
    (referenceOpeningDigestAt heap salt positions offset).extractLsb' (8 * (offset % 32)) 8

theorem reference_opening_length (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) :
    (referenceOpening heap salt positions).length = openingProofBytes positions.card := by
  simp only [referenceOpening, List.length_map, List.length_range]

/-- All bytes emitted by the actual opening image equal the reference proof,
for every opening set (including `k = 0`, `k = BATCH`, and arbitrary `k ≠ BATCH`). -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readBuffer state (5905584160 + 32 * index.val) 32 = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (saltedHeap oracle.compression message salt) salt positions := by
  dsimp only
  rw [Submission.readProof, opening_result_succeeded, if_pos rfl, opening_result_length]
  unfold referenceOpening
  apply List.map_congr_left
  intro offset present
  have below : offset < openingProofBytes positions.card := List.mem_range.mp present
  by_cases batch : positions.card = BATCH
  · have belowCap : offset < 77824 := by
      simp only [openingProofBytes, if_pos batch] at below; exact below
    have capRecs := opening_output_records_cap state positions batch
    unfold referenceOpeningDigestAt
    rw [if_pos batch]
    by_cases inRecs : offset < 73728
    · rw [if_pos inRecs]
      let ordinal := offset / 576
      let part := (offset % 576) / 32
      let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
      have ordLt : ordinal < BATCH := by change offset / 576 < 128; omega
      have partLt : part < 18 := by omega
      have addrEq : submission.layout.proof + 576 * ordinal + 32 * part + offset % 32 =
          submission.layout.proof + offset := by omega
      have digestEq :
          readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
            (submission.layout.proof + 576 * ordinal + 32 * part) 32 =
            if part = 0 then salt index
            else saltedHeap oracle.compression message salt (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1) := by
        by_cases zero : part = 0
        · rw [if_pos zero, zero, Nat.mul_zero, Nat.add_zero]
          exact (capRecs.1 ordinal ordLt).1.trans (salts index)
        · rw [if_neg zero]
          have level : part - 1 < 17 := by omega
          have level24 : part - 1 < LOG_LENGTH := by change part - 1 < 24; omega
          have addrSplit : submission.layout.proof + 576 * ordinal + 32 * part =
              submission.layout.proof + 576 * ordinal + 32 + 32 * (part - 1) := by omega
          rw [addrSplit, (capRecs.1 ordinal ordLt).2 (part - 1) level]
          have bounds := opening_sibling_bounds index (part - 1) level24
          exact committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2
      change _ = (if part = 0 then salt index
        else saltedHeap oracle.compression message salt (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1)).extractLsb'
          (8 * (offset % 32)) 8
      rw [← digestEq, read_buffer_byte _ _ 32 (offset % 32) (by omega), addrEq]
    · rw [if_neg inRecs]
      let slot := (offset - 73728) / 32
      have slotLt : slot < 128 := by omega
      have addrEq : submission.layout.proof + 73728 + 32 * slot + offset % 32 =
          submission.layout.proof + offset := by omega
      have digestEq :
          readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
            (submission.layout.proof + 73728 + 32 * slot) 32 =
            saltedHeap oracle.compression message salt (128 + slot) := by
        rw [capRecs.2 slot slotLt]
        exact committed_heap_reference oracle message state correct salt salts (128 + slot)
          (by omega) (by change 128 + slot < 2 * 16777216; omega)
      change _ = (saltedHeap oracle.compression message salt (128 + slot)).extractLsb' (8 * (offset % 32)) 8
      rw [← digestEq, read_buffer_byte _ _ 32 (offset % 32) (by omega), addrEq]
  · have belowNorm : offset < 800 * positions.card := by
      simp only [openingProofBytes, if_neg batch] at below; exact below
    unfold referenceOpeningDigestAt
    rw [if_neg batch]
    let ordinal := offset / 800
    let part := (offset % 800) / 32
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    have ordLt : ordinal < positions.card := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    have partLt : part < 25 := by omega
    have addrEq : submission.layout.proof + 800 * ordinal + 32 * part + offset % 32 =
        submission.layout.proof + offset := by omega
    have records := opening_output_records state positions batch ordinal ordLt
    have digestEq :
        readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
          (submission.layout.proof + 800 * ordinal + 32 * part) 32 =
          if part = 0 then salt index
          else saltedHeap oracle.compression message salt (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1) := by
      by_cases zero : part = 0
      · rw [if_pos zero, zero, Nat.mul_zero, Nat.add_zero]
        exact records.1.trans (salts index)
      · rw [if_neg zero]
        have level : part - 1 < LOG_LENGTH := by change part - 1 < 24; omega
        have addrSplit : submission.layout.proof + 800 * ordinal + 32 * part =
            submission.layout.proof + 800 * ordinal + 32 + 32 * (part - 1) := by omega
        rw [addrSplit, records.2 (part - 1) level]
        have bounds := opening_sibling_bounds index (part - 1) level
        exact committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2
    change _ = (if part = 0 then salt index
      else saltedHeap oracle.compression message salt (((LENGTH + index.val) / 2 ^ (part - 1)) ^^^ 1)).extractLsb'
        (8 * (offset % 32)) 8
    rw [← digestEq, read_buffer_byte _ _ 32 (offset % 32) (by omega), addrEq]

end CommitGolfCandidate
