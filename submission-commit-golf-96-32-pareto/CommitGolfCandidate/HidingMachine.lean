import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Identify the commitment and every transmitted proof byte with the salted
reference tree, covering both normal openings (`k ≠ 128`, 784 B/pos) and
level-7 cap-table openings (`k = 128`, 560 B/pos + 4096 B cap table = 75,776 B). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The heap constructed by the machine is the unique reference heap for its
message and retained 16-byte salts, on every used slot. -/
theorem committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Salt)
    (salts : ∀ index, readBuffer state (5905584160 + 16 * index.val) 16 = salt index)
    (node : Nat) (positive : 0 < node) (inside : node < 2 * LENGTH) :
    heapDigest state 4294971424 node = saltedHeap oracle.compression message salt node := by
  apply heap_eq_reference oracle.compression LENGTH _ _ correct.2.1 _ node positive inside
  intro index below
  have leaf := correct.2.2 ⟨index, below⟩
  rw [salts] at leaf
  simpa only [dif_pos below] using leaf

theorem committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Salt)
    (salts : ∀ index, readBuffer state (5905584160 + 16 * index.val) 16 = salt index) :
    readBuffer state submission.layout.commitment 32 =
      saltedHeap oracle.compression message salt 1 :=
  correct.1.trans (committed_heap_reference oracle message state correct salt salts
    1 (by decide) (by decide))

/-- One byte of the serialized proof at `offset < openingProofBytes positions.card`:
for `k = BATCH`, bytes `0..71679` hold 128 records of `(16B salt, 17 siblings)` and bytes
`71680..75775` hold the 128 level-7 cap digests `heap[128..255]`;
for `k ≠ BATCH`, bytes `0..784*k - 1` hold `k` records of `(16B salt, 24 siblings)`. -/
def referenceOpeningByte (heap : Nat → Digest) (salt : Index → Salt)
    (positions : Positions) (offset : Nat) : BitVec 8 :=
  if positions.card = BATCH then
    if offset < 71680 then
      let ordinal := offset / 560
      let rem := offset % 560
      let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
      if rem < 16 then
        (salt index).extractLsb' (8 * rem) 8
      else
        let level := (rem - 16) / 32
        (heap (((LENGTH + index.val) / 2 ^ level) ^^^ 1)).extractLsb' (8 * ((rem - 16) % 32)) 8
    else
      (heap (128 + (offset - 71680) / 32)).extractLsb' (8 * ((offset - 71680) % 32)) 8
  else
    let ordinal := offset / 784
    let rem := offset % 784
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    if rem < 16 then
      (salt index).extractLsb' (8 * rem) 8
    else
      let level := (rem - 16) / 32
      (heap (((LENGTH + index.val) / 2 ^ level) ^^^ 1)).extractLsb' (8 * ((rem - 16) % 32)) 8

/-- Exact little-endian proof bytes, in the ABI's sorted position order. -/
def referenceOpening (heap : Nat → Digest) (salt : Index → Salt)
    (positions : Positions) : Proof :=
  (List.range (openingProofBytes positions.card)).map (referenceOpeningByte heap salt positions)

theorem reference_opening_length (heap : Nat → Digest) (salt : Index → Salt)
    (positions : Positions) :
    (referenceOpening heap salt positions).length = openingProofBytes positions.card := by
  simp only [referenceOpening, List.length_map, List.length_range]

/-- All bytes emitted by the actual opening image equal the reference proof,
for every opening set (including `k = 0`, `k = BATCH`, and arbitrary `k ≠ BATCH`). -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Salt)
    (salts : ∀ index, readBuffer state (5905584160 + 16 * index.val) 16 = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (saltedHeap oracle.compression message salt) salt positions := by
  dsimp only
  rw [Submission.readProof, opening_result_succeeded, if_pos rfl, opening_result_length]
  unfold referenceOpening referenceOpeningByte
  apply List.map_congr_left
  intro offset present
  have below : offset < openingProofBytes positions.card := List.mem_range.mp present
  by_cases batch : positions.card = BATCH
  · rw [if_pos batch]
    have belowCap : offset < 75776 := by
      simp only [openingProofBytes, if_pos batch] at below; exact below
    have capRecs := opening_output_records_cap state positions batch
    by_cases inRecs : offset < 71680
    · rw [if_pos inRecs]
      have ordLt : offset / 560 < BATCH := by change offset / 560 < 128; omega
      let index : Index := ⟨openingIndex positions (offset / 560), opening_index_bound positions (offset / 560)⟩
      by_cases inSalt : offset % 560 < 16
      · rw [if_pos inSalt]
        have saltEq : readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
            (submission.layout.proof + 560 * (offset / 560)) 16 = salt index :=
          (capRecs.1 (offset / 560) ordLt).1.trans (salts index)
        have addr : submission.layout.proof + 560 * (offset / 560) + offset % 560 =
            submission.layout.proof + offset := by omega
        dsimp only [index] at saltEq ⊢
        rw [← saltEq, read_buffer_byte _ _ 16 (offset % 560) inSalt, addr]
      · rw [if_neg inSalt]
        have level17 : (offset % 560 - 16) / 32 < 17 := by omega
        have level24 : (offset % 560 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
        have byteIdx : (offset % 560 - 16) % 32 < 32 := Nat.mod_lt _ (by decide)
        have bounds := opening_sibling_bounds index ((offset % 560 - 16) / 32) level24
        have digEq : readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
            (submission.layout.proof + 560 * (offset / 560) + 16 + 32 * ((offset % 560 - 16) / 32)) 32 =
            saltedHeap oracle.compression message salt
              (((LENGTH + index.val) / 2 ^ ((offset % 560 - 16) / 32)) ^^^ 1) :=
          ((capRecs.1 (offset / 560) ordLt).2 _ level17).trans
            (committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2)
        have addr : submission.layout.proof + 560 * (offset / 560) + 16 + 32 * ((offset % 560 - 16) / 32) +
            (offset % 560 - 16) % 32 = submission.layout.proof + offset := by omega
        dsimp only [index] at digEq ⊢
        rw [← digEq, read_buffer_byte _ _ 32 _ byteIdx, addr]
    · rw [if_neg inRecs]
      let slot := (offset - 71680) / 32
      have slotLt : slot < 128 := by omega
      have byteIdx : (offset - 71680) % 32 < 32 := Nat.mod_lt _ (by decide)
      have addrEq : submission.layout.proof + 71680 + 32 * slot + (offset - 71680) % 32 =
          submission.layout.proof + offset := by omega
      have digestEq :
          readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
            (submission.layout.proof + 71680 + 32 * slot) 32 =
            saltedHeap oracle.compression message salt (128 + slot) := by
        rw [capRecs.2 slot slotLt]
        exact committed_heap_reference oracle message state correct salt salts (128 + slot)
          (by omega) (by change 128 + slot < 2 * 16777216; omega)
      change _ = (saltedHeap oracle.compression message salt (128 + slot)).extractLsb'
        (8 * ((offset - 71680) % 32)) 8
      rw [← digestEq, read_buffer_byte _ _ 32 _ byteIdx, addrEq]
  · rw [if_neg batch]
    have belowNorm : offset < 784 * positions.card := by
      simp only [openingProofBytes, if_neg batch] at below; exact below
    have ordinal : offset / 784 < positions.card := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    let index : Index := ⟨openingIndex positions (offset / 784), opening_index_bound positions (offset / 784)⟩
    have records := opening_output_records state positions batch (offset / 784) ordinal
    by_cases inSalt : offset % 784 < 16
    · rw [if_pos inSalt]
      have saltEq : readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
          (submission.layout.proof + 784 * (offset / 784)) 16 = salt index :=
        records.1.trans (salts index)
      have addr : submission.layout.proof + 784 * (offset / 784) + offset % 784 =
          submission.layout.proof + offset := by omega
      dsimp only [index] at saltEq ⊢
      rw [← saltEq, read_buffer_byte _ _ 16 (offset % 784) inSalt, addr]
    · rw [if_neg inSalt]
      have level : (offset % 784 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
      have byteIdx : (offset % 784 - 16) % 32 < 32 := Nat.mod_lt _ (by decide)
      have bounds := opening_sibling_bounds index ((offset % 784 - 16) / 32) level
      have digEq : readBuffer (openingResult (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor) positions).state
          (submission.layout.proof + 784 * (offset / 784) + 16 + 32 * ((offset % 784 - 16) / 32)) 32 =
          saltedHeap oracle.compression message salt
            (((LENGTH + index.val) / 2 ^ ((offset % 784 - 16) / 32)) ^^^ 1) :=
        (records.2 _ level).trans (committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2)
      have addr : submission.layout.proof + 784 * (offset / 784) + 16 + 32 * ((offset % 784 - 16) / 32) +
          (offset % 784 - 16) % 32 = submission.layout.proof + offset := by omega
      dsimp only [index] at digEq ⊢
      rw [← digEq, read_buffer_byte _ _ 32 _ byteIdx, addr]

end CommitGolfCandidate
