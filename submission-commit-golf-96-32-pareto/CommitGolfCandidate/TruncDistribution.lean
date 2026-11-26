import CommitGolfCandidate.TruncCommitCoins
import CommitGolfCandidate.HidingMachine
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 240000
attribute [local irreducible] checkEvaluation parentProgram fixedParents commitLeaves

theorem committed_heap_reference (o : Oracle) (m : Message) (s : MachineState) (ok : CommittedState o m s)
    (salt : Index→Salt) (salts : ∀ i,readBuffer s (5905584160+16*i.val) 16=salt i)
    (n : Nat) (pos : 0<n) (hi : n<2*LENGTH) :
    heapDigest s heapBase n=saltedHeap o.compression m salt n := by
  apply heap_eq_reference o.compression LENGTH _ _ ok.2.1 _ n pos hi
  intro i h;have e:=ok.2.2 ⟨i,h⟩
  rw [salts] at e;simpa only [dif_pos h] using e
theorem committed_root_reference (o : Oracle) (m : Message) (s : MachineState) (ok : CommittedState o m s)
    (salt : Index→Salt) (salts : ∀ i,readBuffer s (5905584160+16*i.val) 16=salt i) :
    readBuffer s submission.layout.commitment 32=saltedHeap o.compression m salt 1 :=
  ok.1.trans (committed_heap_reference o m s ok salt salts 1 (by decide) (by decide))
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Salt)
    (salts : ∀ index, readBuffer state (5905584160 + 16 * index.val) 16 = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor
    CommitGolfCandidate.submission.readProof (openingResult trapdoor positions) =
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
        have saltEq : readBuffer (openingResult (readBuffer state CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor) positions).state
            (CommitGolfCandidate.submission.layout.proof + 560 * (offset / 560)) 16 = salt index :=
          (capRecs.1 (offset / 560) ordLt).1.trans (salts index)
        have addr : CommitGolfCandidate.submission.layout.proof + 560 * (offset / 560) + offset % 560 =
            CommitGolfCandidate.submission.layout.proof + offset := by omega
        dsimp only [index] at saltEq ⊢
        rw [← saltEq, read_buffer_byte _ _ 16 (offset % 560) inSalt, addr]
      · rw [if_neg inSalt]
        have level17 : (offset % 560 - 16) / 32 < 17 := by omega
        have level24 : (offset % 560 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
        have byteIdx : (offset % 560 - 16) % 32 < 32 := Nat.mod_lt _ (by decide)
        have bounds := opening_sibling_bounds index ((offset % 560 - 16) / 32) level24
        have digEq : readBuffer (openingResult (readBuffer state CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor) positions).state
            (CommitGolfCandidate.submission.layout.proof + 560 * (offset / 560) + 16 + 32 * ((offset % 560 - 16) / 32)) 32 =
            saltedHeap oracle.compression message salt
              (((LENGTH + index.val) / 2 ^ ((offset % 560 - 16) / 32)) ^^^ 1) :=
          ((capRecs.1 (offset / 560) ordLt).2 _ level17).trans
            (committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2)
        have addr : CommitGolfCandidate.submission.layout.proof + 560 * (offset / 560) + 16 + 32 * ((offset % 560 - 16) / 32) +
            (offset % 560 - 16) % 32 = CommitGolfCandidate.submission.layout.proof + offset := by omega
        dsimp only [index] at digEq ⊢
        rw [← digEq, read_buffer_byte _ _ 32 _ byteIdx, addr]
    · rw [if_neg inRecs]
      let slot := (offset - 71680) / 32
      have slotLt : slot < 128 := by omega
      have byteIdx : (offset - 71680) % 32 < 32 := Nat.mod_lt _ (by decide)
      have addrEq : CommitGolfCandidate.submission.layout.proof + 71680 + 32 * slot + (offset - 71680) % 32 =
          CommitGolfCandidate.submission.layout.proof + offset := by omega
      have digestEq :
          readBuffer (openingResult (readBuffer state CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor) positions).state
            (CommitGolfCandidate.submission.layout.proof + 71680 + 32 * slot) 32 =
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
      have saltEq : readBuffer (openingResult (readBuffer state CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor) positions).state
          (CommitGolfCandidate.submission.layout.proof + 784 * (offset / 784)) 16 = salt index :=
        records.1.trans (salts index)
      have addr : CommitGolfCandidate.submission.layout.proof + 784 * (offset / 784) + offset % 784 =
          CommitGolfCandidate.submission.layout.proof + offset := by omega
      dsimp only [index] at saltEq ⊢
      rw [← saltEq, read_buffer_byte _ _ 16 (offset % 784) inSalt, addr]
    · rw [if_neg inSalt]
      have level : (offset % 784 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
      have byteIdx : (offset % 784 - 16) % 32 < 32 := Nat.mod_lt _ (by decide)
      have bounds := opening_sibling_bounds index ((offset % 784 - 16) / 32) level
      have digEq : readBuffer (openingResult (readBuffer state CommitGolfCandidate.submission.layout.trapdoor CommitGolfCandidate.submission.sizes.trapdoor) positions).state
          (CommitGolfCandidate.submission.layout.proof + 784 * (offset / 784) + 16 + 32 * ((offset % 784 - 16) / 32)) 32 =
          saltedHeap oracle.compression message salt
            (((LENGTH + index.val) / 2 ^ ((offset % 784 - 16) / 32)) ^^^ 1) :=
        (records.2 _ level).trans (committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2)
      have addr : CommitGolfCandidate.submission.layout.proof + 784 * (offset / 784) + 16 + 32 * ((offset % 784 - 16) / 32) +
          (offset % 784 - 16) % 32 = CommitGolfCandidate.submission.layout.proof + offset := by omega
      dsimp only [index] at digEq ⊢
      rw [← digEq, read_buffer_byte _ _ 32 _ byteIdx, addr]


end CommitGolfCandidate.Trunc
