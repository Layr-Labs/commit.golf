import CommitGolfCandidate.CapPostprocess

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem cap_old_opening_heap_digest (committed : MachineState)
    (positions : Positions) (ordinal part : Nat)
    (present : ordinal < positions.card) (inside : part < 25) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state
      (submission.layout.proof+800*ordinal+32*part) 32 =
      referenceOpeningDigest (heapDigest committed 4294971424)
        (fun index => readNonce committed (5368713248+24*index.val))
        positions ordinal part := by
  dsimp only
  have records := opening_output_records committed positions ordinal present
  by_cases zero : part=0
  · subst part
    simpa only [referenceOpeningDigest,if_pos rfl,ite_true,Nat.mul_zero,Nat.add_zero]
      using records.1
  · have level : part-1 < LOG_LENGTH := by change part-1 < 24; omega
    have address : submission.layout.proof+800*ordinal+32*part =
        submission.layout.proof+800*ordinal+32+32*(part-1) := by omega
    rw [address,records.2 (part-1) level]
    simp only [referenceOpeningDigest,if_neg zero,heapDigest]

theorem cap_old_opening_heap_bytes (committed : MachineState) (positions : Positions) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (heapDigest committed 4294971424)
        (fun index => readNonce committed (5368713248+24*index.val)) positions := by
  dsimp only
  rw [Submission.readProof,opening_result_succeeded,if_pos rfl,opening_result_length]
  unfold referenceOpening
  apply List.map_congr_left
  intro offset member
  have below := List.mem_range.mp member
  have present : offset/800 < positions.card := by omega
  have inside : (offset%800)/32 < 25 := by omega
  have address : submission.layout.proof+800*(offset/800)+32*((offset%800)/32)+offset%32 =
      submission.layout.proof+offset := by omega
  have selected := cap_old_opening_heap_digest committed positions
    (offset/800) ((offset%800)/32) present inside
  rw [← selected,read_buffer_byte _ _ 32 (offset%32) (by omega),address]

theorem cap_postprocess_old_opening (message : Message) (committed : MachineState)
    (positions : Positions) (positive : 0 < positions.card) :
    capPostprocess positions (submission.readProof (openingResult
      (readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor) positions)) =
      capOpenLoadedBytes
        (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
        positions := by
  rw [cap_old_opening_heap_bytes]
  exact cap_postprocess_loaded message committed positions positive

end CommitGolfCandidate
