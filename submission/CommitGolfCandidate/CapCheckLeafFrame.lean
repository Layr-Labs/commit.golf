import CommitGolfCandidate.S3CheckLeafStates

/-! Frames for every supported outcome of the stage-3 checker leaf, including
arbitrary permutation replies. Only the words 0, 8, ..., 280 may change, so
real input buffers, collected cap roots and finalized marks survive. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem s3_leaf_done_word_frame (state : MachineState) (first second : BitVec 1600)
    (address : Word) (outside : ∀ i < 36, address ≠ BitVec.ofNat 64 (8*i)) :
    (s3LeafDone state first second).getMem address = state.getMem address := by
  have reply : ∀ word < 25, address ≠ BitVec.ofNat 64 (8 * word) :=
    fun word small => outside word (by omega)
  rw [s3_leaf_done_outside state first second address (by
      intro pair member
      obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
      have distinct := outside (word + 32) (by have := List.mem_range.mp small; omega)
      rw [show 8 * (word + 32) = 256 + 8 * word by omega] at distinct
      exact distinct),
    s3_leaf_last_eq, s3_reply_outside _ second address reply,
    s3_leaf_second_outside state first address (by
      intro pair member
      obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
      have distinct := outside (word + 11) (by have := List.mem_range.mp small; omega)
      rw [show 8 * (word + 11) = 88 + 8 * word by omega] at distinct
      exact distinct) (by
      intro pair member
      obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
      have distinct := outside (word + 29) (by have := List.mem_range.mp small; omega)
      rw [show 8 * (word + 29) = 232 + 8 * word by omega] at distinct
      exact distinct),
    s3_leaf_middle_eq, s3_reply_outside _ first address reply,
    s3_leaf_first_outside state address (fun word small => by
      have distinct := outside (word + 4) (by omega)
      rw [show 8 * (word + 4) = 32 + 8 * word by omega] at distinct
      exact distinct)]

/-- The routine writes only the words 0, 8, ..., 280. -/
theorem cap_check_leaf_word_frame (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) (address : Word)
    (outside : ∀ i < 36, address ≠ BitVec.ofNat 64 (8*i)) :
    finished.getMem address = state.getMem address := by
  obtain ⟨first, second, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_word_frame state first second address outside

/-- The unchanged backing word also gives exact high-byte preservation. -/
theorem cap_check_leaf_high_frame (state reference finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state))
    (frame : CapHighBytes state reference) : CapHighBytes finished reference := by
  intro address lower upper
  have distinct : ∀ i < 36,
      BitVec.ofNat 64 (8 * (address / 8)) ≠ BitVec.ofNat 64 (8*i) := by
    intro i inside equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : 8*i < 2^64)] at numeric
    omega
  have word := cap_check_leaf_word_frame state finished reachable
    (BitVec.ofNat 64 (8 * (address / 8))) distinct
  have finishedByte := s3_check_byte_word finished (8 * (address / 8)) (address % 8) (by omega)
  have stateByte := s3_check_byte_word state (8 * (address / 8)) (address % 8) (by omega)
  rw [show 8 * (address / 8) + address % 8 = address by omega,
    show 8 * (address / 8) + 8 * (address % 8 / 8) = 8 * (address / 8) by omega]
    at finishedByte stateByte
  rw [finishedByte, word, ← stateByte]
  exact frame address lower upper

end CommitGolfCandidate
