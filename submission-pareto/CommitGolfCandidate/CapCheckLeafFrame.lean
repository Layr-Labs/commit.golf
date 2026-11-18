import CommitGolfCandidate.S3CheckLeafStates

/-! Frames for every supported outcome of the checker leaf, including
arbitrary permutation replies. Only the words 0, 8, ..., 280 may change, so
real input buffers, collected cap roots and finalized marks survive. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem s3_leaf_done_word_frame (state : MachineState) (first second third : BitVec 1600)
    (address : Word) (outside : ∀ i < 36, address ≠ BitVec.ofNat 64 (8*i)) :
    (s3LeafDone state first second third).getMem address = state.getMem address := by
  have slotSmall := s6_slot_small (s3LeafLast state first second)
  have shifted (offset count : Nat) (inside : offset + count ≤ 36) :
      ∀ word < count, address ≠ BitVec.ofNat 64 (8 * offset + 8 * word) := by
    intro word small
    have distinct := outside (offset + word) (by omega)
    rwa [show 8 * (offset + word) = 8 * offset + 8 * word by omega] at distinct
  rw [s3_leaf_done_outside _ _ _ _ address (shifted 32 4 (by decide)), s6_leaf_reply_eq,
    s3_reply_outside _ third address (fun word small => outside word (by omega)),
    s6_leaf_group_outside _ _ _ address (shifted 7 9 (by decide)),
    s6_places_outside _ _ slotSmall (s6_leaf_owned_x7 state first second) 4 (by decide) address
      (fun place placeSmall _ word small => by
        have distinct := outside (16 + 4 * place + word) (by omega)
        rwa [show 8 * (16 + 4 * place + word) = 128 + 32 * place + 8 * word by omega]
          at distinct),
    s6_leaf_owned_outside _ _ _ address (fun word small => by
      have distinct := outside (16 + 4 * s6SlotOf (s3LeafLast state first second) + word)
        (by omega)
      rwa [show 8 * (16 + 4 * s6SlotOf (s3LeafLast state first second) + word) =
        128 + 32 * s6SlotOf (s3LeafLast state first second) + 8 * word by omega] at distinct),
    s3_leaf_last_eq, s3_reply_outside _ second address (fun word small => outside word (by omega)),
    s3_leaf_second_outside _ _ address (fun i inside _ => outside i (by omega)),
    s3_leaf_middle_eq, s3_reply_outside _ first address (fun word small => outside word (by omega)),
    s3_leaf_first_outside state address (fun i inside => outside i (by omega))]

/-- The routine writes only the words 0, 8, ..., 280. -/
theorem cap_check_leaf_word_frame (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) (address : Word)
    (outside : ∀ i < 36, address ≠ BitVec.ofNat 64 (8*i)) :
    finished.getMem address = state.getMem address := by
  obtain ⟨first, second, third, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_word_frame state first second third address outside

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
