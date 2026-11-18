import CommitGolfCandidate.S3CheckLeafMemory

/-! Word-level memory of the checker leaf at each of its program points, for
arbitrary permutation replies. The value buffer and the record's group digests
only have to lie above the 320-byte low workspace. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem s3_far_word (address offset low : Nat) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) (inside : offset < 256) (small : low < 320) :
    BitVec.ofNat 64 (address + offset) ≠ BitVec.ofNat 64 low := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at numeric
  omega

theorem s6_far_low (address low : Nat) (above : 320 ≤ address) (bounded : address < 2^64)
    (small : low < 320) : BitVec.ofNat 64 address ≠ BitVec.ofNat 64 low := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at numeric
  omega

theorem s6_word_memory (left right : MachineState) (same : left.mem = right.mem)
    (address : Word) : left.getMem address = right.getMem address := congrFun same address

theorem s3_salt_small : S3Small s3SaltPairs := by decide
theorem s3_head_small : S3Small s3HeadPairs := by decide
theorem s3_relay_small : S3Small s3RelayPairs := by decide
theorem s3_tail_small : S3Small s3TailPairs := by decide
theorem s6_own_small : S3Small s6OwnPairs := by decide
theorem s6_place_small (place : Nat) (small : place < 4) : S3Small (s6PlacePairs place) := by
  interval_cases place <;> decide
theorem s3_output_small : S3Small s3OutputPairs := by decide

/-- Absolute copies: each destination word receives its source word. -/
theorem s3_copy_absolute (pairs : List (Nat × Nat)) (state : MachineState)
    (small : S3Small pairs) (distinct : pairs.Pairwise fun left right => left.2 ≠ right.2)
    (apart : ∀ source ∈ pairs, ∀ destination ∈ pairs, source.1 ≠ destination.2)
    (pair : Nat × Nat) (inside : pair ∈ pairs) :
    (s3Run (s3Copy .x0 pairs) state).getMem (BitVec.ofNat 64 pair.2) =
      state.getMem (BitVec.ofNat 64 pair.1) := by
  have copied := s3_copy_memory_inside .x0 pairs state (by decide) small distinct (by
    intro source sourceMember destination destinationMember
    rw [s3_zero_register, BitVec.zero_add]
    exact s3_low_distinct _ _ (small source sourceMember).1.2
      (small destination destinationMember).2.2
      (apart source sourceMember destination destinationMember)) pair inside
  rw [s3_zero_register, BitVec.zero_add] at copied
  exact copied

/-- Copies from a far buffer at `address` to low destinations. -/
theorem s3_copy_far (base : Reg) (pairs : List (Nat × Nat)) (state : MachineState)
    (address span : Nat) (pointer : state.getReg base = BitVec.ofNat 64 address)
    (above : 320 ≤ address) (bounded : address + span ≤ 2^64)
    (baseStable : base ≠ .x6) (small : S3Small pairs)
    (sources : ∀ pair ∈ pairs, pair.1 < span)
    (distinct : pairs.Pairwise fun left right => left.2 ≠ right.2)
    (pair : Nat × Nat) (inside : pair ∈ pairs) :
    (s3Run (s3Copy base pairs) state).getMem (BitVec.ofNat 64 pair.2) =
      state.getMem (BitVec.ofNat 64 (address + pair.1)) := by
  have copied := s3_copy_memory_inside base pairs state baseStable small distinct (by
    intro source sourceMember destination destinationMember
    rw [pointer, ← BitVec.ofNat_add]
    exact s6_far_low (address + source.1) destination.2 (by omega)
      (by have := sources source sourceMember; omega)
      (by have := (small destination destinationMember).2.2; omega)) pair inside
  rw [pointer, ← BitVec.ofNat_add] at copied
  exact copied

theorem s6_offset_distinct (base : Word) (pairs : List (Nat × Nat)) (small : S3Small pairs)
    (distinct : pairs.Pairwise fun left right => left.2 ≠ right.2) :
    pairs.Pairwise fun left right =>
      base + BitVec.ofNat 64 left.2 ≠ base + BitVec.ofNat 64 right.2 := by
  refine List.Pairwise.imp_of_mem (fun {left right} leftMember rightMember different equal =>
    different ?_) distinct
  have numeric := congrArg BitVec.toNat (add_left_cancel equal)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := (small left leftMember).2.2; omega),
    Nat.mod_eq_of_lt (by have := (small right rightMember).2.2; omega)] at numeric
  exact numeric

theorem s3_pairs_member {pairs : List (Nat × Nat)} {count : Nat} {f : Nat → Nat × Nat}
    (shape : pairs = (List.range count).map f) (word : Nat) (small : word < count) :
    f word ∈ pairs := by
  rw [shape]
  exact List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩

/-! ### Replies written at address 0 -/

theorem s3_align_low (i : Nat) (small : i < 200) :
    alignToDword (BitVec.ofNat 64 0 + BitVec.ofNat 64 i) = BitVec.ofNat 64 (8 * (i / 8)) :=
  (by decide : ∀ i : Fin 200, alignToDword (BitVec.ofNat 64 0 + BitVec.ofNat 64 i.val) =
    BitVec.ofNat 64 (8 * (i.val / 8))) ⟨i, small⟩

theorem s3_reply_outside (state : MachineState) (answer : BitVec 1600) (query : Word)
    (outside : ∀ word < 25, query ≠ BitVec.ofNat 64 (8 * word)) :
    (writeBits state (BitVec.ofNat 64 0) answer).getMem query = state.getMem query := by
  apply writeBits_memory_outside
  intro i inside
  rw [s3_align_low i (by omega)]
  exact outside (i / 8) (by omega)

theorem s3_check_reply_byte (state : MachineState) (answer : BitVec 1600) (index : Nat)
    (inside : index < 200) :
    (writeBits state (BitVec.ofNat 64 0) answer).getByte (BitVec.ofNat 64 index) =
      answer.extractLsb' (8 * index) 8 := by
  have written := write_bits_byte state (BitVec.ofNat 64 0) answer index (by omega) (by decide)
  rw [BitVec.zero_add] at written
  exact written

theorem s3_leaf_middle_eq (state : MachineState) (first : BitVec 1600) :
    s3LeafMiddle state first = writeBits (s3LeafFirst state) (BitVec.ofNat 64 0) first :=
  congrArg (fun address => writeBits (s3LeafFirst state) address first)
    (s3_leaf_first_selectors state).2.2.2.1

theorem s3_leaf_last_eq (state : MachineState) (first second : BitVec 1600) :
    s3LeafLast state first second =
      writeBits (s3LeafSecond state first) (BitVec.ofNat 64 0) second :=
  congrArg (fun address => writeBits (s3LeafSecond state first) address second)
    ((s3_leaf_second_register state first .x12 (by decide)).trans
      (s3_leaf_first_selectors state).2.2.2.1)

theorem s6_leaf_reply_eq (state : MachineState) (first second third : BitVec 1600) :
    s6LeafReply state first second third =
      writeBits (s6LeafGroup state first second) (BitVec.ofNat 64 0) third :=
  congrArg (fun address => writeBits (s6LeafGroup state first second) address third)
    ((s6_leaf_group_register state first second .x12 (by decide)).trans
      (s3_leaf_first_selectors state).2.2.2.1)

/-- The low 32 bytes of a reply written at address 0. -/
theorem s6_reply_digest (state : MachineState) (answer : BitVec 1600) :
    readBuffer (writeBits state (BitVec.ofNat 64 0) answer) 0 32 =
      BitVec.ofNat 256 answer.toNat := by
  have written := write_bits_digest state 0 0 answer (by decide) (by decide)
  apply BitVec.eq_of_toNat_eq
  have numeric := congrArg BitVec.toNat written
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    at numeric
  rw [numeric, BitVec.toNat_ofNat]

/-! ### The first window -/

theorem s3_select_mem (current : MachineState) : (s3Run s3LeafSelect current).mem = current.mem :=
  rfl

theorem s3_input_mem (current : MachineState) :
    (s3Run [.ADDI .x10 .x0 56] current).mem = current.mem := rfl

theorem s3_finish_tail_mem (current : MachineState) :
    (s3Run [.SRLI .x20 .x20 2, .ADDI .x8 .x8 256] current).mem = current.mem := rfl

theorem s3_leaf_first_memory (state : MachineState) (query : Word) :
    (s3LeafFirst state).getMem query =
      (s3Run (s3Copy .x8 s3HeadPairs) (s3Run (s3Copy .x0 s3SaltPairs) state)).getMem query := by
  unfold s3LeafFirst s3LeafBuild
  rw [s3_run_append, s3_run_append]
  exact s6_word_memory _ _ (s3_select_mem _) query

theorem s3_leaf_first_salt (state : MachineState) (address : Nat)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 3, (s3LeafFirst state).getMem (BitVec.ofNat 64 (8 * word)) =
      state.getMem (BitVec.ofNat 64 (256 + 8 * word)) := by
  intro word small
  rw [s3_leaf_first_memory, s3_copy_memory_outside .x8 s3HeadPairs _ s3_head_small _ (by
      intro pair member
      obtain ⟨other, otherSmall, rfl⟩ := List.mem_map.mp member
      have := List.mem_range.mp otherSmall
      exact s3_low_distinct _ _ (by omega) (by omega) (by omega))]
  exact s3_copy_absolute s3SaltPairs state s3_salt_small (by decide) (by decide)
    (256 + 8 * word, 8 * word) (s3_pairs_member rfl word small)

theorem s3_leaf_first_head (state : MachineState) (address : Nat)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 22, (s3LeafFirst state).getMem (BitVec.ofNat 64 (24 + 8 * word)) =
      state.getMem (BitVec.ofNat 64 (address + 8 * word)) := by
  intro word small
  rw [s3_leaf_first_memory, s3_copy_far .x8 s3HeadPairs _ address 256
      (by rw [s3_copy_register .x0 _ _ .x8 (by decide)]; exact pointer) above (by omega)
      (by decide) s3_head_small (by decide) (by decide) (8 * word, 24 + 8 * word)
      (s3_pairs_member rfl word small)]
  exact s3_copy_memory_outside .x0 s3SaltPairs state s3_salt_small _ (by
    intro pair member
    exact s3_far_word address (8 * word) pair.2 above bounded (by omega)
      (by have := (s3_salt_small pair member).2.2; omega))

theorem s3_leaf_first_outside (state : MachineState) (query : Word)
    (outside : ∀ i < 25, query ≠ BitVec.ofNat 64 (8 * i)) :
    (s3LeafFirst state).getMem query = state.getMem query := by
  rw [s3_leaf_first_memory, s3_copy_memory_outside .x8 s3HeadPairs _ s3_head_small _ (by
      intro pair member
      obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
      have := List.mem_range.mp small
      have distinct := outside (word + 3) (by omega)
      rwa [show 8 * (word + 3) = 24 + 8 * word by omega] at distinct)]
  exact s3_copy_memory_outside .x0 s3SaltPairs state s3_salt_small _ (by
    intro pair member
    obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
    exact outside word (by have := List.mem_range.mp small; omega))

/-! ### The second window -/

def s3LeafRelayed (state : MachineState) (first : BitVec 1600) : MachineState :=
  s3Run (s3Copy .x0 s3RelayPairs) (s3LeafMiddle state first)

theorem s3_leaf_second_memory (state : MachineState) (first : BitVec 1600) (query : Word) :
    (s3LeafSecond state first).getMem query =
      (s3Run (s3Copy .x8 s3TailPairs) (s3LeafRelayed state first)).getMem query := by
  unfold s3LeafSecond s3LeafChain s3LeafRelayed
  rw [s3_run_append, s3_run_append]
  exact s6_word_memory _ _ (s3_input_mem _) query

theorem s3_leaf_second_relay (state : MachineState) (first : BitVec 1600) :
    ∀ word < 8, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (56 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (136 + 8 * word)) := by
  intro word small
  rw [s3_leaf_second_memory, s3_copy_memory_outside .x8 s3TailPairs _ s3_tail_small _ (by
      intro pair member
      obtain ⟨other, otherSmall, rfl⟩ := List.mem_map.mp member
      have := List.mem_range.mp otherSmall
      exact s3_low_distinct _ _ (by omega) (by omega) (by omega)), s3LeafRelayed]
  exact s3_copy_absolute s3RelayPairs _ s3_relay_small (by decide) (by decide)
    (136 + 8 * word, 56 + 8 * word) (s3_pairs_member rfl word small)

theorem s3_leaf_second_tail (state : MachineState) (address : Nat) (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 17, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (120 + 8 * word)) =
      state.getMem (BitVec.ofNat 64 (address + (120 + 8 * word))) := by
  intro word small
  have base : (s3LeafRelayed state first).getReg .x8 = BitVec.ofNat 64 address := by
    rw [s3LeafRelayed, s3_copy_register .x0 _ _ .x8 (by decide), s3_leaf_middle_register,
      s3_leaf_first_register state .x8 (by decide)]
    exact pointer
  have far : ∀ i < 25, BitVec.ofNat 64 (address + (120 + 8 * word)) ≠ BitVec.ofNat 64 (8 * i) :=
    fun i inside => s3_far_word address _ _ above bounded (by omega) (by omega)
  rw [s3_leaf_second_memory, s3_copy_far .x8 s3TailPairs _ address 256 base above (by omega)
      (by decide) s3_tail_small (by decide) (by decide) (120 + 8 * word, 120 + 8 * word)
      (s3_pairs_member rfl word small),
    s3LeafRelayed, s3_copy_memory_outside .x0 s3RelayPairs _ s3_relay_small _ (by
      intro pair member
      exact s3_far_word address _ pair.2 above bounded (by omega)
        (by have := (s3_relay_small pair member).2.2; omega)),
    s3_leaf_middle_eq, s3_reply_outside _ first _ far, s3_leaf_first_outside state _ far]

theorem s3_leaf_second_outside (state : MachineState) (first : BitVec 1600) (query : Word)
    (outside : ∀ i < 32, 7 ≤ i → query ≠ BitVec.ofNat 64 (8 * i)) :
    (s3LeafSecond state first).getMem query = (s3LeafMiddle state first).getMem query := by
  rw [s3_leaf_second_memory, s3_copy_memory_outside .x8 s3TailPairs _ s3_tail_small _ (by
      intro pair member
      obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
      have := List.mem_range.mp small
      have distinct := outside (word + 15) (by omega) (by omega)
      rwa [show 8 * (word + 15) = 120 + 8 * word by omega] at distinct), s3LeafRelayed]
  exact s3_copy_memory_outside .x0 s3RelayPairs _ s3_relay_small _ (by
    intro pair member
    obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
    have := List.mem_range.mp small
    have distinct := outside (word + 7) (by omega) (by omega)
    rwa [show 8 * (word + 7) = 56 + 8 * word by omega] at distinct)

/-! ### The leaf digest at its own place -/

theorem s6_leaf_owned_memory (state : MachineState) (first second : BitVec 1600)
    (query : Word) :
    (s6LeafOwned state first second).getMem query =
      (s3Run s6LeafOwn (s3Run s6LeafSlot (s3LeafLast state first second))).getMem query := rfl

theorem s6_leaf_slot_mem (state : MachineState) : (s3Run s6LeafSlot state).mem = state.mem := rfl

theorem s6_leaf_owned_own (state : MachineState) (first second : BitVec 1600) :
    ∀ word < 4, (s6LeafOwned state first second).getMem
        (BitVec.ofNat 64 (128 + 32 * s6SlotOf (s3LeafLast state first second) + 8 * word)) =
      (s3LeafLast state first second).getMem (BitVec.ofNat 64 (8 * word)) := by
  intro word small
  have x7 := s6_leaf_slot_value (s3LeafLast state first second)
  have slotSmall := s6_slot_small (s3LeafLast state first second)
  have address : BitVec.ofNat 64 (128 + 32 * s6SlotOf (s3LeafLast state first second) +
      8 * word) = (s3Run s6LeafSlot (s3LeafLast state first second)).getReg .x7 +
        BitVec.ofNat 64 (128 + 8 * word) := by
    rw [x7, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  rw [s6_leaf_owned_memory, address]
  unfold s6LeafOwn
  have copied := s6_copy_at_inside .x0 .x7 s6OwnPairs
    (s3Run s6LeafSlot (s3LeafLast state first second)) s6_own_small (by decide) (by decide)
    (s6_offset_distinct _ s6OwnPairs s6_own_small (by decide))
    (by
      intro source sourceMember destination destinationMember
      rw [x7, s3_zero_register, BitVec.zero_add, ← BitVec.ofNat_add]
      obtain ⟨i, iSmall, rfl⟩ := List.mem_map.mp sourceMember
      obtain ⟨j, jSmall, rfl⟩ := List.mem_map.mp destinationMember
      have := List.mem_range.mp iSmall
      have := List.mem_range.mp jSmall
      exact s3_low_distinct _ _ (by omega) (by omega) (by omega))
    (8 * word, 128 + 8 * word) (s3_pairs_member rfl word small)
  dsimp only at copied
  rw [copied, s3_zero_register, BitVec.zero_add]
  exact congrFun (s6_leaf_slot_mem _) _

theorem s6_leaf_owned_outside (state : MachineState) (first second : BitVec 1600)
    (query : Word)
    (outside : ∀ word < 4, query ≠
      BitVec.ofNat 64 (128 + 32 * s6SlotOf (s3LeafLast state first second) + 8 * word)) :
    (s6LeafOwned state first second).getMem query =
      (s3LeafLast state first second).getMem query := by
  have x7 := s6_leaf_slot_value (s3LeafLast state first second)
  unfold s6LeafOwned s6LeafOwn
  rw [s6_copy_at_outside .x0 .x7 s6OwnPairs _ s6_own_small (by decide)
    query (by
      intro pair member
      obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
      have distinct := outside word (List.mem_range.mp small)
      rw [x7, ← BitVec.ofNat_add]
      rwa [show 32 * s6SlotOf (s3LeafLast state first second) + (128 + 8 * word) =
        128 + 32 * s6SlotOf (s3LeafLast state first second) + 8 * word by omega])]
  exact congrFun (s6_leaf_slot_mem _) _

/-! ### The place blocks -/

/-- Rank of the record digest that fills place `place`. -/
def s6Rank (slot place : Nat) : Nat := place - if slot < place then 1 else 0

theorem s6_rank_small (slot place : Nat) (slotSmall : slot < 4) (placeSmall : place < 4)
    (different : place ≠ slot) : s6Rank slot place < 3 := by
  unfold s6Rank
  split <;> omega

theorem s6_place_copy_memory (state : MachineState) (place : Nat) (query : Word) :
    (s3Run (s6PlaceCopy place) state).getMem query =
      (s3Run (s3Copy .x25 (s6PlacePairs place)) state).getMem query := by
  unfold s6PlaceCopy
  rw [s3_run_append]
  rfl

/-- Memory after the first `count` place blocks: every other place filled from the
record's digests in order, everything else unchanged. -/
theorem s6_places_memory (state : MachineState) (slot groupAddress : Nat) (slotSmall : slot < 4)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot))
    (pointer : state.getReg .x25 = BitVec.ofNat 64 groupAddress)
    (above : 320 ≤ groupAddress) (bounded : groupAddress + 96 < 2^64)
    (count : Nat) (few : count ≤ 4) :
    (∀ query : Word, (∀ place < count, place ≠ slot → ∀ word < 4,
        query ≠ BitVec.ofNat 64 (128 + 32 * place + 8 * word)) →
      (s6PlacesUpTo count state).getMem query = state.getMem query) ∧
    (∀ place < count, place ≠ slot → ∀ word < 4,
      (s6PlacesUpTo count state).getMem (BitVec.ofNat 64 (128 + 32 * place + 8 * word)) =
        state.getMem (BitVec.ofNat 64 (groupAddress + 32 * s6Rank slot place + 8 * word))) := by
  induction count with
  | zero => exact ⟨fun _ _ => rfl, fun place inside => absurd inside (by omega)⟩
  | succ count ih =>
    obtain ⟨outsideIH, insideIH⟩ := ih (by omega)
    have blockX7 := (s6_places_x7 state count (by omega)).trans x7
    have cursor : (s6PlacesUpTo count state).getReg .x25 =
        BitVec.ofNat 64 (groupAddress + 32 * s6Rank slot count) := by
      rw [s6_places_cursor state slot slotSmall x7 count (by omega), pointer,
        ← BitVec.ofNat_add]
      rfl
    have step : s6PlacesUpTo (count + 1) state =
        s6PlaceBlock count (s6PlacesUpTo count state) := rfl
    by_cases same : count = slot
    · have unchanged (query : Word) :
          (s6PlacesUpTo (count + 1) state).getMem query =
            (s6PlacesUpTo count state).getMem query := by
        rw [step, s6_place_block_taken _ count slot blockX7 same]
        exact s6_word_memory _ _ (s6_place_test_mem _ _) query
      refine ⟨fun query outside => ?_, fun place inside different word small => ?_⟩
      · rw [unchanged]
        exact outsideIH query (fun place inside => outside place (by omega))
      · rw [unchanged]
        exact insideIH place (by omega) different word small
    · have rankSmall := s6_rank_small slot count slotSmall (by omega) same
      let tested := s3Run (s6PlaceTest count) (s6PlacesUpTo count state)
      have testedCursor : tested.getReg .x25 =
          BitVec.ofNat 64 (groupAddress + 32 * s6Rank slot count) :=
        (s6_place_test_register _ count .x25 (by decide)).trans cursor
      have block (query : Word) :
          (s6PlacesUpTo (count + 1) state).getMem query =
            (s3Run (s3Copy .x25 (s6PlacePairs count)) tested).getMem query := by
        rw [step, s6_place_block_fall _ count slot (by omega) slotSmall blockX7 same,
          s6_place_copy_memory]
      have testedMemory (query : Word) :
          tested.getMem query = (s6PlacesUpTo count state).getMem query :=
        s6_word_memory _ _ (s6_place_test_mem _ _) query
      have destinations : ∀ query : Word, (∀ word < 4,
          query ≠ BitVec.ofNat 64 (128 + 32 * count + 8 * word)) →
          (s6PlacesUpTo (count + 1) state).getMem query =
            (s6PlacesUpTo count state).getMem query := by
        intro query outside
        rw [block, s3_copy_memory_outside .x25 (s6PlacePairs count) tested
          (s6_place_small count (by omega)) query (by
            intro pair member
            obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
            exact outside word (List.mem_range.mp small)), testedMemory]
      refine ⟨fun query outside => ?_, fun place inside different word small => ?_⟩
      · rw [destinations query (outside count (by omega) same)]
        exact outsideIH query (fun place inside => outside place (by omega))
      · by_cases current : place = count
        · subst current
          have placeSmall : place < 4 := by omega
          rw [block, s3_copy_far .x25 (s6PlacePairs place) tested
              (groupAddress + 32 * s6Rank slot place) 32 testedCursor (by omega) (by omega)
              (by decide) (s6_place_small place (by omega)) (by
                intro pair member
                obtain ⟨other, otherSmall, rfl⟩ := List.mem_map.mp member
                have := List.mem_range.mp otherSmall
                show 8 * other < 32
                omega) (by interval_cases place <;> decide)
              (8 * word, 128 + 32 * place + 8 * word) (s3_pairs_member rfl word small),
            testedMemory,
            outsideIH _ (fun other otherInside _ otherWord _ =>
              s6_far_low _ _ (by omega) (by omega) (by omega))]
        · rw [destinations _ (fun other _ equal => by
              have numeric := congrArg BitVec.toNat equal
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)] at numeric
              omega)]
          exact insideIH place (by omega) different word small

theorem s6_leaf_placed_memory (state : MachineState) (first second : BitVec 1600)
    (groupAddress : Nat)
    (pointer : (s6LeafOwned state first second).getReg .x25 = BitVec.ofNat 64 groupAddress)
    (above : 320 ≤ groupAddress) (bounded : groupAddress + 96 < 2^64) :
    (∀ query : Word, (∀ place < 4, place ≠ s6SlotOf (s3LeafLast state first second) →
        ∀ word < 4, query ≠ BitVec.ofNat 64 (128 + 32 * place + 8 * word)) →
      (s6PlacesUpTo 4 (s6LeafOwned state first second)).getMem query =
        (s6LeafOwned state first second).getMem query) ∧
    (∀ place < 4, place ≠ s6SlotOf (s3LeafLast state first second) → ∀ word < 4,
      (s6PlacesUpTo 4 (s6LeafOwned state first second)).getMem
          (BitVec.ofNat 64 (128 + 32 * place + 8 * word)) =
        (s6LeafOwned state first second).getMem (BitVec.ofNat 64 (groupAddress +
          32 * s6Rank (s6SlotOf (s3LeafLast state first second)) place + 8 * word))) :=
  s6_places_memory _ _ groupAddress (s6_slot_small _) (s6_leaf_owned_x7 state first second)
    pointer above bounded 4 (by decide)

/-! ### Clearing and the digest copy -/

theorem s6_leaf_group_memory (state : MachineState) (first second : BitVec 1600) (query : Word) :
    (s6LeafGroup state first second).getMem query =
      (s3Run s6LeafClear (s6PlacesUpTo 4 (s6LeafOwned state first second))).getMem query := rfl

theorem s6_clear_step (current : MachineState) (offset : Nat) (query : Word)
    (small : offset % 8 = 0 ∧ offset < 288) :
    (execInstrBr current (.SD .x0 .x0 (BitVec.ofNat 12 offset))).getMem query =
      if query = BitVec.ofNat 64 offset then 0 else current.getMem query := by
  simp only [execInstrBr, MachineState.getMem_setPC, s3_store_memory, s3_zero_register,
    BitVec.zero_add, s3_word_offset offset small.1 small.2]
  rfl

theorem s6_clear_run (words : List Nat) (current : MachineState) (query : Word)
    (small : ∀ word ∈ words, word < 29) :
    (s3Run (words.map fun word => .SD .x0 .x0 (BitVec.ofNat 12 (56 + 8 * word))) current).getMem
        query =
      if ∃ word ∈ words, query = BitVec.ofNat 64 (56 + 8 * word) then 0
      else current.getMem query := by
  induction words generalizing current with
  | nil => simp [s3Run]
  | cons head rest ih =>
    change (s3Run (rest.map fun word => .SD .x0 .x0 (BitVec.ofNat 12 (56 + 8 * word)))
      (execInstrBr current (.SD .x0 .x0 (BitVec.ofNat 12 (56 + 8 * head))))).getMem query = _
    have headSmall := small head List.mem_cons_self
    rw [ih _ (fun word inside => small word (List.mem_cons_of_mem _ inside)),
      s6_clear_step current _ query ⟨by omega, by omega⟩]
    by_cases hit : query = BitVec.ofNat 64 (56 + 8 * head)
    · simp [hit]
    · by_cases later : ∃ word ∈ rest, query = BitVec.ofNat 64 (56 + 8 * word)
      · simp [later]
      · simp only [if_neg later, if_neg hit, List.mem_cons, exists_eq_or_imp, hit, false_or,
          later, ↓reduceIte]

theorem s6_leaf_group_zero (state : MachineState) (first second : BitVec 1600) :
    ∀ word < 9, (s6LeafGroup state first second).getMem (BitVec.ofNat 64 (56 + 8 * word)) = 0 := by
  intro word small
  rw [s6_leaf_group_memory, s6LeafClear, s6_clear_run _ _ _ (by
      intro other inside
      have := List.mem_range.mp inside
      omega), if_pos ⟨word, List.mem_range.mpr small, rfl⟩]

theorem s6_leaf_group_outside (state : MachineState) (first second : BitVec 1600) (query : Word)
    (outside : ∀ word < 9, query ≠ BitVec.ofNat 64 (56 + 8 * word)) :
    (s6LeafGroup state first second).getMem query =
      (s6PlacesUpTo 4 (s6LeafOwned state first second)).getMem query := by
  rw [s6_leaf_group_memory, s6LeafClear, s6_clear_run _ _ _ (by
      intro other inside
      have := List.mem_range.mp inside
      omega), if_neg (by
        rintro ⟨word, inside, equal⟩
        exact outside word (List.mem_range.mp inside) equal)]

theorem s3_leaf_done_memory (state : MachineState) (first second third : BitVec 1600)
    (query : Word) :
    (s3LeafDone state first second third).getMem query =
      (s3Run (s3Copy .x0 s3OutputPairs) (s6LeafReply state first second third)).getMem query := by
  unfold s3LeafDone s3LeafFinish
  rw [s3_run_append]
  exact s6_word_memory _ _ (s3_finish_tail_mem _) query

theorem s3_leaf_done_digest (state : MachineState) (first second third : BitVec 1600) :
    ∀ word < 4, (s3LeafDone state first second third).getMem
        (BitVec.ofNat 64 (256 + 8 * word)) =
      (s6LeafReply state first second third).getMem (BitVec.ofNat 64 (8 * word)) := by
  intro word small
  rw [s3_leaf_done_memory]
  exact s3_copy_absolute s3OutputPairs _ s3_output_small (by decide) (by decide)
    (8 * word, 256 + 8 * word) (s3_pairs_member rfl word small)

theorem s3_leaf_done_outside (state : MachineState) (first second third : BitVec 1600)
    (query : Word) (outside : ∀ word < 4, query ≠ BitVec.ofNat 64 (256 + 8 * word)) :
    (s3LeafDone state first second third).getMem query =
      (s6LeafReply state first second third).getMem query := by
  rw [s3_leaf_done_memory]
  exact s3_copy_memory_outside .x0 s3OutputPairs _ s3_output_small query (by
    intro pair member
    obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
    exact outside word (List.mem_range.mp small))

/-- The place blocks write only the places other than the leaf's own one, whatever x25 holds. -/
theorem s6_places_outside (state : MachineState) (slot : Nat) (slotSmall : slot < 4)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot)) (count : Nat) (few : count ≤ 4)
    (query : Word) (outside : ∀ place < count, place ≠ slot → ∀ word < 4,
      query ≠ BitVec.ofNat 64 (128 + 32 * place + 8 * word)) :
    (s6PlacesUpTo count state).getMem query = state.getMem query := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have blockX7 := (s6_places_x7 state count (by omega)).trans x7
    have step : s6PlacesUpTo (count + 1) state =
        s6PlaceBlock count (s6PlacesUpTo count state) := rfl
    rw [step, ← ih (by omega) (fun place inside => outside place (by omega))]
    by_cases same : count = slot
    · rw [s6_place_block_taken _ count slot blockX7 same]
      exact s6_word_memory _ _ (s6_place_test_mem _ _) query
    · rw [s6_place_block_fall _ count slot (by omega) slotSmall blockX7 same,
        s6_place_copy_memory, s3_copy_memory_outside .x25 (s6PlacePairs count) _
          (s6_place_small count (by omega)) query (by
            intro pair member
            obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
            exact outside count (by omega) same word (List.mem_range.mp small))]
      exact s6_word_memory _ _ (s6_place_test_mem _ _) query

/-- Above the workspace, the state at the place blocks still holds the entry memory. -/
theorem s6_leaf_owned_far (state : MachineState) (first second : BitVec 1600) (address : Nat)
    (above : 320 ≤ address) (bounded : address < 2^64) :
    (s6LeafOwned state first second).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have far : ∀ i < 36, BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (8 * i) :=
    fun i inside => s6_far_low _ _ above bounded (by omega)
  have slotSmall := s6_slot_small (s3LeafLast state first second)
  rw [s6_leaf_owned_outside state first second _ (fun word small =>
      s6_far_low _ _ above bounded (by omega)),
    s3_leaf_last_eq, s3_reply_outside _ second _ (fun word small => far word (by omega)),
    s3_leaf_second_outside state first _ (fun i inside _ => far i (by omega)),
    s3_leaf_middle_eq, s3_reply_outside _ first _ (fun word small => far word (by omega)),
    s3_leaf_first_outside state _ (fun i inside => far i (by omega))]

end CommitGolfCandidate
