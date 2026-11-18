import CommitGolfCandidate.S3CheckLeafStates
import CommitGolfCandidate.S6Model

/-! Fixed-oracle semantics of the checker leaf: for the real permutation the
routine leaves the group digest of the leaf's group in the scratch digest slot,
with `s3LeafDigest` of the scratch salt and the value at x8 at the leaf's own
place and the record's three digests at the other places. The three 200-byte
inputs are identified with `s3First`, `s3Second` and `s6GroupInput`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The eight 32-byte value blocks are the 256-byte value. -/
theorem s3_value_nat (state : MachineState) (address : Nat) (value : Entry)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    s3ReadNat state address 256 = value.toNat := by
  have chunk (i : Nat) (small : i < 8) :
      s3ReadNat state (address + 32 * i) 32 = value.toNat / 2 ^ (256 * i) % 2 ^ 256 := by
    have equal := congrArg BitVec.toNat (data i small)
    rw [s3_read_buffer_nat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at equal
    exact equal
  have partially (count : Nat) (small : count ≤ 8) :
      s3ReadNat state address (32 * count) = value.toNat % 2 ^ (256 * count) := by
    induction count with
    | zero => simp [s3ReadNat, Nat.mod_one]
    | succ count ih =>
      rw [Nat.mul_succ, s3_read_nat_add, ih (by omega), chunk count (by omega),
        Nat.mul_succ 256 count, Nat.pow_add, Nat.mod_mul,
        show 8 * (32 * count) = 256 * count by omega]
  have whole := partially 8 (by omega)
  rw [show s3ReadNat state address 256 = s3ReadNat state address (32 * 8) from rfl, whole]
  exact Nat.mod_eq_of_lt value.isLt

/-- The first permutation input is `salt[0..24) || value[0..176)`. -/
theorem s3_leaf_first_window (state : MachineState) (address : Nat) (salt : BitVec 256)
    (value : Entry) (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (s3LeafFirst state) 0 200 = s3First salt value := by
  have valueNat := s3_value_nat state address value data
  have saltWords : s3ReadNat (s3LeafFirst state) 0 24 = s3ReadNat state 256 24 :=
    s3_read_nat_words (s3LeafFirst state) state 0 256 3 (by decide) (by decide) (by
      intro word small
      rw [Nat.zero_add]
      exact s3_leaf_first_salt state address pointer above bounded word small)
  have saltNat : salt.toNat = s3ReadNat state 256 32 := by
    rw [← initial, s3_read_buffer_nat]
  have saltSplit := s3_read_nat_add state 256 24 8
  have saltLow := s3_read_nat_bound state 256 24
  simp only [Nat.reduceMul, Nat.reduceAdd] at saltSplit saltLow
  have saltPart : s3ReadNat (s3LeafFirst state) 0 24 = salt.toNat % 2 ^ 192 := by
    rw [saltWords, saltNat, saltSplit, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt saltLow).symm
  have headWords : s3ReadNat (s3LeafFirst state) 24 176 = s3ReadNat state address 176 :=
    s3_read_nat_words (s3LeafFirst state) state 24 address 22 (by decide) aligned
      (s3_leaf_first_head state address pointer above bounded)
  have valueSplit := s3_read_nat_add state address 176 80
  have valueLow := s3_read_nat_bound state address 176
  simp only [Nat.reduceMul, Nat.reduceAdd] at valueSplit valueLow
  have headPart : s3ReadNat (s3LeafFirst state) 24 176 = value.toNat % 2 ^ 1408 := by
    rw [headWords, ← valueNat, valueSplit, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt valueLow).symm
  have whole := s3_read_nat_add (s3LeafFirst state) 0 24 176
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.zero_add] at whole
  have natural : s3ReadNat (s3LeafFirst state) 0 200 =
      salt.toNat % 2 ^ 192 + (value.toNat % 2 ^ 1408) * 2 ^ 192 := by
    rw [whole, saltPart, headPart]
    ring
  rw [s3_read_buffer, natural]
  rfl

/-- The second permutation input is `reply[136..200) || value[120..256)`. -/
theorem s3_leaf_second_window (state : MachineState) (address : Nat) (value : Entry)
    (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (s3LeafSecond state first) 56 200 = s3Second first value := by
  have valueNat := s3_value_nat state address value data
  have chainWords : s3ReadNat (s3LeafSecond state first) 56 64 =
      s3ReadNat (s3LeafMiddle state first) 136 64 :=
    s3_read_nat_words (s3LeafSecond state first) (s3LeafMiddle state first) 56 136 8
      (by decide) (by decide) (s3_leaf_second_relay state first)
  have chainSlice : readBuffer (s3LeafMiddle state first) 136 64 =
      first.extractLsb' (8 * 136) (8 * 64) := by
    apply read_serialized_slice
    intro j inside
    rw [s3_leaf_middle_eq]
    exact s3_check_reply_byte _ first (136 + j) (by omega)
  have chain : s3ReadNat (s3LeafSecond state first) 56 64 = first.toNat / 2 ^ 1088 := by
    have equal := congrArg BitVec.toNat chainSlice
    rw [s3_read_buffer_nat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at equal
    simp only [Nat.reduceMul] at equal
    rw [chainWords, equal]
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact first.isLt
  have tailWords : s3ReadNat (s3LeafSecond state first) 120 136 =
      s3ReadNat state (address + 120) 136 :=
    s3_read_nat_words (s3LeafSecond state first) state 120 (address + 120) 17 (by decide)
      (by omega) (by
        intro word small
        rw [s3_leaf_second_tail state address first pointer above bounded word small,
          Nat.add_assoc])
  have valueSplit := s3_read_nat_add state address 120 136
  have valueLow := s3_read_nat_bound state address 120
  simp only [Nat.reduceMul, Nat.reduceAdd] at valueSplit valueLow
  have tail : s3ReadNat (s3LeafSecond state first) 120 136 = value.toNat / 2 ^ 960 := by
    rw [tailWords, ← valueNat, valueSplit,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 960), Nat.div_eq_of_lt valueLow, Nat.zero_add]
  have whole := s3_read_nat_add (s3LeafSecond state first) 56 64 136
  simp only [Nat.reduceMul, Nat.reduceAdd] at whole
  have natural : s3ReadNat (s3LeafSecond state first) 56 200 =
      first.toNat / 2 ^ 1088 + value.toNat / 2 ^ 960 * 2 ^ 512 := by
    rw [whole, chain, tail]
    ring
  rw [s3_read_buffer, natural]
  rfl

/-! ### The group window -/

/-- Place `place` of the group as the routine fills it. -/
def s6PlaceDigest (own : Digest) (slot : Nat) (others : Fin 3 → Digest) (place : Nat) :
    Digest :=
  if place = slot then own
  else if inside : s6Rank slot place < 3 then others ⟨s6Rank slot place, inside⟩ else 0

theorem s6_leaf_group_place (state : MachineState) (first second : BitVec 1600)
    (groupAddress : Nat) (others : Fin 3 → Digest)
    (groupPointer : state.getReg .x25 = BitVec.ofNat 64 groupAddress)
    (groupAligned : groupAddress % 8 = 0) (groupAbove : 320 ≤ groupAddress)
    (groupBounded : groupAddress + 96 < 2^64)
    (group : ∀ i : Fin 3, readBuffer state (groupAddress + 32*i.val) 32 = others i)
    (place : Nat) (placeSmall : place < 4) :
    s3ReadNat (s6LeafGroup state first second) (128 + 32 * place) 32 =
      (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
        others place).toNat := by
  have slotSmall := s6_slot_small (s3LeafLast state first second)
  have pointer : (s6LeafOwned state first second).getReg .x25 =
      BitVec.ofNat 64 groupAddress := by
    rw [s6_leaf_owned_register state first second .x25 (by decide),
      s3_leaf_first_register state .x25 (by decide)]
    exact groupPointer
  obtain ⟨placedOutside, placedInside⟩ :=
    s6_leaf_placed_memory state first second groupAddress pointer groupAbove groupBounded
  have cleared (word : Nat) (small : word < 4) :
      (s6LeafGroup state first second).getMem
          (BitVec.ofNat 64 (128 + 32 * place + 8 * word)) =
        (s6PlacesUpTo 4 (s6LeafOwned state first second)).getMem
          (BitVec.ofNat 64 (128 + 32 * place + 8 * word)) :=
    s6_leaf_group_outside state first second _ (fun other otherSmall =>
      s3_low_distinct _ _ (by omega) (by omega) (by omega))
  unfold s6PlaceDigest
  by_cases same : place = s6SlotOf (s3LeafLast state first second)
  · rw [if_pos same]
    have own : s3ReadNat (s6LeafGroup state first second) (128 + 32 * place) 32 =
        s3ReadNat (s3LeafLast state first second) 0 32 :=
      s3_read_nat_words _ _ (128 + 32 * place) 0 4 (by omega) (by decide) (by
        intro word small
        rw [Nat.zero_add, cleared word small,
          placedOutside _ (fun other otherSmall different otherWord _ equal => by
            have numeric := congrArg BitVec.toNat equal
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)] at numeric
            omega), same]
        exact s6_leaf_owned_own state first second word small)
    rw [own, ← s3_read_buffer_nat, s3_leaf_last_eq, s6_reply_digest]
  · rw [if_neg same]
    have rankSmall := s6_rank_small _ place slotSmall placeSmall same
    rw [dif_pos rankSmall]
    have copied : s3ReadNat (s6LeafGroup state first second) (128 + 32 * place) 32 =
        s3ReadNat state (groupAddress + 32 * s6Rank (s6SlotOf (s3LeafLast state first second))
          place) 32 :=
      s3_read_nat_words _ _ (128 + 32 * place) _ 4 (by omega) (by omega) (by
        intro word small
        rw [cleared word small, placedInside place placeSmall same word small,
          s6_leaf_owned_far state first second _ (by omega) (by omega)])
    rw [copied, ← s3_read_buffer_nat]
    exact congrArg BitVec.toNat (group ⟨_, rankSmall⟩)

/-- The third permutation input: 72 zero bytes, then the four places of the group. -/
theorem s6_leaf_group_window (state : MachineState) (first second : BitVec 1600)
    (groupAddress : Nat) (others : Fin 3 → Digest)
    (groupPointer : state.getReg .x25 = BitVec.ofNat 64 groupAddress)
    (groupAligned : groupAddress % 8 = 0) (groupAbove : 320 ≤ groupAddress)
    (groupBounded : groupAddress + 96 < 2^64)
    (group : ∀ i : Fin 3, readBuffer state (groupAddress + 32*i.val) 32 = others i) :
    readBuffer (s6LeafGroup state first second) 56 200 =
      s6GroupInput
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 0)
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 1)
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 2)
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 3) := by
  have place := s6_leaf_group_place state first second groupAddress others groupPointer
    groupAligned groupAbove groupBounded group
  have zero : s3ReadNat (s6LeafGroup state first second) 56 72 = 0 :=
    s3_read_nat_zero _ 56 9 (by decide) (s6_leaf_group_zero state first second)
  have split0 := s3_read_nat_add (s6LeafGroup state first second) 56 72 128
  have split1 := s3_read_nat_add (s6LeafGroup state first second) 128 32 96
  have split2 := s3_read_nat_add (s6LeafGroup state first second) 160 32 64
  have split3 := s3_read_nat_add (s6LeafGroup state first second) 192 32 32
  simp only [Nat.reduceMul, Nat.reduceAdd] at split0 split1 split2 split3
  have p0 := place 0 (by decide)
  have p1 := place 1 (by decide)
  have p2 := place 2 (by decide)
  have p3 := place 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at p0 p1 p2 p3
  have natural : s3ReadNat (s6LeafGroup state first second) 56 200 =
      ((s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 0).toNat +
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 1).toNat * 2 ^ 256 +
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 2).toNat * 2 ^ 512 +
        (s6PlaceDigest (BitVec.ofNat 256 second.toNat) (s6SlotOf (s3LeafLast state first second))
          others 3).toNat * 2 ^ 768) * 2 ^ 576 := by
    rw [split0, zero, split1, split2, split3, p0, p1, p2, p3,
      show (2 : Nat) ^ 512 = 2 ^ 256 * 2 ^ 256 by
        rw [show (512 : Nat) = 256 + 256 from rfl, Nat.pow_add],
      show (2 : Nat) ^ 768 = 2 ^ 256 * 2 ^ 256 * 2 ^ 256 by
        rw [show (768 : Nat) = 256 + 256 + 256 from rfl, Nat.pow_add, Nat.pow_add]]
    generalize (2 : Nat) ^ 256 = B
    generalize (2 : Nat) ^ 576 = C
    ring
  rw [s3_read_buffer, natural]
  rfl

/-- The digest slot receives the low 32 bytes of the third reply. -/
theorem s3_leaf_done_output (state : MachineState) (first second third : BitVec 1600) :
    readBuffer (s3LeafDone state first second third) 256 32 = BitVec.ofNat 256 third.toNat := by
  have copied : readBuffer (s3LeafDone state first second third) 256 32 =
      readBuffer (s6LeafReply state first second third) 0 32 :=
    (read_digest_eq_iff _ _ 256 0 (by decide) (by decide)).mpr (fun word small => by
      rw [s3_leaf_done_digest state first second third word small, Nat.zero_add])
  rw [copied, s6_leaf_reply_eq, s6_reply_digest]

theorem cap_check_leaf_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (capCheckLeaf state)).1 =
      s3LeafDone state (oracle.permutation (readBuffer (s3LeafFirst state) 0 200))
        (oracle.permutation (readBuffer (s3LeafSecond state
          (oracle.permutation (readBuffer (s3LeafFirst state) 0 200))) 56 200))
        (oracle.permutation (readBuffer (s6LeafGroup state
          (oracle.permutation (readBuffer (s3LeafFirst state) 0 200))
          (oracle.permutation (readBuffer (s3LeafSecond state
            (oracle.permutation (readBuffer (s3LeafFirst state) 0 200))) 56 200))) 56 200)) := by
  unfold capCheckLeaf s3PermutationQuery
  erw [check_evaluation_public_bind]
  erw [check_evaluation_public_bind]
  erw [check_evaluation_public_bind]
  erw [check_evaluation_pure]
  rfl

/-- The routine's places are the record group's places. -/
theorem s6_record_group_places (permutation : Perm) (salt : Digest) (value : Entry)
    (index : Nat) (others : Fin 3 → Digest) :
    s6GroupDigest permutation
        (s6PlaceDigest (s3LeafDigest permutation salt value) (index % 4) others 0)
        (s6PlaceDigest (s3LeafDigest permutation salt value) (index % 4) others 1)
        (s6PlaceDigest (s3LeafDigest permutation salt value) (index % 4) others 2)
        (s6PlaceDigest (s3LeafDigest permutation salt value) (index % 4) others 3) =
      s6RecordGroup permutation salt value index others := by
  rw [s6_record_group_digest]
  have cases : index % 4 = 0 ∨ index % 4 = 1 ∨ index % 4 = 2 ∨ index % 4 = 3 := by omega
  rcases cases with slot | slot | slot | slot <;>
    simp [s6PlaceDigest, s6Rank, slot] <;> rfl

/-- The digest slot after the routine, for the actual first two replies. -/
theorem s6_leaf_done_record (oracle : Oracle) (state : MachineState) (address groupAddress : Nat)
    (salt : BitVec 256) (value : Entry) (index : Nat) (others : Fin 3 → Digest)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (groupPointer : state.getReg .x25 = BitVec.ofNat 64 groupAddress)
    (groupAligned : groupAddress % 8 = 0) (groupAbove : 320 ≤ groupAddress)
    (groupBounded : groupAddress + 96 < 2^64)
    (position : state.getReg .x20 = BitVec.ofNat 64 index)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256)
    (group : ∀ i : Fin 3, readBuffer state (groupAddress + 32*i.val) 32 = others i)
    (first second : BitVec 1600)
    (firstEq : first = oracle.permutation (s3First salt value))
    (secondEq : second = oracle.permutation (readBuffer (s3LeafSecond state first) 56 200)) :
    readBuffer (s3LeafDone state first second
        (oracle.permutation (readBuffer (s6LeafGroup state first second) 56 200))) 256 32 =
      s6RecordGroup oracle.permutation salt value index others := by
  have slot : s6SlotOf (s3LeafLast state first second) = index % 4 := by
    unfold s6SlotOf
    rw [s3_leaf_last_register, s3_leaf_second_register state first .x20 (by decide),
      s3_leaf_first_register state .x20 (by decide), position, BitVec.toNat_ofNat]
    omega
  rw [s3_leaf_done_output state first second
      (oracle.permutation (readBuffer (s6LeafGroup state first second) 56 200)),
    s6_leaf_group_window state first second groupAddress others groupPointer groupAligned
      groupAbove groupBounded group, slot, secondEq,
    s3_leaf_second_window state address value first pointer aligned above bounded data, firstEq]
  exact s6_record_group_places oracle.permutation salt value index others

/-- The checking leaf leaves the group digest of the leaf's group in the scratch
digest slot: the leaf digest of the scratch salt and the value at x8 at place
`index % 4`, the record's three digests at x25 at the other places. -/
theorem cap_check_leaf_digest (oracle : Oracle) (state : MachineState) (address groupAddress : Nat)
    (salt : BitVec 256) (value : Entry) (index : Nat) (others : Fin 3 → Digest)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (groupPointer : state.getReg .x25 = BitVec.ofNat 64 groupAddress)
    (groupAligned : groupAddress % 8 = 0) (groupAbove : 320 ≤ groupAddress)
    (groupBounded : groupAddress + 96 < 2^64)
    (position : state.getReg .x20 = BitVec.ofNat 64 index)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256)
    (group : ∀ i : Fin 3, readBuffer state (groupAddress + 32*i.val) 32 = others i) :
    readBuffer (checkEvaluation oracle (capCheckLeaf state)).1 256 32 =
      s6RecordGroup oracle.permutation salt value index others := by
  have firstInput := s3_leaf_first_window state address salt value pointer aligned above bounded
    initial data
  rw [cap_check_leaf_evaluation]
  exact s6_leaf_done_record oracle state address groupAddress salt value index others pointer
    aligned above bounded groupPointer groupAligned groupAbove groupBounded position data group
    _ _ (congrArg (fun input : BitVec PERMUTATION_WIDTH => oracle.permutation input) firstInput)
    rfl

end CommitGolfCandidate
