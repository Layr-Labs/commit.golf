import CommitGolfCandidate.S3CheckLeafStates

/-! Fixed-oracle semantics of the stage-3 checker leaf: for the real
permutation the routine leaves `s3LeafDigest` of the scratch salt and the value
at x8 in the scratch digest slot. The two 200-byte inputs are identified with
`s3First` and `s3Second` from the actual words written by the routine. -/
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

/-- The first permutation input is `0^16 || value[0..184)`. -/
theorem s3_leaf_first_window (state : MachineState) (address : Nat) (value : Entry)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (s3LeafFirst state) 0 200 = s3First value := by
  have valueNat := s3_value_nat state address value data
  have zero : s3ReadNat (s3LeafFirst state) 0 16 = 0 :=
    s3_read_nat_zero (s3LeafFirst state) 0 2 (by decide) (by
      intro word small
      interval_cases word
      · exact (s3_leaf_first_zero state).1
      · exact (s3_leaf_first_zero state).2)
  have copied : s3ReadNat (s3LeafFirst state) 16 184 = s3ReadNat state address 184 :=
    s3_read_nat_words (s3LeafFirst state) state 16 address 23 (by decide) aligned
      (s3_leaf_first_value state address pointer above bounded)
  have split := s3_read_nat_add (s3LeafFirst state) 0 16 184
  have valueSplit := s3_read_nat_add state address 184 72
  have low := s3_read_nat_bound state address 184
  simp only [Nat.reduceMul, Nat.reduceAdd] at split valueSplit low
  have front : s3ReadNat state address 184 = value.toNat % 2 ^ 1472 := by
    rw [← valueNat, valueSplit, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt low).symm
  have natural : s3ReadNat (s3LeafFirst state) 0 200 = value.toNat % 2 ^ 1472 * 2 ^ 128 := by
    rw [split, zero, copied, front, Nat.zero_add, Nat.mul_comm]
  rw [s3_read_buffer, natural]
  rfl

/-- The second permutation input is `nonce || reply[96..200) || value[184..256)`. -/
theorem s3_leaf_second_window (state : MachineState) (address : Nat) (salt : BitVec 256)
    (value : Entry) (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (s3LeafSecond state first) 72 200 = s3Second salt first value := by
  have valueNat := s3_value_nat state address value data
  have lowWord (source : Nat) (small : source < 288) (aligned : source % 8 = 0)
      (high : 200 ≤ source) : ∀ word < 25,
      BitVec.ofNat 64 source ≠ BitVec.ofNat 64 (8 * word) :=
    fun word inside => s3_low_distinct _ _ small (by omega) (by omega)
  have farWord (offset : Nat) (inside : offset < 256) : ∀ word < 25,
      BitVec.ofNat 64 (address + offset) ≠ BitVec.ofNat 64 (8 * word) :=
    fun word small => s3_far_word address offset (8 * word) above bounded inside (by omega)
  -- the nonce
  have nonceWords : s3ReadNat (s3LeafSecond state first) 72 24 = s3ReadNat state 256 24 :=
    s3_read_nat_words (s3LeafSecond state first) state 72 256 3 (by decide) (by decide) (by
      intro word small
      rw [s3_leaf_second_nonce state first word small, s3_leaf_middle_eq,
        s3_reply_outside _ first _ (lowWord (256 + 8 * word) (by omega) (by omega) (by omega)),
        s3_leaf_first_outside state _
          (lowWord (256 + 8 * word) (by omega) (by omega) (by omega))])
  have saltNat : salt.toNat = s3ReadNat state 256 32 := by
    rw [← initial, s3_read_buffer_nat]
  have saltSplit := s3_read_nat_add state 256 24 8
  have saltLow := s3_read_nat_bound state 256 24
  simp only [Nat.reduceMul, Nat.reduceAdd] at saltSplit saltLow
  have nonce : s3ReadNat (s3LeafSecond state first) 72 24 = salt.toNat % 2 ^ 192 := by
    rw [nonceWords, saltNat, saltSplit, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt saltLow).symm
  -- the chaining bytes
  have chainWords : s3ReadNat (s3LeafSecond state first) 96 104 =
      s3ReadNat (s3LeafMiddle state first) 96 104 :=
    s3_read_nat_words (s3LeafSecond state first) (s3LeafMiddle state first) 96 96 13
      (by decide) (by decide) (by
        intro word small
        apply s3_leaf_second_outside
        · intro pair member
          exact s3_low_distinct _ _ (by omega) (s3_nonce_small pair member).2.2
            (by have := s3_nonce_destinations pair member; omega)
        · intro pair member
          exact s3_low_distinct _ _ (by omega) (s3_tail_small pair member).2.2
            (by have := s3_tail_destinations pair member; omega))
  have chainSlice : readBuffer (s3LeafMiddle state first) 96 104 =
      first.extractLsb' (8 * 96) (8 * 104) := by
    apply read_serialized_slice
    intro j inside
    rw [s3_leaf_middle_eq]
    exact s3_check_reply_byte _ first (96 + j) (by omega)
  have chain : s3ReadNat (s3LeafSecond state first) 96 104 = first.toNat / 2 ^ 768 := by
    have equal := congrArg BitVec.toNat chainSlice
    rw [s3_read_buffer_nat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at equal
    simp only [Nat.reduceMul] at equal
    rw [chainWords, equal]
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact first.isLt
  -- the value tail
  have tailWords : s3ReadNat (s3LeafSecond state first) 200 72 =
      s3ReadNat state (address + 184) 72 :=
    s3_read_nat_words (s3LeafSecond state first) state 200 (address + 184) 9 (by decide)
      (by omega) (by
        intro word small
        rw [s3_leaf_second_tail state address first pointer above bounded word small,
          s3_leaf_middle_eq, s3_reply_outside _ first _ (farWord (184 + 8 * word) (by omega)),
          s3_leaf_first_outside state _ (farWord (184 + 8 * word) (by omega)),
          Nat.add_assoc])
  have valueSplit := s3_read_nat_add state address 184 72
  have valueLow := s3_read_nat_bound state address 184
  simp only [Nat.reduceMul, Nat.reduceAdd] at valueSplit valueLow
  have tail : s3ReadNat (s3LeafSecond state first) 200 72 = value.toNat / 2 ^ 1472 := by
    rw [tailWords, ← valueNat, valueSplit,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 1472), Nat.div_eq_of_lt valueLow, Nat.zero_add]
  -- assembly
  have outer := s3_read_nat_add (s3LeafSecond state first) 72 24 176
  have inner := s3_read_nat_add (s3LeafSecond state first) 96 104 72
  simp only [Nat.reduceMul, Nat.reduceAdd] at outer inner
  have power : (2 : Nat) ^ 1024 = 2 ^ 192 * 2 ^ 832 := Nat.pow_add 2 192 832
  have natural : s3ReadNat (s3LeafSecond state first) 72 200 =
      salt.toNat % 2 ^ 192 + first.toNat / 2 ^ 768 * 2 ^ 192 +
        value.toNat / 2 ^ 1472 * 2 ^ 1024 := by
    rw [outer, inner, nonce, chain, tail, power]
    ring
  rw [s3_read_buffer, natural]
  rfl

/-- The digest slot receives the low 32 bytes of the second reply. -/
theorem s3_leaf_done_output (state : MachineState) (first second : BitVec 1600) :
    readBuffer (s3LeafDone state first second) 256 32 = BitVec.ofNat 256 second.toNat := by
  have copied : readBuffer (s3LeafDone state first second) 256 32 =
      readBuffer (s3LeafLast state first second) 0 32 :=
    (read_digest_eq_iff _ _ 256 0 (by decide) (by decide)).mpr (fun word small => by
      rw [s3_leaf_done_digest state first second word small, Nat.zero_add])
  have written := write_bits_digest (s3LeafSecond state first) 0 0 second (by decide)
    (by decide)
  rw [copied, s3_leaf_last_eq]
  apply BitVec.eq_of_toNat_eq
  have numeric := congrArg BitVec.toNat written
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    at numeric
  rw [numeric, BitVec.toNat_ofNat]

theorem cap_check_leaf_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (capCheckLeaf state)).1 =
      s3LeafDone state (oracle.permutation (readBuffer (s3LeafFirst state) 0 200))
        (oracle.permutation (readBuffer (s3LeafSecond state
          (oracle.permutation (readBuffer (s3LeafFirst state) 0 200))) 72 200)) := by
  unfold capCheckLeaf s3PermutationQuery
  erw [check_evaluation_public_bind]
  erw [check_evaluation_public_bind]
  erw [check_evaluation_pure]
  rfl

/-- The checking leaf leaves the stage-3 digest of the scratch salt and the
value at x8 in the scratch digest slot. Only the low 24 salt bytes matter. -/
theorem cap_check_leaf_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (salt : BitVec 256) (value : Entry)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (checkEvaluation oracle (capCheckLeaf state)).1 256 32 =
      s3LeafDigest oracle.permutation salt value := by
  have firstInput := s3_leaf_first_window state address value pointer aligned above bounded data
  have firstReply : oracle.permutation (readBuffer (s3LeafFirst state) 0 200) =
      oracle.permutation (s3First value) :=
    congrArg (fun input : BitVec PERMUTATION_WIDTH => oracle.permutation input) firstInput
  have chained : ∀ first : BitVec 1600, first = oracle.permutation (s3First value) →
      BitVec.ofNat 256 (oracle.permutation
        (readBuffer (s3LeafSecond state first) 72 200)).toNat =
        s3LeafDigest oracle.permutation salt value := by
    intro first equal
    subst equal
    have secondInput := s3_leaf_second_window state address salt value
      (oracle.permutation (s3First value)) pointer aligned above bounded initial data
    exact congrArg (fun input : BitVec PERMUTATION_WIDTH =>
      BitVec.ofNat 256 (oracle.permutation input).toNat) secondInput
  rw [cap_check_leaf_evaluation]
  exact (s3_leaf_done_output state _ _).trans (chained _ firstReply)

end CommitGolfCandidate
