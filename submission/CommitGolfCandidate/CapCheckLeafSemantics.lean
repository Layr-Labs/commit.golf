import CommitGolfCandidate.S3CheckLeafStates

/-! Fixed-oracle semantics of the stage-3 checker leaf: for the real
permutation the routine leaves `s3LeafDigest` of the scratch salt and the value
at x8 in the scratch digest slot. The first 200-byte input is the value read in
place, the second is identified with `s3Second` from the actual words written by
the routine. -/
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

/-- The first permutation input is `value[0..200)`, read in place. -/
theorem s3_leaf_first_window (state : MachineState) (address : Nat) (value : Entry)
    (aligned : address % 8 = 0)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (s3LeafFirst state) address 200 = s3First value := by
  have valueNat := s3_value_nat state address value data
  have copied : s3ReadNat (s3LeafFirst state) address 200 = s3ReadNat state address 200 :=
    s3_read_nat_words (s3LeafFirst state) state address address 25 aligned aligned
      (fun word _ => s3_leaf_first_memory state _)
  have valueSplit := s3_read_nat_add state address 200 56
  have low := s3_read_nat_bound state address 200
  simp only [Nat.reduceMul, Nat.reduceAdd] at valueSplit low
  have natural : s3ReadNat (s3LeafFirst state) address 200 = value.toNat % 2 ^ 1600 := by
    rw [copied, ← valueNat, valueSplit, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt low).symm
  rw [s3_read_buffer, natural]
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 1600 (value.toNat % 2 ^ 1600)).toNat = (BitVec.ofNat 1600 value.toNat).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_mod _ _

/-- The second permutation input is `reply[120..176) || nonce || value[136..256)`. -/
theorem s3_leaf_second_window (state : MachineState) (address : Nat) (salt : BitVec 256)
    (value : Entry) (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (s3LeafSecond state first) 0 200 = s3Second salt first value := by
  have valueNat := s3_value_nat state address value data
  have lowWord (source : Nat) (small : source < 288) (aligned : source % 8 = 0)
      (high : 200 ≤ source) : ∀ word < 25,
      BitVec.ofNat 64 source ≠ BitVec.ofNat 64 (8 * word) :=
    fun word inside => s3_low_distinct _ _ small (by omega) (by omega)
  have farWord (offset : Nat) (inside : offset < 256) : ∀ word < 25,
      BitVec.ofNat 64 (address + offset) ≠ BitVec.ofNat 64 (8 * word) :=
    fun word small => s3_far_word address offset (8 * word) above bounded inside (by omega)
  -- the chaining bytes
  have chainWords : s3ReadNat (s3LeafSecond state first) 0 56 =
      s3ReadNat (s3LeafMiddle state first) 120 56 :=
    s3_read_nat_words (s3LeafSecond state first) (s3LeafMiddle state first) 0 120 7
      (by decide) (by decide) (by
        intro word small
        rw [Nat.zero_add]
        exact s3_leaf_second_chain state first word small)
  have chainSlice : readBuffer (s3LeafMiddle state first) 120 56 =
      first.extractLsb' (8 * 120) (8 * 56) := by
    apply read_serialized_slice
    intro j inside
    rw [s3_leaf_middle_eq]
    exact s3_check_reply_byte _ first (120 + j) (by omega)
  have chain : s3ReadNat (s3LeafSecond state first) 0 56 =
      first.toNat / 2 ^ 960 % 2 ^ 448 := by
    have equal := congrArg BitVec.toNat chainSlice
    rw [s3_read_buffer_nat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at equal
    simp only [Nat.reduceMul] at equal
    rw [chainWords, equal]
  -- the nonce
  have nonceWords : s3ReadNat (s3LeafSecond state first) 56 24 = s3ReadNat state 256 24 :=
    s3_read_nat_words (s3LeafSecond state first) state 56 256 3 (by decide) (by decide) (by
      intro word small
      rw [s3_leaf_second_nonce state first word small, s3_leaf_middle_eq,
        s3_reply_outside _ first _ (lowWord (256 + 8 * word) (by omega) (by omega) (by omega)),
        s3_leaf_first_memory state _])
  have saltNat : salt.toNat = s3ReadNat state 256 32 := by
    rw [← initial, s3_read_buffer_nat]
  have saltSplit := s3_read_nat_add state 256 24 8
  have saltLow := s3_read_nat_bound state 256 24
  simp only [Nat.reduceMul, Nat.reduceAdd] at saltSplit saltLow
  have nonce : s3ReadNat (s3LeafSecond state first) 56 24 = salt.toNat % 2 ^ 192 := by
    rw [nonceWords, saltNat, saltSplit, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt saltLow).symm
  -- the value tail
  have tailWords : s3ReadNat (s3LeafSecond state first) 80 120 =
      s3ReadNat state (address + 136) 120 :=
    s3_read_nat_words (s3LeafSecond state first) state 80 (address + 136) 15 (by decide)
      (by omega) (by
        intro word small
        rw [s3_leaf_second_tail state address first pointer above bounded word small,
          s3_leaf_middle_eq, s3_reply_outside _ first _ (farWord (136 + 8 * word) (by omega)),
          s3_leaf_first_memory state _, Nat.add_assoc])
  have valueSplit := s3_read_nat_add state address 136 120
  have valueLow := s3_read_nat_bound state address 136
  simp only [Nat.reduceMul, Nat.reduceAdd] at valueSplit valueLow
  have tail : s3ReadNat (s3LeafSecond state first) 80 120 = value.toNat / 2 ^ 1088 := by
    rw [tailWords, ← valueNat, valueSplit,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 1088), Nat.div_eq_of_lt valueLow, Nat.zero_add]
  -- assembly
  have outer := s3_read_nat_add (s3LeafSecond state first) 0 56 144
  have inner := s3_read_nat_add (s3LeafSecond state first) 56 24 120
  simp only [Nat.reduceMul, Nat.reduceAdd] at outer inner
  have power : (2 : Nat) ^ 640 = 2 ^ 448 * 2 ^ 192 := Nat.pow_add 2 448 192
  have natural : s3ReadNat (s3LeafSecond state first) 0 200 =
      first.toNat / 2 ^ 960 % 2 ^ 448 + salt.toNat % 2 ^ 192 * 2 ^ 448 +
        value.toNat / 2 ^ 1088 * 2 ^ 640 := by
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
      s3LeafDone state
        (oracle.permutation (readBuffer (s3LeafFirst state) (state.getReg .x8).toNat 200))
        (oracle.permutation (readBuffer (s3LeafSecond state
          (oracle.permutation
            (readBuffer (s3LeafFirst state) (state.getReg .x8).toNat 200))) 0 200)) := by
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
  have located : (state.getReg .x8).toNat = address := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have firstInput := s3_leaf_first_window state address value aligned data
  have firstReply :
      oracle.permutation (readBuffer (s3LeafFirst state) (state.getReg .x8).toNat 200) =
      oracle.permutation (s3First value) := by
    rw [located]
    exact congrArg (fun input : BitVec PERMUTATION_WIDTH => oracle.permutation input) firstInput
  have chained : ∀ first : BitVec 1600, first = oracle.permutation (s3First value) →
      BitVec.ofNat 256 (oracle.permutation
        (readBuffer (s3LeafSecond state first) 0 200)).toNat =
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
