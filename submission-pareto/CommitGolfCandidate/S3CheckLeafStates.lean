import CommitGolfCandidate.S3CheckLeafMemory

/-! Word-level memory of the stage-3 checker leaf at each of its five program
points, for arbitrary permutation replies. The value buffer only has to lie
above the 320-byte low workspace. -/
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

theorem s3_window_small : S3Small s3WindowPairs := by decide
theorem s3_nonce_small : S3Small s3NoncePairs := by decide
theorem s3_tail_small : S3Small s3TailPairs := by decide
theorem s3_output_small : S3Small s3OutputPairs := by decide
theorem s3_window_sources : ∀ pair ∈ s3WindowPairs, pair.1 < 256 := by decide
theorem s3_tail_sources : ∀ pair ∈ s3TailPairs, pair.1 < 256 := by decide
theorem s3_tail_destinations : ∀ pair ∈ s3TailPairs, 200 ≤ pair.2 := by decide
theorem s3_nonce_destinations : ∀ pair ∈ s3NoncePairs, pair.2 < 96 := by decide

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

theorem s3_addi_memory (rd rs : Reg) (immediate : BitVec 12) (state : MachineState)
    (query : Word) :
    (s3Run [.ADDI rd rs immediate] state).getMem query = state.getMem query := by
  simp only [s3Run, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getMem_setPC,
    MachineState.getMem_setReg]

/-! ### The first window -/

def s3LeafZeroed (state : MachineState) : MachineState :=
  s3Run [.SD .x0 .x0 0, .SD .x0 .x0 8] state

theorem s3_zeroed_memory (state : MachineState) (query : Word) :
    (s3LeafZeroed state).getMem query =
      if query = BitVec.ofNat 64 8 then 0#64
      else if query = BitVec.ofNat 64 0 then 0#64 else state.getMem query := by
  simp only [s3LeafZeroed, s3Run, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getMem_setPC, s3_store_memory, MachineState.getReg_setPC, s3_store_register,
    s3_zero_register, BitVec.zero_add,
    show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from rfl,
    show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 from rfl]

theorem s3_zeroed_register (state : MachineState) (reg : Reg) :
    (s3LeafZeroed state).getReg reg = state.getReg reg := by
  simp only [s3LeafZeroed, s3Run, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, s3_store_register]

theorem s3_leaf_first_memory (state : MachineState) (query : Word) :
    (s3LeafFirst state).getMem query =
      (s3Run (s3Copy .x8 s3WindowPairs) (s3LeafZeroed state)).getMem query := by
  unfold s3LeafFirst s3LeafBuild s3LeafWindow
  rw [s3_run_append, s3_run_append]
  rfl

theorem s3_leaf_first_zero (state : MachineState) :
    (s3LeafFirst state).getMem (BitVec.ofNat 64 0) = 0#64 ∧
    (s3LeafFirst state).getMem (BitVec.ofNat 64 8) = 0#64 := by
  constructor
  · rw [s3_leaf_first_memory, s3_copy_memory_outside .x8 s3WindowPairs (s3LeafZeroed state)
        s3_window_small (BitVec.ofNat 64 0) (by decide), s3_zeroed_memory,
      if_neg (by decide), if_pos rfl]
  · rw [s3_leaf_first_memory, s3_copy_memory_outside .x8 s3WindowPairs (s3LeafZeroed state)
        s3_window_small (BitVec.ofNat 64 8) (by decide), s3_zeroed_memory, if_pos rfl]

theorem s3_leaf_first_value (state : MachineState) (address : Nat)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 23, (s3LeafFirst state).getMem (BitVec.ofNat 64 (16 + 8 * word)) =
      state.getMem (BitVec.ofNat 64 (address + 8 * word)) := by
  intro word small
  have base : (s3LeafZeroed state).getReg .x8 = BitVec.ofNat 64 address :=
    (s3_zeroed_register state .x8).trans pointer
  have copied : (s3Run (s3Copy .x8 s3WindowPairs) (s3LeafZeroed state)).getMem
        (BitVec.ofNat 64 (16 + 8 * word)) =
      (s3LeafZeroed state).getMem
        ((s3LeafZeroed state).getReg .x8 + BitVec.ofNat 64 (8 * word)) :=
    s3_copy_memory_inside .x8 s3WindowPairs (s3LeafZeroed state) (by decide) s3_window_small
      (by decide)
      (by
        intro source sourceMember destination destinationMember
        rw [base, ← BitVec.ofNat_add]
        exact s3_far_word address source.1 destination.2 above bounded
          (s3_window_sources source sourceMember)
          (by have := (s3_window_small destination destinationMember).2.2; omega))
      (8 * word, 16 + 8 * word) (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)
  rw [s3_leaf_first_memory, copied, base, ← BitVec.ofNat_add, s3_zeroed_memory,
    if_neg (s3_far_word address (8 * word) 8 above bounded (by omega) (by omega)),
    if_neg (s3_far_word address (8 * word) 0 above bounded (by omega) (by omega))]

theorem s3_leaf_first_outside (state : MachineState) (query : Word)
    (outside : ∀ word < 25, query ≠ BitVec.ofNat 64 (8 * word)) :
    (s3LeafFirst state).getMem query = state.getMem query := by
  rw [s3_leaf_first_memory, s3_copy_memory_outside .x8 s3WindowPairs (s3LeafZeroed state)
      s3_window_small query (by
        intro pair member
        obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
        have distinct := outside (word + 2) (by have := List.mem_range.mp small; omega)
        rw [show 8 * (word + 2) = 16 + 8 * word by omega] at distinct
        exact distinct),
    s3_zeroed_memory,
    if_neg (show query ≠ BitVec.ofNat 64 8 from outside 1 (by decide)),
    if_neg (show query ≠ BitVec.ofNat 64 0 from outside 0 (by decide))]

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

/-! ### The second window -/

def s3LeafNonced (state : MachineState) (first : BitVec 1600) : MachineState :=
  s3Run (s3Copy .x0 s3NoncePairs) (s3LeafMiddle state first)

theorem s3_leaf_second_memory (state : MachineState) (first : BitVec 1600) (query : Word) :
    (s3LeafSecond state first).getMem query =
      (s3Run (s3Copy .x8 s3TailPairs) (s3LeafNonced state first)).getMem query := by
  unfold s3LeafSecond s3LeafChain
  rw [s3_run_append, s3_run_append, s3_addi_memory]
  unfold s3CheckLeafTail s3LeafNonce s3LeafNonced
  rfl

theorem s3_leaf_second_nonce (state : MachineState) (first : BitVec 1600) :
    ∀ word < 3, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (72 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (256 + 8 * word)) := by
  intro word small
  have copied : (s3LeafNonced state first).getMem (BitVec.ofNat 64 (72 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (256 + 8 * word)) :=
    s3_copy_absolute s3NoncePairs (s3LeafMiddle state first) s3_nonce_small (by decide)
      (by decide) (256 + 8 * word, 72 + 8 * word)
      (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)
  rw [s3_leaf_second_memory, s3_copy_memory_outside .x8 s3TailPairs (s3LeafNonced state first)
      s3_tail_small (BitVec.ofNat 64 (72 + 8 * word)) (by
        intro pair member
        exact s3_low_distinct _ _ (by omega) (s3_tail_small pair member).2.2
          (by have := s3_tail_destinations pair member; omega)), copied]

theorem s3_leaf_second_tail (state : MachineState) (address : Nat) (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 9, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (200 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (address + (184 + 8 * word))) := by
  intro word small
  have base : (s3LeafNonced state first).getReg .x8 = BitVec.ofNat 64 address := by
    rw [s3LeafNonced, s3_copy_register .x0 s3NoncePairs _ .x8 (by decide),
      s3_leaf_middle_register, s3_leaf_first_register state .x8 (by decide)]
    exact pointer
  have copied : (s3Run (s3Copy .x8 s3TailPairs) (s3LeafNonced state first)).getMem
        (BitVec.ofNat 64 (200 + 8 * word)) =
      (s3LeafNonced state first).getMem
        ((s3LeafNonced state first).getReg .x8 + BitVec.ofNat 64 (184 + 8 * word)) :=
    s3_copy_memory_inside .x8 s3TailPairs (s3LeafNonced state first) (by decide) s3_tail_small
      (by decide)
      (by
        intro source sourceMember destination destinationMember
        rw [base, ← BitVec.ofNat_add]
        exact s3_far_word address source.1 destination.2 above bounded
          (s3_tail_sources source sourceMember)
          (by have := (s3_tail_small destination destinationMember).2.2; omega))
      (184 + 8 * word, 200 + 8 * word)
      (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)
  rw [s3_leaf_second_memory, copied, base, ← BitVec.ofNat_add]
  exact s3_copy_memory_outside .x0 s3NoncePairs (s3LeafMiddle state first) s3_nonce_small _ (by
    intro pair member
    exact s3_far_word address (184 + 8 * word) pair.2 above bounded (by omega)
      (by have := (s3_nonce_small pair member).2.2; omega))

theorem s3_leaf_second_outside (state : MachineState) (first : BitVec 1600) (query : Word)
    (nonce : ∀ pair ∈ s3NoncePairs, query ≠ BitVec.ofNat 64 pair.2)
    (tail : ∀ pair ∈ s3TailPairs, query ≠ BitVec.ofNat 64 pair.2) :
    (s3LeafSecond state first).getMem query = (s3LeafMiddle state first).getMem query := by
  rw [s3_leaf_second_memory, s3_copy_memory_outside .x8 s3TailPairs (s3LeafNonced state first)
    s3_tail_small query tail]
  exact s3_copy_memory_outside .x0 s3NoncePairs (s3LeafMiddle state first) s3_nonce_small
    query nonce

/-! ### The digest copy -/

theorem s3_leaf_last_eq (state : MachineState) (first second : BitVec 1600) :
    s3LeafLast state first second =
      writeBits (s3LeafSecond state first) (BitVec.ofNat 64 0) second :=
  congrArg (fun address => writeBits (s3LeafSecond state first) address second)
    ((s3_leaf_second_register state first .x12 (by decide)).trans
      (s3_leaf_first_selectors state).2.2.2.1)

theorem s3_leaf_done_memory (state : MachineState) (first second : BitVec 1600)
    (query : Word) :
    (s3LeafDone state first second).getMem query =
      (s3Run (s3Copy .x0 s3OutputPairs) (s3LeafLast state first second)).getMem query := by
  unfold s3LeafDone s3LeafFinish
  rw [s3_run_append, s3_addi_memory]
  unfold s3LeafOutput
  rfl

theorem s3_leaf_done_digest (state : MachineState) (first second : BitVec 1600) :
    ∀ word < 4, (s3LeafDone state first second).getMem (BitVec.ofNat 64 (256 + 8 * word)) =
      (s3LeafLast state first second).getMem (BitVec.ofNat 64 (8 * word)) := by
  intro word small
  rw [s3_leaf_done_memory]
  exact s3_copy_absolute s3OutputPairs _ s3_output_small (by decide) (by decide)
    (8 * word, 256 + 8 * word) (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)

theorem s3_leaf_done_outside (state : MachineState) (first second : BitVec 1600)
    (query : Word) (outside : ∀ pair ∈ s3OutputPairs, query ≠ BitVec.ofNat 64 pair.2) :
    (s3LeafDone state first second).getMem query =
      (s3LeafLast state first second).getMem query := by
  rw [s3_leaf_done_memory]
  exact s3_copy_memory_outside .x0 s3OutputPairs _ s3_output_small query outside

end CommitGolfCandidate
