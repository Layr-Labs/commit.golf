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
theorem s3_tail_destinations : ∀ pair ∈ s3TailPairs, 232 ≤ pair.2 := by decide
theorem s3_nonce_destinations : ∀ pair ∈ s3NoncePairs, 88 ≤ pair.2 ∧ pair.2 < 112 := by decide

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

theorem s3_leaf_first_memory (state : MachineState) (query : Word) :
    (s3LeafFirst state).getMem query =
      (s3Run (s3Copy .x8 s3WindowPairs) state).getMem query := by
  unfold s3LeafFirst s3LeafBuild s3LeafWindow
  rw [s3_run_append]
  rfl

theorem s3_leaf_first_value (state : MachineState) (address : Nat)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 25, (s3LeafFirst state).getMem (BitVec.ofNat 64 (32 + 8 * word)) =
      state.getMem (BitVec.ofNat 64 (address + 8 * word)) := by
  intro word small
  have copied : (s3Run (s3Copy .x8 s3WindowPairs) state).getMem
        (BitVec.ofNat 64 (32 + 8 * word)) =
      state.getMem (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) :=
    s3_copy_memory_inside .x8 s3WindowPairs state (by decide) s3_window_small
      (by decide)
      (by
        intro source sourceMember destination destinationMember
        rw [pointer, ← BitVec.ofNat_add]
        exact s3_far_word address source.1 destination.2 above bounded
          (s3_window_sources source sourceMember)
          (by have := (s3_window_small destination destinationMember).2.2; omega))
      (8 * word, 32 + 8 * word) (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)
  rw [s3_leaf_first_memory, copied, pointer, ← BitVec.ofNat_add]

/-- The window copy writes only the words 32, 40, ..., 224. -/
theorem s3_leaf_first_outside (state : MachineState) (query : Word)
    (outside : ∀ word < 25, query ≠ BitVec.ofNat 64 (32 + 8 * word)) :
    (s3LeafFirst state).getMem query = state.getMem query := by
  rw [s3_leaf_first_memory]
  exact s3_copy_memory_outside .x8 s3WindowPairs state s3_window_small query (by
    intro pair member
    obtain ⟨word, small, rfl⟩ := List.mem_map.mp member
    exact outside word (List.mem_range.mp small))

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
    ∀ word < 3, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (88 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (256 + 8 * word)) := by
  intro word small
  have copied : (s3LeafNonced state first).getMem (BitVec.ofNat 64 (88 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (256 + 8 * word)) :=
    s3_copy_absolute s3NoncePairs (s3LeafMiddle state first) s3_nonce_small (by decide)
      (by decide) (256 + 8 * word, 88 + 8 * word)
      (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)
  rw [s3_leaf_second_memory, s3_copy_memory_outside .x8 s3TailPairs (s3LeafNonced state first)
      s3_tail_small (BitVec.ofNat 64 (88 + 8 * word)) (by
        intro pair member
        exact s3_low_distinct _ _ (by omega) (s3_tail_small pair member).2.2
          (by have := s3_tail_destinations pair member; omega)), copied]

theorem s3_leaf_second_tail (state : MachineState) (address : Nat) (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 7, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (232 + 8 * word)) =
      (s3LeafMiddle state first).getMem (BitVec.ofNat 64 (address + (200 + 8 * word))) := by
  intro word small
  have base : (s3LeafNonced state first).getReg .x8 = BitVec.ofNat 64 address := by
    rw [s3LeafNonced, s3_copy_register .x0 s3NoncePairs _ .x8 (by decide),
      s3_leaf_middle_register, s3_leaf_first_register state .x8 (by decide)]
    exact pointer
  have copied : (s3Run (s3Copy .x8 s3TailPairs) (s3LeafNonced state first)).getMem
        (BitVec.ofNat 64 (232 + 8 * word)) =
      (s3LeafNonced state first).getMem
        ((s3LeafNonced state first).getReg .x8 + BitVec.ofNat 64 (200 + 8 * word)) :=
    s3_copy_memory_inside .x8 s3TailPairs (s3LeafNonced state first) (by decide) s3_tail_small
      (by decide)
      (by
        intro source sourceMember destination destinationMember
        rw [base, ← BitVec.ofNat_add]
        exact s3_far_word address source.1 destination.2 above bounded
          (s3_tail_sources source sourceMember)
          (by have := (s3_tail_small destination destinationMember).2.2; omega))
      (200 + 8 * word, 232 + 8 * word)
      (List.mem_map.mpr ⟨word, List.mem_range.mpr small, rfl⟩)
  rw [s3_leaf_second_memory, copied, base, ← BitVec.ofNat_add]
  exact s3_copy_memory_outside .x0 s3NoncePairs (s3LeafMiddle state first) s3_nonce_small _ (by
    intro pair member
    exact s3_far_word address (200 + 8 * word) pair.2 above bounded (by omega)
      (by have := (s3_nonce_small pair member).2.2; omega))

theorem s3_leaf_second_outside (state : MachineState) (first : BitVec 1600) (query : Word)
    (nonce : ∀ pair ∈ s3NoncePairs, query ≠ BitVec.ofNat 64 pair.2)
    (tail : ∀ pair ∈ s3TailPairs, query ≠ BitVec.ofNat 64 pair.2) :
    (s3LeafSecond state first).getMem query = (s3LeafMiddle state first).getMem query := by
  rw [s3_leaf_second_memory, s3_copy_memory_outside .x8 s3TailPairs (s3LeafNonced state first)
    s3_tail_small query tail]
  exact s3_copy_memory_outside .x0 s3NoncePairs (s3LeafMiddle state first) s3_nonce_small
    query nonce

/-- At the second call the words 200, 208, ..., 280 hold value bytes 168..256:
words 21..24 of the first window survive the reply, the rest is the tail copy. -/
theorem s3_leaf_second_value (state : MachineState) (address : Nat) (first : BitVec 1600)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64) :
    ∀ word < 11, (s3LeafSecond state first).getMem (BitVec.ofNat 64 (200 + 8 * word)) =
      state.getMem (BitVec.ofNat 64 (address + 168 + 8 * word)) := by
  intro word small
  by_cases window : word < 4
  · have low : ∀ k < 25, BitVec.ofNat 64 (200 + 8 * word) ≠ BitVec.ofNat 64 (8 * k) :=
      fun k inside => s3_low_distinct _ _ (by omega) (by omega) (by omega)
    rw [s3_leaf_second_outside state first (BitVec.ofNat 64 (200 + 8 * word))
        (by
          intro pair member
          exact s3_low_distinct _ _ (by omega) (s3_nonce_small pair member).2.2
            (by have := s3_nonce_destinations pair member; omega))
        (by
          intro pair member
          exact s3_low_distinct _ _ (by omega) (s3_tail_small pair member).2.2
            (by have := s3_tail_destinations pair member; omega)),
      s3_leaf_middle_eq, s3_reply_outside _ first _ low,
      show 200 + 8 * word = 32 + 8 * (21 + word) by omega,
      s3_leaf_first_value state address pointer above bounded (21 + word) (by omega),
      show address + 8 * (21 + word) = address + 168 + 8 * word by omega]
  · have far : ∀ k < 25, BitVec.ofNat 64 (address + (200 + 8 * (word - 4))) ≠
        BitVec.ofNat 64 (8 * k) :=
      fun k inside => s3_far_word address _ (8 * k) above bounded (by omega) (by omega)
    have farWindow : ∀ k < 25, BitVec.ofNat 64 (address + (200 + 8 * (word - 4))) ≠
        BitVec.ofNat 64 (32 + 8 * k) :=
      fun k inside => s3_far_word address _ (32 + 8 * k) above bounded (by omega) (by omega)
    rw [show 200 + 8 * word = 232 + 8 * (word - 4) by omega,
      s3_leaf_second_tail state address first pointer above bounded (word - 4) (by omega),
      s3_leaf_middle_eq, s3_reply_outside _ first _ far, s3_leaf_first_outside state _ farWindow,
      show address + (200 + 8 * (word - 4)) = address + 168 + 8 * word by omega]

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
  rw [s3_run_append, show [Instr.ADDI .x8 .x8 256, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0] =
      [Instr.ADDI .x8 .x8 256] ++ [.ADDI .x0 .x0 0] ++ [.ADDI .x0 .x0 0] from rfl,
    s3_run_append, s3_run_append, s3_addi_memory, s3_addi_memory, s3_addi_memory]
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
