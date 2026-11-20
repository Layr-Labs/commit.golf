import CommitGolfCandidate.Model
import CommitGolfCandidate.Memory
import CommitGolfCandidate.CommitLeaf
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory

/-! Refinement of the machine's salted leaf hash to the reference computation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

set_option maxHeartbeats 2000000 in
/-- Word-level effect of copying a message block into the upper scratch half.
The source is disjoint from scratch, so earlier stores cannot affect later loads. -/
theorem check_leaf_copy_word (state : MachineState) (word : Nat) (bounded : word < 4)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    (checkLeafCopyState state).getMem (BitVec.ofNat 64 (288+8*word)) =
      state.getMem (state.getReg .x8 + BitVec.ofNat 64 (8*word)) := by
  change (([.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
    .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56] : List Instr).foldl
      execInstrBr state).getMem _ = _
  have disjoint : ∀ i : Fin 4, ∀ j : Fin 4,
      state.getReg .x8 + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (288+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
    BitVec.add_zero] at disjoint
  simp only [List.foldl, execInstrBr, signExtend12]
  interval_cases word <;>
    simp [register_set_mem, scratch, disjoint, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]


/-- Copying the message block leaves every word outside upper scratch untouched. -/
theorem check_leaf_copy_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : address ≠ 288 ∧ address ≠ 296 ∧ address ≠ 304 ∧ address ≠ 312) :
    (checkLeafCopyState state).getMem address = state.getMem address := by
  change (([.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
    .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56] : List Instr).foldl
      execInstrBr state).getMem address = _
  change address ≠ 288#64 ∧ address ≠ 296#64 ∧ address ≠ 304#64 ∧ address ≠ 312#64 at outside
  simp only [List.foldl, execInstrBr, signExtend12]
  simp [register_set_mem, scratch, outside, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

/-- Exact compression input: the old digest is the low half, the next message
block is the high half, matching `combine` in the reference model. -/
theorem check_leaf_input (state : MachineState)
    (scratch : state.getReg .x21 = 256)
    (aligned : (state.getReg .x8).toNat % 8 = 0)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    readBuffer (checkLeafCopyState state) 256 64 =
      readBuffer state (state.getReg .x8).toNat 32 ++ readBuffer state 256 32 := by
  rw [read_compression_halves _ _ (by decide)]
  have low : readBuffer (checkLeafCopyState state) 256 32 = readBuffer state 256 32 := by
    apply read_digest_congr _ _ _ (by decide)
    intro i hi
    apply check_leaf_copy_outside _ _ scratch
    interval_cases i <;> decide
  rw [low, read_digest_words _ _ (by decide), read_digest_words _ _ aligned]
  have words (i : Nat) (hi : i < 4) := check_leaf_copy_word state i hi scratch separated
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The loop latch changes only registers and the PC after writing the reply. -/
theorem check_leaf_step_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkLeafStepState state answer) 256 32 = answer := by
  change readBuffer (checkCompressionState (checkLeafCopyState state) answer) 256 32 = answer
  exact check_compression_digest _ _

/-- Each leaf iteration preserves all memory outside the 64-byte scratch region. -/
theorem check_leaf_step_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (checkLeafStepState state answer).getMem address = state.getMem address := by
  change (checkCompressionState (checkLeafCopyState state) answer).getMem address = _
  rw [check_compression_memory_outside]
  · apply check_leaf_copy_outside _ _ scratch
    exact ⟨outside 4 (by decide), outside 5 (by decide), outside 6 (by decide), outside 7 (by decide)⟩
  · exact ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩

/-- Commit and check use the identical leaf copy operation. The compression call site
now writes the answer directly because its arguments are hoisted out of the loop. -/
theorem commit_leaf_copy_eq_check (state : MachineState) :
    commitLeafCopyState state = checkLeafCopyState state := rfl

theorem commit_compression_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280 ∧
      address ≠ 288 ∧ address ≠ 296 ∧ address ≠ 304 ∧ address ≠ 312) :
    (commitCompressionState state answer).getMem address = state.getMem address := by
  unfold commitCompressionState
  rw [writeBits_memory_outside]
  intro i hi
  change i < 32 at hi
  interval_cases i <;> norm_num [alignToDword] <;> tauto

theorem commit_leaf_step_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (commitLeafStepState state answer) 256 32 = answer := by
  change readBuffer (commitCompressionState (commitLeafCopyState state) answer) 256 32 = answer
  unfold commitCompressionState
  simpa using (write_bits_digest (commitLeafCopyState state) 256 0 answer
    (by decide) (by decide))

/-- Commitment uses the same input block ordering as checking. -/
theorem commit_leaf_input (state : MachineState)
    (scratch : state.getReg .x21 = 256)
    (aligned : (state.getReg .x8).toNat % 8 = 0)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    readBuffer (commitLeafCopyState state) 256 64 =
      readBuffer state (state.getReg .x8).toNat 32 ++ readBuffer state 256 32 := by
  rw [commit_leaf_copy_eq_check]
  exact check_leaf_input state scratch aligned separated

theorem commit_leaf_step_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (commitLeafStepState state answer).getMem address = state.getMem address := by
  change (commitCompressionState (commitLeafCopyState state) answer).getMem address =
    state.getMem address
  rw [commit_compression_memory_outside]
  · apply check_leaf_copy_outside _ _ scratch
    exact ⟨outside 4 (by decide), outside 5 (by decide), outside 6 (by decide), outside 7 (by decide)⟩
  · exact ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide),
      outside 4 (by decide), outside 5 (by decide), outside 6 (by decide), outside 7 (by decide)⟩

/-- The checker leaf loop computes the reference fold over the message blocks.
The source region lies above scratch, stays aligned, and does not wrap. -/
theorem check_leaf_loop_digest (oracle : Oracle) (state : MachineState)
    (address count : Nat) (blocks : Nat → Digest)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * count < 2^64)
    (data : ∀ i < count, readBuffer state (address + 32*i) 32 = blocks i) :
    readBuffer (checkEvaluation oracle (checkLeafLoop state count)).1 256 32 =
      (List.range count).foldl
        (fun digest i => combine oracle.compression digest (blocks i)) (readBuffer state 256 32) := by
  induction count generalizing state address blocks with
  | zero => simp [checkLeafLoop, check_evaluation_pure]
  | succ count ih =>
    have pointerNat : (state.getReg .x8).toNat = address := by
      rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have separated : ∀ i < 4, ∀ j < 4,
        state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j) := by
      intro i hi j hj equal
      have natural := congrArg BitVec.toNat equal
      rw [pointer, ← BitVec.ofNat_add] at natural
      simp only [BitVec.toNat_ofNat] at natural
      rw [Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
        Nat.mod_eq_of_lt (by omega : 288+8*j < 2^64)] at natural
      omega
    have input := check_leaf_input state scratch (by simpa [pointerNat] using aligned) separated
    rw [pointerNat, show address = address + 32*0 by omega, data 0 (by omega)] at input
    let answer := combine oracle.compression (readBuffer state 256 32) (blocks 0)
    let next := checkLeafStepState state answer
    have registers := check_leaf_block_registers state answer
    have nextScratch : next.getReg .x21 = 256 := registers.2.2.1.trans scratch
    have nextPointer : next.getReg .x8 = BitVec.ofNat 64 (address + 32) := by
      rw [show next.getReg .x8 = state.getReg .x8 + 32 from registers.1, pointer]
      rw [BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < count) :
        readBuffer next (address + 32 + 32*i) 32 = blocks (i+1) := by
      have memory : readBuffer next (address + 32 + 32*i) 32 =
          readBuffer state (address + 32 + 32*i) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro word hw
        apply check_leaf_step_outside _ _ _ scratch
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by omega : address + 32 + 32*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 32 + 32*i = address + 32*(i+1) by omega]
      exact data (i+1) (by omega)
    have induction := ih next (address+32) (fun i => blocks (i+1)) nextScratch nextPointer
      (by omega) (by omega) (by omega) nextData
    rw [checkLeafLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (checkLeafLoop
      (checkLeafStepState state (oracle.compression (readBuffer (checkLeafCopyState state) 256 64)))
      count)).1 256 32 = _
    rw [input]
    change readBuffer (checkEvaluation oracle (checkLeafLoop next count)).1 256 32 = _
    rw [induction, check_leaf_step_digest]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
      Nat.succ_eq_add_one]
    rfl

/-- The commitment leaf loop computes the reference fold over the message blocks.
The source region lies above scratch, stays aligned, and does not wrap. -/
theorem commit_leaf_loop_digest (oracle : Oracle) (state : MachineState)
    (address count : Nat) (blocks : Nat → Digest)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * count < 2^64)
    (data : ∀ i < count, readBuffer state (address + 32*i) 32 = blocks i) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state count)).1 256 32 =
      (List.range count).foldl
        (fun digest i => combine oracle.compression digest (blocks i)) (readBuffer state 256 32) := by
  induction count generalizing state address blocks with
  | zero => simp [commitLeafLoop, check_evaluation_pure]
  | succ count ih =>
    have pointerNat : (state.getReg .x8).toNat = address := by
      rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have separated : ∀ i < 4, ∀ j < 4,
        state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j) := by
      intro i hi j hj equal
      have natural := congrArg BitVec.toNat equal
      rw [pointer, ← BitVec.ofNat_add] at natural
      simp only [BitVec.toNat_ofNat] at natural
      rw [Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
        Nat.mod_eq_of_lt (by omega : 288+8*j < 2^64)] at natural
      omega
    have input := commit_leaf_input state scratch (by simpa [pointerNat] using aligned) separated
    rw [pointerNat, show address = address + 32*0 by omega, data 0 (by omega)] at input
    let answer := combine oracle.compression (readBuffer state 256 32) (blocks 0)
    let next := commitLeafStepState state answer
    have registers := commit_leaf_block_registers state answer
    have nextScratch : next.getReg .x21 = 256 := registers.2.2.1.trans scratch
    have nextPointer : next.getReg .x8 = BitVec.ofNat 64 (address + 32) := by
      rw [show next.getReg .x8 = state.getReg .x8 + 32 from registers.1, pointer]
      rw [BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < count) :
        readBuffer next (address + 32 + 32*i) 32 = blocks (i+1) := by
      have memory : readBuffer next (address + 32 + 32*i) 32 =
          readBuffer state (address + 32 + 32*i) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro word hw
        apply commit_leaf_step_outside _ _ _ scratch
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by omega : address + 32 + 32*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 32 + 32*i = address + 32*(i+1) by omega]
      exact data (i+1) (by omega)
    have induction := ih next (address+32) (fun i => blocks (i+1)) nextScratch nextPointer
      (by omega) (by omega) (by omega) nextData
    rw [commitLeafLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (commitLeafLoop
      (commitLeafStepState state (oracle.compression (readBuffer (commitLeafCopyState state) 256 64)))
      count)).1 256 32 = _
    rw [input]
    change readBuffer (checkEvaluation oracle (commitLeafLoop next count)).1 256 32 = _
    rw [induction, commit_leaf_step_digest]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
      Nat.succ_eq_add_one]
    rfl

/-- Leaf hashing preserves every memory word outside scratch. -/
theorem check_leaf_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkLeafLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, check_evaluation_pure]
  | succ count ih =>
    rw [checkLeafLoop, check_evaluation_public_bind]
    let answer := oracle.compression (readBuffer (checkLeafCopyState state) 256 64)
    change (checkEvaluation oracle (checkLeafLoop (checkLeafStepState state answer) count)).1.getMem address = _
    rw [ih _ ((check_leaf_block_registers state answer).2.2.1.trans scratch)]
    exact check_leaf_step_outside state answer address scratch outside

/-- Commitment leaf hashing preserves every memory word outside scratch. -/
theorem commit_leaf_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (commitLeafLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [commitLeafLoop, check_evaluation_pure]
  | succ count ih =>
    rw [commitLeafLoop, check_evaluation_public_bind]
    let answer := oracle.compression (readBuffer (commitLeafCopyState state) 256 64)
    change (checkEvaluation oracle (commitLeafLoop (commitLeafStepState state answer) count)).1.getMem address = _
    rw [ih _ ((commit_leaf_block_registers state answer).2.2.1.trans scratch)]
    exact commit_leaf_step_outside state answer address scratch outside

/-- The full checker leaf subroutine hashes exactly the eight message blocks
starting from the supplied salt, as defined by `leafDigest`. -/
theorem check_leaf_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (salt : Digest) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (checkEvaluation oracle (checkLeafLoop state 8)).1 256 32 =
      leafDigest oracle.compression salt value := by
  rw [check_leaf_loop_digest oracle state address 8 _ scratch pointer aligned above bounded data, initial]
  rfl

/-- Commitment and checking compute the same salted leaf digest from their
respective machine loops. No cryptographic assumption is used for this equality. -/
theorem commit_leaf_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (salt : Digest) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state 8)).1 256 32 =
      leafDigest oracle.compression salt value := by
  rw [commit_leaf_loop_digest oracle state address 8 _ scratch pointer aligned above bounded data, initial]
  rfl

end CommitGolfCandidate
