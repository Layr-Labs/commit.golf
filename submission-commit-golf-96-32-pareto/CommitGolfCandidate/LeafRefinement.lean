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

set_option maxHeartbeats 4000000 in
/-- Word-level effect of copying a 64-byte message block behind the chaining value.
The source is disjoint from scratch, so earlier stores cannot affect later loads. -/
theorem check_leaf_copy_word (state : MachineState) (word : Nat) (bounded : word < 8)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 8, ∀ j < 8,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    (checkLeafCopyState state).getMem (BitVec.ofNat 64 (288+8*word)) =
      state.getMem (state.getReg .x8 + BitVec.ofNat 64 (8*word)) := by
  rw [check_leaf_copy_expansion]
  have disjoint : ∀ i : Fin 8, ∀ j : Fin 8,
      state.getReg .x8 + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (288+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
    BitVec.add_zero] at disjoint
  simp only [List.foldl, execInstrBr, signExtend12]
  interval_cases word <;>
    simp [register_set_mem, scratch, disjoint, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]

/-- Copying the message block leaves every word outside the block area of scratch untouched. -/
theorem check_leaf_copy_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ j < 8, address ≠ BitVec.ofNat 64 (288+8*j)) :
    (checkLeafCopyState state).getMem address = state.getMem address := by
  rw [check_leaf_copy_expansion]
  have o0 := outside 0 (by decide)
  have o1 := outside 1 (by decide)
  have o2 := outside 2 (by decide)
  have o3 := outside 3 (by decide)
  have o4 := outside 4 (by decide)
  have o5 := outside 5 (by decide)
  have o6 := outside 6 (by decide)
  have o7 := outside 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at o0 o1 o2 o3 o4 o5 o6 o7
  change address ≠ 288#64 at o0
  change address ≠ 296#64 at o1
  change address ≠ 304#64 at o2
  change address ≠ 312#64 at o3
  change address ≠ 320#64 at o4
  change address ≠ 328#64 at o5
  change address ≠ 336#64 at o6
  change address ≠ 344#64 at o7
  simp only [List.foldl, execInstrBr, signExtend12]
  simp [register_set_mem, scratch, o0, o1, o2, o3, o4, o5, o6, o7, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

/-- 64-byte reads depend only on their eight words. -/
theorem read_block_eq_of_words (left right : MachineState) (leftAddress rightAddress : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0)
    (words : ∀ word < 8, left.getMem (BitVec.ofNat 64 (leftAddress+8*word)) =
      right.getMem (BitVec.ofNat 64 (rightAddress+8*word))) :
    readBuffer left leftAddress 64 = readBuffer right rightAddress 64 := by
  rw [read_compression_halves _ _ leftAligned, read_compression_halves _ _ rightAligned]
  have low : readBuffer left leftAddress 32 = readBuffer right rightAddress 32 :=
    (read_digest_eq_iff _ _ _ _ leftAligned rightAligned).mpr
      (fun word bounded => words word (by omega))
  have high : readBuffer left (leftAddress+32) 32 = readBuffer right (rightAddress+32) 32 :=
    (read_digest_eq_iff _ _ _ _ (by omega) (by omega)).mpr (fun word bounded => by
      have := words (word+4) (by omega)
      rw [show leftAddress + 8 * (word + 4) = leftAddress + 32 + 8*word by omega,
        show rightAddress + 8 * (word + 4) = rightAddress + 32 + 8*word by omega] at this
      exact this)
  rw [low, high]

set_option maxHeartbeats 1600000 in
/-- Exact compression input: the old digest is the low 256 bits, the next 64-byte
message block the high 512 bits, matching `absorb` in the reference model. -/
theorem check_leaf_input (state : MachineState)
    (scratch : state.getReg .x21 = 256)
    (aligned : (state.getReg .x8).toNat % 8 = 0)
    (separated : ∀ i < 8, ∀ j < 8,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    leafQuery (checkLeafCopyState state) =
      leafInput (readBuffer state 256 32) (readBuffer state (state.getReg .x8).toNat 64) := by
  unfold leafQuery leafInput
  rw [read_leaf_query]
  have low : readBuffer (checkLeafCopyState state) 256 32 = readBuffer state 256 32 := by
    apply read_digest_congr _ _ _ (by decide)
    intro i hi
    apply check_leaf_copy_outside _ _ scratch
    intro j hj
    interval_cases i <;> interval_cases j <;> decide
  have high : readBuffer (checkLeafCopyState state) (256+32) 64 =
      readBuffer state (state.getReg .x8).toNat 64 := by
    apply read_block_eq_of_words _ _ _ _ (by decide) aligned
    intro word bounded
    rw [show 256 + 32 + 8*word = 288 + 8*word by omega,
      check_leaf_copy_word state word bounded scratch separated]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [low, high]

/-- The loop latch changes only registers and the PC after writing the reply. -/
theorem check_leaf_step_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkLeafStepState state answer) 256 32 = answer := by
  change readBuffer (checkLeafCompressionState (checkLeafCopyState state) answer) 256 32 = answer
  unfold checkLeafCompressionState
  exact (write_bits_digest _ 256 0 answer (by decide) (by decide)).trans (by simp)

/-- Each leaf iteration preserves all memory outside the 96-byte scratch region. -/
theorem check_leaf_step_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (checkLeafStepState state answer).getMem address = state.getMem address := by
  change (checkLeafCompressionState (checkLeafCopyState state) answer).getMem address = _
  rw [check_leaf_compression_memory_outside]
  · apply check_leaf_copy_outside _ _ scratch
    intro j hj
    have := outside (j+4) (by omega)
    rwa [show 256 + 8*(j+4) = 288 + 8*j by omega] at this
  · exact ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩

/-- The checker leaf loop computes the reference fold over the message blocks.
The source region lies above scratch, stays aligned, and does not wrap. -/
theorem check_leaf_loop_digest (oracle : Oracle) (state : MachineState)
    (address count : Nat) (blocks : Nat → LeafBlock)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 352 ≤ address)
    (bounded : address + 64 * count < 2^64)
    (data : ∀ i < count, readBuffer state (address + 64*i) 64 = blocks i) :
    readBuffer (checkEvaluation oracle (checkLeafLoop state count)).1 256 32 =
      (List.range count).foldl
        (fun digest i => absorb oracle.compression digest (blocks i)) (readBuffer state 256 32) := by
  induction count generalizing state address blocks with
  | zero => simp [checkLeafLoop, check_evaluation_pure]
  | succ count ih =>
    have pointerNat : (state.getReg .x8).toNat = address := by
      rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have separated : ∀ i < 8, ∀ j < 8,
        state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j) := by
      intro i hi j hj equal
      have natural := congrArg BitVec.toNat equal
      rw [pointer, ← BitVec.ofNat_add] at natural
      simp only [BitVec.toNat_ofNat] at natural
      rw [Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
        Nat.mod_eq_of_lt (by omega : 288+8*j < 2^64)] at natural
      omega
    have input := check_leaf_input state scratch (by simpa [pointerNat] using aligned) separated
    rw [pointerNat, show address = address + 64*0 by omega, data 0 (by omega)] at input
    let answer := absorb oracle.compression (readBuffer state 256 32) (blocks 0)
    let next := checkLeafStepState state answer
    have registers := check_leaf_block_registers state answer
    have nextScratch : next.getReg .x21 = 256 := registers.2.2.1.trans scratch
    have nextPointer : next.getReg .x8 = BitVec.ofNat 64 (address + 64) := by
      rw [show next.getReg .x8 = state.getReg .x8 + 64 from registers.1, pointer]
      rw [BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < count) :
        readBuffer next (address + 64 + 64*i) 64 = blocks (i+1) := by
      have memory : readBuffer next (address + 64 + 64*i) 64 =
          readBuffer state (address + 64 + 64*i) 64 := by
        apply read_block_eq_of_words _ _ _ _ (by omega) (by omega)
        intro word hw
        apply check_leaf_step_outside _ _ _ scratch
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by omega : address + 64 + 64*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 64 + 64*i = address + 64*(i+1) by omega]
      exact data (i+1) (by omega)
    have induction := ih next (address+64) (fun i => blocks (i+1)) nextScratch nextPointer
      (by omega) (by omega) (by omega) nextData
    rw [checkLeafLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (checkLeafLoop
      (checkLeafStepState state (oracle.compression (leafQuery (checkLeafCopyState state))))
      count)).1 256 32 = _
    rw [input]
    change readBuffer (checkEvaluation oracle (checkLeafLoop next count)).1 256 32 = _
    rw [induction, check_leaf_step_digest]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
      Nat.succ_eq_add_one]
    rfl

/-- Leaf hashing preserves every memory word outside scratch. -/
theorem check_leaf_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkLeafLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, check_evaluation_pure]
  | succ count ih =>
    rw [checkLeafLoop, check_evaluation_public_bind]
    let answer := oracle.compression (leafQuery (checkLeafCopyState state))
    change (checkEvaluation oracle (checkLeafLoop (checkLeafStepState state answer) count)).1.getMem address = _
    rw [ih _ ((check_leaf_block_registers state answer).2.2.1.trans scratch)]
    exact check_leaf_step_outside state answer address scratch outside

/-- The full checker leaf subroutine hashes exactly the four 512-bit message blocks
starting from the supplied salt, as defined by `leafDigest` (four 512-bit blocks). -/
theorem check_leaf_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (salt : Digest) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 352 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 4, readBuffer state (address + 64*i) 64 = value.extractLsb' (512*i) 512) :
    readBuffer (checkEvaluation oracle (checkLeafLoop state 4)).1 256 32 =
      leafDigest oracle.compression salt value := by
  rw [check_leaf_loop_digest oracle state address 4 _ scratch pointer aligned above bounded data, initial]
  rfl

end CommitGolfCandidate
