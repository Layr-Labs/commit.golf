import CommitGolfCandidate.Model
import CommitGolfCandidate.Memory
import CommitGolfCandidate.Check
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory

/-! Refinement of the checker's 4-call tagged salted leaf hash to `leafDigest`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

/-! ### Call 0 head copy (9 words into scratch `[280, 352)`) -/

set_option maxHeartbeats 4000000 in
theorem check_leaf_init_copy_word (state : MachineState) (word : Nat) (bounded : word < 9)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 9, ∀ j < 9,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (280+8*j)) :
    (checkLeafInitCopyState state).getMem (BitVec.ofNat 64 (280+8*word)) =
      state.getMem (state.getReg .x8 + BitVec.ofNat 64 (8*word)) := by
  rw [check_leaf_init_copy_expansion]
  have disjoint : ∀ i : Fin 9, ∀ j : Fin 9,
      state.getReg .x8 + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (280+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
    BitVec.add_zero] at disjoint
  simp only [List.foldl, execInstrBr, signExtend12]
  interval_cases word <;>
    simp [register_set_mem, scratch, disjoint, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]

theorem check_leaf_init_copy_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ j < 9, address ≠ BitVec.ofNat 64 (280+8*j)) :
    (checkLeafInitCopyState state).getMem address = state.getMem address := by
  rw [check_leaf_init_copy_expansion]
  have o0 := outside 0 (by decide)
  have o1 := outside 1 (by decide)
  have o2 := outside 2 (by decide)
  have o3 := outside 3 (by decide)
  have o4 := outside 4 (by decide)
  have o5 := outside 5 (by decide)
  have o6 := outside 6 (by decide)
  have o7 := outside 7 (by decide)
  have o8 := outside 8 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at o0 o1 o2 o3 o4 o5 o6 o7 o8
  change address ≠ 280#64 at o0
  change address ≠ 288#64 at o1
  change address ≠ 296#64 at o2
  change address ≠ 304#64 at o3
  change address ≠ 312#64 at o4
  change address ≠ 320#64 at o5
  change address ≠ 328#64 at o6
  change address ≠ 336#64 at o7
  change address ≠ 344#64 at o8
  simp only [List.foldl, execInstrBr, signExtend12]
  simp [register_set_mem, scratch, o0, o1, o2, o3, o4, o5, o6, o7, o8, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

/-! ### 8-word block copy (into scratch `[288, 352)`) -/

set_option maxHeartbeats 4000000 in
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

theorem read_head72_eq_of_words (left right : MachineState) (leftAddress rightAddress : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0)
    (words : ∀ word < 9, left.getMem (BitVec.ofNat 64 (leftAddress+8*word)) =
      right.getMem (BitVec.ofNat 64 (rightAddress+8*word))) :
    readBuffer left leftAddress 72 = readBuffer right rightAddress 72 := by
  rw [read_head72_split, read_head72_split]
  have low := read_block_eq_of_words left right leftAddress rightAddress leftAligned rightAligned
    (fun word hw => words word (by omega))
  have high : readBuffer left (leftAddress+64) 8 = readBuffer right (rightAddress+64) 8 := by
    rw [read_word_eq _ _ (by omega), read_word_eq _ _ (by omega)]
    exact words 8 (by decide)
  rw [low, high]

/-- Reconstruct the 72-byte leaf head from the first two 64-byte leaf blocks. -/
theorem read_head72_of_blocks (state : MachineState) (address : Nat) (value : Entry)
    (b0 : readBuffer state address 64 = value.extractLsb' 0 512)
    (b1 : readBuffer state (address + 64) 64 = value.extractLsb' 512 512) :
    readBuffer state address 72 = value.extractLsb' 0 576 := by
  rw [read_head72_split, b0]
  have tail8 : readBuffer state (address + 64) 8 = value.extractLsb' 512 64 := by
    have sl := read_buffer_slice state (address + 64) 64 0 8 (by decide)
    simp only [Nat.add_zero, Nat.mul_zero] at sl
    rw [← sl, b1]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_extractLsb', hi, show i < 512 by omega]
  rw [tail8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi576 : i < 576 := by change i < 8 * 72 at hi; omega
  by_cases low : i < 512
  · rw [BitVec.getLsbD_append, if_pos low, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [low, hi576]
  · rw [BitVec.getLsbD_append, if_neg low, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp only [hi576, show i - 512 < 64 by omega, decide_true, Bool.true_and]
    exact congrArg value.getLsbD (by omega)

set_option maxHeartbeats 1600000 in
/-- Exact Call 0 compression input: 16-byte salt || 8-byte leaf tag || 72-byte head. -/
theorem check_leaf_init_input (state : MachineState)
    (scratch : state.getReg .x21 = 256)
    (aligned : (state.getReg .x8).toNat % 8 = 0)
    (separated : ∀ i < 9, ∀ j < 9,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (280+8*j)) :
    leafQuery (checkLeafInitCopyState state) =
      readBuffer state (state.getReg .x8).toNat 72 ++
        readBuffer state 272 8 ++ readBuffer state 256 16 := by
  unfold leafQuery
  rw [read_init_query]
  have saltEq : readBuffer (checkLeafInitCopyState state) 256 16 = readBuffer state 256 16 := by
    apply read_salt_congr _ _ _ (by decide)
    intro i hi
    apply check_leaf_init_copy_outside _ _ scratch
    intro j hj
    interval_cases i <;> interval_cases j <;> decide
  have tagEq : readBuffer (checkLeafInitCopyState state) (256+16) 8 = readBuffer state 272 8 := by
    rw [read_word_eq _ _ (by decide), read_word_eq _ _ (by decide)]
    apply check_leaf_init_copy_outside _ _ scratch
    intro j hj
    interval_cases j <;> decide
  have headEq : readBuffer (checkLeafInitCopyState state) (256+24) 72 =
      readBuffer state (state.getReg .x8).toNat 72 := by
    apply read_head72_eq_of_words _ _ _ _ (by decide) aligned
    intro word bounded
    rw [show 256 + 24 + 8*word = 280 + 8*word by omega,
      check_leaf_init_copy_word state word bounded scratch separated]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [saltEq, tagEq, headEq]

theorem check_leaf_init_step_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkLeafInitStepState state answer) 256 32 = answer := by
  change readBuffer (checkLeafCompressionState (checkLeafInitCopyState state) answer) 256 32 = answer
  unfold checkLeafCompressionState
  exact (write_bits_digest _ 256 0 answer (by decide) (by decide)).trans (by simp)

theorem check_leaf_init_step_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (checkLeafInitStepState state answer).getMem address = state.getMem address := by
  change (checkLeafCompressionState (checkLeafInitCopyState state) answer).getMem address = _
  rw [check_leaf_compression_memory_outside]
  · apply check_leaf_init_copy_outside _ _ scratch
    intro j hj
    have := outside (j+3) (by omega)
    rwa [show 256 + 8*(j+3) = 280 + 8*j by omega] at this
  · exact ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩

set_option maxHeartbeats 1600000 in
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

theorem check_leaf_step_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkLeafStepState state answer) 256 32 = answer := by
  change readBuffer (checkLeafCompressionState (checkLeafCopyState state) answer) 256 32 = answer
  unfold checkLeafCompressionState
  exact (write_bits_digest _ 256 0 answer (by decide) (by decide)).trans (by simp)

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

theorem check_leaf_subroutine_outside (oracle : Oracle) (state : MachineState)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkLeafSubroutineRun state)).1.getMem address = state.getMem address := by
  rw [checkLeafSubroutineRun, check_evaluation_public_bind]
  let answer := oracle.compression (leafQuery (checkLeafInitCopyState state))
  change (checkEvaluation oracle (checkLeafLoop (checkLeafInitStepState state answer) 3)).1.getMem address = _
  rw [check_leaf_loop_outside oracle _ 3 address ((check_leaf_init_registers state answer).2.2.1.trans scratch) outside]
  exact check_leaf_init_step_outside state answer address scratch outside

/-- The full checker leaf subroutine hashes `[salt(16B) || leafTag index || head72]`
followed by the remaining three 512-bit message blocks, producing `leafDigest`. -/
theorem check_leaf_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (index : Index) (salt : Salt) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 352 ≤ address)
    (bounded : address + 256 < 2^64)
    (initialSalt : readBuffer state 256 16 = salt)
    (initialTag : readBuffer state 272 8 = leafTag index)
    (data : ∀ i < 4, readBuffer state (address + 64*i) 64 = value.extractLsb' (512*i) 512) :
    readBuffer (checkEvaluation oracle (checkLeafSubroutineRun state)).1 256 32 =
      leafDigest oracle.compression index salt value := by
  have pointerNat : (state.getReg .x8).toNat = address := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have separated : ∀ i < 9, ∀ j < 9,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (280+8*j) := by
    intro i hi j hj equal
    have natural := congrArg BitVec.toNat equal
    rw [pointer, ← BitVec.ofNat_add] at natural
    simp only [BitVec.toNat_ofNat] at natural
    rw [Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
      Nat.mod_eq_of_lt (by omega : 280+8*j < 2^64)] at natural
    omega
  have head72 : readBuffer state address 72 = value.extractLsb' 0 576 :=
    read_head72_of_blocks state address value
      (by simpa using data 0 (by decide)) (by simpa using data 1 (by decide))
  have initInput := check_leaf_init_input state scratch (by simpa [pointerNat] using aligned) separated
  rw [pointerNat, head72, initialTag, initialSalt] at initInput
  let d0 : BitVec 256 := oracle.compression (leafInitInput index salt value)
  let s1 := checkLeafInitStepState state d0
  have iregs := check_leaf_init_registers state d0
  have s1Scratch : s1.getReg .x21 = 256 := iregs.2.2.1.trans scratch
  have s1Ptr : s1.getReg .x8 = BitVec.ofNat 64 (address + 64) := by
    rw [show s1.getReg .x8 = state.getReg .x8 + 64 from iregs.1, pointer, BitVec.ofNat_add]; rfl
  have s1Data (i : Nat) (hi : i < 3) :
      readBuffer s1 (address + 64 + 64*i) 64 = value.extractLsb' (512*(i+1)) 512 := by
    have mem : readBuffer s1 (address + 64 + 64*i) 64 = readBuffer state (address + 64 + 64*i) 64 := by
      apply read_block_eq_of_words _ _ _ _ (by omega) (by omega)
      intro word hw
      apply check_leaf_init_step_outside _ _ _ scratch
      intro j hj equal
      have natural := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat] at natural
      rw [Nat.mod_eq_of_lt (by omega : address + 64 + 64*i + 8*word < 2^64),
        Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
      omega
    rw [mem, show address + 64 + 64*i = address + 64*(i+1) by omega]
    exact data (i+1) (by omega)
  rw [checkLeafSubroutineRun, check_evaluation_public_bind]
  change readBuffer (checkEvaluation oracle (checkLeafLoop
    (checkLeafInitStepState state (oracle.compression (leafQuery (checkLeafInitCopyState state)))) 3)).1 256 32 = _
  rw [initInput]
  change readBuffer (checkEvaluation oracle (checkLeafLoop s1 3)).1 256 32 = _
  rw [check_leaf_loop_digest oracle s1 (address + 64) 3 (fun i => value.extractLsb' (512*(i+1)) 512)
    s1Scratch s1Ptr (by omega) (by omega) (by omega) s1Data]
  dsimp only [s1]
  rw [check_leaf_init_step_digest state _]
  rfl

end CommitGolfCandidate
