import CommitGolfCandidate.PathRefinement
import CommitGolfCandidate.CheckLoop
import CommitGolfCandidate.CheckCap

/-! Functional refinement of the actual checker's complete position computation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

/-- The per-position setup copies the proof salt into the leaf accumulator. -/
theorem check_position_salt (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address%8 = 0) (above : 320 ≤ address) (bounded : address+32 < 2^64) :
    readBuffer (checkPositionState state) 256 32 = readBuffer state address 32 := by
  have indexScratch : (checkIndexState state).getReg .x21 = 256 := by
    simpa [checkIndexState, MachineState.getReg_setReg_ne] using scratch
  have indexPointer : (checkIndexState state).getReg .x25 = BitVec.ofNat 64 address := by
    simpa [checkIndexState, MachineState.getReg_setReg_ne] using pointer
  change readBuffer (checkPathCopyState (checkIndexState state) 63) 256 32 = _
  exact check_salt_copy_digest (checkIndexState state) address
    indexScratch indexPointer aligned above bounded

/-- The index load and salt copy preserve all words outside the accumulator. -/
theorem check_position_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkPositionState state).getMem address = state.getMem address := by
  change (checkPathCopyState (checkIndexState state) 63).getMem address = _
  exact check_salt_copy_outside (checkIndexState state) address
    (by simpa [checkIndexState, MachineState.getReg_setReg_ne] using scratch) outside

private theorem word_outside_scratch (address offset : Nat) (above : 352 ≤ address)
    (bounded : address+offset < 2^64) (i : Nat) (hi : i < 12) :
    BitVec.ofNat 64 (address+offset) ≠ BitVec.ofNat 64 (256+8*i) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at natural
  omega

private theorem check_path_setup_memory (state : MachineState) :
    (checkPathInitializedState state).mem = state.mem := rfl

attribute [local irreducible] checkPositionState checkLeafLoop checkPathLoop
  checkPathInitializedState checkEvaluation checkPositionHash

set_option maxRecDepth 4096 in
theorem check_position_hash_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (checkPositionHash state)).1 =
      (checkEvaluation oracle (checkPathLoop (checkPathInitializedState
        (((checkEvaluation oracle (checkLeafLoop
          (((checkPositionState state).setReg .x28 4).setPC 4648) 4)).1).setPC 4388)) 17)).1 := by
  rw [checkPositionHash, check_evaluation_bind]

set_option maxRecDepth 4096 in
private theorem finish_check_path (oracle : Oracle) (state leaf : MachineState)
    (proofAddress : Nat) (path : List (Bool × Digest)) (digest : Digest)
    (leafScratch : leaf.getReg .x21 = 256)
    (leafPointer : leaf.getReg .x25 = BitVec.ofNat 64 (proofAddress+32))
    (leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24))
    (leafOutside : ∀ address : Word,
      (∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) → leaf.getMem address = state.getMem address)
    (leafDigestEq : readBuffer leaf 256 32 = digest)
    (proofAligned : proofAddress%8 = 0) (proofAbove : 352 ≤ proofAddress)
    (proofBound : proofAddress+576 < 2^64) (pathLength : path.length = 17)
    (pathData : ∀ i (hi : i < path.length),
      readBuffer state (proofAddress+32+32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle
      (checkPathLoop (checkPathInitializedState (leaf.setPC 4388)) 17)).1 256 32 =
      climb oracle.compression digest path := by
  let pathReady := checkPathInitializedState (leaf.setPC 4388)
  have pathScratch : pathReady.getReg .x21 = 256 :=
    (check_path_setup_register (leaf.setPC 4388) .x21 (by decide)).trans leafScratch
  have pathPointer : pathReady.getReg .x25 = BitVec.ofNat 64 (proofAddress+32) :=
    (check_path_setup_register (leaf.setPC 4388) .x25 (by decide)).trans leafPointer
  have pathMemory (address : Word) : pathReady.getMem address = leaf.getMem address :=
    congrFun (check_path_setup_memory (leaf.setPC 4388)) address
  have afterData (i : Nat) (hi : i < path.length) :
      readBuffer pathReady (proofAddress+32+32*i) 32 = (path[i]'hi).2 := by
    have same : readBuffer pathReady (proofAddress+32+32*i) 32 =
        readBuffer state (proofAddress+32+32*i) 32 := by
      apply read_digest_congr _ _ _ (by omega)
      intro word hw
      rw [pathMemory]
      apply leafOutside
      intro j hj
      simpa only [Nat.add_assoc] using word_outside_scratch proofAddress (32+32*i+8*word) proofAbove
        (by rw [pathLength] at hi; omega) j hj
    exact same.trans (pathData i hi)
  have afterDirections (i : Nat) (hi : i < path.length) :
      (pathReady.getReg .x20).getLsbD i = (path[i]'hi).1 := by
    rw [check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC, leafIndex]
    exact directions i hi
  have folded := check_path_loop_digest oracle pathReady (proofAddress+32) path pathScratch pathPointer
    (by omega) (by omega) (by rw [pathLength]; omega) afterData afterDirections
  have startDigest : readBuffer pathReady 256 32 = digest := by
    have same : readBuffer pathReady 256 32 = readBuffer leaf 256 32 := by
      apply read_digest_congr _ _ _ (by decide)
      intro word hw
      exact pathMemory _
    exact same.trans leafDigestEq
  have sameLength := congrArg (fun count =>
    readBuffer (checkEvaluation oracle (checkPathLoop pathReady count)).1 256 32) pathLength.symm
  exact sameLength.trans (folded.trans
    (congrArg (fun value => climb oracle.compression value path) startDigest))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- One complete checker iteration computes the submitted leaf digest and folds its
17 supplied siblings in the direction determined by the submitted position. -/
theorem check_position_hash_digest (oracle : Oracle) (state : MachineState)
    (valueAddress proofAddress : Nat) (value : Entry) (salt : Digest) (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress%8 = 0) (proofAligned : proofAddress%8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress+256 < 2^64) (proofBound : proofAddress+576 < 2^64)
    (saltData : readBuffer state proofAddress 32 = salt)
    (valueData : ∀ block < 4, readBuffer state (valueAddress+64*block) 64 =
      value.extractLsb' (512*block) 512)
    (pathLength : path.length = 17)
    (pathData : ∀ i (hi : i < path.length),
      readBuffer state (proofAddress+32+32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle (checkPositionHash state)).1 256 32 =
      climb oracle.compression (leafDigest oracle.compression salt value) path := by
  let ready := ((checkPositionState state).setReg .x28 4).setPC 4648
  let leaf := (checkEvaluation oracle (checkLeafLoop ready 4)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have readyPointer : ready.getReg .x8 = BitVec.ofNat 64 valueAddress :=
    (check_position_register state .x8 (by decide)).trans valuePointer
  have readySalt : readBuffer ready 256 32 = salt :=
    (check_position_salt state proofAddress scratch proofPointer proofAligned (by omega) (by omega)).trans saltData
  have readyOutside (address : Word) (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+8*i)) :
      ready.getMem address = state.getMem address := check_position_outside state address scratch outside
  have readyHalf (address : Nat) (aligned : address % 8 = 0) (above : 352 ≤ address)
      (bounded : address + 32 < 2^64) : readBuffer ready address 32 = readBuffer state address 32 := by
    apply read_digest_congr _ _ _ aligned
    intro word hw
    apply readyOutside
    intro i hi
    exact word_outside_scratch address (8*word) above (by omega) i (by omega)
  have readyData (block : Nat) (hb : block < 4) :
      readBuffer ready (valueAddress+64*block) 64 = value.extractLsb' (512*block) 512 := by
    rw [read_compression_halves _ _ (by omega),
      readyHalf (valueAddress+64*block+32) (by omega) (by omega) (by omega),
      readyHalf (valueAddress+64*block) (by omega) (by omega) (by omega),
      ← read_compression_halves _ _ (by omega)]
    exact valueData block hb
  have leafDigestEq : readBuffer leaf 256 32 = leafDigest oracle.compression salt value :=
    check_leaf_digest oracle ready valueAddress salt value readyScratch readyPointer
      valueAligned valueAbove valueBound readySalt readyData
  have leafRegs := check_leaf_loop_registers ready 4 leaf (check_evaluation_support oracle _)
  have leafScratch : leaf.getReg .x21 = 256 := (leafRegs.2 .x21 (by decide)).trans readyScratch
  have leafPointer : leaf.getReg .x25 = BitVec.ofNat 64 (proofAddress+32) := by
    rw [leafRegs.2 .x25 (by decide)]
    change (checkPositionState state).getReg .x25 = _
    rw [check_position_proof_pointer, proofPointer]
    exact (BitVec.ofNat_add proofAddress 32).symm
  have leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [leafRegs.2 .x20 (by decide)]
    exact check_position_index state
  have leafOutside (address : Word) (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
      leaf.getMem address = state.getMem address :=
    (check_leaf_loop_outside oracle ready 4 address readyScratch outside).trans
      (readyOutside address (fun i hi => outside i (by omega)))
  rw [check_position_hash_evaluation]
  exact finish_check_path oracle state leaf proofAddress path _ leafScratch leafPointer leafIndex
    leafOutside leafDigestEq proofAligned proofAbove proofBound pathLength pathData directions

private theorem check_path_phase_outside (oracle : Oracle) (leaf : MachineState) (address : Word)
    (scratch : leaf.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle
      (checkPathLoop (checkPathInitializedState (leaf.setPC 4388)) 17)).1.getMem address =
        leaf.getMem address := by
  have pathScratch : (checkPathInitializedState (leaf.setPC 4388)).getReg .x21 = 256 :=
    (check_path_setup_register (leaf.setPC 4388) .x21 (by decide)).trans scratch
  exact (check_path_loop_outside oracle (checkPathInitializedState (leaf.setPC 4388))
    17 address pathScratch (fun i hi => outside i (by omega))).trans
      (congrFun (check_path_setup_memory (leaf.setPC 4388)) address)

set_option maxRecDepth 4096 in
/-- Computing one position does not modify any input buffer or the supplied root. -/
theorem check_position_hash_outside (oracle : Oracle) (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkPositionHash state)).1.getMem address = state.getMem address := by
  let ready := ((checkPositionState state).setReg .x28 4).setPC 4648
  let leaf := (checkEvaluation oracle (checkLeafLoop ready 4)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have leafScratch : leaf.getReg .x21 = 256 :=
    ((check_leaf_loop_registers ready 4 leaf (check_evaluation_support oracle _)).2 .x21 (by decide)).trans
      readyScratch
  have initialMemory : ready.getMem address = state.getMem address :=
    check_position_outside state address scratch (fun i hi => outside i (by omega))
  have leafMemory := check_leaf_loop_outside oracle ready 4 address readyScratch outside
  rw [check_position_hash_evaluation]
  exact (check_path_phase_outside oracle leaf address leafScratch outside).trans
    (leafMemory.trans initialMemory)

/-- The four machine-word comparisons of either comparison block are exactly a digest
equality between scratch and the reference digest addressed by the compared register. -/
theorem check_compare_digest (cap : Bool) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg (compareReg cap) = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) :
    (∀ word < 4, state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8*word)) =
      state.getMem (state.getReg (compareReg cap) + BitVec.ofNat 64 (8*word))) ↔
    readBuffer state 256 32 = readBuffer state address 32 := by
  rw [read_digest_eq_iff _ _ _ _ (by decide) aligned, scratch, pointer]
  constructor <;> intro words word hw
  · have agree := words word hw
    change state.getMem (BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*word)) = _ at agree
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add] at agree
    exact agree
  · have agree := words word hw
    change state.getMem (BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*word)) = _
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact agree

/-- The selected cap-node address for an in-range index. -/
theorem cap_node_address (base index : Nat) (small : index < 2^24) (bounded : base + 4096 < 2^64) :
    BitVec.ofNat 64 base + (BitVec.ofNat 64 index >>> 17) <<< 5 =
      BitVec.ofNat 64 (base + 32 * (index / 2^17)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  norm_num at small bounded ⊢
  omega

/-! The cap chain refines the reference `capRoot`. -/

private theorem register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

set_option maxHeartbeats 4000000 in
theorem check_cap_copy_word (state : MachineState) (word : Nat) (bounded : word < 8)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 8, ∀ j < 8,
      state.getReg .x25 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    (checkCapCopyState state).getMem (BitVec.ofNat 64 (288+8*word)) =
      state.getMem (state.getReg .x25 + BitVec.ofNat 64 (8*word)) := by
  rw [check_cap_copy_expansion]
  have disjoint : ∀ i : Fin 8, ∀ j : Fin 8,
      state.getReg .x25 + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (288+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
    BitVec.add_zero] at disjoint
  simp only [List.foldl, execInstrBr, signExtend12]
  interval_cases word <;>
    simp [register_set_mem, scratch, disjoint, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]

theorem check_cap_copy_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ j < 8, address ≠ BitVec.ofNat 64 (288+8*j)) :
    (checkCapCopyState state).getMem address = state.getMem address := by
  rw [check_cap_copy_expansion]
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

set_option maxHeartbeats 1600000 in
theorem check_cap_input (state : MachineState)
    (scratch : state.getReg .x21 = 256)
    (aligned : (state.getReg .x25).toNat % 8 = 0)
    (separated : ∀ i < 8, ∀ j < 8,
      state.getReg .x25 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    leafQuery (checkCapCopyState state) =
      leafInput (readBuffer state 256 32) (readBuffer state (state.getReg .x25).toNat 64) := by
  unfold leafQuery leafInput
  rw [read_leaf_query]
  have low : readBuffer (checkCapCopyState state) 256 32 = readBuffer state 256 32 := by
    apply read_digest_congr _ _ _ (by decide)
    intro i hi
    apply check_cap_copy_outside _ _ scratch
    intro j hj
    interval_cases i <;> interval_cases j <;> decide
  have high : readBuffer (checkCapCopyState state) (256+32) 64 =
      readBuffer state (state.getReg .x25).toNat 64 := by
    apply read_block_eq_of_words _ _ _ _ (by decide) aligned
    intro word bounded
    rw [show 256 + 32 + 8*word = 288 + 8*word by omega,
      check_cap_copy_word state word bounded scratch separated]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [low, high]

theorem check_cap_call_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280) :
    (checkCapCallState state answer).getMem address = state.getMem address := by
  unfold checkCapCallState
  apply writeBits_memory_outside
  intro i hi
  change i < 32 at hi
  interval_cases i <;> norm_num [alignToDword] <;> tauto

theorem check_cap_step_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkCapStepState state answer) 256 32 = answer := by
  change readBuffer (checkCapCallState (checkCapCopyState state) answer) 256 32 = answer
  unfold checkCapCallState
  exact (write_bits_digest _ 256 0 answer (by decide) (by decide)).trans (by simp)

theorem check_cap_step_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (checkCapStepState state answer).getMem address = state.getMem address := by
  change (checkCapCallState (checkCapCopyState state) answer).getMem address = _
  rw [check_cap_call_memory_outside]
  · apply check_cap_copy_outside _ _ scratch
    intro j hj
    have := outside (j+4) (by omega)
    rwa [show 256 + 8*(j+4) = 288 + 8*j by omega] at this
  · exact ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩

/-- The checker cap loop computes the reference chain over its supplied 64-byte blocks. -/
theorem check_cap_loop_digest (oracle : Oracle) (state : MachineState)
    (address count : Nat) (blocks : Nat → LeafBlock)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 352 ≤ address)
    (bounded : address + 64 * count < 2^64)
    (data : ∀ i < count, readBuffer state (address + 64*i) 64 = blocks i) :
    readBuffer (checkEvaluation oracle (checkCapLoop state count)).1 256 32 =
      (List.range count).foldl
        (fun digest i => absorb oracle.compression digest (blocks i)) (readBuffer state 256 32) := by
  induction count generalizing state address blocks with
  | zero => simp [checkCapLoop, check_evaluation_pure]
  | succ count ih =>
    have pointerNat : (state.getReg .x25).toNat = address := by
      rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have separated : ∀ i < 8, ∀ j < 8,
        state.getReg .x25 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j) := by
      intro i hi j hj equal
      have natural := congrArg BitVec.toNat equal
      rw [pointer, ← BitVec.ofNat_add] at natural
      simp only [BitVec.toNat_ofNat] at natural
      rw [Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
        Nat.mod_eq_of_lt (by omega : 288+8*j < 2^64)] at natural
      omega
    have input := check_cap_input state scratch (by simpa [pointerNat] using aligned) separated
    rw [pointerNat, show address = address + 64*0 by omega, data 0 (by omega)] at input
    let answer := absorb oracle.compression (readBuffer state 256 32) (blocks 0)
    let next := checkCapStepState state answer
    have nextScratch : next.getReg .x21 = 256 :=
      (check_cap_step_register state answer .x21 (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans scratch
    have nextPointer : next.getReg .x25 = BitVec.ofNat 64 (address + 64) := by
      rw [show next.getReg .x25 = state.getReg .x25 + 64 from (check_cap_step_registers state answer).1,
        pointer, BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < count) :
        readBuffer next (address + 64 + 64*i) 64 = blocks (i+1) := by
      have memory : readBuffer next (address + 64 + 64*i) 64 =
          readBuffer state (address + 64 + 64*i) 64 := by
        apply read_block_eq_of_words _ _ _ _ (by omega) (by omega)
        intro word hw
        apply check_cap_step_outside _ _ _ scratch
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
    rw [checkCapLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (checkCapLoop
      (checkCapStepState state (oracle.compression (leafQuery (checkCapCopyState state))))
      count)).1 256 32 = _
    rw [input]
    change readBuffer (checkEvaluation oracle (checkCapLoop next count)).1 256 32 = _
    rw [induction, check_cap_step_digest]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
      Nat.succ_eq_add_one]
    rfl

theorem check_cap_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkCapLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [checkCapLoop, check_evaluation_pure]
  | succ count ih =>
    rw [checkCapLoop, check_evaluation_public_bind]
    let answer := oracle.compression (leafQuery (checkCapCopyState state))
    change (checkEvaluation oracle (checkCapLoop (checkCapStepState state answer) count)).1.getMem address = _
    rw [ih _ ((check_cap_step_register state answer .x21 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans scratch)]
    exact check_cap_step_outside state answer address scratch outside

/-- The state reached by the cap block for a fixed oracle. -/
def capPhaseState (oracle : Oracle) (state : MachineState) : MachineState :=
  (checkEvaluation oracle (checkCapLoop (checkCapSetupState state) 64)).1

/-- The cap block preserves all memory outside scratch. -/
theorem cap_phase_outside (oracle : Oracle) (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (capPhaseState oracle state).getMem address = state.getMem address := by
  have readyScratch : (checkCapSetupState state).getReg .x21 = 256 :=
    (check_cap_setup_register state .x21 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans scratch
  exact (check_cap_loop_outside oracle _ 64 address readyScratch outside).trans
    (check_cap_setup_memory state scratch address (fun i hi => outside i (by omega)))

theorem cap_phase_digest_outside (oracle : Oracle) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0) (above : 352 ≤ address)
    (bounded : address + 32 < 2^64) :
    readBuffer (capPhaseState oracle state) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro word hw
  apply cap_phase_outside oracle state _ scratch
  intro i hi equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address + 8*word < 2^64),
    Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at natural
  omega

/-- The cap block computes the reference cap root over the 128 supplied cap nodes. -/
theorem cap_phase_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (cap : Nat → Digest)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 352 ≤ address) (bounded : address + 4096 < 2^64)
    (capData : ∀ node < 128, readBuffer state (address + 32*node) 32 = cap node) :
    readBuffer (capPhaseState oracle state) 256 32 = capRoot oracle.compression cap := by
  let ready := checkCapSetupState state
  have keep (reg : Reg) (not5 : reg ≠ .x5) (not11 : reg ≠ .x11) (not13 : reg ≠ .x13)
      (not28 : reg ≠ .x28) (not30 : reg ≠ .x30) :=
    check_cap_setup_register state reg not5 not11 not13 not28 not30
  have readyScratch : ready.getReg .x21 = 256 :=
    (keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch
  have readyPointer : ready.getReg .x25 = BitVec.ofNat 64 address :=
    (keep .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pointer
  have readyDigest (offset : Nat) (offsetAligned : offset % 8 = 0) (inside : offset + 32 ≤ 4096) :
      readBuffer ready (address + offset) 32 = readBuffer state (address + offset) 32 := by
    apply read_digest_congr _ _ _ (by omega)
    intro word hw
    apply check_cap_setup_memory state scratch
    intro i hi equal
    have natural := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address + offset + 8*word < 2^64),
      Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at natural
    omega
  have data (i : Nat) (hi : i < 64) : readBuffer ready (address + 64*i) 64 = capBlock cap i := by
    rw [read_compression_halves _ _ (by omega),
      show address + 64*i + 32 = address + (64*i+32) by omega,
      readyDigest (64*i+32) (by omega) (by omega), readyDigest (64*i) (by omega) (by omega),
      show address + (64*i+32) = address + 32*(2*i+1) by omega,
      show address + 64*i = address + 32*(2*i) by omega,
      capData (2*i+1) (by omega), capData (2*i) (by omega)]
    rfl
  have zero : readBuffer ready 256 32 = 0 := by
    have z0 : ready.getMem (BitVec.ofNat 64 256) = 0 := check_cap_setup_zero state scratch 0 (by decide)
    have z1 : ready.getMem (BitVec.ofNat 64 (256+8)) = 0 := check_cap_setup_zero state scratch 1 (by decide)
    have z2 : ready.getMem (BitVec.ofNat 64 (256+16)) = 0 := check_cap_setup_zero state scratch 2 (by decide)
    have z3 : ready.getMem (BitVec.ofNat 64 (256+24)) = 0 := check_cap_setup_zero state scratch 3 (by decide)
    rw [read_digest_words _ _ (by decide), z0, z1, z2, z3]
    rfl
  have folded := check_cap_loop_digest oracle ready address 64 (capBlock cap) readyScratch readyPointer
    aligned above (by omega) data
  change readBuffer (checkEvaluation oracle (checkCapLoop ready 64)).1 256 32 = _
  rw [folded, zero]
  simp only [capRoot, capBlocks, List.foldl_map] <;> rfl

end CommitGolfCandidate
