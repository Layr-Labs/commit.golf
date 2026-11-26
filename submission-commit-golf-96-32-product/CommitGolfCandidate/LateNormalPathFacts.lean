import CommitGolfCandidate.Model
import CommitGolfCandidate.LateNormalOuter

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

def copyBlock (state : MachineState) (source : Reg) (offset : Nat) : MachineState :=
  ([.LD .x6 source 0, .SD .x21 .x6 (BitVec.ofNat 12 offset),
    .LD .x6 source 8, .SD .x21 .x6 (BitVec.ofNat 12 (offset+8)),
    .LD .x6 source 16, .SD .x21 .x6 (BitVec.ofNat 12 (offset+16)),
    .LD .x6 source 24, .SD .x21 .x6 (BitVec.ofNat 12 (offset+24))] : List Instr).foldl execInstrBr state

theorem path_copy_eq (state : MachineState) (start : Nat) :
    checkPathCopyState state start =
      copyBlock state (if start = 29 then .x21 else .x25)
        (if start = 37 ∨ start = 16 then 0 else 32) := rfl

theorem copy_block_word (state : MachineState) (source : Reg) (offset word : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32) (bounded : word < 4)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg source + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    (copyBlock state source offset).getMem (BitVec.ofNat 64 (256+offset+8*word)) =
      state.getMem (state.getReg source + BitVec.ofNat 64 (8*word)) := by
  have disjoint : ∀ i : Fin 4, ∀ j : Fin 4,
      state.getReg source + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (256+offset+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_zero] at disjoint <;>
    simp only [copyBlock, List.foldl, execInstrBr, signExtend12] <;>
    interval_cases word <;>
    simp [register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem copy_block_outside (state : MachineState) (source : Reg) (offset : Nat)
    (address : Word) (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+offset+8*i)) :
    (copyBlock state source offset).getMem address = state.getMem address := by
  have disjoint : ∀ i : Fin 4, address ≠ BitVec.ofNat 64 (256+offset+8*i.val) :=
    fun i => outside i i.isLt
  rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul] at disjoint <;>
    simp only [copyBlock, List.foldl, execInstrBr, signExtend12] <;>
    simp [register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem copy_block_digest (state : MachineState) (source : Reg) (offset : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : (state.getReg source).toNat % 8 = 0)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg source + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (copyBlock state source offset) (256+offset) 32 =
      readBuffer state (state.getReg source).toNat 32 := by
  rw [read_digest_words _ _ (by rcases offsets with rfl | rfl <;> decide),
    read_digest_words _ _ aligned]
  have w0 := copy_block_word state source offset 0 notTemp offsets (by decide) scratch separated
  have w1 := copy_block_word state source offset 1 notTemp offsets (by decide) scratch separated
  have w2 := copy_block_word state source offset 2 notTemp offsets (by decide) scratch separated
  have w3 := copy_block_word state source offset 3 notTemp offsets (by decide) scratch separated
  simp only [Nat.reduceMul, Nat.add_zero, BitVec.add_zero] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem copy_block_register (state : MachineState) (source : Reg) (offset : Nat)
    (reg : Reg) (notTemp : reg ≠ .x6) :
    (copyBlock state source offset).getReg reg = state.getReg reg := by
  simp [copyBlock, List.foldl, execInstrBr, register_set_mem, Ne.symm notTemp,
    MachineState.getReg_setReg_ne]

theorem copy_block_preserves (state : MachineState) (source : Reg) (offset address : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (outside : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (address+8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (copyBlock state source offset) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  exact copy_block_outside state source offset _ notTemp offsets scratch (outside i hi)

attribute [local irreducible] copyBlock

theorem check_path_input (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 32 < 2^64) :
    readBuffer (checkPathPreparedState state) 256 64 =
      if state.getReg .x20 &&& 1 = 0 then
        readBuffer state address 32 ++ readBuffer state 256 32
      else readBuffer state 256 32 ++ readBuffer state address 32 := by
  let branch := checkPathBranchState state
  have branchScratch : branch.getReg .x21 = 256 := by
    simpa [branch, checkPathBranchState, MachineState.getReg_setReg_ne] using scratch
  have branchPointer : branch.getReg .x25 = BitVec.ofNat 64 address := by
    simpa [branch, checkPathBranchState, MachineState.getReg_setReg_ne] using pointer
  have pointerNat : (branch.getReg .x25).toNat = address := by
    rw [branchPointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have separate (offset : Nat) (ho : offset = 0 ∨ offset = 32) : ∀ i < 4, ∀ j < 4,
      branch.getReg .x25 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j) := by
    intro i hi j hj equal
    have natural := congrArg BitVec.toNat equal
    rw [branchPointer, ← BitVec.ofNat_add] at natural
    simp only [BitVec.toNat_ofNat] at natural
    rw [Nat.mod_eq_of_lt (by omega : address+8*i < 2^64),
      Nat.mod_eq_of_lt (by rcases ho with rfl | rfl <;> omega : 256+offset+8*j < 2^64)] at natural
    rcases ho with rfl | rfl <;> omega
  have sourceOutside (offset : Nat) (ho : offset = 0 ∨ offset = 32) : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (address+8*i) ≠ BitVec.ofNat 64 (256+offset+8*j) := by
    intro i hi j hj
    simpa only [branchPointer, BitVec.ofNat_add] using separate offset ho i hi j hj
  have lowHigh : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (256+8*i) ≠ BitVec.ofNat 64 (256+32+8*j) := by
    intro i hi j hj
    interval_cases i <;> interval_cases j <;> decide
  have highLow : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (288+8*i) ≠ BitVec.ofNat 64 (256+0+8*j) := by
    intro i hi j hj
    exact Ne.symm (lowHigh j hj i hi)
  by_cases left : state.getReg .x20 &&& 1 = 0
  · rw [checkPathPreparedState, if_pos left, if_pos left, path_copy_eq]
    change readBuffer (copyBlock branch .x25 32) 256 64 = _
    rw [read_compression_halves _ _ (by decide)]
    have high := copy_block_digest branch .x25 32 (by decide) (Or.inr rfl)
      branchScratch (by simpa [pointerNat] using aligned) (separate 32 (Or.inr rfl))
    have low := copy_block_preserves branch .x25 32 256 (by decide) (Or.inr rfl)
      branchScratch (by decide) lowHigh
    rw [high, low, pointerNat]
    rfl
  · rw [checkPathPreparedState, if_neg left, if_neg left, path_copy_eq, path_copy_eq]
    let moved := copyBlock branch .x21 32
    change readBuffer (copyBlock moved .x25 0) 256 64 = _
    have movedScratch : moved.getReg .x21 = 256 :=
      (copy_block_register _ _ _ _ (by decide)).trans branchScratch
    have movedPointer : moved.getReg .x25 = branch.getReg .x25 :=
      copy_block_register _ _ _ _ (by decide)
    have saved := copy_block_digest branch .x21 32 (by decide) (Or.inr rfl)
      branchScratch (by rw [branchScratch]; decide)
      (by
        intro i hi j hj
        rw [branchScratch]
        change BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*i) ≠ _
        rw [← BitVec.ofNat_add]
        exact lowHigh i hi j hj)
    have source := copy_block_preserves branch .x21 32 address (by decide) (Or.inr rfl)
      branchScratch aligned (sourceOutside 32 (Or.inr rfl))
    have low := copy_block_digest moved .x25 0 (by decide) (Or.inl rfl) movedScratch
      (by rw [movedPointer, pointerNat]; exact aligned)
      (by rw [movedPointer]; exact separate 0 (Or.inl rfl))
    have high := copy_block_preserves moved .x25 0 288 (by decide) (Or.inl rfl)
      movedScratch (by decide) highLow
    rw [read_compression_halves _ _ (by decide), high, low, movedPointer, pointerNat, source, saved]
    rw [branchScratch]
    rfl

theorem low_bit_zero (index : Word) :
    (index &&& 1 = 0) ↔ index.getLsbD 0 = false := by
  change (index &&& 1#64 = 0#64) ↔ _
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : index.getLsbD 0 <;> simp [BitVec.ofBool]

theorem check_path_step_digest (state : MachineState) (answer : Digest) :
    readBuffer (checkPathStepState state answer) 256 32 = tcompDigest (tcompBit state) answer := by
  change readBuffer (checkCompressionState (checkPathPreparedState state) answer) 256 32 = _
  rw [check_compression_digest]
  simp only [tcompBit, check_path_prepared_x9]

/-- The adapter stores a node in cut form when bit 0 of the mask flags its height. -/
theorem tcomp_digest_cut (state : MachineState) (height : Nat) (answer : Digest)
    (flag : (state.getReg .x9).getLsbD 0 = decide (CutHeight height)) :
    tcompDigest (tcompBit state) answer = cut height answer := by
  unfold tcompDigest tcompBit cut
  by_cases inside : CutHeight height
  · have bit : ¬ (state.getReg .x9 &&& 1 = 0) := by
      rw [low_bit_zero, flag]; simp [inside]
    rw [if_neg bit, if_pos inside]
  · have bit : state.getReg .x9 &&& 1 = 0 := by
      rw [low_bit_zero, flag]; simp [inside]
    rw [if_pos bit, if_neg inside]

theorem check_path_step_outside (state : MachineState) (answer : Digest)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkPathStepState state answer).getMem address = state.getMem address := by
  change (checkCompressionState (checkPathPreparedState state) answer).getMem address = _
  rw [check_compression_memory_outside _ _ _
    ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩]
  have lower : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+0+8*i) :=
    fun i hi => outside i (by omega)
  have upper : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+32+8*i) := by
    intro i hi
    simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      outside (i+4) (by omega)
  have branchScratch : (checkPathBranchState state).getReg .x21 = 256 := by
    simpa [checkPathBranchState, MachineState.getReg_setReg_ne] using scratch
  unfold checkPathPreparedState
  split
  · rw [path_copy_eq]
    change (copyBlock (checkPathBranchState state) .x25 32).getMem address = _
    rw [copy_block_outside _ .x25 32 _ (by decide) (Or.inr rfl) branchScratch upper]
    rfl
  · rw [MachineState.getMem_setPC, path_copy_eq, path_copy_eq]
    change (copyBlock (copyBlock (checkPathBranchState state) .x21 32) .x25 0).getMem address = _
    have movedScratch : (copyBlock (checkPathBranchState state) .x21 32).getReg .x21 = 256 :=
      (copy_block_register _ _ _ _ (by decide)).trans branchScratch
    rw [copy_block_outside _ .x25 0 _ (by decide) (Or.inl rfl) movedScratch lower,
      copy_block_outside _ .x21 32 _ (by decide) (Or.inr rfl) branchScratch upper]
    rfl

attribute [local irreducible] checkPathStepState checkPathPreparedState checkPathLoop checkEvaluation

theorem check_path_loop_digest (oracle : Oracle) (state : MachineState)
    (address height : Nat) (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * path.length < 2^64)
    (data : ∀ i (hi : i < path.length), readBuffer state (address + 32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length), (state.getReg .x20).getLsbD i = (path[i]'hi).1)
    (masks : ∀ i < path.length, (state.getReg .x9).getLsbD i = decide (CutHeight (height + i + 1))) :
    readBuffer (checkEvaluation oracle (checkPathLoop state path.length)).1 256 32 =
      climbAt oracle.compression height (readBuffer state 256 32) path := by
  induction path generalizing state address height with
  | nil => simp [checkPathLoop, check_evaluation_pure, climbAt]
  | cons pair rest ih =>
    rcases pair with ⟨right, sibling⟩
    have input := check_path_input state address scratch pointer aligned above (by simp only [List.length_cons] at bounded; omega)
    have headData := data 0 (by simp)
    have headDirection := directions 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at headData headDirection
    simp only [headData, low_bit_zero, headDirection] at input
    let answer := if right then
      combine oracle.compression sibling (readBuffer state 256 32)
      else combine oracle.compression (readBuffer state 256 32) sibling
    let next := checkPathStepState state answer
    have registers := check_path_step_registers state answer
    have nextScratch : next.getReg .x21 = 256 := registers.2.2.2.trans scratch
    have nextPointer : next.getReg .x25 = BitVec.ofNat 64 (address + 32) := by
      rw [show next.getReg .x25 = state.getReg .x25 + 32 from registers.1, pointer, BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < rest.length) :
        readBuffer next (address + 32 + 32*i) 32 = (rest[i]'hi).2 := by
      have memory : readBuffer next (address + 32 + 32*i) 32 =
          readBuffer state (address + 32 + 32*i) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro word hw
        apply check_path_step_outside _ _ _ scratch
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by simp only [List.length_cons] at bounded; omega : address + 32 + 32*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 32 + 32*i = address + 32*(i+1) by omega]
      exact data (i+1) (by simp; omega)
    have nextDirections (i : Nat) (hi : i < rest.length) :
        (next.getReg .x20).getLsbD i = (rest[i]'hi).1 := by
      rw [show next.getReg .x20 = state.getReg .x20 >>> 1 from registers.2.1,
        BitVec.getLsbD_ushiftRight]
      rw [show 1 + i = i + 1 by omega]
      exact directions (i+1) (by simp; omega)
    have nextMasks (i : Nat) (hi : i < rest.length) :
        (next.getReg .x9).getLsbD i = decide (CutHeight (height + 1 + i + 1)) := by
      rw [show next.getReg .x9 = state.getReg .x9 >>> 1 from check_path_step_x9 state answer,
        BitVec.getLsbD_ushiftRight, show 1 + i = i + 1 by omega,
        show height + 1 + i + 1 = height + (i+1) + 1 by omega]
      exact masks (i+1) (by simp; omega)
    have headMask : (state.getReg .x9).getLsbD 0 = decide (CutHeight (height + 1)) := by
      simpa using masks 0 (by simp)
    have induction := ih next (address+32) (height+1) nextScratch nextPointer (by omega) (by omega)
      (by simp only [List.length_cons] at bounded; omega) nextData nextDirections nextMasks
    rw [List.length_cons, checkPathLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (checkPathLoop
      (checkPathStepState state (oracle.compression (padInput (readBuffer (checkPathPreparedState state) 256 64))))
      rest.length)).1 256 32 = _
    rw [input]
    cases right <;>
      change readBuffer (checkEvaluation oracle (checkPathLoop next rest.length)).1 256 32 = _
    all_goals
      rw [induction, check_path_step_digest, tcomp_digest_cut state (height+1) _ headMask]
      simp only [answer, climbAt_cons, climbStep, Bool.false_eq_true, ite_false, ite_true]

theorem check_path_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkPathLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [checkPathLoop, check_evaluation_pure]
  | succ count ih =>
    rw [checkPathLoop, check_evaluation_public_bind]
    let answer := oracle.compression (padInput (readBuffer (checkPathPreparedState state) 256 64))
    change (checkEvaluation oracle (checkPathLoop (checkPathStepState state answer) count)).1.getMem address = _
    have nextScratch : (checkPathStepState state answer).getReg .x21 = 256 :=
      (check_path_step_registers state answer).2.2.2.trans scratch
    rw [ih _ nextScratch]
    exact check_path_step_outside state answer address scratch outside

end CommitGolfCandidate.Late.Check.Normal
