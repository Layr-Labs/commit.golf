import CommitGolfCandidate.PairControl

import CommitGolfCandidate.PathRefinement

import CommitGolfCandidate.PairHash

namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 1400000

def rec_copyBlock (state : MachineState) (source : Reg) (offset : Nat) : MachineState :=
  ([.LD .x6 source 0, .SD .x21 .x6 (BitVec.ofNat 12 offset),
    .LD .x6 source 8, .SD .x21 .x6 (BitVec.ofNat 12 (offset+8)),
    .LD .x6 source 16, .SD .x21 .x6 (BitVec.ofNat 12 (offset+16)),
    .LD .x6 source 24, .SD .x21 .x6 (BitVec.ofNat 12 (offset+24))] : List Instr).foldl execInstrBr state

theorem rec_register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

theorem rec_path_copy_eq (state : MachineState) (start : Nat) :
    checkPathCopyState state start =
      rec_copyBlock state (if start = 29 then .x21 else .x25)
        (if start = 37 then 0 else 32) := rfl

theorem rec_copy_block_word (state : MachineState) (source : Reg) (offset word : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32) (bounded : word < 4)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg source + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    (rec_copyBlock state source offset).getMem (BitVec.ofNat 64 (256+offset+8*word)) =
      state.getMem (state.getReg source + BitVec.ofNat 64 (8*word)) := by
  have disjoint : ∀ i : Fin 4, ∀ j : Fin 4,
      state.getReg source + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (256+offset+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_zero] at disjoint <;>
    simp only [rec_copyBlock, List.foldl, execInstrBr, signExtend12] <;>
    interval_cases word <;>
    simp [rec_register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem rec_copy_block_outside (state : MachineState) (source : Reg) (offset : Nat)
    (address : Word) (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+offset+8*i)) :
    (rec_copyBlock state source offset).getMem address = state.getMem address := by
  have disjoint : ∀ i : Fin 4, address ≠ BitVec.ofNat 64 (256+offset+8*i.val) :=
    fun i => outside i i.isLt
  rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul] at disjoint <;>
    simp only [rec_copyBlock, List.foldl, execInstrBr, signExtend12] <;>
    simp [rec_register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem rec_copy_block_digest (state : MachineState) (source : Reg) (offset : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : (state.getReg source).toNat % 8 = 0)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg source + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (rec_copyBlock state source offset) (256+offset) 32 =
      readBuffer state (state.getReg source).toNat 32 := by
  rw [read_digest_words _ _ (by rcases offsets with rfl | rfl <;> decide),
    read_digest_words _ _ aligned]
  have w0 := rec_copy_block_word state source offset 0 notTemp offsets (by decide) scratch separated
  have w1 := rec_copy_block_word state source offset 1 notTemp offsets (by decide) scratch separated
  have w2 := rec_copy_block_word state source offset 2 notTemp offsets (by decide) scratch separated
  have w3 := rec_copy_block_word state source offset 3 notTemp offsets (by decide) scratch separated
  simp only [Nat.reduceMul, Nat.add_zero, BitVec.add_zero] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem rec_copy_block_register (state : MachineState) (source : Reg) (offset : Nat)
    (reg : Reg) (notTemp : reg ≠ .x6) :
    (rec_copyBlock state source offset).getReg reg = state.getReg reg := by
  simp [rec_copyBlock, List.foldl, execInstrBr, rec_register_set_mem, Ne.symm notTemp,
    MachineState.getReg_setReg_ne]

theorem rec_copy_block_preserves (state : MachineState) (source : Reg) (offset address : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (outside : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (address+8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (rec_copyBlock state source offset) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  exact rec_copy_block_outside state source offset _ notTemp offsets scratch (outside i hi)

theorem rec_check_path_input (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 32 < 2^64) :
    readBuffer (rec_checkPathPreparedState state) 256 64 =
      if state.getReg .x20 &&& 1 = 0 then
        readBuffer state address 32 ++ readBuffer state 256 32
      else readBuffer state 256 32 ++ readBuffer state address 32 := by
  let branch := rec_checkPathBranchState state
  have branchScratch : branch.getReg .x21 = 256 := by
    simpa [branch, rec_checkPathBranchState, MachineState.getReg_setReg_ne] using scratch
  have branchPointer : branch.getReg .x25 = BitVec.ofNat 64 address := by
    simpa [branch, rec_checkPathBranchState, MachineState.getReg_setReg_ne] using pointer
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
  · rw [rec_checkPathPreparedState, if_pos left, if_pos left, rec_path_copy_eq]
    change readBuffer (rec_copyBlock branch .x25 32) 256 64 = _
    rw [read_compression_halves _ _ (by decide)]
    have high := rec_copy_block_digest branch .x25 32 (by decide) (Or.inr rfl)
      branchScratch (by simpa [pointerNat] using aligned) (separate 32 (Or.inr rfl))
    have low := rec_copy_block_preserves branch .x25 32 256 (by decide) (Or.inr rfl)
      branchScratch (by decide) lowHigh
    rw [high, low, pointerNat]
    rfl
  · rw [rec_checkPathPreparedState, if_neg left, if_neg left, rec_path_copy_eq, rec_path_copy_eq]
    have dropPC (s : MachineState) (pc : Word) : readBuffer (s.setPC pc) 256 64 = readBuffer s 256 64 :=
      read_buffer_memory_congr _ _ rfl _ _
    rw [dropPC]
    let moved := rec_copyBlock branch .x21 32
    change readBuffer (rec_copyBlock moved .x25 0) 256 64 = _
    have movedScratch : moved.getReg .x21 = 256 :=
      (rec_copy_block_register _ _ _ _ (by decide)).trans branchScratch
    have movedPointer : moved.getReg .x25 = branch.getReg .x25 :=
      rec_copy_block_register _ _ _ _ (by decide)
    have saved := rec_copy_block_digest branch .x21 32 (by decide) (Or.inr rfl)
      branchScratch (by rw [branchScratch]; decide)
      (by
        intro i hi j hj
        rw [branchScratch]
        change BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*i) ≠ _
        rw [← BitVec.ofNat_add]
        exact lowHigh i hi j hj)
    have source := rec_copy_block_preserves branch .x21 32 address (by decide) (Or.inr rfl)
      branchScratch aligned (sourceOutside 32 (Or.inr rfl))
    have low := rec_copy_block_digest moved .x25 0 (by decide) (Or.inl rfl) movedScratch
      (by rw [movedPointer, pointerNat]; exact aligned)
      (by rw [movedPointer]; exact separate 0 (Or.inl rfl))
    have high := rec_copy_block_preserves moved .x25 0 288 (by decide) (Or.inl rfl)
      movedScratch (by decide) highLow
    rw [read_compression_halves _ _ (by decide), high, low, movedPointer, pointerNat, source, saved]
    rw [branchScratch]
    rfl

theorem rec_check_path_step_digest (state : MachineState) (answer : Digest) :
    readBuffer (rec_checkPathStepState state answer) 256 32 = answer := by
  change readBuffer (checkCompressionState (rec_checkPathPreparedState state) answer) 256 32 = answer
  exact check_compression_digest _ _

theorem rec_check_path_step_outside (state : MachineState) (answer : Digest)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (rec_checkPathStepState state answer).getMem address = state.getMem address := by
  change (checkCompressionState (rec_checkPathPreparedState state) answer).getMem address = _
  rw [check_compression_memory_outside _ _ _
    ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩]
  have lower : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+0+8*i) :=
    fun i hi => outside i (by omega)
  have upper : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+32+8*i) := by
    intro i hi
    simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      outside (i+4) (by omega)
  have branchScratch : (rec_checkPathBranchState state).getReg .x21 = 256 := by
    simpa [rec_checkPathBranchState, MachineState.getReg_setReg_ne] using scratch
  unfold rec_checkPathPreparedState
  split
  · rw [rec_path_copy_eq]
    change (rec_copyBlock (rec_checkPathBranchState state) .x25 32).getMem address = _
    rw [rec_copy_block_outside _ .x25 32 _ (by decide) (Or.inr rfl) branchScratch upper]
    rfl
  · rw [MachineState.getMem_setPC, rec_path_copy_eq, rec_path_copy_eq]
    change (rec_copyBlock (rec_copyBlock (rec_checkPathBranchState state) .x21 32) .x25 0).getMem address = _
    have movedScratch : (rec_copyBlock (rec_checkPathBranchState state) .x21 32).getReg .x21 = 256 :=
      (rec_copy_block_register _ _ _ _ (by decide)).trans branchScratch
    rw [rec_copy_block_outside _ .x25 0 _ (by decide) (Or.inl rfl) movedScratch lower,
      rec_copy_block_outside _ .x21 32 _ (by decide) (Or.inr rfl) branchScratch upper]
    rfl

theorem rec_low_bit_zero (index : Word) :
    (index &&& 1 = 0) ↔ index.getLsbD 0 = false := by
  change (index &&& 1#64 = 0#64) ↔ _
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : index.getLsbD 0 <;> simp [BitVec.ofBool]

theorem rec_check_path_loop_digest (oracle : Oracle) (state : MachineState)
    (address : Nat) (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * path.length < 2^64)
    (data : ∀ i (hi : i < path.length), readBuffer state (address + 32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length), (state.getReg .x20).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle (rec_checkPathLoop state path.length)).1 256 32 =
      climb oracle.compression (readBuffer state 256 32) path := by
  induction path generalizing state address with
  | nil => simp [rec_checkPathLoop, check_evaluation_pure, climb]
  | cons pair rest ih =>
    rcases pair with ⟨right, sibling⟩
    have input := rec_check_path_input state address scratch pointer aligned above (by simp only [List.length_cons] at bounded; omega)
    have headData := data 0 (by simp)
    have headDirection := directions 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at headData headDirection
    simp only [headData, rec_low_bit_zero, headDirection] at input
    let answer := if right then
      combine oracle.compression sibling (readBuffer state 256 32)
      else combine oracle.compression (readBuffer state 256 32) sibling
    let next := rec_checkPathStepState state answer
    have registers := rec_check_path_step_registers state answer
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
        apply rec_check_path_step_outside _ _ _ scratch
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
    have induction := ih next (address+32) nextScratch nextPointer (by omega) (by omega)
      (by simp only [List.length_cons] at bounded; omega) nextData nextDirections
    rw [List.length_cons, rec_checkPathLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (rec_checkPathLoop
      (rec_checkPathStepState state (oracle.compression (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))
      rest.length)).1 256 32 = _
    rw [input]
    cases right <;>
      change readBuffer (checkEvaluation oracle (rec_checkPathLoop next rest.length)).1 256 32 = _
    all_goals
      rw [induction, rec_check_path_step_digest]
      simp only [answer, climb, List.foldl_cons, Bool.false_eq_true, ite_false, ite_true]

theorem rec_check_path_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (rec_checkPathLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [rec_checkPathLoop, check_evaluation_pure]
  | succ count ih =>
    rw [rec_checkPathLoop, check_evaluation_public_bind]
    let answer := oracle.compression (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))
    change (checkEvaluation oracle (rec_checkPathLoop (rec_checkPathStepState state answer) count)).1.getMem address = _
    have nextScratch : (rec_checkPathStepState state answer).getReg .x21 = 256 :=
      (rec_check_path_step_registers state answer).2.2.2.trans scratch
    rw [ih _ nextScratch]
    exact rec_check_path_step_outside state answer address scratch outside

end CommitGolfCandidate.PairCap
