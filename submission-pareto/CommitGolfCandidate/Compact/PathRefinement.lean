import CommitGolfCandidate.NonceBits
import CommitGolfCandidate.Compact.NonceMemory
import CommitGolfCandidate.Compact.Programs
import CommitGolfCandidate.Compact.LeafRefinement
import CommitGolfCandidate.Compact.CheckPath

/-! The checker prepares and hashes each Merkle sibling in the reference order. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem nonce_pad_concat (a b c : Word) :
    (((0#64++c)++b)++a : BitVec 256)=expandNonce192 ((c++b)++a) := by
  exact nonce_bits_pad_concat a b c

private def copyBlock (state : MachineState) (source : Reg) (offset : Nat) (nonce : Prop := False) [Decidable nonce] : MachineState :=
  ([.LD .x6 source 0, .SD .x21 .x6 (BitVec.ofNat 12 offset),
    .LD .x6 source 8, .SD .x21 .x6 (BitVec.ofNat 12 (offset+8)),
    .LD .x6 source 16, .SD .x21 .x6 (BitVec.ofNat 12 (offset+16)),
    (if nonce then .ADDI .x6 .x0 0 else .LD .x6 source 24), .SD .x21 .x6 (BitVec.ofNat 12 (offset+24))] : List Instr).foldl execInstrBr state

private theorem copy_block_false (state : MachineState) (source : Reg) (offset : Nat)
    (nonce : Prop) [Decidable nonce] (negative : ¬nonce) :
    copyBlock state source offset nonce=copyBlock state source offset False := by
  simp only [copyBlock,if_neg negative,ite_false]

private theorem copy_block_true (state : MachineState) (source : Reg) (offset : Nat)
    (nonce : Prop) [Decidable nonce] (positive : nonce) :
    copyBlock state source offset nonce=copyBlock state source offset True := by
  simp only [copyBlock,if_pos positive,ite_true]

private theorem register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

private theorem path_copy_eq (state : MachineState) (start : Nat) :
    checkPathCopyState state start =
      copyBlock state (if start = 31 then .x21 else .x25)
        (if start = 39 ∨ start = 15 then 0 else 32) (start=15) := rfl

private theorem path_copy_31 (state : MachineState) :
    checkPathCopyState state 31=copyBlock state .x21 32 := by
  rw [path_copy_eq,copy_block_false _ _ _ (31=15) (by decide)]
  rfl

private theorem path_copy_39 (state : MachineState) :
    checkPathCopyState state 39=copyBlock state .x25 0 := by
  rw [path_copy_eq,copy_block_false _ _ _ (39=15) (by decide)]
  rfl

private theorem path_copy_48 (state : MachineState) :
    checkPathCopyState state 48=copyBlock state .x25 32 := by
  rw [path_copy_eq,copy_block_false _ _ _ (48=15) (by decide)]
  rfl

private theorem path_copy_15 (state : MachineState) :
    checkPathCopyState state 15=copyBlock state .x25 0 True := by
  rw [path_copy_eq,copy_block_true _ _ _ (15=15) (by decide)]
  rfl

set_option maxHeartbeats 2000000 in
private theorem copy_block_word (state : MachineState) (source : Reg) (offset word : Nat)
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

private theorem copy_block_outside (state : MachineState) (source : Reg) (offset : Nat)
    (address : Word) (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+offset+8*i))
    (nonce : Prop := False) [Decidable nonce] :
    (copyBlock state source offset nonce).getMem address = state.getMem address := by
  have disjoint : ∀ i : Fin 4, address ≠ BitVec.ofNat 64 (256+offset+8*i.val) :=
    fun i => outside i i.isLt
  by_cases padded : nonce <;> rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul] at disjoint <;>
    simp only [copyBlock, padded, ↓reduceIte, List.foldl, execInstrBr, signExtend12] <;>
    simp [register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

private theorem copy_block_digest (state : MachineState) (source : Reg) (offset : Nat)
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

private theorem copy_block_register (state : MachineState) (source : Reg) (offset : Nat)
    (reg : Reg) (notTemp : reg ≠ .x6) :
    (copyBlock state source offset).getReg reg = state.getReg reg := by
  simp [copyBlock, List.foldl, execInstrBr, register_set_mem, Ne.symm notTemp,
    MachineState.getReg_setReg_ne]

/-- Reads of a digest outside the copied half remain unchanged. -/
private theorem copy_block_preserves (state : MachineState) (source : Reg) (offset address : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (outside : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (address+8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (copyBlock state source offset) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  exact copy_block_outside state source offset _ notTemp offsets scratch (outside i hi)

private theorem nonce_copy_word (state : MachineState) (word : Nat) (bounded : word<4)
    (scratch : state.getReg .x21=256)
    (separated : ∀ i<3,∀ j<4,state.getReg .x25+BitVec.ofNat 64 (8*i)≠
      BitVec.ofNat 64 (256+8*j)) :
    (copyBlock state .x25 0 True).getMem (BitVec.ofNat 64 (256+8*word))=
      if word<3 then state.getMem (state.getReg .x25+BitVec.ofNat 64 (8*word)) else 0 := by
  have disjoint : ∀ i : Fin 3,∀ j : Fin 4,state.getReg .x25+BitVec.ofNat 64 (8*i.val)≠
      BitVec.ofNat 64 (256+8*j.val) := fun i j => separated i i.isLt j j.isLt
  simp only [Fin.forall_fin_succ,Fin.val_zero,Fin.val_succ,Nat.reduceAdd,Nat.reduceMul,
    BitVec.add_zero] at disjoint
  interval_cases word <;>
    simp [copyBlock,List.foldl,execInstrBr,signExtend12,register_set_mem,scratch,disjoint,
      MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq] <;> rfl

attribute [local irreducible] copyBlock

set_option maxHeartbeats 2000000 in
/-- The prepared syscall hashes (node,sibling) for a left child and (sibling,node)
for a right child, exactly as the reference Merkle path does. -/
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
  · rw [checkPathPreparedState, if_pos left, if_pos left, path_copy_48]
    change readBuffer (copyBlock branch .x25 32) 256 64 = _
    rw [read_compression_halves _ _ (by decide)]
    have high := copy_block_digest branch .x25 32 (by decide) (Or.inr rfl)
      branchScratch (by simpa [pointerNat] using aligned) (separate 32 (Or.inr rfl))
    have low := copy_block_preserves branch .x25 32 256 (by decide) (Or.inr rfl)
      branchScratch (by decide) lowHigh
    rw [high, low, pointerNat]
    rfl
  · rw [checkPathPreparedState, if_neg left, if_neg left, path_copy_39, path_copy_31]
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

/-- A path step leaves its oracle reply as the next node digest. -/
theorem check_path_step_digest (state : MachineState) (answer : Digest) :
    readBuffer (checkPathStepState state answer) 256 32 = answer := by
  change readBuffer (checkCompressionState (checkPathPreparedState state) answer) 256 32 = answer
  exact check_compression_digest _ _

/-- Path preparation and hashing preserve the unread proof above scratch. -/
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
  · rw [path_copy_48]
    change (copyBlock (checkPathBranchState state) .x25 32).getMem address = _
    rw [copy_block_outside _ .x25 32 _ (by decide) (Or.inr rfl) branchScratch upper]
    rfl
  · rw [MachineState.getMem_setPC, path_copy_39,path_copy_31]
    change (copyBlock (copyBlock (checkPathBranchState state) .x21 32) .x25 0).getMem address = _
    have movedScratch : (copyBlock (checkPathBranchState state) .x21 32).getReg .x21 = 256 :=
      (copy_block_register _ _ _ _ (by decide)).trans branchScratch
    rw [copy_block_outside _ .x25 0 _ (by decide) (Or.inl rfl) movedScratch lower,
      copy_block_outside _ .x21 32 _ (by decide) (Or.inr rfl) branchScratch upper]
    rfl

private theorem low_bit_zero (index : Word) :
    (index &&& 1 = 0) ↔ index.getLsbD 0 = false := by
  change (index &&& 1#64 = 0#64) ↔ _
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : index.getLsbD 0 <;> simp [BitVec.ofBool]

attribute [local irreducible] checkPathStepState checkPathPreparedState checkPathLoop checkEvaluation

set_option maxHeartbeats 2000000 in
/-- The complete authentication-path machine loop computes `climb`, including
all position-dependent left/right choices and preservation of unread siblings. -/
theorem check_path_loop_digest (oracle : Oracle) (state : MachineState)
    (address : Nat) (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * path.length < 2^64)
    (data : ∀ i (hi : i < path.length), readBuffer state (address + 32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length), (state.getReg .x20).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle (checkPathLoop state path.length)).1 256 32 =
      climb oracle.compression (readBuffer state 256 32) path := by
  induction path generalizing state address with
  | nil => simp [checkPathLoop, check_evaluation_pure, climb]
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
    have induction := ih next (address+32) nextScratch nextPointer (by omega) (by omega)
      (by simp only [List.length_cons] at bounded; omega) nextData nextDirections
    rw [List.length_cons, checkPathLoop, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (checkPathLoop
      (checkPathStepState state (oracle.compression (readBuffer (checkPathPreparedState state) 256 64)))
      rest.length)).1 256 32 = _
    rw [input]
    cases right <;>
      change readBuffer (checkEvaluation oracle (checkPathLoop next rest.length)).1 256 32 = _
    all_goals
      rw [induction, check_path_step_digest]
      simp only [answer, climb, List.foldl_cons, Bool.false_eq_true, ite_false, ite_true]

/-- Copying the proof salt initializes the hash accumulator to that exact digest. -/
theorem check_salt_copy_digest (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address%8 = 0) (above : 320 ≤ address) (bounded : address+32 < 2^64) :
    readBuffer (checkPathCopyState state 15) 256 32 = expandNonce192 (readBuffer state address 24) := by
  have pointerNat : (state.getReg .x25).toNat = address := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have separated : ∀ i < 4, ∀ j < 4,
      state.getReg .x25 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+0+8*j) := by
    intro i hi j hj equal
    have natural := congrArg BitVec.toNat equal
    rw [pointer, ← BitVec.ofNat_add] at natural
    simp only [BitVec.toNat_ofNat] at natural
    rw [Nat.mod_eq_of_lt (by omega : address+8*i < 2^64),
      Nat.mod_eq_of_lt (by omega : 256+0+8*j < 2^64)] at natural
    omega
  rw [path_copy_15]
  change readBuffer (copyBlock state .x25 0 True) 256 32 = _
  rw [read_digest_words _ _ (by decide),read_nonce_words _ _ aligned]
  have words (word : Nat) (inside : word<4) := nonce_copy_word state word inside scratch
    (fun i hi j hj => by simpa using separated i (by omega) j hj)
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  simp only [Nat.reduceMul,Nat.reduceAdd,BitVec.add_zero,ite_true,ite_false] at w0 w1 w2 w3
  rw [w0,w1,w2,w3]
  simp only [pointer,←BitVec.ofNat_add]
  exact nonce_pad_concat _ _ _

/-- Salt copying changes only the four words of the low scratch half. -/
theorem check_salt_copy_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkPathCopyState state 15).getMem address = state.getMem address := by
  rw [path_copy_15]
  exact copy_block_outside state .x25 0 address (by decide) (Or.inl rfl) scratch outside True

/-- The entire authentication path preserves input and output buffers outside scratch. -/
theorem check_path_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkPathLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [checkPathLoop, check_evaluation_pure]
  | succ count ih =>
    rw [checkPathLoop, check_evaluation_public_bind]
    let answer := oracle.compression (readBuffer (checkPathPreparedState state) 256 64)
    change (checkEvaluation oracle (checkPathLoop (checkPathStepState state answer) count)).1.getMem address = _
    have nextScratch : (checkPathStepState state answer).getReg .x21 = 256 :=
      (check_path_step_registers state answer).2.2.2.trans scratch
    rw [ih _ nextScratch]
    exact check_path_step_outside state answer address scratch outside

end CommitGolfCandidate.Compact
