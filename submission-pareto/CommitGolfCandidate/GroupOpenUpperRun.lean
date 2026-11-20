import CommitGolfCandidate.GroupOpenFoldRun

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
set_option maxRecDepth 18000

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

/-! ### Levels 0..12 -/

def lowerRun (level : Nat) : Nat → MachineState → MachineState
  | 0, state => state
  | left+1, state =>
    if live : level < 14 then lowerRun (level+1) left (siblingBlock ⟨level,live⟩ state) else state

def lowerCost (ordinal level : Nat) : Nat → Nat
  | 0 => 0
  | left+1 => siblingCost ordinal level+lowerCost ordinal (level+1) left

theorem lower_total_cost (ordinal : Nat) : lowerCost ordinal 0 13 = 65+levelCopies ordinal+recordCopyCost ordinal := by
  simp [lowerCost, siblingCost, levelCopies]
  omega

theorem destination_mono (ordinal : Nat) : Monotone (siblingDestination ordinal) := by
  intro a b le
  unfold siblingDestination
  have := sibling_offset_mono le
  omega

theorem field_outside {before after : MachineState} {source dest size : Nat}
    (copy : ByteCopy before after source dest size) (address : Nat)
    (fit : address < 2^64) (endFit : dest+size ≤ 2^64)
    (outside : address < dest ∨ dest+size ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  apply copy.frame
  intro i inside equal
  have same := Opening.nat_address_injective fit (by omega) equal
  omega

structure LowerTrace (before after : MachineState) (index : Index) (ordinal first count : Nat) : Prop where
  run : RunsOpeningBlock before after (lowerCost ordinal first count)
  next : LowerCursor after index ordinal (first+count)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 → reg ≠ .x29 →
    after.getReg reg = before.getReg reg
  input : ∀ address < proofBase,
    after.getMem (BitVec.ofNat 64 address) = before.getMem (BitVec.ofNat 64 address)
  frame : ∀ address < 2^64,
    address < siblingDestination ordinal first ∨ siblingDestination ordinal (first+count) ≤ address →
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address)
  fields : ∀ level, first ≤ level → level < first+count → ∀ byte < siblingWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      before.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))

theorem execute_lower (state : MachineState) (index : Index) (ordinal first count : Nat)
    (ordinalBound : ordinal < LENGTH) (limit : first+count ≤ 13)
    (cursor : LowerCursor state index ordinal first) :
    LowerTrace state (lowerRun first count state) index ordinal first count := by
  induction count generalizing first state with
  | zero =>
    refine ⟨?_, by simpa only [lowerRun, Nat.add_zero] using cursor, ?_, ?_, ?_, ?_⟩
    · intro fuel coins
      simp [lowerCost, lowerRun, Execution.charge]
    · intros
      rfl
    · intros
      rfl
    · intros
      rfl
    · intro level lower upper
      omega
  | succ count ih =>
    have live : first < 14 := by omega
    let level : Fin 14 := ⟨first,live⟩
    let middle := siblingBlock level state
    have step := execute_sibling state index ordinal ordinalBound level (by simp [level]; omega) cursor
    have rest := ih middle (first+1) (by omega) step.next
    have total : first+(count+1) = first+1+count := by omega
    have width : siblingDestination ordinal (first+1) =
        siblingDestination ordinal first+siblingWidth first := by
      simp only [siblingDestination, sibling_offset_next first live, Nat.add_assoc]
    have levels := destination_mono ordinal
    have endFit := all_record_ends_fit ordinal ordinalBound
    have within (l : Nat) (hl : l ≤ 14) : siblingDestination ordinal l ≤ MEMORY_BYTES := by
      exact (levels hl).trans ((record_end ordinal).le.trans endFit)
    have ram : MEMORY_BYTES < 2^64 := by decide
    have writeEnd := within (first+1) (by omega)
    have writeFit : siblingDestination ordinal first+siblingWidth first ≤ 2^64 := by omega
    have data : ByteCopy state middle (siblingAddress index first) (siblingDestination ordinal first)
        (siblingWidth first) := step.bytes
    simp only [lowerRun, dite_eq_left live]
    refine ⟨?_, by rw [total]; exact rest.next,
      fun reg a b c d e => (rest.register reg a b c d e).trans (step.register reg a b c d e),
      fun address below => (rest.input address below).trans (step.input address below), ?_, ?_⟩
    · have cost : lowerCost ordinal first (count+1) = siblingCost ordinal first+lowerCost ordinal (first+1) count := rfl
      rw [cost]
      exact step.run.next rest.run
    · intro address fit outside
      rw [total] at outside
      have firstBelow := levels (show first ≤ first+1 by omega)
      have nextBelow := levels (show first+1 ≤ first+1+count by omega)
      exact (rest.frame address fit (outside.imp (by omega) id)).trans
        (field_outside data address fit writeFit (outside.imp id (by omega)))
    · intro l low hi byte valid
      by_cases initial : l = first
      · subst l
        have left : siblingDestination ordinal first+byte < siblingDestination ordinal (first+1) := by omega
        exact (rest.frame _ (by omega) (Or.inl left)).trans (data.copied byte valid)
      · have later := rest.fields l (by omega) (by omega) byte valid
        have inputBefore : siblingAddress index l+byte < siblingDestination ordinal first := by
          have srcBound := upper_swap_bound index l
          have heapEnd := heap_before_nonces
          have nonceEnd := nonces_end_at_indices
          have order := indices_before_records
          have small := sibling_width_le l
          have start := sibling_offset_start first
          unfold siblingAddress siblingDestination recordBase
          omega
        exact later.trans (field_outside data _ (by omega) writeFit (Or.inl inputBefore))

/-! ### Level 13 and the record fold -/

def lastHead : List (Nat × Instr) :=
  [(638, .LHU .x31 .x7 28), (639, .JAL .x0 (BitVec.ofNat 21 (4*(foldStart-639))))]

def lastTail : List (Nat × Instr) :=
  [(foldStart+34, .JAL .x0 (BitVec.ofNat 21 (2^21-4*(foldStart+34-640)))), (640, .ADDI .x21 .x21 28),
   (641, .SRLI .x6 .x6 1)]

theorem last_head_code : RowsCode lastHead := by decide +kernel
theorem last_tail_code : RowsCode lastTail := by decide +kernel
theorem last_head_next : rowNext lastHead[1] = BitVec.ofNat 64 (4096+4*foldStart) := by decide +kernel
theorem last_tail_next : rowNext lastTail[2] = BitVec.ofNat 64 (4096+4*642) := by decide +kernel

/-- Level 13: head, 14 halfwords, `lhu x31,28(x7)` (the top halfword of the last packed node), the fold of
its 14 high bits into slots 0..6 of the packed block, `addi x21,x21,28; srli x6,x6,1`. -/
def lastCopy (state : MachineState) : MachineState := Writer28.state (headPrefix state 3)
def lastLoaded (state : MachineState) : MachineState := rowsState (lastCopy state) lastHead 2
def lastFolded (state : MachineState) : MachineState := foldUpTo foldStart 7 (lastLoaded state)
def lastLevel (state : MachineState) : MachineState := rowsState (lastFolded state) lastTail 3

/-- The level-13 head rows for any jump immediate (kept abstract so `simp` does not evaluate it). -/
def lastHeadShape (state : MachineState) (j : BitVec 21) : MachineState :=
  execInstrBr (execInstrBr state (.LHU .x31 .x7 28)) (.JAL .x0 j)

theorem last_head_unfold (state : MachineState) :
    rowsState state lastHead 2 = lastHeadShape state (BitVec.ofNat 21 (4*(foldStart-639))) := rfl

theorem last_head_shape (state : MachineState) (j : BitVec 21) :
    (lastHeadShape state j).mem = state.mem ∧
    (lastHeadShape state j).getReg .x31 = (state.getHalfword (state.getReg .x7 + signExtend12 28)).zeroExtend 64 ∧
    ∀ reg, reg ≠ .x31 → (lastHeadShape state j).getReg reg = state.getReg reg := by
  unfold lastHeadShape
  refine ⟨?_, ?_, ?_⟩
  · simp [execInstrBr]
  · simp [execInstrBr]
  · intro reg a
    simp [execInstrBr, Ne.symm a]

/-- The level-13 tail rows (`jal <640>; addi x21,x21,28; srli x6,x6,1`) for any jump immediate. -/
def lastTailShape (state : MachineState) (j : BitVec 21) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr state (.JAL .x0 j)) (.ADDI .x21 .x21 28)) (.SRLI .x6 .x6 1)

theorem last_tail_unfold (state : MachineState) :
    rowsState state lastTail 3 = lastTailShape state (BitVec.ofNat 21 (2^21-4*(foldStart+34-640))) := rfl

theorem last_tail_shape (state : MachineState) (j : BitVec 21) :
    (lastTailShape state j).mem = state.mem ∧
    (lastTailShape state j).getReg .x21 = state.getReg .x21 + 28#64 ∧
    (lastTailShape state j).getReg .x6 = state.getReg .x6 >>> 1 ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x6 → (lastTailShape state j).getReg reg = state.getReg reg := by
  unfold lastTailShape
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [execInstrBr]
  · simp [execInstrBr, signExtend12]
  · simp [execInstrBr]
  · intro reg a b
    simp [execInstrBr, Ne.symm a, Ne.symm b]

/-- Dword alignment as a number, for every address (no headroom needed). -/
private theorem align_nat_full (q : Nat) (fit : q < 2^64) :
    (alignToDword (BitVec.ofNat 64 q)).toNat = q - q % 8 := by
  let word : Word := BitVec.ofNat 64 q
  have wordAsNat : word.toNat = q := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  have offset : byteOffset word = q % 8 := byte_offset_nat q fit
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  have lt := (alignToDword word).isLt
  change ((alignToDword word)+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, offset, Nat.mod_eq_of_lt (by omega : q % 8 < 2^64)] at whole
  change (alignToDword word).toNat = _
  omega

structure LastTrace (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state (lastLevel state) (42+lastCopyCost ordinal)
  next : LowerCursor (lastLevel state) index ordinal 14
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x28 → reg ≠ .x29 → reg ≠ .x31 →
    (lastLevel state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (lastLevel state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)
  copied : ∀ byte < 28, (lastLevel state).getByte (BitVec.ofNat 64 (siblingDestination ordinal 13+byte)) =
    state.getByte (BitVec.ofNat 64 (siblingAddress index 13+byte))
  folds : ∀ k < 7, ∀ b < 2,
    (lastLevel state).getByte (BitVec.ofNat 64 (siblingDestination ordinal (6+k)+28+b)) =
      (foldValue (state.getHalfword (BitVec.ofNat 64 (siblingDestination ordinal (6+k)+28)))
        ((state.getHalfword (BitVec.ofNat 64 (siblingAddress index 13+28))).zeroExtend 64 >>> (2*k))).extractLsb' (8*b) 8
  frame : ∀ address < 2^64,
    (address < siblingDestination ordinal 13 ∨ siblingDestination ordinal 14 ≤ address) →
    (∀ k < 7, address ≠ siblingDestination ordinal (6+k)+28 ∧ address ≠ siblingDestination ordinal (6+k)+29) →
    (lastLevel state).getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address)

private theorem fold_codes : ∀ j < 7, RowsCode (foldIterRows foldStart j) :=
  fun j inside => (fold_iter_code ⟨j, inside⟩).1

theorem execute_last (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (cursor : LowerCursor state index ordinal 13) : LastTrace state index ordinal := by
  let level : Fin 14 := 13
  let site := siblingSite level
  let prepared := headPrefix state 3
  let copied := lastCopy state
  let loaded := lastLoaded state
  let folded := lastFolded state
  have ram : MEMORY_BYTES < 2^64 := by decide
  have ramv : MEMORY_BYTES = 68719476736 := rfl
  have o13 : siblingOffset 13 = 506 := rfl
  have head := sibling_head_post state
  have ordinalFit := all_sibling_copies_fit index ordinal 13 bounded (by decide)
  have start : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level) := cursor.pc
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*site.start) := by
    rw [head.1, start]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 12 = _
    rw [← BitVec.ofNat_add, ← sibling_copy_start level]
    congr 1
  let src := siblingAddress index 13
  let dst := siblingDestination ordinal 13
  have srcReg : prepared.getReg .x7 = BitVec.ofNat 64 src :=
    physical_sibling_source state index _ cursor.heap cursor.node
  have dstReg : prepared.getReg .x21 = BitVec.ofNat 64 dst :=
    (head.2.2.2 .x21 (by decide)).trans cursor.dest
  have width13 : siblingWidth 13 = 28 := rfl
  have sa : src%8=0 := by
    unfold src siblingAddress
    have : trapdoorBase%8=0 := by decide
    omega
  have field := Writer28.copy prepared src dst before srcReg dstReg sa ordinalFit.2.1
    (by have := ordinalFit.2.2.1; rw [width13] at this; exact this)
    (by have := ordinalFit.2.2.2; rw [width13] at this; exact this)
  have copyPC : copied.pc = BitVec.ofNat 64 (4096+4*638) := field.pc
  have keptCopy (reg : Reg) (d : reg ≠ .x31) (b : reg ≠ .x7) : copied.getReg reg = state.getReg reg :=
    (field.regs reg d).trans (head.2.2.2 reg b)
  have srcCopied : copied.getReg .x7 = BitVec.ofNat 64 src :=
    (field.regs .x7 (by decide)).trans srcReg
  have dstCopied : copied.getReg .x21 = BitVec.ofNat 64 dst :=
    (field.regs .x21 (by decide)).trans dstReg
  -- the head rows: lhu x31,28(x7); jal F
  have headStart : ∀ h : 0 < lastHead.length, copied.pc = BitVec.ofNat 64 (4096+4*lastHead[0].1) := fun _ => copyPC
  have srcHalfFit : src+28+2 ≤ MEMORY_BYTES := by have := ordinalFit.2.2.1; have := ordinalFit.2.2.2; omega
  have srcEven : (src+28) % 2 = 0 := by have := ordinalFit.1; omega
  have ranLoad : RunsOpeningBlock copied loaded 2 := fun fuel coins =>
    execute_rows copied lastHead last_head_code headStart (by
      intro i inside
      have small : i < 2 := inside
      interval_cases i
      · change accessValid (copied.getReg .x7 + signExtend12 28) 2 = true
        rw [srcCopied, show signExtend12 (28 : BitVec 12) = BitVec.ofNat 64 28 by decide, ← BitVec.ofNat_add]
        exact half_access _ srcEven srcHalfFit
      · rfl) fuel coins
  have loadPC : loaded.pc = BitVec.ofNat 64 (4096+4*foldStart) :=
    (rows_after_pc copied lastHead last_head_code headStart 1 rfl).trans last_head_next
  have loadMem : loaded.mem = copied.mem :=
    (last_head_shape copied (BitVec.ofNat 21 (4*(foldStart-639)))).1
  let x := copied.getHalfword (BitVec.ofNat 64 (src+28))
  have loadTop : loaded.getReg .x31 = x.zeroExtend 64 := by
    have top : loaded.getReg .x31 = (copied.getHalfword (copied.getReg .x7 + signExtend12 28)).zeroExtend 64 :=
      (last_head_shape copied (BitVec.ofNat 21 (4*(foldStart-639)))).2.1
    rw [top, srcCopied, show signExtend12 (28 : BitVec 12) = BitVec.ofNat 64 28 by decide, ← BitVec.ofNat_add]
  have loadReg (reg : Reg) (a : reg ≠ .x31) : loaded.getReg reg = copied.getReg reg :=
    (last_head_shape copied (BitVec.ofNat 21 (4*(foldStart-639)))).2.2 reg a
  have dstAbove : proofBase + 506 ≤ dst := by
    show proofBase + 506 ≤ proofBase + recordBytes*ordinal + siblingOffset 13
    rw [o13]; omega
  have dstLow : 182 ≤ dst := by omega
  have dstFit : dst+8 ≤ MEMORY_BYTES := by
    have := ordinalFit.2.2.2; rw [width13] at this; omega
  have dstEven : dst % 2 = 0 := ordinalFit.2.1
  have loadDst : loaded.getReg .x21 = BitVec.ofNat 64 dst := (loadReg .x21 (by decide)).trans dstCopied
  obtain ⟨ranFold, foldPC, foldDst, -, foldKeep, -, -⟩ :=
    fold_up_to foldStart fold_codes loaded dst x dstLow (by omega) dstEven loadPC loadDst loadTop 7 (by omega)
  have foldWords7 : foldWords 7 = 34 := rfl
  rw [foldWords7] at ranFold foldPC
  have foldKeep' : ∀ reg, reg ≠ .x28 → reg ≠ .x29 → reg ≠ .x31 → folded.getReg reg = loaded.getReg reg := foldKeep
  have foldDst' : folded.getReg .x21 = BitVec.ofNat 64 dst := foldDst
  have tailStart : ∀ h : 0 < lastTail.length, folded.pc = BitVec.ofNat 64 (4096+4*lastTail[0].1) := fun _ => foldPC
  have ranTail : RunsOpeningBlock folded (lastLevel state) 3 := fun fuel coins =>
    execute_rows folded lastTail last_tail_code tailStart (by
      intro i inside
      have small : i < 3 := inside
      interval_cases i <;> rfl) fuel coins
  have tailPC : (lastLevel state).pc = BitVec.ofNat 64 (4096+4*642) :=
    (rows_after_pc folded lastTail last_tail_code tailStart 2 rfl).trans last_tail_next
  have tailMem : (lastLevel state).mem = folded.mem :=
    (last_tail_shape folded (BitVec.ofNat 21 (2^21-4*(foldStart+34-640)))).1
  have tailReg (reg : Reg) (a : reg ≠ .x21) (b : reg ≠ .x6) : (lastLevel state).getReg reg = folded.getReg reg :=
    (last_tail_shape folded (BitVec.ofNat 21 (2^21-4*(foldStart+34-640)))).2.2.2 reg a b
  have tail21 : (lastLevel state).getReg .x21 = folded.getReg .x21 + 28#64 :=
    (last_tail_shape folded (BitVec.ofNat 21 (2^21-4*(foldStart+34-640)))).2.1
  have tail6 : (lastLevel state).getReg .x6 = folded.getReg .x6 >>> 1 :=
    (last_tail_shape folded (BitVec.ofNat 21 (2^21-4*(foldStart+34-640)))).2.2.1
  -- bytes of the copy
  have copiedBytes : ByteCopy state copied src dst 28 := by
    exact field.bytes.move head.2.1.symm rfl
  have copiedInput (address : Nat) (below : address < proofBase) :
      copied.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
    have above : proofBase ≤ dst := by unfold dst siblingDestination recordBase; omega
    have stable := field.below (BitVec.ofNat 64 address) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address<2^64)]
      have aligned : proofBase%8=0 := by decide
      omega)
    have reads : prepared.mem = state.mem := head.2.1
    show (Writer28.state prepared).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)
    simpa only [MachineState.getMem, reads] using stable
  -- the fold slots
  have slotAt (k : Nat) (inside : k < 7) : foldAddress dst k = siblingDestination ordinal (6+k)+28 := by
    have := fold_slot_offset ordinal k inside
    unfold foldAddress dst
    omega
  have finalByte (q : Nat) : (lastLevel state).getByte (BitVec.ofNat 64 q) = folded.getByte (BitVec.ofNat 64 q) := by
    unfold MachineState.getByte; rw [show (lastLevel state).getMem = folded.getMem from by
      funext w; exact congrFun tailMem w]
  have loadedByte (q : Nat) : loaded.getByte (BitVec.ofNat 64 q) = copied.getByte (BitVec.ofNat 64 q) := by
    unfold MachineState.getByte; rw [show loaded.getMem = copied.getMem from by funext w; exact congrFun loadMem w]
  have loadedHalf (q : Nat) : loaded.getHalfword (BitVec.ofNat 64 q) = copied.getHalfword (BitVec.ofNat 64 q) := by
    unfold MachineState.getHalfword; rw [show loaded.getMem = copied.getMem from by funext w; exact congrFun loadMem w]
  have frameFold (q : Nat) (qfit : q+8 ≤ 2^64) (away : ∀ j < 7, q ≠ foldAddress dst j ∧ q ≠ foldAddress dst j+1) :
      folded.getByte (BitVec.ofNat 64 q) = loaded.getByte (BitVec.ofNat 64 q) :=
    fold_frame_bytes foldStart fold_codes loaded dst x dstLow dstFit dstEven loadPC loadDst loadTop q qfit away
  have foldFrame : ∀ w, (∀ j < 7, w ≠ alignToDword (BitVec.ofNat 64 (foldAddress dst j))) →
      folded.getMem w = loaded.getMem w :=
    (fold_up_to foldStart fold_codes loaded dst x dstLow (by omega) dstEven loadPC loadDst loadTop
      7 (by omega)).2.2.2.2.2.1
  have frameAll (q : Nat) (qfit : q < 2^64) (away : ∀ j < 7, q ≠ foldAddress dst j ∧ q ≠ foldAddress dst j+1) :
      folded.getByte (BitVec.ofNat 64 q) = loaded.getByte (BitVec.ofNat 64 q) := by
    by_cases low : q+8 ≤ 2^64
    · exact frameFold q low away
    · apply byte_of_dword
      apply foldFrame
      intro j hj same
      have small : foldAddress dst j < 2^36 := by unfold foldAddress; omega
      have a1 := align_nat_full q qfit
      have a2 := align_nat (foldAddress dst j) (by omega)
      rw [same] at a1
      omega
  have srcBelow : src+32 ≤ dst := by
    have a := upper_swap_bound index 13
    have b := heap_before_nonces
    have c := nonces_end_at_indices
    have d := indices_before_records
    unfold src dst siblingAddress siblingDestination recordBase
    have := sibling_offset_start 13
    omega
  have xState : x = state.getHalfword (BitVec.ofNat 64 (src+28)) := by
    apply halfword_of_bytes state copied (src+28) srcEven (by omega)
    · exact field_outside copiedBytes _ (by omega) (by omega) (Or.inl (by omega))
    · exact field_outside copiedBytes _ (by omega) (by omega) (Or.inl (by omega))
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have total := ((((show RunsOpeningBlock state prepared 3 from
      fun fuel coins => execute_sibling_head state level start fuel coins).next field.run).next ranLoad).next
      ranFold).next ranTail
    convert total using 1 <;> simp only [lastCopyCost, dst] <;> omega
  · exact tailPC
  · rw [tailReg .x9 (by decide) (by decide), foldKeep' .x9 (by decide) (by decide) (by decide),
      loadReg .x9 (by decide), keptCopy .x9 (by decide) (by decide)]
    exact cursor.heap
  · rw [tail6, foldKeep' .x6 (by decide) (by decide) (by decide), loadReg .x6 (by decide),
      keptCopy .x6 (by decide) (by decide), cursor.node, node_shift]
  · rw [tail21, foldDst', show (28#64 : Word) = BitVec.ofNat 64 (siblingWidth 13) from rfl,
      destination_next ordinal 13 (by decide)]
  · intro reg a b c d e f
    rw [tailReg reg c a, foldKeep' reg d e f, loadReg reg f, keptCopy reg f b]
  · intro address below
    change (lastLevel state).mem _ = _
    rw [tailMem]
    change folded.getMem _ = _
    rw [foldFrame]
    · change loaded.mem _ = _
      rw [loadMem]
      exact copiedInput address below
    · intro j hj same
      have above := aligned_dword_above proofBase (foldAddress dst j) (by decide)
        (by unfold foldAddress; omega) (by unfold foldAddress; omega)
      rw [← same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)] at above
      omega
  · intro byte inside
    rw [finalByte, frameFold _ (by omega) (fun j hj => by
      have := slotAt j hj; constructor <;> (intro e; have := sibling_offset_start (6+j); unfold dst at e; rw [← slotAt j hj] at *; unfold foldAddress at e; omega)),
      loadedByte]
    exact copiedBytes.copied byte inside
  · intro k inside b small
    rw [finalByte, ← slotAt k inside, show folded = foldUpTo foldStart 7 loaded from rfl]
    rw [fold_slot_bytes foldStart fold_codes loaded dst x dstLow dstFit dstEven loadPC loadDst loadTop k b inside small,
      loadedHalf, xState]
    have same : copied.getHalfword (BitVec.ofNat 64 (foldAddress dst k)) =
        state.getHalfword (BitVec.ofNat 64 (foldAddress dst k)) := by
      apply halfword_of_bytes state copied _ (by unfold foldAddress; omega) (by unfold foldAddress; omega)
      · exact field_outside copiedBytes _ (by unfold foldAddress; omega) (by omega) (Or.inl (by unfold foldAddress; omega))
      · exact field_outside copiedBytes _ (by unfold foldAddress; omega) (by omega) (Or.inl (by unfold foldAddress; omega))
    exact congrArg (fun h => (foldValue h ((state.getHalfword (BitVec.ofNat 64 (src+28))).zeroExtend 64 >>> (2*k))).extractLsb' (8*b) 8) same
  · intro address fit outside away
    have end14 : siblingDestination ordinal 14 = dst+28 := by
      unfold dst siblingDestination siblingOffset; simp
    rw [finalByte, frameAll _ fit (fun j hj => by
        rw [slotAt j hj]; exact ⟨(away j hj).1, by have := (away j hj).2; omega⟩), loadedByte]
    exact field_outside copiedBytes _ fit (by omega) (by rw [end14] at outside; exact outside)

end TwoPermutationPrototype.GroupedOpening
