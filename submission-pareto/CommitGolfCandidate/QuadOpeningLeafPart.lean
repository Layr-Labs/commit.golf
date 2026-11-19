import CommitGolfCandidate.QuadOpeningSiblingRun

/-! The quad leaf part of one opening record (words 37..158, 122 unit cycles): locate the
leaf group of the opened index, copy the three other leaf digests of its quad group in
rotation order `r+1, r+2, r+3 (mod 4)` into the record, and step `x6` to the quad node
`(LENGTH + index) / 4`, where the quad-group part (`QuadOpeningQuadPart`) starts. -/

namespace TwoPermutationPrototype.QuadOpening
set_option maxRecDepth 8192
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open QOpening (trapdoorBase proofBase groupBase)

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

attribute [local simp] MachineState.getReg_setPC QOpening.getReg_setReg

@[local simp] private theorem pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

def groupCode : List Instr :=
  [.SRLI .x30 .x6 2, .SLLI .x10 .x30 8, .SLLI .x11 .x30 6, .ADD .x10 .x10 .x11, .SLLI .x11 .x30 5,
   .ADD .x10 .x10 .x11, .SLLI .x11 .x30 4, .ADD .x10 .x10 .x11, .ADD .x30 .x24 .x10]

def leafHeadCode (j : Fin 3) : List Instr :=
  [.ADDI .x7 .x6 (BitVec.ofNat 12 (j.val+1)), .ANDI .x7 .x7 3, .SLLI .x7 .x7 5, .ADD .x7 .x30 .x7]

def leafTailCode : List Instr := [.ADDI .x21 .x21 32]

def entryCode : List Instr := [.ADD .x6 .x6 .x19, .SRLI .x6 .x6 2]

def runCode (code : List Instr) (state : MachineState) (count : Nat) : MachineState :=
  (code.take count).foldl execInstrBr state

def leafHeadStart (j : Fin 3) : Nat := 46+37*j.val
def leafTailStart (j : Fin 3) : Nat := 82+37*j.val

/-- Trapdoor address of the `j`-th other leaf digest of the quad group (rotation order). -/
def leafAddress (index : Index) (j : Nat) : Nat :=
  groupBase+368*(index.val/4)+32*((index.val+j+1)%4)

set_option maxRecDepth 8192 in
private theorem group_decode : ∀ i : Fin 9,
    (openingImage.code[37+i.val]?).bind QOpening.decodeBase = some (groupCode[i.val]?.getD .EBREAK) := by
  decide

set_option maxRecDepth 8192 in
private theorem head_decode : ∀ (j : Fin 3) (i : Fin 4),
    (openingImage.code[leafHeadStart j+i.val]?).bind QOpening.decodeBase =
      some ((leafHeadCode j)[i.val]?.getD .EBREAK) := by
  decide

set_option maxRecDepth 8192 in
private theorem tail_decode : ∀ (j : Fin 3),
    (openingImage.code[leafTailStart j]?).bind QOpening.decodeBase = some (.ADDI .x21 .x21 32) := by
  decide

set_option maxRecDepth 8192 in
private theorem entry_decode : ∀ i : Fin 2,
    (openingImage.code[157+i.val]?).bind QOpening.decodeBase = some (entryCode[i.val]?.getD .EBREAK) := by
  decide

private theorem head_site (j : Fin 3) : leafHeadStart j+4 = (CopySite.leaf j).start := by
  simp [leafHeadStart, CopySite.start]; omega

private theorem tail_site (j : Fin 3) :
    (CopySite.leaf j).start+2*(CopySite.leaf j).halfwords = leafTailStart j := by
  simp [leafTailStart, CopySite.start, CopySite.halfwords]; omega

private theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem execute_group (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*37))
    (fuel : Nat) (coins : Bool) :
    execute openingImage (9+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode groupCode state 9) coins
          return result.charge 9 0) := by
  apply execute_unit_steps (states := runCode groupCode state)
  intro i inside
  refine ⟨.base (groupCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (37+i) _ (by omega)
    · rw [← pc_offset]
      interval_cases i <;> simp [runCode, groupCode, execInstrBr, pc, BitVec.add_assoc]
    · exact group_decode ⟨i, inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_leaf_head (state : MachineState) (j : Fin 3)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*leafHeadStart j)) (fuel : Nat) (coins : Bool) :
    execute openingImage (4+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode (leafHeadCode j) state 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := runCode (leafHeadCode j) state)
  intro i inside
  refine ⟨.base ((leafHeadCode j)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (leafHeadStart j+i) _ (by have := j.isLt; unfold leafHeadStart; omega)
    · rw [← pc_offset]
      interval_cases i <;> simp [runCode, leafHeadCode, execInstrBr, pc, BitVec.add_assoc]
    · exact head_decode j ⟨i, inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_leaf_tail (state : MachineState) (j : Fin 3)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*leafTailStart j)) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode leafTailCode state 1) coins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state (leafTailStart j) (.ADDI .x21 .x21 32)
    (by have := j.isLt; unfold leafTailStart; omega) pc (tail_decode j)
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched (show ordinaryStep state _ = _ from rfl)]
  rfl

theorem execute_entry (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*157))
    (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode entryCode state 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := runCode entryCode state)
  intro i inside
  refine ⟨.base (entryCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (157+i) _ (by omega)
    · rw [← pc_offset]
      interval_cases i <;> simp [runCode, entryCode, execInstrBr, pc, BitVec.add_assoc]
    · exact entry_decode ⟨i, inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem group_value (index : Index) :
    BitVec.ofNat 64 groupBase +
      ((((BitVec.ofNat 64 index.val >>> 2) <<< 8) + ((BitVec.ofNat 64 index.val >>> 2) <<< 6)) +
        ((BitVec.ofNat 64 index.val >>> 2) <<< 5) + ((BitVec.ofNat 64 index.val >>> 2) <<< 4)) =
      BitVec.ofNat 64 (groupBase+368*(index.val/4)) := by
  have bound := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have hG : groupBase = 4294971424 + 268439552 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem group_post (state : MachineState) (index : Index)
    (groups : state.getReg .x24 = BitVec.ofNat 64 groupBase)
    (node : state.getReg .x6 = BitVec.ofNat 64 index.val) :
    let next := runCode groupCode state 9
    next.pc = state.pc+36#64 ∧ next.mem = state.mem ∧
      next.getReg .x30 = BitVec.ofNat 64 (groupBase+368*(index.val/4)) ∧
      ∀ reg, reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x30 → next.getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [runCode, groupCode, execInstrBr, BitVec.add_assoc]
  · simp [runCode, groupCode, execInstrBr]
  · simp [runCode, groupCode, execInstrBr, groups, node]
    rw [← group_value index]
  · intro reg a b c
    simp [runCode, groupCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

private theorem ofNat_mask (n : Nat) : BitVec.ofNat 64 n &&& 3#64 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  have mask (x : Nat) : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2
  have small : n % 4 < 2^64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  rw [show (3 : Nat) % 2^64 = 3 by decide, mask]
  omega

private theorem ofNat_shift (n k : Nat) (fit : n*2^k < 2^64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n*2^k) := by
  apply BitVec.eq_of_toNat_eq
  have nfit : n < 2^64 := by
    have : n ≤ n*2^k := Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)
    omega
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt nfit,
    Nat.mod_eq_of_lt fit]

private theorem ofNat_shr (n k : Nat) (fit : n < 2^64) :
    BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n/2^k) := by
  apply BitVec.eq_of_toNat_eq
  have qfit : n/2^k < 2^64 := lt_of_le_of_lt (Nat.div_le_self n _) fit
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt fit,
    Nat.mod_eq_of_lt qfit]

private theorem leaf_value (index : Index) (j : Fin 3) :
    BitVec.ofNat 64 (groupBase+368*(index.val/4)) +
      (((BitVec.ofNat 64 index.val + BitVec.ofNat 64 (j.val+1)) &&& 3#64) <<< 5) =
      BitVec.ofNat 64 (leafAddress index j.val) := by
  have r := Nat.mod_lt (index.val+(j.val+1)) (show 0 < 4 by decide)
  rw [← BitVec.ofNat_add, ofNat_mask, ofNat_shift _ 5 (by omega), ← BitVec.ofNat_add]
  congr 1
  unfold leafAddress
  rw [show index.val+j.val+1 = index.val+(j.val+1) by omega]
  omega

theorem leaf_head_post (state : MachineState) (index : Index) (j : Fin 3)
    (group : state.getReg .x30 = BitVec.ofNat 64 (groupBase+368*(index.val/4)))
    (node : state.getReg .x6 = BitVec.ofNat 64 index.val) :
    let next := runCode (leafHeadCode j) state 4
    next.pc = state.pc+16#64 ∧ next.mem = state.mem ∧
      next.getReg .x7 = BitVec.ofNat 64 (leafAddress index j.val) ∧
      ∀ reg, reg ≠ .x7 → next.getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [runCode, leafHeadCode, execInstrBr, BitVec.add_assoc]
  · simp [runCode, leafHeadCode, execInstrBr]
  · rw [← leaf_value index j]
    fin_cases j <;> simp [runCode, leafHeadCode, execInstrBr, group, node, signExtend12] <;> rfl
  · intro reg a
    simp [runCode, leafHeadCode, execInstrBr, Ne.symm a]

theorem leaf_tail_post (state : MachineState) :
    let next := runCode leafTailCode state 1
    next.pc = state.pc+4#64 ∧ next.mem = state.mem ∧
      next.getReg .x21 = state.getReg .x21+32#64 ∧
      ∀ reg, reg ≠ .x21 → next.getReg reg = state.getReg reg := by
  simp [runCode, leafTailCode, execInstrBr, signExtend12]
  intro reg a
  simp [Ne.symm a]

theorem entry_post (state : MachineState) (index : Index)
    (node : state.getReg .x6 = BitVec.ofNat 64 index.val)
    (leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH) :
    let next := runCode entryCode state 2
    next.pc = state.pc+8#64 ∧ next.mem = state.mem ∧
      next.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 2) ∧
      ∀ reg, reg ≠ .x6 → next.getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [runCode, entryCode, execInstrBr, BitVec.add_assoc]
  · simp [runCode, entryCode, execInstrBr]
  · have bound := index.isLt
    have hL : LENGTH = 16777216 := rfl
    have value : (BitVec.ofNat 64 index.val + BitVec.ofNat 64 LENGTH) >>> 2 =
        BitVec.ofNat 64 (QOpening.lowerNode index 2) := by
      rw [← BitVec.ofNat_add, ofNat_shr _ 2 (by omega)]
      unfold QOpening.lowerNode
      congr 1
      rw [Nat.add_comm]
    rw [← value, ← node, ← leaves]
    simp [runCode, entryCode, execInstrBr]
  · intro reg a
    simp [runCode, entryCode, execInstrBr, Ne.symm a]

/-! Geometry of the three leaf copies. -/

theorem leaf_offset_inside (j : Nat) (inside : j < 3) : leafOffset j+32 ≤ quadOffset 0 := by
  unfold leafOffset quadOffset; omega

theorem all_leaf_copies_fit (index : Index) (ordinal j : Nat) (inside : ordinal < LENGTH) (valid : j < 3) :
    leafAddress index j % 2 = 0 ∧ leafDestination ordinal j % 2 = 0 ∧
      leafAddress index j+32 ≤ leafDestination ordinal j ∧
      leafDestination ordinal j+32 ≤ MEMORY_BYTES ∧
      leafAddress index j+32 ≤ proofBase := by
  have endRecord := all_record_ends_fit ordinal inside
  have bound := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have hG : groupBase = 4294971424 + 268439552 := rfl
  have hP : proofBase = 4294971424 + 2466267136 + 8 * 16777216 + 64 + 256 * 16777216 := rfl
  have r := Nat.mod_lt (index.val+j+1) (show 0 < 4 by decide)
  refine ⟨?_, even_leaf_destination ordinal j, ?_, ?_, ?_⟩
  all_goals simp only [leafAddress, leafDestination, leafOffset, recordBase, recordBytes] at * <;> omega

/-! One leaf copy block: head, 16 halfword pairs, pointer bump. -/

def leafBlock (j : Fin 3) (state : MachineState) : MachineState :=
  runCode leafTailCode (copyState (.leaf j) (runCode (leafHeadCode j) state 4)) 1

theorem leaf_address_aligned (index : Index) (j : Nat) : leafAddress index j % 8 = 0 := by
  have base : groupBase % 8 = 0 := by decide
  unfold leafAddress; omega

structure LeafStep (state : MachineState) (index : Index) (ordinal : Nat) (j : Fin 3) : Prop where
  run : RunsOpeningBlock state (leafBlock j state) (4+siteCost (.leaf j) (leafDestination ordinal j.val)+1)
  pc : (leafBlock j state).pc = BitVec.ofNat 64 (4096+4*(leafHeadStart j+37))
  dest : (leafBlock j state).getReg .x21 = BitVec.ofNat 64 (leafDestination ordinal j.val+32)
  bytes : ByteCopy state (leafBlock j state) (leafAddress index j.val) (leafDestination ordinal j.val) 32
  register : ∀ reg, reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 → reg ≠ .x10 →
    (leafBlock j state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (leafBlock j state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

theorem execute_leaf (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (j : Fin 3) (pc : state.pc = BitVec.ofNat 64 (4096+4*leafHeadStart j))
    (group : state.getReg .x30 = BitVec.ofNat 64 (groupBase+368*(index.val/4)))
    (node : state.getReg .x6 = BitVec.ofNat 64 index.val)
    (dest : state.getReg .x21 = BitVec.ofNat 64 (leafDestination ordinal j.val)) :
    LeafStep state index ordinal j := by
  let prepared := runCode (leafHeadCode j) state 4
  let copied := copyState (.leaf j) prepared
  have head := leaf_head_post state index j group node
  have tail := leaf_tail_post copied
  have fit := all_leaf_copies_fit index ordinal j.val bounded j.isLt
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*(CopySite.leaf j).start) := by
    rw [head.1, pc, ← head_site j]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 16 = _
    rw [← BitVec.ofNat_add]
    congr 1
  have field : FieldInputs (.leaf j) prepared (leafAddress index j.val) (leafDestination ordinal j.val) :=
    ⟨before, head.2.2.1, (head.2.2.2 .x21 (by decide)).trans dest,
      by simpa [CopySite.halfwords] using fit.2.2.1,
      by simpa [CopySite.halfwords] using fit.2.2.2.1, fit.1, fit.2.1, fun _ => leaf_address_aligned index j.val⟩
  have tailPC : copied.pc = BitVec.ofNat 64 (4096+4*leafTailStart j) := by
    rw [field.final_pc, tail_site]
  have ranHead : RunsOpeningBlock state prepared 4 :=
    fun fuel coins => execute_leaf_head state j pc fuel coins
  have ranTail : RunsOpeningBlock copied (leafBlock j state) 1 :=
    fun fuel coins => execute_leaf_tail copied j tailPC fuel coins
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ranHead.next field.run).next ranTail
  · change (runCode leafTailCode copied 1).pc = _
    rw [tail.1, tailPC]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
    simp [leafTailStart, leafHeadStart]
    omega
  · change (runCode leafTailCode copied 1).getReg .x21 = _
    rw [tail.2.2.1, copy_register _ prepared .x21 (by decide) (Or.inr (by decide)), head.2.2.2 .x21 (by decide), dest,
      ← BitVec.ofNat_add]
  · change ByteCopy state (runCode leafTailCode copied 1) _ _ _
    simpa [CopySite.halfwords] using field.bytes.move head.2.1.symm tail.2.1
  · intro reg a b c d
    change (runCode leafTailCode copied 1).getReg reg = _
    rw [tail.2.2.2 reg b, copy_register _ prepared reg c (Or.inr d), head.2.2.2 reg a]
  · intro address below
    have above : proofBase ≤ leafDestination ordinal j.val := by
      unfold leafDestination recordBase; omega
    have stable := field.words_before proofBase address below above (by decide)
    have saved : (runCode leafTailCode copied 1).mem = copied.mem := tail.2.1
    have reads : prepared.mem = state.mem := head.2.1
    change (runCode leafTailCode copied 1).getMem _ = _
    simpa only [MachineState.getMem, saved, reads] using stable

/-! The whole leaf part. -/

def leafPart (state : MachineState) : MachineState :=
  runCode entryCode (leafBlock 2 (leafBlock 1 (leafBlock 0 (runCode groupCode state 9)))) 2

/-- `x28` holds `trapdoorBase + 0x7C004000 - 368 * 2^20`: the quad-group part indexes it with
the quad node `(LENGTH + index) / 4` shifted right by two, i.e. `2^20 + index / 16`. -/
def quadBase : Nat := trapdoorBase + 0x65004000

/-- State at the start of the quad-group part (word 159). -/
structure QuadEntry (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*159)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  quads : state.getReg .x28 = BitVec.ofNat 64 quadBase
  node : state.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 2)
  dest : state.getReg .x21 = BitVec.ofNat 64 (quadDestination ordinal 0)

structure LeafEntry (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*37)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  quads : state.getReg .x28 = BitVec.ofNat 64 quadBase
  groups : state.getReg .x24 = BitVec.ofNat 64 groupBase
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  node : state.getReg .x6 = BitVec.ofNat 64 index.val
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal+16)

def leafPartCost (ordinal : Nat) : Nat :=
  9+(4+siteCost (.leaf 0) (leafDestination ordinal 0)+1)+(4+siteCost (.leaf 1) (leafDestination ordinal 1)+1)+
    (4+siteCost (.leaf 2) (leafDestination ordinal 2)+1)+2

structure LeafTrace (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state (leafPart state) (leafPartCost ordinal)
  next : QuadEntry (leafPart state) index ordinal
  leaf : ∀ j < 3, ∀ byte < 32,
    (leafPart state).getByte (BitVec.ofNat 64 (leafDestination ordinal j+byte)) =
      state.getByte (BitVec.ofNat 64 (leafAddress index j+byte))
  frame : ∀ address < 2^64, address < recordBase ordinal+16 ∨ quadDestination ordinal 0 ≤ address →
    (leafPart state).getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x21 → reg ≠ .x30 →
    reg ≠ .x31 → (leafPart state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (leafPart state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

private theorem byte_of_mem {one two : MachineState} (same : one.mem = two.mem) (address : Word) :
    one.getByte address = two.getByte address := by
  simp only [MachineState.getByte, MachineState.getMem, same]

private theorem leaf_copy_outside {before after : MachineState} {source dest size : Nat}
    (copy : ByteCopy before after source dest size) (address : Nat)
    (fit : address < 2^64) (endFit : dest+size ≤ 2^64)
    (outside : address < dest ∨ dest+size ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  apply copy.frame
  intro i inside equal
  have same := QOpening.nat_address_injective fit (by omega) equal
  omega

theorem execute_leaf_part (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (entry : LeafEntry state index ordinal) : LeafTrace state index ordinal := by
  let s0 := runCode groupCode state 9
  let s1 := leafBlock 0 s0
  let s2 := leafBlock 1 s1
  let s3 := leafBlock 2 s2
  have g := group_post state index entry.groups entry.node
  have g6 : s0.getReg .x6 = BitVec.ofNat 64 index.val :=
    (g.2.2.2 .x6 (by decide) (by decide) (by decide)).trans entry.node
  have g21 : s0.getReg .x21 = BitVec.ofNat 64 (leafDestination ordinal 0) :=
    (g.2.2.2 .x21 (by decide) (by decide) (by decide)).trans entry.dest
  have pc0 : s0.pc = BitVec.ofNat 64 (4096+4*leafHeadStart 0) := by
    rw [g.1, entry.pc]; rfl
  have l0 := execute_leaf s0 index ordinal bounded 0 pc0 g.2.2.1 g6 g21
  have l1 := execute_leaf s1 index ordinal bounded 1 l0.pc
    ((l0.register .x30 (by decide) (by decide) (by decide) (by decide)).trans g.2.2.1)
    ((l0.register .x6 (by decide) (by decide) (by decide) (by decide)).trans g6) l0.dest
  have l2 := execute_leaf s2 index ordinal bounded 2 l1.pc
    ((l1.register .x30 (by decide) (by decide) (by decide) (by decide)).trans
      ((l0.register .x30 (by decide) (by decide) (by decide) (by decide)).trans g.2.2.1))
    ((l1.register .x6 (by decide) (by decide) (by decide) (by decide)).trans
      ((l0.register .x6 (by decide) (by decide) (by decide) (by decide)).trans g6)) l1.dest
  have keep (reg : Reg) (a : reg ≠ .x7) (b : reg ≠ .x21) (c : reg ≠ .x31) (d : reg ≠ .x10) :
      s3.getReg reg = s0.getReg reg :=
    (l2.register reg a b c d).trans ((l1.register reg a b c d).trans (l0.register reg a b c d))
  have e := entry_post s3 index ((keep .x6 (by decide) (by decide) (by decide) (by decide)).trans g6)
    ((keep .x19 (by decide) (by decide) (by decide) (by decide)).trans
      ((g.2.2.2 .x19 (by decide) (by decide) (by decide)).trans entry.leaves))
  have ram : MEMORY_BYTES < 2^64 := by decide
  have b0 : ByteCopy s0 s1 (leafAddress index 0) (leafDestination ordinal 0) 32 := l0.bytes
  have b1 : ByteCopy s1 s2 (leafAddress index 1) (leafDestination ordinal 1) 32 := l1.bytes
  have b2 : ByteCopy s2 s3 (leafAddress index 2) (leafDestination ordinal 2) 32 := l2.bytes
  have fits (j : Nat) (valid : j < 3) := all_leaf_copies_fit index ordinal j bounded valid
  have destOrder (j : Nat) : leafDestination ordinal j = recordBase ordinal+16+32*j := by
    unfold leafDestination leafOffset; omega
  have recordFit := all_record_ends_fit ordinal bounded
  have endFit : quadDestination ordinal 0 = recordBase ordinal+112 := rfl
  have recordWide : recordBase ordinal+112 ≤ recordBase (ordinal+1) := by
    unfold recordBase recordBytes; omega
  -- memory equalities of the non-copy blocks
  have m0 : s0.mem = state.mem := g.2.1
  have m4 : (leafPart state).mem = s3.mem := e.2.1
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have ranGroup : RunsOpeningBlock state s0 9 :=
      fun fuel coins => execute_group state entry.pc fuel coins
    have pc3 : s3.pc = BitVec.ofNat 64 (4096+4*157) := l2.pc
    have ranEntry : RunsOpeningBlock s3 (leafPart state) 2 :=
      fun fuel coins => execute_entry s3 pc3 fuel coins
    exact (((ranGroup.next l0.run).next l1.run).next l2.run).next ranEntry
  · change (runCode entryCode s3 2).pc = _
    rw [e.1, l2.pc]
    rfl
  · change (runCode entryCode s3 2).getReg .x9 = _
    rw [e.2.2.2 .x9 (by decide), keep .x9 (by decide) (by decide) (by decide) (by decide),
      g.2.2.2 .x9 (by decide) (by decide) (by decide), entry.heap]
  · change (runCode entryCode s3 2).getReg .x28 = _
    rw [e.2.2.2 .x28 (by decide), keep .x28 (by decide) (by decide) (by decide) (by decide),
      g.2.2.2 .x28 (by decide) (by decide) (by decide), entry.quads]
  · exact e.2.2.1
  · change (runCode entryCode s3 2).getReg .x21 = _
    rw [e.2.2.2 .x21 (by decide), l2.dest]
    congr 1
  · intro j valid byte inside
    have f := fits j valid
    have f0 := fits 0 (by decide)
    have f1 := fits 1 (by decide)
    have f2 := fits 2 (by decide)
    have d0 := destOrder 0
    have d1 := destOrder 1
    have d2 := destOrder 2
    have top : (leafPart state).getByte (BitVec.ofNat 64 (leafDestination ordinal j+byte)) =
        s3.getByte (BitVec.ofNat 64 (leafDestination ordinal j+byte)) := byte_of_mem m4 _
    have bottom : s0.getByte (BitVec.ofNat 64 (leafAddress index j+byte)) =
        state.getByte (BitVec.ofNat 64 (leafAddress index j+byte)) := byte_of_mem m0 _
    refine top.trans (Eq.trans ?_ bottom)
    have dj := destOrder j
    have pr : proofBase ≤ recordBase ordinal := by unfold recordBase; omega
    interval_cases j
    · exact (leaf_copy_outside b2 _ (by omega) (by omega) (Or.inl (by omega))).trans
        ((leaf_copy_outside b1 _ (by omega) (by omega) (Or.inl (by omega))).trans
          (b0.copied byte inside))
    · exact (leaf_copy_outside b2 _ (by omega) (by omega) (Or.inl (by omega))).trans
        ((b1.copied byte inside).trans
          (leaf_copy_outside b0 _ (by omega) (by omega) (Or.inl (by omega))))
    · exact (b2.copied byte inside).trans
        ((leaf_copy_outside b1 _ (by omega) (by omega) (Or.inl (by omega))).trans
          (leaf_copy_outside b0 _ (by omega) (by omega) (Or.inl (by omega))))
  · intro address fit outside
    have f0 := fits 0 (by decide)
    have f1 := fits 1 (by decide)
    have f2 := fits 2 (by decide)
    have d0 := destOrder 0
    have d1 := destOrder 1
    have d2 := destOrder 2
    rw [endFit] at outside
    exact (byte_of_mem m4 _).trans
      ((leaf_copy_outside b2 _ fit (by omega) (by omega)).trans
      ((leaf_copy_outside b1 _ fit (by omega) (by omega)).trans
      ((leaf_copy_outside b0 _ fit (by omega) (by omega)).trans
        (byte_of_mem m0 _))))
  · intro reg a b c d e' f h
    change (runCode entryCode s3 2).getReg reg = _
    rw [e.2.2.2 reg a, keep reg b e' h c, g.2.2.2 reg c d f]
  · intro address below
    have top : (leafPart state).getMem (BitVec.ofNat 64 address) = s3.getMem (BitVec.ofNat 64 address) := by
      simp only [MachineState.getMem, m4]
    have bottom : s0.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
      simp only [MachineState.getMem, m0]
    exact top.trans ((l2.input address below).trans ((l1.input address below).trans
      ((l0.input address below).trans bottom)))

end TwoPermutationPrototype.QuadOpening
