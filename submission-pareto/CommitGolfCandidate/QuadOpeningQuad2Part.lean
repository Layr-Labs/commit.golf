import CommitGolfCandidate.QuadOpeningQuadPart

/-! The level-2 group part of one opening record (words 282..402, 121 unit cycles): with `x6`
holding the level-2 node `(LENGTH + index) / 16`, locate the level-2 group of the opened index,
copy the three other level-2 nodes of its level-3 group in rotation order `u+1, u+2, u+3 (mod 4)`,
`u = (index / 16) % 4`, into the record, and enter the lower path at the level-3 node
`(LENGTH + index) / 64`. Same code shape as `QuadOpeningQuadPart`, with base register `x29`. -/

namespace TwoPermutationPrototype.QuadOpening
set_option maxRecDepth 8192
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open QOpening (trapdoorBase proofBase quad2GroupBase)

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

attribute [local simp] MachineState.getReg_setPC QOpening.getReg_setReg

@[local simp] private theorem pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

def quad2GroupCode : List Instr :=
  [.SRLI .x30 .x6 2, .SLLI .x10 .x30 8, .SLLI .x11 .x30 6, .ADD .x10 .x10 .x11, .SLLI .x11 .x30 5,
   .ADD .x10 .x10 .x11, .SLLI .x11 .x30 4, .ADD .x10 .x10 .x11, .ADD .x30 .x29 .x10]

def quad2ExitCode : List Instr := [.SRLI .x6 .x6 2]

def quad2HeadStart (j : Fin 3) : Nat := 291+37*j.val
def quad2TailStart (j : Fin 3) : Nat := 327+37*j.val

/-- Trapdoor address of the `j`-th other level-2 node of the level-3 group (rotation order). -/
def quad2Address (index : Index) (j : Nat) : Nat :=
  quad2GroupBase+368*(index.val/64)+32*((index.val/16+j+1)%4)

set_option maxRecDepth 8192 in
private theorem group_decode : ∀ i : Fin 9,
    (openingImage.code[282+i.val]?).bind QOpening.decodeBase = some (quad2GroupCode[i.val]?.getD .EBREAK) := by
  decide

set_option maxRecDepth 8192 in
private theorem head_decode : ∀ (j : Fin 3) (i : Fin 4),
    (openingImage.code[quad2HeadStart j+i.val]?).bind QOpening.decodeBase =
      some ((leafHeadCode j)[i.val]?.getD .EBREAK) := by
  decide

set_option maxRecDepth 8192 in
private theorem tail_decode : ∀ (j : Fin 3),
    (openingImage.code[quad2TailStart j]?).bind QOpening.decodeBase = some (.ADDI .x21 .x21 32) := by
  decide

private theorem exit_decode :
    (openingImage.code[402]?).bind QOpening.decodeBase = some (.SRLI .x6 .x6 2) := by
  decide

private theorem head_site (j : Fin 3) : quad2HeadStart j+4 = (CopySite.quad2 j).start := by
  simp [quad2HeadStart, CopySite.start]; omega

private theorem tail_site (j : Fin 3) :
    (CopySite.quad2 j).start+2*(CopySite.quad2 j).halfwords = quad2TailStart j := by
  simp [quad2TailStart, CopySite.start, CopySite.halfwords]; omega

private theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem execute_quad2_group (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*282))
    (fuel : Nat) (coins : Bool) :
    execute openingImage (9+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode quad2GroupCode state 9) coins
          return result.charge 9 0) := by
  apply execute_unit_steps (states := runCode quad2GroupCode state)
  intro i inside
  refine ⟨.base (quad2GroupCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (282+i) _ (by omega)
    · rw [← pc_offset]
      interval_cases i <;> simp [runCode, quad2GroupCode, execInstrBr, pc, BitVec.add_assoc]
    · exact group_decode ⟨i, inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_quad2_head (state : MachineState) (j : Fin 3)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*quad2HeadStart j)) (fuel : Nat) (coins : Bool) :
    execute openingImage (4+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode (leafHeadCode j) state 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := runCode (leafHeadCode j) state)
  intro i inside
  refine ⟨.base ((leafHeadCode j)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (quad2HeadStart j+i) _ (by have := j.isLt; unfold quad2HeadStart; omega)
    · rw [← pc_offset]
      interval_cases i <;> simp [runCode, leafHeadCode, execInstrBr, pc, BitVec.add_assoc]
    · exact head_decode j ⟨i, inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_quad2_tail (state : MachineState) (j : Fin 3)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*quad2TailStart j)) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode leafTailCode state 1) coins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state (quad2TailStart j) (.ADDI .x21 .x21 32)
    (by have := j.isLt; unfold quad2TailStart; omega) pc (tail_decode j)
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched (show ordinaryStep state _ = _ from rfl)]
  rfl

theorem execute_quad2_exit (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*402))
    (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) state coins =
      (do let result ← execute openingImage fuel (runCode quad2ExitCode state 1) coins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 402 (.SRLI .x6 .x6 2) (by decide) pc exit_decode
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched (show ordinaryStep state _ = _ from rfl)]
  rfl

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

private theorem quad2_group_value (index : Index) :
    BitVec.ofNat 64 quad2Base +
      ((((BitVec.ofNat 64 (QOpening.lowerNode index 4) >>> 2) <<< 8) +
        ((BitVec.ofNat 64 (QOpening.lowerNode index 4) >>> 2) <<< 6)) +
        ((BitVec.ofNat 64 (QOpening.lowerNode index 4) >>> 2) <<< 5) +
        ((BitVec.ofNat 64 (QOpening.lowerNode index 4) >>> 2) <<< 4)) =
      BitVec.ofNat 64 (quad2GroupBase+368*(index.val/64)) := by
  have bound := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have hQ : quad2Base = 4294971424 - 62910464 := rfl
  have hG : quad2GroupBase = 4294971424 + 0x02001000 := rfl
  have node : QOpening.lowerNode index 4 = (16777216+index.val)/16 := by
    unfold QOpening.lowerNode; rfl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, node]
  omega

theorem quad2_group_post (state : MachineState) (index : Index)
    (quads : state.getReg .x29 = BitVec.ofNat 64 quad2Base)
    (node : state.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 4)) :
    let next := runCode quad2GroupCode state 9
    next.pc = state.pc+36#64 ∧ next.mem = state.mem ∧
      next.getReg .x30 = BitVec.ofNat 64 (quad2GroupBase+368*(index.val/64)) ∧
      ∀ reg, reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x30 → next.getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [runCode, quad2GroupCode, execInstrBr, BitVec.add_assoc]
  · simp [runCode, quad2GroupCode, execInstrBr]
  · simp [runCode, quad2GroupCode, execInstrBr, quads, node]
    rw [← quad2_group_value index]
  · intro reg a b c
    simp [runCode, quad2GroupCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

private theorem quad2_value_eq (index : Index) (j : Fin 3) :
    BitVec.ofNat 64 (quad2GroupBase+368*(index.val/64)) +
      (((BitVec.ofNat 64 (QOpening.lowerNode index 4) + BitVec.ofNat 64 (j.val+1)) &&& 3#64) <<< 5) =
      BitVec.ofNat 64 (quad2Address index j.val) := by
  have r := Nat.mod_lt (QOpening.lowerNode index 4+(j.val+1)) (show 0 < 4 by decide)
  rw [← BitVec.ofNat_add, ofNat_mask, ofNat_shift _ 5 (by omega), ← BitVec.ofNat_add]
  congr 1
  have hL : LENGTH = 16777216 := rfl
  have node : QOpening.lowerNode index 4 = (16777216+index.val)/16 := by
    unfold QOpening.lowerNode; rfl
  unfold quad2Address
  rw [node]
  omega

theorem quad2_head_post (state : MachineState) (index : Index) (j : Fin 3)
    (group : state.getReg .x30 = BitVec.ofNat 64 (quad2GroupBase+368*(index.val/64)))
    (node : state.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 4)) :
    let next := runCode (leafHeadCode j) state 4
    next.pc = state.pc+16#64 ∧ next.mem = state.mem ∧
      next.getReg .x7 = BitVec.ofNat 64 (quad2Address index j.val) ∧
      ∀ reg, reg ≠ .x7 → next.getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [runCode, leafHeadCode, execInstrBr, BitVec.add_assoc]
  · simp [runCode, leafHeadCode, execInstrBr]
  · rw [← quad2_value_eq index j]
    fin_cases j <;> simp [runCode, leafHeadCode, execInstrBr, group, node, signExtend12] <;> rfl
  · intro reg a
    simp [runCode, leafHeadCode, execInstrBr, Ne.symm a]

theorem quad2_exit_post (state : MachineState) (index : Index)
    (node : state.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 4)) :
    let next := runCode quad2ExitCode state 1
    next.pc = state.pc+4#64 ∧ next.mem = state.mem ∧
      next.getReg .x6 = BitVec.ofNat 64 (lowerNode index 0) ∧
      ∀ reg, reg ≠ .x6 → next.getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [runCode, quad2ExitCode, execInstrBr]
  · simp [runCode, quad2ExitCode, execInstrBr]
  · have bound := index.isLt
    have hL : LENGTH = 16777216 := rfl
    have value : BitVec.ofNat 64 (QOpening.lowerNode index 4) >>> 2 =
        BitVec.ofNat 64 (lowerNode index 0) := by
      rw [ofNat_shr _ 2 (by unfold QOpening.lowerNode; omega)]
      unfold lowerNode QOpening.lowerNode
      congr 1
      rw [Nat.div_div_eq_div_mul]
      norm_num
    rw [← value, ← node]
    simp [runCode, quad2ExitCode, execInstrBr]
  · intro reg a
    simp [runCode, quad2ExitCode, execInstrBr, Ne.symm a]

/-! Geometry of the three quad copies. -/

theorem quad2_offset_inside (j : Nat) (inside : j < 3) : quad2Offset j+32 ≤ siblingOffset 0 := by
  unfold quad2Offset siblingOffset; simp; omega

theorem all_quad2_copies_fit (index : Index) (ordinal j : Nat) (inside : ordinal < LENGTH) (valid : j < 3) :
    quad2Address index j % 2 = 0 ∧ quad2Destination ordinal j % 2 = 0 ∧
      quad2Address index j+32 ≤ quad2Destination ordinal j ∧
      quad2Destination ordinal j+32 ≤ MEMORY_BYTES ∧
      quad2Address index j+32 ≤ proofBase ∧ trapdoorBase ≤ quad2Address index j := by
  have endRecord := all_record_ends_fit ordinal inside
  have bound := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have hG : quad2GroupBase = 4294971424 + 0x02001000 := rfl
  have hT : trapdoorBase = 4294971424 := rfl
  have hP : proofBase = 4294971424 + 2466267136 + 8 * 16777216 + 64 + 256 * 16777216 := rfl
  have r := Nat.mod_lt (index.val/16+j+1) (show 0 < 4 by decide)
  refine ⟨?_, even_quad2_destination ordinal j, ?_, ?_, ?_, ?_⟩
  all_goals simp only [quad2Address, quad2Destination, quad2Offset, recordBase, recordBytes] at * <;> omega

/-! One quad copy block: head, 16 halfword pairs, pointer bump. -/

def quad2Block (j : Fin 3) (state : MachineState) : MachineState :=
  runCode leafTailCode (copyState (.quad2 j) (runCode (leafHeadCode j) state 4)) 1

structure Quad2Step (state : MachineState) (index : Index) (ordinal : Nat) (j : Fin 3) : Prop where
  run : RunsOpeningBlock state (quad2Block j state) 37
  pc : (quad2Block j state).pc = BitVec.ofNat 64 (4096+4*(quad2HeadStart j+37))
  dest : (quad2Block j state).getReg .x21 = BitVec.ofNat 64 (quad2Destination ordinal j.val+32)
  bytes : ByteCopy state (quad2Block j state) (quad2Address index j.val) (quad2Destination ordinal j.val) 32
  register : ∀ reg, reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 → (quad2Block j state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (quad2Block j state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

theorem execute_quad2 (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (j : Fin 3) (pc : state.pc = BitVec.ofNat 64 (4096+4*quad2HeadStart j))
    (group : state.getReg .x30 = BitVec.ofNat 64 (quad2GroupBase+368*(index.val/64)))
    (node : state.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 4))
    (dest : state.getReg .x21 = BitVec.ofNat 64 (quad2Destination ordinal j.val)) :
    Quad2Step state index ordinal j := by
  let prepared := runCode (leafHeadCode j) state 4
  let copied := copyState (.quad2 j) prepared
  have head := quad2_head_post state index j group node
  have tail := leaf_tail_post copied
  have fit := all_quad2_copies_fit index ordinal j.val bounded j.isLt
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*(CopySite.quad2 j).start) := by
    rw [head.1, pc, ← head_site j]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 16 = _
    rw [← BitVec.ofNat_add]
    congr 1
  have field : FieldInputs (.quad2 j) prepared (quad2Address index j.val) (quad2Destination ordinal j.val) :=
    ⟨before, head.2.2.1, (head.2.2.2 .x21 (by decide)).trans dest,
      by simpa [CopySite.halfwords] using fit.2.2.1,
      by simpa [CopySite.halfwords] using fit.2.2.2.1, fit.1, fit.2.1⟩
  have tailPC : copied.pc = BitVec.ofNat 64 (4096+4*quad2TailStart j) := by
    rw [field.final_pc, tail_site]
  have ranHead : RunsOpeningBlock state prepared 4 :=
    fun fuel coins => execute_quad2_head state j pc fuel coins
  have ranTail : RunsOpeningBlock copied (quad2Block j state) 1 :=
    fun fuel coins => execute_quad2_tail copied j tailPC fuel coins
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have trace := (ranHead.next field.run).next ranTail
    simpa [CopySite.halfwords] using trace
  · change (runCode leafTailCode copied 1).pc = _
    rw [tail.1, tailPC]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
    simp [quad2TailStart, quad2HeadStart]
    omega
  · change (runCode leafTailCode copied 1).getReg .x21 = _
    rw [tail.2.2.1, copy_register _ prepared .x21 (by decide), head.2.2.2 .x21 (by decide), dest,
      ← BitVec.ofNat_add]
  · change ByteCopy state (runCode leafTailCode copied 1) _ _ _
    simpa [CopySite.halfwords] using field.bytes.move head.2.1.symm tail.2.1
  · intro reg a b c
    change (runCode leafTailCode copied 1).getReg reg = _
    rw [tail.2.2.2 reg b, copy_register _ prepared reg c, head.2.2.2 reg a]
  · intro address below
    have above : proofBase ≤ quad2Destination ordinal j.val := by
      unfold quad2Destination recordBase; omega
    have stable := field.words_before proofBase address below above (by decide)
    have saved : (runCode leafTailCode copied 1).mem = copied.mem := tail.2.1
    have reads : prepared.mem = state.mem := head.2.1
    change (runCode leafTailCode copied 1).getMem _ = _
    simpa only [MachineState.getMem, saved, reads] using stable

/-! The whole quad-group part. -/

def quad2Part (state : MachineState) : MachineState :=
  runCode quad2ExitCode (quad2Block 2 (quad2Block 1 (quad2Block 0 (runCode quad2GroupCode state 9)))) 1

structure Quad2Trace (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state (quad2Part state) 121
  next : LowerCursor (quad2Part state) index ordinal 0
  quad : ∀ j < 3, ∀ byte < 32,
    (quad2Part state).getByte (BitVec.ofNat 64 (quad2Destination ordinal j+byte)) =
      state.getByte (BitVec.ofNat 64 (quad2Address index j+byte))
  frame : ∀ address < 2^64, address < quad2Destination ordinal 0 ∨ siblingDestination ordinal 0 ≤ address →
    (quad2Part state).getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x21 → reg ≠ .x30 →
    reg ≠ .x31 → (quad2Part state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (quad2Part state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

private theorem byte_of_mem {one two : MachineState} (same : one.mem = two.mem) (address : Word) :
    one.getByte address = two.getByte address := by
  simp only [MachineState.getByte, MachineState.getMem, same]

private theorem quad2_copy_outside {before after : MachineState} {source dest size : Nat}
    (copy : ByteCopy before after source dest size) (address : Nat)
    (fit : address < 2^64) (endFit : dest+size ≤ 2^64)
    (outside : address < dest ∨ dest+size ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  apply copy.frame
  intro i inside equal
  have same := QOpening.nat_address_injective fit (by omega) equal
  omega

theorem execute_quad2_part (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (entry : Quad2Entry state index ordinal) : Quad2Trace state index ordinal := by
  let s0 := runCode quad2GroupCode state 9
  let s1 := quad2Block 0 s0
  let s2 := quad2Block 1 s1
  let s3 := quad2Block 2 s2
  have g := quad2_group_post state index entry.quad2s entry.node
  have g6 : s0.getReg .x6 = BitVec.ofNat 64 (QOpening.lowerNode index 4) :=
    (g.2.2.2 .x6 (by decide) (by decide) (by decide)).trans entry.node
  have g21 : s0.getReg .x21 = BitVec.ofNat 64 (quad2Destination ordinal 0) :=
    (g.2.2.2 .x21 (by decide) (by decide) (by decide)).trans entry.dest
  have pc0 : s0.pc = BitVec.ofNat 64 (4096+4*quad2HeadStart 0) := by
    rw [g.1, entry.pc]; rfl
  have l0 := execute_quad2 s0 index ordinal bounded 0 pc0 g.2.2.1 g6 g21
  have l1 := execute_quad2 s1 index ordinal bounded 1 l0.pc
    ((l0.register .x30 (by decide) (by decide) (by decide)).trans g.2.2.1)
    ((l0.register .x6 (by decide) (by decide) (by decide)).trans g6) l0.dest
  have l2 := execute_quad2 s2 index ordinal bounded 2 l1.pc
    ((l1.register .x30 (by decide) (by decide) (by decide)).trans
      ((l0.register .x30 (by decide) (by decide) (by decide)).trans g.2.2.1))
    ((l1.register .x6 (by decide) (by decide) (by decide)).trans
      ((l0.register .x6 (by decide) (by decide) (by decide)).trans g6)) l1.dest
  have keep (reg : Reg) (a : reg ≠ .x7) (b : reg ≠ .x21) (c : reg ≠ .x31) :
      s3.getReg reg = s0.getReg reg :=
    (l2.register reg a b c).trans ((l1.register reg a b c).trans (l0.register reg a b c))
  have e := quad2_exit_post s3 index ((keep .x6 (by decide) (by decide) (by decide)).trans g6)
  have ram : MEMORY_BYTES < 2^64 := by decide
  have b0 : ByteCopy s0 s1 (quad2Address index 0) (quad2Destination ordinal 0) 32 := l0.bytes
  have b1 : ByteCopy s1 s2 (quad2Address index 1) (quad2Destination ordinal 1) 32 := l1.bytes
  have b2 : ByteCopy s2 s3 (quad2Address index 2) (quad2Destination ordinal 2) 32 := l2.bytes
  have fits (j : Nat) (valid : j < 3) := all_quad2_copies_fit index ordinal j bounded valid
  have destOrder (j : Nat) : quad2Destination ordinal j = recordBase ordinal+208+32*j := by
    unfold quad2Destination quad2Offset; omega
  have recordFit := all_record_ends_fit ordinal bounded
  have endFit : siblingDestination ordinal 0 = recordBase ordinal+304 := rfl
  have recordWide : recordBase ordinal+304 ≤ recordBase (ordinal+1) := by
    unfold recordBase recordBytes; omega
  have m0 : s0.mem = state.mem := g.2.1
  have m4 : (quad2Part state).mem = s3.mem := e.2.1
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have ranGroup : RunsOpeningBlock state s0 9 :=
      fun fuel coins => execute_quad2_group state entry.pc fuel coins
    have pc3 : s3.pc = BitVec.ofNat 64 (4096+4*402) := l2.pc
    have ranExit : RunsOpeningBlock s3 (quad2Part state) 1 :=
      fun fuel coins => execute_quad2_exit s3 pc3 fuel coins
    exact (((ranGroup.next l0.run).next l1.run).next l2.run).next ranExit
  · change (runCode quad2ExitCode s3 1).pc = lowerPC 0
    rw [e.1, l2.pc]
    rfl
  · change (runCode quad2ExitCode s3 1).getReg .x9 = _
    rw [e.2.2.2 .x9 (by decide), keep .x9 (by decide) (by decide) (by decide),
      g.2.2.2 .x9 (by decide) (by decide) (by decide), entry.heap]
  · exact e.2.2.1
  · change (runCode quad2ExitCode s3 1).getReg .x21 = _
    rw [e.2.2.2 .x21 (by decide), l2.dest]
    congr 1
  · intro j valid byte inside
    have f0 := fits 0 (by decide)
    have f1 := fits 1 (by decide)
    have f2 := fits 2 (by decide)
    have d0 := destOrder 0
    have d1 := destOrder 1
    have d2 := destOrder 2
    have top : (quad2Part state).getByte (BitVec.ofNat 64 (quad2Destination ordinal j+byte)) =
        s3.getByte (BitVec.ofNat 64 (quad2Destination ordinal j+byte)) := byte_of_mem m4 _
    have bottom : s0.getByte (BitVec.ofNat 64 (quad2Address index j+byte)) =
        state.getByte (BitVec.ofNat 64 (quad2Address index j+byte)) := byte_of_mem m0 _
    refine top.trans (Eq.trans ?_ bottom)
    have pr : proofBase ≤ recordBase ordinal := by unfold recordBase; omega
    interval_cases j
    · exact (quad2_copy_outside b2 _ (by omega) (by omega) (Or.inl (by omega))).trans
        ((quad2_copy_outside b1 _ (by omega) (by omega) (Or.inl (by omega))).trans
          (b0.copied byte inside))
    · exact (quad2_copy_outside b2 _ (by omega) (by omega) (Or.inl (by omega))).trans
        ((b1.copied byte inside).trans
          (quad2_copy_outside b0 _ (by omega) (by omega) (Or.inl (by omega))))
    · exact (b2.copied byte inside).trans
        ((quad2_copy_outside b1 _ (by omega) (by omega) (Or.inl (by omega))).trans
          (quad2_copy_outside b0 _ (by omega) (by omega) (Or.inl (by omega))))
  · intro address fit outside
    have f0 := fits 0 (by decide)
    have f1 := fits 1 (by decide)
    have f2 := fits 2 (by decide)
    have d0 := destOrder 0
    have d1 := destOrder 1
    have d2 := destOrder 2
    rw [endFit] at outside
    exact (byte_of_mem m4 _).trans
      ((quad2_copy_outside b2 _ fit (by omega) (by omega)).trans
      ((quad2_copy_outside b1 _ fit (by omega) (by omega)).trans
      ((quad2_copy_outside b0 _ fit (by omega) (by omega)).trans
        (byte_of_mem m0 _))))
  · intro reg a b c d e' f h
    change (runCode quad2ExitCode s3 1).getReg reg = _
    rw [e.2.2.2 reg a, keep reg b e' h, g.2.2.2 reg c d f]
  · intro address below
    have top : (quad2Part state).getMem (BitVec.ofNat 64 address) = s3.getMem (BitVec.ofNat 64 address) := by
      simp only [MachineState.getMem, m4]
    have bottom : s0.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
      simp only [MachineState.getMem, m0]
    exact top.trans ((l2.input address below).trans ((l1.input address below).trans
      ((l0.input address below).trans bottom)))

end TwoPermutationPrototype.QuadOpening
