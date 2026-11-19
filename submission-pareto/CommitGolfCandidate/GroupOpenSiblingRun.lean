import CommitGolfCandidate.GroupOpenCopy
import CommitGolfCandidate.TwoPermutationPackedOpeningCapEmit
import CommitGolfCandidate.GroupOpenGeometry

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

theorem set_half_eq (state : MachineState) (address : Word) (value : BitVec 16) :
    state.setHalfword address value = state.setMem (alignToDword address)
      (replaceHalfword (state.getMem (alignToDword address)) ((byteOffset address)/2) value) := rfl

@[simp] theorem get_reg_set_half (state : MachineState) (address : Word) (value : BitVec 16) (reg : Reg) :
    (state.setHalfword address value).getReg reg = state.getReg reg := by
  rw [set_half_eq]; exact Opening.getReg_setMem _ _ _ _

@[simp] theorem pc_set_half (state : MachineState) (address : Word) (value : BitVec 16) :
    (state.setHalfword address value).pc = state.pc := rfl

@[simp] theorem get_half_set_reg (state : MachineState) (reg : Reg) (value : Word) (address : Word) :
    (state.setReg reg value).getHalfword address = state.getHalfword address := by
  simp [MachineState.getHalfword]

@[simp] theorem get_half_set_pc (state : MachineState) (pc : Word) (address : Word) :
    (state.setPC pc).getHalfword address = state.getHalfword address := by
  simp [MachineState.getHalfword]

theorem half_mem_congr {s t : MachineState} (same : s.mem = t.mem) (address : Word) (value : BitVec 16) :
    (s.setHalfword address value).mem = (t.setHalfword address value).mem := by
  rw [set_half_eq, set_half_eq]
  simp only [MachineState.setMem, MachineState.getMem, same]

theorem get_half_congr {s t : MachineState} (same : s.mem = t.mem) (address : Word) :
    s.getHalfword address = t.getHalfword address := by
  simp only [MachineState.getHalfword, MachineState.getMem, same]

/-! ### Halfword moves -/

theorem half_access (address : Nat) (even : address % 2 = 0) (fit : address+2 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 2 = true := by
  have small : address < 2^64 := by unfold MEMORY_BYTES at fit; omega
  have natural : (BitVec.ofNat 64 address).toNat = address := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp [accessValid, rangeValid, natural, even, fit]

theorem truncate_zero_extend (h : BitVec 16) : ((h.zeroExtend 64).truncate 16) = h := by
  apply BitVec.eq_of_toNat_eq
  have fit : h.toNat < 2^16 := h.isLt
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (show h.toNat < 2^64 by omega)]

theorem word_succ (base : Nat) : BitVec.ofNat 64 (base+1) = BitVec.ofNat 64 base+1 := by
  rw [BitVec.ofNat_add]
  rfl

theorem even_word (address : Nat) (even : address % 2 = 0) (fit : address < 2^64) :
    (BitVec.ofNat 64 address).toNat % 2 = 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  exact even

/-- `lhu x31; sh x31` moves one halfword: a two-byte copy. -/
theorem halfword_copy (state : MachineState) (source target : Nat)
    (sourceEven : source % 2 = 0) (targetEven : target % 2 = 0)
    (sourceFit : source+2 ≤ MEMORY_BYTES) (targetFit : target+2 ≤ MEMORY_BYTES) :
    ByteCopy state (state.setHalfword (BitVec.ofNat 64 target)
      (((state.getHalfword (BitVec.ofNat 64 source)).zeroExtend 64).truncate 16)) source target 2 := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  rw [truncate_zero_extend]
  obtain ⟨low, high⟩ := ProjectedHalfword.copy_bytes state (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)
    (even_word source sourceEven (by omega)) (even_word target targetEven (by omega))
  constructor
  · intro i inside
    interval_cases i
    · simpa only [Nat.add_zero] using low
    · rw [word_succ, word_succ]
      exact high
  · intro address outside
    apply ProjectedHalfword.store_outside state _ _ _ (even_word target targetEven (by omega))
    refine ⟨by simpa only [Nat.add_zero] using outside 0 (by omega), ?_⟩
    rw [← word_succ]
    exact outside 1 (by omega)

/-- Two adjacent copies whose second source the first does not overwrite. -/
theorem byte_copy_extend {before middle after : MachineState} {source target first second : Nat}
    (head : ByteCopy before middle source target first)
    (tail : ByteCopy middle after (source+first) (target+first) second)
    (apart : source+first+second ≤ target) (fit : target+first+second ≤ 2^64) :
    ByteCopy before after source target (first+second) := by
  constructor
  · intro i inside
    by_cases low : i < first
    · rw [tail.frame]
      · exact head.copied i low
      · intro j hj same
        have eq := Opening.nat_address_injective (by omega) (by omega) same
        omega
    · have shifted := tail.copied (i-first) (by omega)
      rw [show target+first+(i-first) = target+i by omega, show source+first+(i-first) = source+i by omega] at shifted
      rw [shifted, head.frame]
      intro j hj same
      have eq := Opening.nat_address_injective (by omega) (by omega) same
      omega
  · intro address outside
    rw [tail.frame _ (fun j hj => by
      have := outside (first+j) (by omega)
      rwa [← Nat.add_assoc] at this)]
    exact head.frame _ (fun j hj => outside j (by omega))

/-! ### Level blocks -/

def lowerPC (level : Nat) : Word :=
  if bounded : level < 14 then BitVec.ofNat 64 (4096+4*siblingStart ⟨level,bounded⟩) else 0x1a08

structure LowerCursor (state : MachineState) (index : Index) (ordinal level : Nat) : Prop where
  pc : state.pc = lowerPC level
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  node : state.getReg .x6 = BitVec.ofNat 64 (upperNode index level)
  dest : state.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level)

def a1Block (state : MachineState) : MachineState := rowsState state a1Rows 6

/-- Levels 0..12 (level 13 is the fold block): head, copy, then the plain tail, or A1 for level 1. -/
def siblingBlock (level : Fin 14) (state : MachineState) : MachineState :=
  if level.val = 1 then a1Block (copyState (siblingSite level) (headPrefix state 3))
  else tailPrefix (copyState (siblingSite level) (headPrefix state 3)) level 2

/-- Cycles of one 32-byte wide copy into record `ordinal` (all four wide sites of a record share its
alignment, since the site offsets 16, 48, 80 and 112 are multiples of 8). -/
def recordCopyCost (ordinal : Nat) : Nat := wideCost (recordBase ordinal)

theorem wide_cost_shift (a k : Nat) : wideCost (a+8*k) = wideCost a := by
  unfold wideCost
  rw [Nat.add_mul_mod_self_left]

/-- Cycles of the 30-byte copy of writer level `level` (1..12) of record `ordinal`. -/
def levelCopyCost (ordinal level : Nat) : Nat := wide30Cost (siblingDestination ordinal level)

/-- The 30-byte copies of writer levels 1..12 of record `ordinal`. -/
def levelCopies (ordinal : Nat) : Nat :=
  levelCopyCost ordinal 1+levelCopyCost ordinal 2+levelCopyCost ordinal 3+levelCopyCost ordinal 4+levelCopyCost ordinal 5+
    levelCopyCost ordinal 6+levelCopyCost ordinal 7+levelCopyCost ordinal 8+levelCopyCost ordinal 9+
    levelCopyCost ordinal 10+levelCopyCost ordinal 11+levelCopyCost ordinal 12

theorem wide30_cost_shift (a k : Nat) : wide30Cost (a+8*k) = wide30Cost a := by
  unfold wide30Cost
  rw [Nat.add_mul_mod_self_left, show a+8*k = a+4*(2*k) by omega, Nat.add_mul_mod_self_left]

theorem level_copy_cost_mod (ordinal level : Nat) : levelCopyCost ordinal level = levelCopyCost (ordinal%4) level := by
  unfold levelCopyCost siblingDestination recordBase
  rw [show proofBase+recordBytes*ordinal+siblingOffset level =
    proofBase+recordBytes*(ordinal%4)+siblingOffset level+8*(267*(ordinal/4)) by
      unfold recordBytes; have := Nat.mod_add_div ordinal 4; omega, wide30_cost_shift]

theorem record_copy_cost_mod (ordinal : Nat) : recordCopyCost ordinal = recordCopyCost (ordinal%4) := by
  unfold recordCopyCost recordBase
  rw [show proofBase+recordBytes*ordinal = proofBase+recordBytes*(ordinal%4)+8*(267*(ordinal/4)) by
      unfold recordBytes; have := Nat.mod_add_div ordinal 4; omega, wide_cost_shift]

theorem level_copies_mod (ordinal : Nat) : levelCopies ordinal = levelCopies (ordinal%4) := by
  unfold levelCopies
  simp only [level_copy_cost_mod ordinal, Nat.mod_mod]

/-- The wide-copy cycles of record `ordinal`: its four 32-byte copies and its twelve 30-byte ones. -/
def recordExtra (ordinal : Nat) : Nat := 4*recordCopyCost ordinal+levelCopies ordinal

theorem record_extra_mod (ordinal : Nat) : recordExtra ordinal = recordExtra (ordinal%4) := by
  unfold recordExtra
  rw [record_copy_cost_mod ordinal, level_copies_mod ordinal]

theorem record_extra_le (ordinal : Nat) : recordExtra ordinal ≤ 479 := by
  rw [record_extra_mod]
  have small : ordinal % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize ordinal % 4 = r at small
  interval_cases r <;> decide +kernel

/-- Cycles of the block of level `level < 13` of record `ordinal`: level 0 is a 32-byte wide copy, levels
1..12 30-byte wide copies. -/
def siblingCost (ordinal level : Nat) : Nat :=
  if level = 0 then 5+recordCopyCost ordinal else if level = 1 then 9+levelCopyCost ordinal level else 5+levelCopyCost ordinal level

theorem sibling_site_wide : ∀ level : Fin 14, (siblingSite level).wide = decide (level.val = 0) := by
  decide

theorem sibling_site_wide30 : ∀ level : Fin 14,
    (siblingSite level).wide30 = decide (1 ≤ level.val ∧ level.val ≤ 12) := by
  decide

theorem sibling_copy_cost (level : Fin 14) (ordinal : Nat) :
    copyCost (siblingSite level) (siblingDestination ordinal level.val) =
      if level.val = 0 then recordCopyCost ordinal
      else if 1 ≤ level.val ∧ level.val ≤ 12 then levelCopyCost ordinal level.val
      else 2*(siblingSite level).halfwords := by
  unfold copyCost
  rw [sibling_site_wide level, sibling_site_wide30 level]
  by_cases zero : level.val = 0
  · rw [if_pos (decide_eq_true zero), if_pos zero]
    simp only [recordCopyCost, siblingDestination, zero, siblingOffset]
    rw [show recordBase ordinal + (if 0 < 2 then 112 + 32 * 0 else if 0 < 14 then 176 + 30 * (0 - 2) else 534) =
      recordBase ordinal + 8*14 by simp, wide_cost_shift]
  · rw [if_neg (by simpa using zero), if_neg zero]
    by_cases mid : 1 ≤ level.val ∧ level.val ≤ 12
    · rw [if_pos (decide_eq_true mid), if_pos mid]; rfl
    · rw [if_neg (by simpa using mid), if_neg mid]

theorem lower_pc_next (level : Fin 14) (inner : level.val < 13) :
    BitVec.ofNat 64 (4096+4*(siblingEnd level+2)) = lowerPC (level.val+1) := by
  unfold lowerPC
  rw [dif_pos (by omega), sibling_next level (by omega)]

private theorem mem_set_mem (state : MachineState) (address value : Word) :
    (state.setMem address value).mem =
      fun atAddress => if atAddress = address then value else state.mem atAddress := by
  funext atAddress
  simp [MachineState.setMem]

theorem a1_unfold (state : MachineState) :
    a1Block state = execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr state
      (.JAL .x0 (BitVec.ofNat 21 (4*(a1Start-220))))) (.LHU .x31 .x7 30)) (.SH .x21 .x31 30))
      (.ADDI .x21 .x21 32)) (.JAL .x0 (BitVec.ofNat 21 (2^21-4*(a1Start+3-221))))) (.SRLI .x6 .x6 1) := rfl

/-- The A1 block for any jump immediates (kept abstract so `simp` does not evaluate them). -/
def a1Shape (state : MachineState) (j1 j2 : BitVec 21) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr state
    (.JAL .x0 j1)) (.LHU .x31 .x7 30)) (.SH .x21 .x31 30)) (.ADDI .x21 .x21 32)) (.JAL .x0 j2)) (.SRLI .x6 .x6 1)

theorem a1_shape_memory (state : MachineState) (j1 j2 : BitVec 21) :
    (a1Shape state j1 j2).mem = (state.setHalfword (state.getReg .x21 + signExtend12 30)
      (((state.getHalfword (state.getReg .x7 + signExtend12 30)).zeroExtend 64).truncate 16)).mem := by
  unfold a1Shape
  simp only [execInstrBr, mem_set_pc, mem_set_register, MachineState.getReg_setPC, Opening.getReg_setReg,
    get_half_set_reg, get_half_set_pc, reduceCtorEq, false_and, and_true, ite_false, ne_eq, not_false_eq_true,
    and_self, ite_true]
  exact half_mem_congr (by simp only [mem_set_pc, mem_set_register]) _ _

theorem a1_shape_register (state : MachineState) (j1 j2 : BitVec 21) :
    (a1Shape state j1 j2).getReg .x21 = state.getReg .x21 + 32#64 ∧
    (a1Shape state j1 j2).getReg .x6 = state.getReg .x6 >>> 1 ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x6 → reg ≠ .x31 → (a1Shape state j1 j2).getReg reg = state.getReg reg := by
  unfold a1Shape
  refine ⟨?_, ?_, ?_⟩
  · simp [execInstrBr, signExtend12]
  · simp [execInstrBr]
  · intro reg a b c
    simp [execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

theorem a1_block_memory (state : MachineState) :
    (a1Block state).mem = (state.setHalfword (state.getReg .x21 + signExtend12 30)
      (((state.getHalfword (state.getReg .x7 + signExtend12 30)).zeroExtend 64).truncate 16)).mem := by
  rw [a1_unfold]
  exact a1_shape_memory state _ _

theorem a1_block_register (state : MachineState) :
    (a1Block state).getReg .x21 = state.getReg .x21 + 32#64 ∧
    (a1Block state).getReg .x6 = state.getReg .x6 >>> 1 ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x6 → reg ≠ .x31 → (a1Block state).getReg reg = state.getReg reg := by
  rw [a1_unfold]
  exact a1_shape_register state _ _

theorem signed_thirty : signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 := by decide

theorem a1_block_run (state : MachineState) (source target : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*220))
    (src : state.getReg .x7 = BitVec.ofNat 64 source) (dst : state.getReg .x21 = BitVec.ofNat 64 target)
    (sourceEven : source % 2 = 0) (targetEven : target % 2 = 0)
    (sourceFit : source+32 ≤ MEMORY_BYTES) (targetFit : target+32 ≤ MEMORY_BYTES) :
    RunsOpeningBlock state (a1Block state) 6 ∧ (a1Block state).pc = BitVec.ofNat 64 (4096+4*222) := by
  have start : ∀ inside : 0 < a1Rows.length, state.pc = BitVec.ofNat 64 (4096+4*a1Rows[0].1) :=
    fun _ => pc
  refine ⟨fun fuel coins => execute_rows state a1Rows a1_code start ?_ fuel coins, ?_⟩
  · intro i inside
    have small : i < 6 := inside
    interval_cases i
    · rfl
    · change accessValid ((rowsState state a1Rows 1).getReg .x7 + signExtend12 30) 2 = true
      have r : (rowsState state a1Rows 1).getReg .x7 = BitVec.ofNat 64 source := by
        simp [rowsState, a1Rows, execInstrBr, src]
      rw [r, signed_thirty, ← BitVec.ofNat_add]
      exact half_access _ (by omega) (by omega)
    · change accessValid ((rowsState state a1Rows 2).getReg .x21 + signExtend12 30) 2 = true
      have r : (rowsState state a1Rows 2).getReg .x21 = BitVec.ofNat 64 target := by
        simp [rowsState, a1Rows, execInstrBr, dst]
      rw [r, signed_thirty, ← BitVec.ofNat_add]
      exact half_access _ (by omega) (by omega)
    · rfl
    · rfl
    · rfl
  · exact (rows_after_pc state a1Rows a1_code start 5 rfl).trans a1_final_pc

theorem a1_block_bytes (state : MachineState) (source target : Nat)
    (src : state.getReg .x7 = BitVec.ofNat 64 source) (dst : state.getReg .x21 = BitVec.ofNat 64 target)
    (sourceEven : source % 2 = 0) (targetEven : target % 2 = 0)
    (sourceFit : source+32 ≤ MEMORY_BYTES) (targetFit : target+32 ≤ MEMORY_BYTES) :
    ByteCopy state (a1Block state) (source+30) (target+30) 2 := by
  have copy := halfword_copy state (source+30) (target+30) (by omega) (by omega) (by omega) (by omega)
  apply copy.move rfl
  rw [a1_block_memory, src, dst, signed_thirty, ← BitVec.ofNat_add, ← BitVec.ofNat_add]

structure SiblingTrace (state after : MachineState) (index : Index) (ordinal : Nat) (level : Fin 14) : Prop where
  run : RunsOpeningBlock state after (siblingCost ordinal level.val)
  next : LowerCursor after index ordinal (level.val+1)
  bytes : ByteCopy state after (siblingAddress index level.val)
    (siblingDestination ordinal level.val) (siblingWidth level.val)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 → reg ≠ .x29 →
    after.getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    after.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

private theorem halfword_words_below (state : MachineState) (address target : Nat) (value : BitVec 16)
    (below : address < proofBase) (above : proofBase ≤ target) (fit : target+2 ≤ MEMORY_BYTES) :
    (state.setHalfword (BitVec.ofNat 64 target) value).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  rw [set_half_eq]
  apply MachineState.getMem_setMem_ne
  intro equal
  have limit : MEMORY_BYTES+8 ≤ 2^64 := by decide
  have align := aligned_dword_above proofBase target (by decide) above (by omega)
  rw [← equal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)] at align
  omega

theorem execute_sibling (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (level : Fin 14) (inner : level.val < 13) (cursor : LowerCursor state index ordinal level.val) :
    SiblingTrace state (siblingBlock level state) index ordinal level := by
  let site := siblingSite level
  let prepared := headPrefix state 3
  let copied := copyState site prepared
  have head := sibling_head_post state
  have ordinalFit := all_sibling_copies_fit index ordinal level.val bounded level.isLt
  have exact := sibling_width_exact level
  have narrow : 2*site.halfwords ≤ siblingWidth level.val := by
    change 2*(siblingSite level).halfwords ≤ _
    rw [exact]
    split
    · rename_i one; simp [siblingWidth, one]
    · exact Nat.le_refl _
  have start : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level) := by
    simpa only [lowerPC, dif_pos level.isLt, Fin.eta] using cursor.pc
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*site.start) := by
    rw [head.1, start]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 12 = _
    rw [← BitVec.ofNat_add, ← sibling_copy_start level]
    congr 1
  have srcReg : prepared.getReg .x7 = BitVec.ofNat 64 (siblingAddress index level.val) :=
    physical_sibling_source state index _ cursor.heap cursor.node
  have dstReg : prepared.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level.val) :=
    (head.2.2.2 .x21 (by decide)).trans cursor.dest
  have field : FieldInputs site prepared (siblingAddress index level.val)
      (siblingDestination ordinal level.val) := by
    refine ⟨before, by simpa [site] using srcReg, by simpa [site] using dstReg, ?_, ?_, ordinalFit.1, ordinalFit.2.1,
      fun _ => ?_⟩
    · have := ordinalFit.2.2.1; omega
    · have := ordinalFit.2.2.2; omega
    · have base : trapdoorBase % 8 = 0 := by decide
      unfold siblingAddress; omega
  have tailPC : copied.pc = BitVec.ofNat 64 (4096+4*siblingEnd level) := field.final_pc
  have ranHead : RunsOpeningBlock state prepared 3 :=
    fun fuel coins => execute_sibling_head state level start fuel coins
  have keptCopy (reg : Reg) (d : reg ≠ .x31) (b : reg ≠ .x7) (e : reg ≠ .x29) :
      copied.getReg reg = state.getReg reg :=
    (copy_register site prepared reg d (.inr e)).trans (head.2.2.2 reg b)
  have fieldCost := sibling_copy_cost level ordinal
  have copiedBytes : ByteCopy state copied (siblingAddress index level.val)
      (siblingDestination ordinal level.val) (2*site.halfwords) :=
    field.bytes.move head.2.1.symm rfl
  have copiedInput (address : Nat) (below : address < proofBase) :
      copied.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
    have above : proofBase ≤ siblingDestination ordinal level.val := by
      unfold siblingDestination recordBase; omega
    have stable := field.words_before proofBase address below above (by decide)
    have reads : prepared.mem = state.mem := head.2.1
    simpa only [MachineState.getMem, reads] using stable
  have ram : MEMORY_BYTES < 2^64 := by decide
  by_cases one : level.val = 1
  · have blockEq : siblingBlock level state = a1Block copied := by unfold siblingBlock; rw [if_pos one]
    have srcCopied : copied.getReg .x7 = BitVec.ofNat 64 (siblingAddress index level.val) :=
      (copy_register site prepared .x7 (by decide) (.inr (by decide))).trans srcReg
    have dstCopied : copied.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level.val) :=
      (copy_register site prepared .x21 (by decide) (.inr (by decide))).trans dstReg
    have width : siblingWidth level.val = 32 := by rw [one]; rfl
    have halves : 2*site.halfwords = 30 := by change 2*(siblingSite level).halfwords = 30; rw [exact, if_pos one]
    have srcFit : siblingAddress index level.val+32 ≤ MEMORY_BYTES := by
      have := ordinalFit.2.2.1; have := ordinalFit.2.2.2; omega
    have dstFit : siblingDestination ordinal level.val+32 ≤ MEMORY_BYTES := by
      have := ordinalFit.2.2.2; omega
    have tail220 : copied.pc = BitVec.ofNat 64 (4096+4*220) := by
      rw [tailPC]; rw [show level = 1 from Fin.ext one]; rfl
    obtain ⟨ranA1, a1PC⟩ := a1_block_run copied _ _ tail220 srcCopied dstCopied ordinalFit.1 ordinalFit.2.1
      srcFit dstFit
    have a1Bytes := a1_block_bytes copied _ _ srcCopied dstCopied ordinalFit.1 ordinalFit.2.1 srcFit dstFit
    obtain ⟨r21, r6, rKept⟩ := a1_block_register copied
    rw [blockEq]
    refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · have total := (ranHead.next field.run).next ranA1
      rw [fieldCost, if_neg (by omega), if_pos (by omega)] at total
      have cost : siblingCost ordinal level.val = 3+levelCopyCost ordinal level.val+6 := by simp [siblingCost, one]; omega
      rw [cost]
      exact total
    · rw [a1PC, one]
      rfl
    · rw [rKept .x9 (by decide) (by decide) (by decide), keptCopy .x9 (by decide) (by decide) (by decide)]
      exact cursor.heap
    · rw [r6, keptCopy .x6 (by decide) (by decide) (by decide), cursor.node, node_shift]
    · rw [r21, dstCopied, show (32#64 : Word) = BitVec.ofNat 64 (siblingWidth level.val) by rw [width],
        destination_next ordinal level.val level.isLt]
    · rw [width]
      have c30 : ByteCopy state copied (siblingAddress index level.val)
          (siblingDestination ordinal level.val) 30 := by
        rw [← halves]; exact copiedBytes
      exact byte_copy_extend c30 a1Bytes (by have := ordinalFit.2.2.1; rw [width] at this; omega) (by omega)
    · intro reg a b c d e
      rw [rKept reg c a d, keptCopy reg d b e]
    · intro address below
      have above : proofBase ≤ siblingDestination ordinal level.val := by
        unfold siblingDestination recordBase; omega
      rw [show (a1Block copied).getMem (BitVec.ofNat 64 address) = copied.getMem (BitVec.ofNat 64 address) from by
        change (a1Block copied).mem _ = copied.mem _
        rw [a1_block_memory, dstCopied, srcCopied, signed_thirty, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
        exact halfword_words_below copied address _ _ below (by omega) (by omega)]
      exact copiedInput address below
  · have plain : PlainTail level := ⟨one, by omega⟩
    have blockEq : siblingBlock level state = tailPrefix copied level 2 := by
      unfold siblingBlock; rw [if_neg one]
    let done := tailPrefix copied level 2
    have tail := sibling_tail_post copied level
    have halves : 2*site.halfwords = siblingWidth level.val := by
      change 2*(siblingSite level).halfwords = _; rw [exact, if_neg one]
    have ranTail : RunsOpeningBlock copied done 2 :=
      fun fuel coins => execute_sibling_tail copied level plain tailPC fuel coins
    have kept (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x31) (e : reg ≠ .x29) :
        done.getReg reg = state.getReg reg :=
      (tail.2.2.2.2 reg c a).trans (keptCopy reg d b e)
    rw [blockEq]
    refine ⟨?_, ⟨?_, (kept .x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.heap, ?_, ?_⟩,
      ?_, kept, ?_⟩
    · have total := (ranHead.next field.run).next ranTail
      rw [fieldCost] at total
      by_cases zero : level.val = 0
      · rw [if_pos zero] at total
        have cost : siblingCost ordinal level.val = 3+recordCopyCost ordinal+2 := by
          simp only [siblingCost, if_pos zero]; omega
        rw [cost]
        exact total
      · rw [if_neg zero, if_pos (by omega)] at total
        have cost : siblingCost ordinal level.val = 3+levelCopyCost ordinal level.val+2 := by
          rw [siblingCost, if_neg zero, if_neg one]; omega
        rw [cost]
        exact total
    · have final : done.pc = BitVec.ofNat 64 (4096+4*(siblingEnd level+2)) := by
        change (tailPrefix copied level 2).pc = _
        rw [tail.1, tailPC]
        change BitVec.ofNat 64 _+BitVec.ofNat 64 8 = _
        rw [← BitVec.ofNat_add]
        congr 1
      exact final.trans (lower_pc_next level inner)
    · apply physical_sibling_parent
      exact (copy_register site prepared .x6 (by decide) (.inr (by decide))).trans
        ((head.2.2.2 .x6 (by decide)).trans cursor.node)
    · apply physical_sibling_destination
      exact (copy_register site prepared .x21 (by decide) (.inr (by decide))).trans dstReg
    · rw [← halves]
      exact copiedBytes.move rfl tail.2.1
    · intro address below
      change done.mem _ = _
      rw [show done.mem = copied.mem from tail.2.1]
      exact copiedInput address below


/-! ### Bytes, halfwords and dwords -/

theorem byte_offset_nat (q : Nat) (fit : q < 2^64) : byteOffset (BitVec.ofNat 64 q) = q % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem align_nat (q : Nat) (fit : q+8 ≤ 2^64) : (alignToDword (BitVec.ofNat 64 q)).toNat = q - q % 8 := by
  let word : Word := BitVec.ofNat 64 q
  let aligned := alignToDword word
  have wordAsNat : word.toNat = q := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2^64)]
  have alignedAtMost : aligned.toNat ≤ q := by
    rw [show aligned.toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word = q % 8 := byte_offset_nat q (by omega)
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  change (aligned+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, offset, Nat.mod_eq_of_lt (by omega : q % 8 < 2^64),
    Nat.mod_eq_of_lt (by omega)] at whole
  change aligned.toNat = _
  omega

theorem same_dword (a b : Nat) (fa : a+8 ≤ 2^64) (fb : b+8 ≤ 2^64) (same : a - a % 8 = b - b % 8) :
    alignToDword (BitVec.ofNat 64 a) = alignToDword (BitVec.ofNat 64 b) :=
  BitVec.eq_of_toNat_eq (by rw [align_nat a fa, align_nat b fb]; exact same)

theorem extract_shift (x : BitVec 16) (k : Nat) : x.extractLsb' k 8 = (x >>> k).truncate 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.truncate, BitVec.toNat_setWidth]

theorem half_ext (x y : BitVec 16) (low : x.extractLsb' 0 8 = y.extractLsb' 0 8)
    (high : x.extractLsb' 8 8 = y.extractLsb' 8 8) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have l := congrArg BitVec.toNat low
  have h := congrArg BitVec.toNat high
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at l h
  have hx : x.toNat < 65536 := x.isLt
  have hy : y.toNat < 65536 := y.isLt
  norm_num at l h
  omega

theorem halfword_bytes (s : MachineState) (a : Nat) (even : a % 2 = 0) (fit : a+16 ≤ 2^64) :
    (s.getHalfword (BitVec.ofNat 64 a)).extractLsb' 0 8 = s.getByte (BitVec.ofNat 64 a) ∧
    (s.getHalfword (BitVec.ofNat 64 a)).extractLsb' 8 8 = s.getByte (BitVec.ofNat 64 (a+1)) := by
  have oa := byte_offset_nat a (by omega)
  have ob := byte_offset_nat (a+1) (by omega)
  constructor
  · have low := ProjectedHalfword.load_byte s (BitVec.ofNat 64 a) (BitVec.ofNat 64 a) rfl rfl
    rw [oa, show a % 8 % 2 = 0 by omega, Nat.zero_mul] at low
    rw [extract_shift]
    exact low
  · have high := ProjectedHalfword.load_byte s (BitVec.ofNat 64 a) (BitVec.ofNat 64 (a+1))
      (same_dword _ _ (by omega) (by omega) (by omega)) (by rw [oa, ob]; omega)
    rw [ob, show (a+1) % 8 % 2 = 1 by omega, Nat.one_mul] at high
    rw [extract_shift]
    exact high

theorem halfword_of_bytes (s t : MachineState) (a : Nat) (even : a % 2 = 0) (fit : a+16 ≤ 2^64)
    (low : t.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))
    (high : t.getByte (BitVec.ofNat 64 (a+1)) = s.getByte (BitVec.ofNat 64 (a+1))) :
    t.getHalfword (BitVec.ofNat 64 a) = s.getHalfword (BitVec.ofNat 64 a) := by
  have hs := halfword_bytes s a even fit
  have ht := halfword_bytes t a even fit
  exact half_ext _ _ (by rw [ht.1, hs.1, low]) (by rw [ht.2, hs.2, high])

theorem byte_after_halfword (s : MachineState) (a b : Nat) (v : BitVec 16) (even : a % 2 = 0)
    (fit : a+16 ≤ 2^64) (small : b < 2) :
    (s.setHalfword (BitVec.ofNat 64 a) v).getByte (BitVec.ofNat 64 (a+b)) = v.extractLsb' (8*b) 8 := by
  have oa := byte_offset_nat a (by omega)
  have ob := byte_offset_nat (a+b) (by omega)
  have cond : alignToDword (BitVec.ofNat 64 (a+b)) = alignToDword (BitVec.ofNat 64 a) ∧
      byteOffset (BitVec.ofNat 64 (a+b)) / 2 = byteOffset (BitVec.ofNat 64 a) / 2 :=
    ⟨same_dword _ _ (by omega) (by omega) (by omega), by rw [oa, ob]; omega⟩
  rw [ProjectedHalfword.store_byte, if_pos cond, ob, show (a+b) % 8 % 2 = b by omega, extract_shift, Nat.mul_comm]

/-- Reading a byte only looks at its dword. -/
theorem byte_of_dword (s t : MachineState) (q : Word)
    (same : s.getMem (alignToDword q) = t.getMem (alignToDword q)) : s.getByte q = t.getByte q := by
  unfold MachineState.getByte
  rw [same]

end TwoPermutationPrototype.GroupedOpening
