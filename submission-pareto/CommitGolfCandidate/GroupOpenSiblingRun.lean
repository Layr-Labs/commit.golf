import CommitGolfCandidate.GroupOpenCopy
import CommitGolfCandidate.TwoPermutationPackedOpeningCapEmit
import CommitGolfCandidate.GroupOpenGeometry
import CommitGolfCandidate.GroupOpenWideCopy28
import CommitGolfCandidate.GroupOpenWideCopyA1
import CommitGolfCandidate.GroupOpenWideCopy16

import CommitGolfCandidate.GroupOpenAlignedFields
import CommitGolfCandidate.GroupOpenWholeLayout

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

def levelPC (ordinal level : Nat) : Word :=
  if 3 ≤ level ∧ level ≤ 12 then AlignedFields.pcAt (AlignedFields.start (AlignedFields.classOf ordinal) (level-2))
  else lowerPC level

structure LowerCursor (state : MachineState) (index : Index) (ordinal level : Nat) : Prop where
  pc : state.pc = levelPC ordinal level
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  node : state.getReg .x6 = BitVec.ofNat 64 (upperNode index level)
  dest : state.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level)

def a1Block (state : MachineState) : MachineState := rowsState state a1Rows 2

/-- Level 0's two-row head (pointer load and jump). -/
def zeroBlock (state : MachineState) : MachineState := rowsState state zeroRows 2

/-- Levels 0..12 (level 13 is the fold block): head, copy, then the plain tail, or A1 for level 1. Level 0's head
loads the copy source from the pointer word. -/
def siblingBlock (level : Fin 14) (state : MachineState) : MachineState :=
  if level.val = 0 then tailPrefix (copyState (siblingSite level) (zeroBlock state)) level 2
  else if level.val = 1 then a1Block (WriterA1.state (headPrefix state 3))
  else AlignedFields.block level state

/-- Cycles of one 32-byte wide copy into record `ordinal` (all four wide sites of a record share its
alignment, since the site offsets 16, 48, 80 and 112 are multiples of 8). -/
def recordCopyCost (ordinal : Nat) : Nat := wideCost (recordBase ordinal)

theorem wide_cost_shift (a k : Nat) : wideCost (a+8*k) = wideCost a := by
  unfold wideCost
  rw [Nat.add_mul_mod_self_left]

/-- Cycles of the 32-byte level-1 copy or 30-byte copy of writer levels 2..12. -/
def levelCopyCost (ordinal level : Nat) : Nat :=
  if level = 1 then WriterA1.cycles (siblingDestination ordinal level) else AlignedFields.cost (siblingDestination ordinal level)+AlignedFields.enterCost level+AlignedFields.leaveCost level

/-- The copies of writer levels 1..12 of record `ordinal`. -/
def levelCopies (ordinal : Nat) : Nat :=
  levelCopyCost ordinal 1+levelCopyCost ordinal 2+levelCopyCost ordinal 3+levelCopyCost ordinal 4+levelCopyCost ordinal 5+
    levelCopyCost ordinal 6+levelCopyCost ordinal 7+levelCopyCost ordinal 8+levelCopyCost ordinal 9+
    levelCopyCost ordinal 10+levelCopyCost ordinal 11+levelCopyCost ordinal 12

theorem wide30_cost_shift (a k : Nat) : wide30Cost (a+8*k) = wide30Cost a := by
  unfold wide30Cost
  rw [Nat.add_mul_mod_self_left, show a+8*k = a+4*(2*k) by omega, Nat.add_mul_mod_self_left]

theorem level_copy_cost_mod (ordinal level : Nat) : levelCopyCost ordinal level = levelCopyCost (ordinal%4) level := by
  unfold levelCopyCost WriterA1.cycles AlignedFields.cost siblingDestination recordBase
  rw [show proofBase+recordBytes*ordinal+siblingOffset level =
    proofBase+recordBytes*(ordinal%4)+siblingOffset level+8*(267*(ordinal/4)) by
      unfold recordBytes; have := Nat.mod_add_div ordinal 4; omega]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, show 8 % 4 = 0 from rfl,
    show 8 % 8 = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem record_copy_cost_mod (ordinal : Nat) : recordCopyCost ordinal = recordCopyCost (ordinal%4) := by
  unfold recordCopyCost recordBase
  rw [show proofBase+recordBytes*ordinal = proofBase+recordBytes*(ordinal%4)+8*(267*(ordinal/4)) by
      unfold recordBytes; have := Nat.mod_add_div ordinal 4; omega, wide_cost_shift]

theorem level_copies_mod (ordinal : Nat) : levelCopies ordinal = levelCopies (ordinal%4) := by
  unfold levelCopies
  simp only [level_copy_cost_mod ordinal, Nat.mod_mod]

/-- The final 28-byte copy of a record. -/
def lastCopyCost (ordinal : Nat) : Nat := Writer28.cycles (siblingDestination ordinal 13)

theorem last_copy_cost_mod (ordinal : Nat) : lastCopyCost ordinal = lastCopyCost (ordinal%4) := by
  unfold lastCopyCost siblingDestination recordBase
  rw [show proofBase+recordBytes*ordinal+siblingOffset 13 =
    proofBase+recordBytes*(ordinal%4)+siblingOffset 13+8*(267*(ordinal/4)) by
      unfold recordBytes; have := Nat.mod_add_div ordinal 4; omega]
  unfold Writer28.cycles
  rw [Nat.add_mul_mod_self_left, show
    proofBase+recordBytes*(ordinal%4)+siblingOffset 13+8*(267*(ordinal/4)) =
    proofBase+recordBytes*(ordinal%4)+siblingOffset 13+4*(2*(267*(ordinal/4))) by omega,
    Nat.add_mul_mod_self_left]

def nonceCopyCost (ordinal : Nat) : Nat := Writer16.cycles (recordBase ordinal)

theorem nonce_copy_cost_mod (ordinal : Nat) : nonceCopyCost ordinal = nonceCopyCost (ordinal%4) := by
  unfold nonceCopyCost Writer16.cycles recordBase
  have eq : proofBase+recordBytes*ordinal = proofBase+recordBytes*(ordinal%4)+4*(534*(ordinal/4)) := by
    unfold recordBytes; have := Nat.mod_add_div ordinal 4; omega
  rw [eq, Nat.add_mul_mod_self_left]

/-- Alignment-dependent cycles of all writer copies in a record. -/
def recordExtra (ordinal : Nat) := Whole.pageCost ordinal-124+Whole.firstCost ordinal

theorem record_extra_le (ordinal : Nat) : recordExtra ordinal≤517 := by
  have h : ∀ c : Fin 4, Whole.row c 22-Whole.row c 0-124≤516 := by decide
  have k : Whole.row (Whole.pageClass ordinal) 22-Whole.row (Whole.pageClass ordinal) 0-124≤516 := h ⟨Whole.pageClass ordinal,Whole.class_lt ordinal⟩
  unfold recordExtra Whole.pageCost Whole.firstCost;split <;> omega

/-- Cycles of a lower-level block: levels 0..1 copy 32 bytes, levels 2..12 copy 30; level 0's head is two rows. -/
def siblingCost (ordinal level : Nat) : Nat :=
  if level = 0 then 4+recordCopyCost ordinal else 5+levelCopyCost ordinal level

theorem sibling_site_wide : ∀ level : Fin 14, (siblingSite level).wide = decide (level.val = 0) := by
  decide

theorem sibling_site_wide30 : ∀ level : Fin 14,
    (siblingSite level).wide30 = decide (2 ≤ level.val ∧ level.val ≤ 12) := by
  decide

theorem zero_copy_cost (ordinal : Nat) : copyCost (siblingSite 0) (siblingDestination ordinal 0) = recordCopyCost ordinal := by
  change wideCost (recordBase ordinal+112) = wideCost (recordBase ordinal)
  exact wide_cost_shift (recordBase ordinal) 14

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
    a1Block state = execInstrBr (execInstrBr state (.ADDI .x21 .x21 32)) (.SRLI .x6 .x6 1) := rfl

theorem a1_block_memory (state : MachineState) : (a1Block state).mem = state.mem := rfl

theorem a1_block_register (state : MachineState) :
    (a1Block state).getReg .x21 = state.getReg .x21 + 32#64 ∧
    (a1Block state).getReg .x6 = state.getReg .x6 >>> 1 ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x6 → reg ≠ .x31 → (a1Block state).getReg reg = state.getReg reg := by
  rw [a1_unfold]
  refine ⟨by simp [execInstrBr, signExtend12], by simp [execInstrBr], ?_⟩
  intro reg a b c
  simp [execInstrBr, Ne.symm a, Ne.symm b]

theorem a1_block_run (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*220)) :
    RunsOpeningBlock state (a1Block state) 2 ∧ (a1Block state).pc = BitVec.ofNat 64 (4096+4*222) := by
  have start : ∀ inside : 0 < a1Rows.length, state.pc = BitVec.ofNat 64 (4096+4*a1Rows[0].1) :=
    fun _ => pc
  refine ⟨fun fuel coins => execute_rows state a1Rows a1_code start ?_ fuel coins, ?_⟩
  · intro i inside
    have small : i < 2 := inside
    interval_cases i <;> rfl
  · exact (rows_after_pc state a1Rows a1_code start 1 rfl).trans a1_final_pc

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

private theorem execute_aligned_sibling (s : MachineState) (i : Index) (o : Nat) (bounded : o < LENGTH)
    (l : Fin 14) (lo : 2 ≤ l.val) (hi : l.val ≤ 12) (cur : LowerCursor s i o l.val) :
    SiblingTrace s (siblingBlock l s) i o l := by
  let c : Fin 4 := ⟨AlignedFields.classOf o, AlignedFields.class_lt o⟩
  let k : Fin 11 := ⟨l.val-2, by omega⟩
  let T := siblingDestination o l.val
  let S := siblingAddress i l.val
  let e := AlignedFields.enter l s
  let h := headPrefix e 3
  let m := AlignedFields.copyBody ((s.getReg .x21).toNat%8) h
  let t := tailPrefix m l 2
  let u := AlignedFields.leave l t
  have width : siblingWidth l.val = 30 := by simp [siblingWidth,show ¬l.val<2 by omega,show l.val<13 by omega]
  have fits := all_sibling_copies_fit i o l.val bounded l.isLt
  rw [width] at fits
  obtain ⟨_,even,apart,room⟩ := fits
  have fit : T < 2^64 := by unfold T; unfold MEMORY_BYTES at room; omega
  have tn : (s.getReg .x21).toNat=T := by rw [cur.dest,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  have rr : T%8=AlignedFields.residue c k := AlignedFields.target_class o l.val lo hi
  have entry : RunsOpeningBlock s e (AlignedFields.enterCost l.val) ∧
      e.pc=AlignedFields.pcAt (AlignedFields.start c k) ∧ e.mem=s.mem ∧
      ∀ r, r ≠ .x31 → r ≠ .x29 → e.getReg r=s.getReg r := by
    by_cases first : l.val=2
    · have at222 : s.pc=AlignedFields.pcAt 222 := by simpa [first,levelPC,lowerPC,siblingStart,siblingSite,CopySite.start,AlignedFields.pcAt] using cur.pc
      have bits := CapCopy.mask_bits s T 7 (by simp) cur.dest fit
      have cls : T%8=2*c.val := by simpa [first,k,AlignedFields.residue, Nat.mod_eq_of_lt (show 2*c.val<8 by have := c.isLt; omega)] using rr
      rw [show 7+1=8 by decide, cls] at bits
      simpa [e,AlignedFields.enter,AlignedFields.enterCost,first,k] using AlignedFields.dispatch_run s c at222 bits
    · have range : 3≤l.val ∧ l.val≤12 := by omega
      have entryPC : s.pc = AlignedFields.pcAt (AlignedFields.start c k) := by simpa only [levelPC,if_pos range,c,k] using cur.pc
      simp only [e,AlignedFields.enter,AlignedFields.enterCost,if_neg first]
      exact ⟨run_zero s,entryPC,trivial,fun _ _ _ => trivial⟩
  obtain ⟨runE,pcE,memE,regE⟩ := entry
  have head := sibling_head_post e
  have runH : RunsOpeningBlock e h 3 := AlignedFields.head_run c k e pcE
  have pcH : h.pc=AlignedFields.pcAt (AlignedFields.start c k+3) := by
    change (headPrefix e 3).pc=_
    rw [head.1,pcE]
    exact ofNat_step _ 3
  have srcH : h.getReg .x7=BitVec.ofNat 64 S := physical_sibling_source e i l.val (by omega)
    ((regE _ (by decide) (by decide)).trans cur.heap) ((regE _ (by decide) (by decide)).trans cur.node)
  have dstH : h.getReg .x21=BitVec.ofNat 64 T :=
    (head.2.2.2 _ (by decide)).trans ((regE _ (by decide) (by decide)).trans cur.dest)
  have copy : CapCopy.Done h m S T 30 (AlignedFields.cost T) (AlignedFields.start c k+3+AlignedFields.cost T) := by
    unfold m
    rw [tn]
    exact AlignedFields.copy_body_run c k h S T pcH srcH dstH (sibling_address_inside i l.val).1 even rr apart room
  have round : AlignedFields.cost T = AlignedFields.cost (AlignedFields.residue c k) := by
    simp only [AlignedFields.cost,← rr,Nat.mod_mod]
  have runT : RunsOpeningBlock m t 2 := AlignedFields.tail_run c k m l width (by rw [← round]; exact copy.pc)
  have tail := sibling_tail_post m l
  have pcT : t.pc = AlignedFields.pcAt (AlignedFields.start c (k.val+1)) := by
    change (tailPrefix m l 2).pc=_
    rw [tail.1,copy.pc,round]
    exact ofNat_step _ 2
  have exit : RunsOpeningBlock t u (AlignedFields.leaveCost l.val) ∧ u.pc=levelPC o (l.val+1) ∧
      u.mem=t.mem ∧ ∀ r, u.getReg r=t.getReg r := by
    by_cases last : l.val=12
    · have k10 : k.val=10 := by simp [k,last]
      rw [k10] at pcT
      simp only [u,AlignedFields.leave,AlignedFields.leaveCost,if_pos last]
      exact ⟨AlignedFields.return_run t c pcT, by rw [last]; rfl, rfl, fun _ => MachineState.getReg_setPC ..⟩
    · have range : 3≤l.val+1 ∧ l.val+1≤12 := by omega
      have eq : l.val+1-2=k.val+1 := by dsimp [k]; omega
      simp only [u,AlignedFields.leave,AlignedFields.leaveCost,if_neg last,levelPC,if_pos range,eq]
      exact ⟨run_zero t,pcT,trivial,fun _ => trivial⟩
  obtain ⟨runU,pcU,memU,regU⟩ := exit
  have regH (r : Reg) (a : r ≠ .x7) (b : r ≠ .x31) (d : r ≠ .x29) : h.getReg r=s.getReg r :=
    (head.2.2.2 r a).trans (regE r b d)
  have kept (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (cc : r ≠ .x21) (d : r ≠ .x31) (ee : r ≠ .x29) :
      u.getReg r=s.getReg r :=
    (regU r).trans ((tail.2.2.2.2 r cc a).trans ((copy.regs r d).trans (regH r b d ee)))
  have memH : h.mem=s.mem := head.2.1.trans memE
  have memEnd : u.mem=m.mem := memU.trans tail.2.1
  have block : siblingBlock l s = u := by simp only [siblingBlock,if_neg (show l.val ≠ 0 by omega),if_neg (show l.val ≠ 1 by omega)]; rfl
  rw [block]
  refine ⟨?_,⟨pcU, (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans cur.heap, ?_, ?_⟩,
    ?_, kept, ?_⟩
  · have cost : siblingCost o l.val = AlignedFields.enterCost l.val+3+AlignedFields.cost T+2+AlignedFields.leaveCost l.val := by
      simp only [siblingCost,levelCopyCost,if_neg (show l.val≠0 by omega),if_neg (show l.val≠1 by omega),T]
      omega
    rw [cost]
    exact (((runE.next runH).next copy.run).next runT).next runU
  · rw [regU]
    exact physical_sibling_parent i l ((copy.regs _ (by decide)).trans ((regH _ (by decide) (by decide) (by decide)).trans cur.node))
  · rw [regU]
    exact physical_sibling_destination o l ((copy.regs _ (by decide)).trans dstH)
  · rw [width]
    exact copy.bytes.move memH.symm memEnd
  · intro a low
    have base : proofBase≤T := by unfold T siblingDestination recordBase; omega
    have al : proofBase%8=0 := by decide
    have le : (BitVec.ofNat 64 a).toNat<T-T%8 := by
      rw [BitVec.toNat_ofNat]; have := Nat.mod_le a (2^64); omega
    have saved := copy.below _ le
    simpa only [MachineState.getMem,memH,memEnd] using saved

private theorem execute_sibling_one (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (level : Fin 14) (inner : level.val < 13) (nz : level.val ≠ 0) (one : level.val=1) (cursor : LowerCursor state index ordinal level.val) :
    SiblingTrace state (siblingBlock level state) index ordinal level := by
  let site := siblingSite level
  let prepared := headPrefix state 3
  let copied := copyState site prepared
  have head := sibling_head_post state
  have ordinalFit := all_sibling_copies_fit index ordinal level.val bounded level.isLt
  have start : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level) := by
    have h : levelPC ordinal level.val = lowerPC level.val := by simp [levelPC,one]
    simpa only [h, lowerPC, dif_pos level.isLt, Fin.eta] using cursor.pc
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*site.start) := by
    rw [head.1, start]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 12 = _
    rw [← BitVec.ofNat_add, ← sibling_copy_start level nz]
    congr 1
  have srcReg : prepared.getReg .x7 = BitVec.ofNat 64 (siblingAddress index level.val) :=
    physical_sibling_source state index _ nz cursor.heap cursor.node
  have dstReg : prepared.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level.val) :=
    (head.2.2.2 .x21 (by decide)).trans cursor.dest
  have ranHead : RunsOpeningBlock state prepared 3 :=
    fun fuel coins => execute_sibling_head state level nz (by omega) start fuel coins
  have ram : MEMORY_BYTES < 2^64 := by decide
  have levelEq : level = 1 := Fin.ext one
  have blockEq : siblingBlock level state = a1Block (WriterA1.state prepared) := by
    unfold siblingBlock; rw [if_neg nz, if_pos one]
  have width : siblingWidth level.val = 32 := by rw [one]; rfl
  have srcFit := ordinalFit.2.2.1
  have dstFit := ordinalFit.2.2.2
  rw [width] at srcFit dstFit
  have copy := WriterA1.copy prepared (siblingAddress index level.val) (siblingDestination ordinal level.val)
    (by simpa [site, levelEq, siblingSite, CopySite.start] using before) srcReg dstReg
    (sibling_address_inside index level.val).1
    ordinalFit.2.1 (by omega) dstFit
  obtain ⟨ranA1, a1PC⟩ := a1_block_run (WriterA1.state prepared) copy.pc
  obtain ⟨r21, r6, rKept⟩ := a1_block_register (WriterA1.state prepared)
  have kept (reg : Reg) (d : reg ≠ .x31) (b : reg ≠ .x7) :
      (WriterA1.state prepared).getReg reg = state.getReg reg :=
    (copy.regs reg d).trans (head.2.2.2 reg b)
  rw [blockEq]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have total := (ranHead.next copy.run).next ranA1
    rw [show 3+WriterA1.cycles (siblingDestination ordinal level.val)+2 =
      siblingCost ordinal level.val by simp [siblingCost, levelCopyCost, one]; omega] at total
    exact total
  · rw [a1PC, one]; rfl
  · rw [rKept .x9 (by decide) (by decide) (by decide), kept .x9 (by decide) (by decide)]
    exact cursor.heap
  · rw [r6, kept .x6 (by decide) (by decide), cursor.node, node_shift]
  · rw [r21, (copy.regs .x21 (by decide)).trans dstReg,
      show (32#64 : Word) = BitVec.ofNat 64 (siblingWidth level.val) by rw [width],
      destination_next ordinal level.val level.isLt]
  · rw [width]
    exact copy.bytes.move head.2.1.symm (a1_block_memory _)
  · intro reg a b c d e
    rw [rKept reg c a d, kept reg d b]
  · intro address below
    change (a1Block (WriterA1.state prepared)).mem _ = _
    rw [a1_block_memory]
    have above : proofBase+32 ≤ siblingDestination ordinal level.val := by
      rw [one]
      change proofBase+32 ≤ proofBase+recordBytes*ordinal+144
      omega
    have low : (BitVec.ofNat 64 address).toNat < siblingDestination ordinal level.val-
        siblingDestination ordinal level.val%8 := by
      simp only [BitVec.toNat_ofNat]
      have := Nat.mod_le address (2^64)
      have := Nat.mod_lt (siblingDestination ordinal level.val) (by decide : 0 < 8)
      omega
    exact (copy.below _ low).trans (by
      change prepared.mem _ = state.mem _
      rw [head.2.1])

theorem execute_sibling (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (level : Fin 14) (inner : level.val < 13) (nz : level.val ≠ 0) (cursor : LowerCursor state index ordinal level.val) :
    SiblingTrace state (siblingBlock level state) index ordinal level := by
  by_cases one : level.val=1
  · exact execute_sibling_one state index ordinal bounded level inner nz one cursor
  · exact execute_aligned_sibling state index ordinal bounded level (by omega) (by omega) cursor

/-- Level 0: the head loads the copy source from the pointer word, then the wide copy and the plain tail. -/
theorem execute_sibling_zero (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (cursor : LowerCursor state index ordinal 0)
    (slot : state.getReg .x7 = BitVec.ofNat 64 (groupSlots+1024*(index.val/4)+584))
    (pointer : state.getMem (BitVec.ofNat 64 (pointerAddress index.val)) = BitVec.ofNat 64 (quadAddress index.val)) :
    SiblingTrace state (siblingBlock 0 state) index ordinal 0 := by
  let prepared := zeroBlock state
  let copied := copyState (siblingSite 0) prepared
  have ordinalFit := all_sibling_copies_fit index ordinal 0 bounded (by decide)
  have start : state.pc = BitVec.ofNat 64 (4096+4*148) := cursor.pc
  have ptrFacts := pointer_address_inside index.val index.isLt
  have addr : state.getReg .x7+signExtend12 128#12 = BitVec.ofNat 64 (pointerAddress index.val) := by
    rw [slot, show signExtend12 128#12 = BitVec.ofNat 64 128 by decide, ← BitVec.ofNat_add]
    unfold pointerAddress
    congr 1
  have access : accessValid (BitVec.ofNat 64 (pointerAddress index.val)) 8 = true :=
    Opening.aligned_access _ ptrFacts.1 (by
      have := ptrFacts.2.2
      have nb : nonceBase = 9126809632 := rfl
      have mb : MEMORY_BYTES = 68719476736 := rfl
      omega)
  have startAll : ∀ inside : 0 < zeroRows.length, state.pc = BitVec.ofNat 64 (4096+4*zeroRows[0].1) :=
    fun _ => start
  have valid : ∀ i (inside : i < zeroRows.length),
      memoryArgumentsValid (rowsState state zeroRows i) zeroRows[i].2 = true := by
    intro i inside
    have small : i < 2 := inside
    interval_cases i
    · simp [rowsState, zeroRows, memoryArgumentsValid, memAccess, addr, access]
    · rfl
  have ranHead : RunsOpeningBlock state prepared 2 :=
    fun fuel coins => execute_rows state zeroRows zero_code startAll valid fuel coins
  have headPC : prepared.pc = BitVec.ofNat 64 (4096+4*(siblingSite 0).start) :=
    (rows_after_pc state zeroRows zero_code startAll 1 rfl).trans zero_final_pc
  have headMem : prepared.mem = state.mem := by
    simp [prepared, zeroBlock, rowsState, zeroRows, execInstrBr]
  have srcReg : prepared.getReg .x7 = BitVec.ofNat 64 (siblingAddress index 0) := by
    have value : prepared.getReg .x7 = state.getMem (BitVec.ofNat 64 (pointerAddress index.val)) := by
      simp [prepared, zeroBlock, rowsState, zeroRows, execInstrBr, addr]
    rw [value, pointer]
    simp [siblingAddress]
  have headKeep (reg : Reg) (b : reg ≠ .x7) : prepared.getReg reg = state.getReg reg := by
    simp [prepared, zeroBlock, rowsState, zeroRows, execInstrBr, Ne.symm b]
  have dstReg : prepared.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal 0) :=
    (headKeep .x21 (by decide)).trans cursor.dest
  have halves : 2*(siblingSite 0).halfwords = siblingWidth 0 := rfl
  have field : FieldInputs (siblingSite 0) prepared (siblingAddress index 0) (siblingDestination ordinal 0) := by
    refine ⟨headPC, by simpa using srcReg, by simpa using dstReg, ?_, ?_, ordinalFit.1, ordinalFit.2.1,
      fun _ => (sibling_address_inside index 0).1⟩
    · rw [halves]; exact ordinalFit.2.2.1
    · rw [halves]; exact ordinalFit.2.2.2
  have keptCopy (reg : Reg) (d : reg ≠ .x31) (b : reg ≠ .x7) (e : reg ≠ .x29) :
      copied.getReg reg = state.getReg reg :=
    (copy_register (siblingSite 0) prepared reg d (.inr e)).trans (headKeep reg b)
  have fieldCost : copyCost (siblingSite 0) (siblingDestination ordinal 0) = recordCopyCost ordinal := by
    exact zero_copy_cost ordinal
  have copiedBytes : ByteCopy state copied (siblingAddress index 0) (siblingDestination ordinal 0)
      (2*(siblingSite 0).halfwords) :=
    field.bytes.move headMem.symm rfl
  have copiedInput (address : Nat) (below : address < proofBase) :
      copied.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
    have above : proofBase ≤ siblingDestination ordinal 0 := by
      unfold siblingDestination recordBase; omega
    have stable := field.words_before proofBase address below above (by decide)
    simpa only [MachineState.getMem, headMem] using stable
  have plain : PlainTail 0 := ⟨by decide, by decide⟩
  have tailPC : copied.pc = BitVec.ofNat 64 (4096+4*siblingEnd 0) := field.final_pc
  have blockEq : siblingBlock 0 state = tailPrefix copied 0 2 := by
    unfold siblingBlock; rw [if_pos (show (0:Fin 14).val = 0 from rfl)]
  let done := tailPrefix copied 0 2
  have tail := sibling_tail_post copied 0
  have ranTail : RunsOpeningBlock copied done 2 :=
    fun fuel coins => execute_sibling_tail copied 0 plain tailPC fuel coins
  have kept (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x31) (e : reg ≠ .x29) :
      done.getReg reg = state.getReg reg :=
    (tail.2.2.2.2 reg c a).trans (keptCopy reg d b e)
  rw [blockEq]
  refine ⟨?_, ⟨?_, (kept .x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.heap, ?_, ?_⟩,
    ?_, kept, ?_⟩
  · have total := (ranHead.next field.run).next ranTail
    rw [fieldCost] at total
    have cost : siblingCost ordinal (0 : Fin 14).val = 2+recordCopyCost ordinal+2 := by
      show (if (0:Fin 14).val = 0 then 4+recordCopyCost ordinal else 5+levelCopyCost ordinal (0:Fin 14).val) = _
      rw [if_pos (show (0:Fin 14).val = 0 from rfl)]; omega
    rw [cost]
    exact total
  · have final : done.pc = BitVec.ofNat 64 (4096+4*(siblingEnd 0+2)) := by
      change (tailPrefix copied 0 2).pc = _
      rw [tail.1, tailPC]
      change BitVec.ofNat 64 _+BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_add]
      congr 1
    exact final.trans (lower_pc_next 0 (by decide))
  · apply physical_sibling_parent
    exact (copy_register (siblingSite 0) prepared .x6 (by decide) (.inr (by decide))).trans
      ((headKeep .x6 (by decide)).trans cursor.node)
  · apply physical_sibling_destination
    exact (copy_register (siblingSite 0) prepared .x21 (by decide) (.inr (by decide))).trans dstReg
  · exact copiedBytes.move rfl tail.2.1
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
