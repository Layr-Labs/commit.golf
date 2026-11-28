import CommitGolfCandidate.QuadOpeningLevel
import CommitGolfCandidate.Counting
import CommitGolfCandidate.Machine
import CommitGolfCandidate.PentaCapSpec

/-! The dispatching hybrid record writer (words 527-887) and the level-9 table copy (words 888-2775).
Word 11 jumps to word 527; the two setup words turn `x18` into the end pointer of the index list.
Each record copies the salt (words 529-535); each 5-ary level `k = 0 … 4` (words `536 + 10 k`)
computes its digit `d = x6 % 5` and group pointer `x30`, then `jalr`s into copy variant `d` of level
`k` (words `3072 + 320 k + 64 d`), which copies the four other slots in rotation order with fixed
offsets and jumps back to the next level. The 3-ary level 5 (word 586) does the same with the
3-ary variants at words `656 + 32 d`; the binary levels 6-8 (words 597-644) are straight-line.
The latch (words 645-647) loops; word 648 jumps to the table copy, which appends the 224 level-9
nodes. 102 doublewords per record, 301 steps and 364 cycles. Nothing calls the oracle. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling OracleComp
open QOpening (OpeningLayout trapdoorBase proofBase nonceBase indicesBase)
open TwoPermutationPrototype.RV64

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

structure EntryAt (init state : MachineState) (positions : Positions) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*11)
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*0)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  left : state.getReg .x18 = BitVec.ofNat 64 (positions.card-0)
  five : state.getReg .x19 = BitVec.ofNat 64 5
  begin : state.getReg .x15 = BitVec.ofNat 64 proofBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(142*0))
  salts : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  width : state.getReg .x23 = BitVec.ofNat 64 368
  table : state.getReg .x26 = BitVec.ofNat 64 tableBase
  inv : Inv init state (wordSource positions) (142*0)

theorem card_le (positions : Positions) : positions.card ≤ LENGTH := by
  simpa [Index] using Finset.card_le_univ positions

theorem ordinal_index (positions : Positions) (o : Nat) (present : o < positions.card) :
    ordinalIndex positions o = ((positions.sort (· ≤ ·))[o]'(by simpa using present)).val := by
  unfold ordinalIndex
  rw [List.getElem?_eq_getElem (by simpa using present)]
  rfl

theorem ordinal_index_lt (positions : Positions) (o : Nat) : ordinalIndex positions o < LENGTH := by
  unfold ordinalIndex
  cases h : (positions.sort (· ≤ ·))[o]? with
  | none => simp <;> decide
  | some x => simpa using x.isLt

theorem set_pc_pc (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
theorem set_pc_mem (state : MachineState) (pc : Word) : (state.setPC pc).mem = state.mem := rfl

theorem bne_shape (state : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr state (.BNE r₁ r₂ imm) =
      state.setPC (if state.getReg r₁ != state.getReg r₂ then state.pc + signExtend13 imm else state.pc + 4) := by
  simp only [execInstrBr]
  split <;> rfl

theorem decrement (n : Nat) (positive : 1 ≤ n) (small : n < 2^64) :
    BitVec.ofNat 64 n + signExtend12 4095 = BitVec.ofNat 64 (n-1) := by
  rw [show signExtend12 4095 = BitVec.ofNat 64 (2^64-1) by decide, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

private theorem shift_salt (i : Nat) (small : i < 2^40) :
    BitVec.ofNat 64 i <<< (4 : Nat) = BitVec.ofNat 64 (16*i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show i*2^4 % 2^64 = _
  omega

theorem shift_count (c : Nat) (small : c < 2^40) :
    BitVec.ofNat 64 c <<< (3 : Nat) = BitVec.ofNat 64 (8*c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show c*2^3 % 2^64 = _
  omega

theorem tb_val : trapdoorBase = 4294971424 := rfl
theorem pb_val : proofBase = 10804535392 := rfl
theorem nb_val : nonceBase = 6106914848 := rfl

set_option maxRecDepth 100000 in
theorem hyb_codes_rest :
    program[11]? = some hybJump ∧ CodeAt 527 hybSetup ∧ CodeAt 529 hybSalt ∧
    (∀ k < 5, CodeAt (536+10*k) (hybPentaD k)) ∧ (∀ m < 3, CodeAt (597+16*m) (hybBin (m+6))) ∧
    CodeAt 645 [.ADDI .x21 .x21 816, .ADDI .x8 .x8 8] ∧ program[647]? = some (.BNE .x8 .x18 7720) ∧
    CodeAt 888 [.LUI .x30 (hybPage 9), .ADD .x30 .x30 .x9] ∧
    CodeAt 2738 hybHalf ∧ CodeAt 2772 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧
    program[2775]? = some .ECALL := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_done_code : program[648]? = some hybDone ∧ CodeAt 586 hybQuadD := by
  decide +kernel

/-- The copy blocks and the return jump of the five copy variants of 5-ary level `k`. -/
def VariantCodes (k : Nat) : Prop :=
  ∀ v < 5, (∀ j < 4, CodeAt (levelVariantStart k v+8*j) (hybFour .x30 (32*((v+j+1)%5)) (16+128*k+32*j))) ∧
    program[levelVariantStart k v+32]? = some (.JAL .x0 (backJump (levelExitWord k v) (nextStart k)))

instance (k : Nat) : Decidable (VariantCodes k) := by unfold VariantCodes; infer_instance

set_option maxRecDepth 100000 in
theorem variant_codes_0 : VariantCodes 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem variant_codes_1 : VariantCodes 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem variant_codes_2 : VariantCodes 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem variant_codes_3 : VariantCodes 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem variant_codes_4 : VariantCodes 4 := by decide +kernel

theorem variant_codes (k : Nat) (hk : k < 5) : VariantCodes k := by
  interval_cases k
  exacts [variant_codes_0, variant_codes_1, variant_codes_2, variant_codes_3, variant_codes_4]

set_option maxRecDepth 100000 in
theorem quad_variant_codes : ∀ v < 3,
    (∀ t < 2, CodeAt (656+32*v+8*t) (hybFour .x30 (64+32*((v+t+1)%3)) (656+32*t))) ∧
      program[672+32*v]? = some (.JAL .x0 (backJump (672+32*v) 597)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_0 : ∀ i < 3, 3*0+i < 44 → CodeAt (890+42*(3*0+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_1 : ∀ i < 3, 3*1+i < 44 → CodeAt (890+42*(3*1+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_2 : ∀ i < 3, 3*2+i < 44 → CodeAt (890+42*(3*2+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_3 : ∀ i < 3, 3*3+i < 44 → CodeAt (890+42*(3*3+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_4 : ∀ i < 3, 3*4+i < 44 → CodeAt (890+42*(3*4+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_5 : ∀ i < 3, 3*5+i < 44 → CodeAt (890+42*(3*5+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_6 : ∀ i < 3, 3*6+i < 44 → CodeAt (890+42*(3*6+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_7 : ∀ i < 3, 3*7+i < 44 → CodeAt (890+42*(3*7+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_8 : ∀ i < 3, 3*8+i < 44 → CodeAt (890+42*(3*8+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_9 : ∀ i < 3, 3*9+i < 44 → CodeAt (890+42*(3*9+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_10 : ∀ i < 3, 3*10+i < 44 → CodeAt (890+42*(3*10+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_11 : ∀ i < 3, 3*11+i < 44 → CodeAt (890+42*(3*11+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_12 : ∀ i < 3, 3*12+i < 44 → CodeAt (890+42*(3*12+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_13 : ∀ i < 3, 3*13+i < 44 → CodeAt (890+42*(3*13+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_14 : ∀ i < 3, 3*14+i < 44 → CodeAt (890+42*(3*14+i)) hybGroup := by
  decide +kernel

theorem hyb_groups : ∀ g < 44, CodeAt (890+42*g) hybGroup := by
  intro g hg
  have e : g = 3*(g/3)+g%3 := by omega
  have hq : g/3 < 15 := by omega
  have hi : g%3 < 3 := Nat.mod_lt _ (by decide)
  have hr : 3*(g/3)+g%3 < 44 := by omega
  rw [e]; revert hr hi hq; generalize g/3 = q; generalize g%3 = i; intro hq hi hr
  interval_cases q <;> first
    | exact hyb_groups_0 i hi hr
    | exact hyb_groups_1 i hi hr
    | exact hyb_groups_2 i hi hr
    | exact hyb_groups_3 i hi hr
    | exact hyb_groups_4 i hi hr
    | exact hyb_groups_5 i hi hr
    | exact hyb_groups_6 i hi hr
    | exact hyb_groups_7 i hi hr
    | exact hyb_groups_8 i hi hr
    | exact hyb_groups_9 i hi hr
    | exact hyb_groups_10 i hi hr
    | exact hyb_groups_11 i hi hr
    | exact hyb_groups_12 i hi hr
    | exact hyb_groups_13 i hi hr
    | exact hyb_groups_14 i hi hr

theorem hyb_codes :
    program[11]? = some hybJump ∧ CodeAt 527 hybSetup ∧ CodeAt 529 hybSalt ∧
    (∀ k < 5, CodeAt (536+10*k) (hybPentaD k)) ∧ (∀ m < 3, CodeAt (597+16*m) (hybBin (m+6))) ∧
    CodeAt 645 [.ADDI .x21 .x21 816, .ADDI .x8 .x8 8] ∧ program[647]? = some (.BNE .x8 .x18 7720) ∧
    CodeAt 888 [.LUI .x30 (hybPage 9), .ADD .x30 .x30 .x9] ∧ (∀ g < 44, CodeAt (890+42*g) hybGroup) ∧
    CodeAt 2738 hybHalf ∧ CodeAt 2772 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧
    program[2775]? = some .ECALL :=
  let ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hyb_codes_rest
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, hyb_groups, c8, c9, c10⟩

theorem sext_small (x : Nat) (small : x < 2048) : signExtend12 (BitVec.ofNat 12 x) = BitVec.ofNat 64 x := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega),
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]

theorem code_one {start : Nat} {code : List Instr} (at_ : CodeAt start code) (i : Nat) (h : i < code.length) :
    program[start+i]? = some code[i] := by
  rw [at_ i h, List.getElem?_eq_getElem h]

/-- One load/store pair: output word `count` is the doubleword at `S + a`. -/
theorem copy_step (init state : MachineState) (source : Nat → Nat) (index : Nat) (x : Reg) (hx : x ≠ .x31)
    (a b S D count : Nat) (ha : a < 2048) (hb : b < 2048)
    (codeL : program[index]? = some (.LD .x31 x (BitVec.ofNat 12 a)))
    (codeS : program[index+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 b)))
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (from_ : state.getReg x = BitVec.ofNat 64 S) (to_ : state.getReg .x21 = BitVec.ofNat 64 D)
    (target : D+b = proofBase+8*count) (aligned : (S+a) % 8 = 0) (low : trapdoorBase ≤ S+a)
    (high : S+a+8 ≤ proofBase) (fits : proofBase+8*count+8 ≤ MEMORY_BYTES)
    (named : source count = S+a) (inv : Inv init state source count) :
    let after := execInstrBr (execInstrBr state (.LD .x31 x (BitVec.ofNat 12 a))) (.SD .x21 .x31 (BitVec.ofNat 12 b))
    Runs state after 2 2 ∧ Inv init after source (count+1) ∧ after.pc = BitVec.ofNat 64 (4096+4*(index+2)) ∧
      ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  have room : MEMORY_BYTES < 2^64 := by decide
  have below : proofBase ≤ MEMORY_BYTES := by decide
  let loaded := execInstrBr state (.LD .x31 x (BitVec.ofNat 12 a))
  have loadAddress : state.getReg x + signExtend12 (BitVec.ofNat 12 a) = BitVec.ofNat 64 (S+a) := by
    rw [from_, sext_small a ha, ← BitVec.ofNat_add]
  have storeAddress : loaded.getReg .x21 + signExtend12 (BitVec.ofNat 12 b) =
      BitVec.ofNat 64 (proofBase+8*count) := by
    have keep : loaded.getReg .x21 = state.getReg .x21 := by
      simp [loaded, execInstrBr, QOpening.getReg_setReg]
    rw [keep, to_, sext_small b hb, ← BitVec.ofNat_add, target]
  have loadValid : memoryArgumentsValid state (.LD .x31 x (BitVec.ofNat 12 a)) = true := by
    simp only [memoryArgumentsValid, memAccess, loadAddress]
    exact QOpening.aligned_access _ aligned (by omega)
  have storeValid : memoryArgumentsValid loaded (.SD .x21 .x31 (BitVec.ofNat 12 b)) = true := by
    simp only [memoryArgumentsValid, memAccess, storeAddress]
    exact QOpening.aligned_access _ (by have : proofBase % 8 = 0 := by decide
                                        omega) (by omega)
  have loadPC : loaded.pc = BitVec.ofNat 64 (4096+4*(index+1)) :=
    (straight_pc state _ rfl).trans (pc_next _ _ pc)
  have run₁ := runs_one state _ index codeL pc rfl loadValid
  have run₂ := runs_one loaded _ (index+1) codeS loadPC rfl storeValid
  have value : loaded.getReg .x31 = init.getMem (BitVec.ofNat 64 (source count)) := by
    simp only [loaded, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp only [loadAddress, ite_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, named]
    exact inv.input _ low (by omega) aligned
  have memory : after.mem = (state.setMem (BitVec.ofNat 64 (proofBase+8*count))
      (init.getMem (BitVec.ofNat 64 (source count)))).mem := by
    show (execInstrBr loaded _).mem = _
    simp only [execInstrBr, storeAddress, value]
    rfl
  refine ⟨run₁.trans run₂, ?_, ?_, ?_⟩
  · exact (inv.store fits _ rfl).of_mem memory
  · show (execInstrBr loaded _).pc = _
    rw [straight_pc loaded _ rfl, loadPC, pc_next _ _ rfl]
  · intro r other
    show (execInstrBr loaded _).getReg r = _
    simp [loaded, execInstrBr, QOpening.getReg_setReg, QOpening.getReg_setMem, Ne.symm other]

theorem hyb_four_eq (x : Reg) (src off : Nat) : hybFour x src off =
    [.LD .x31 x (BitVec.ofNat 12 src), .SD .x21 .x31 (BitVec.ofNat 12 off),
     .LD .x31 x (BitVec.ofNat 12 (src+8)), .SD .x21 .x31 (BitVec.ofNat 12 (off+8)),
     .LD .x31 x (BitVec.ofNat 12 (src+16)), .SD .x21 .x31 (BitVec.ofNat 12 (off+16)),
     .LD .x31 x (BitVec.ofNat 12 (src+24)), .SD .x21 .x31 (BitVec.ofNat 12 (off+24))] := by
  simp [hybFour, List.range_succ]

/-- Four load/store pairs copy the doublewords `S + src + 8 w` to output words `count + w`. -/
theorem four_run (init : MachineState) (source : Nat → Nat) (start : Nat) (x : Reg) (hx : x ≠ .x31)
    (hx21 : x ≠ .x21) (src off S D count : Nat) (code : CodeAt start (hybFour x src off))
    (hs : src+24 < 2048) (ho : off+24 < 2048) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*start))
    (from_ : state.getReg x = BitVec.ofNat 64 S) (to_ : state.getReg .x21 = BitVec.ofNat 64 D)
    (target : D+off = proofBase+8*count) (aligned : (S+src) % 8 = 0) (low : trapdoorBase ≤ S+src)
    (high : S+src+32 ≤ proofBase) (fits : proofBase+8*count+32 ≤ MEMORY_BYTES)
    (named : ∀ w < 4, source (count+w) = S+src+8*w) (inv : Inv init state source count) :
    let after := (hybFour x src off).foldl execInstrBr state
    Runs state after 8 8 ∧ Inv init after source (count+4) ∧ after.pc = BitVec.ofNat 64 (4096+4*(start+8)) ∧
      ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  have c := code
  rw [hyb_four_eq] at c
  have cl (i : Nat) (h : i < 8) := code_one c i (by simpa using h)
  obtain ⟨r1, i1, p1, k1⟩ := copy_step init state source start x hx src off S D count (by omega) (by omega)
    (cl 0 (by decide)) (cl 1 (by decide)) pc from_ to_ target aligned low (by omega) (by omega)
    (by simpa using named 0 (by decide)) inv
  let s1 := execInstrBr (execInstrBr state (.LD .x31 x (BitVec.ofNat 12 src))) (.SD .x21 .x31 (BitVec.ofNat 12 off))
  obtain ⟨r2, i2, p2, k2⟩ := copy_step init s1 source (start+2) x hx (src+8) (off+8) S D (count+1) (by omega)
    (by omega) (cl 2 (by decide)) (cl 3 (by decide)) p1 ((k1 x hx).trans from_) ((k1 .x21 (by decide)).trans to_)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [named 1 (by decide)]; omega) i1
  let s2 := execInstrBr (execInstrBr s1 (.LD .x31 x (BitVec.ofNat 12 (src+8)))) (.SD .x21 .x31 (BitVec.ofNat 12 (off+8)))
  obtain ⟨r3, i3, p3, k3⟩ := copy_step init s2 source (start+2+2) x hx (src+16) (off+16) S D (count+1+1) (by omega)
    (by omega) (cl 4 (by decide)) (cl 5 (by decide)) p2 ((k2 x hx).trans ((k1 x hx).trans from_))
    ((k2 .x21 (by decide)).trans ((k1 .x21 (by decide)).trans to_))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [named 2 (by decide)]; omega) i2
  let s3 := execInstrBr (execInstrBr s2 (.LD .x31 x (BitVec.ofNat 12 (src+16)))) (.SD .x21 .x31 (BitVec.ofNat 12 (off+16)))
  obtain ⟨r4, i4, p4, k4⟩ := copy_step init s3 source (start+2+2+2) x hx (src+24) (off+24) S D (count+1+1+1) (by omega)
    (by omega) (cl 6 (by decide)) (cl 7 (by decide)) p3 ((k3 x hx).trans ((k2 x hx).trans ((k1 x hx).trans from_)))
    ((k3 .x21 (by decide)).trans ((k2 .x21 (by decide)).trans ((k1 .x21 (by decide)).trans to_)))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [named 3 (by decide)]; omega) i3
  have shape : after = execInstrBr (execInstrBr s3 (.LD .x31 x (BitVec.ofNat 12 (src+24))))
      (.SD .x21 .x31 (BitVec.ofNat 12 (off+24))) := by
    show List.foldl execInstrBr state (hybFour x src off) = _
    rw [hyb_four_eq]; rfl
  rw [shape]
  refine ⟨(((r1.trans r2).trans r3).trans r4).cast rfl rfl, by simpa using i4, by rw [p4], ?_⟩
  intro r h
  rw [k4 r h, k3 r h, k2 r h, k1 r h]

/-! ### Jumps -/

theorem CodeAt.left {start : Nat} {a b : List Instr} (h : CodeAt start (a ++ b)) : CodeAt start a :=
  fun i hi => by rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem CodeAt.right {start : Nat} {a b : List Instr} (h : CodeAt start (a ++ b)) :
    CodeAt (start+a.length) b := fun i hi => by
  have := h (a.length+i) (by simp; omega)
  rw [show start+a.length+i = start+(a.length+i) by omega, this,
    List.getElem?_append_right (by omega)]
  simp

theorem runs_jump (state : MachineState) (instruction : Instr) (index : Nat)
    (code : program[index]? = some instruction) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (step : ordinaryStep state (.base instruction) = some (execInstrBr state instruction))
    (one : instructionCycles (.base instruction) = 1) :
    Runs state (execInstrBr state instruction) 1 1 := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ index _ code pc) step, one]

theorem jalr_zero (s : MachineState) (rs : Reg) (imm : BitVec 12) :
    execInstrBr s (.JALR .x0 rs imm) = s.setPC ((s.getReg rs + signExtend12 imm) &&& ~~~1#64) := by
  simp only [execInstrBr]
  congr 1

theorem jal_zero (s : MachineState) (imm : BitVec 21) :
    execInstrBr s (.JAL .x0 imm) = s.setPC (s.pc + signExtend21 imm) := by
  simp only [execInstrBr]
  congr 1

/-- The dispatch of 5-ary level `k`: `x7 = 256 d + 4096 hi`, and the `jalr` target is variant `d`. -/
theorem penta_dispatch (k : Nat) (hk : k < 5) (t : MachineState) (d : Nat) (hd : d < 5)
    (x25 : t.getReg .x25 = BitVec.ofNat 64 d) :
    let u := ([.SLLI .x7 .x25 8, .LUI .x28 (dispHi k), .ADD .x7 .x7 .x28] : List Instr).foldl execInstrBr t
    (u.getReg .x7 + signExtend12 (dispLo k)) &&& ~~~1#64 = BitVec.ofNat 64 (4096+4*levelVariantStart k d) ∧
      (∀ r, r ≠ .x7 → r ≠ .x28 → u.getReg r = t.getReg r) := by
  intro u
  constructor
  · simp only [u, List.foldl_cons, List.foldl_nil, execInstrBr, QOpening.getReg_setReg,
      MachineState.getReg_setPC, x25, reduceCtorEq, ne_eq, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, and_self]
    interval_cases k <;> interval_cases d <;> decide
  · intro r h1 h2
    simp [u, execInstrBr, Ne.symm h1, Ne.symm h2]

theorem penta_back (k d : Nat) (hk : k < 5) (hd : d < 5) :
    BitVec.ofNat 64 (4096+4*(levelVariantStart k d+8*(3+1))) +
        signExtend21 (backJump (levelExitWord k d) (nextStart k)) =
      BitVec.ofNat 64 (4096+4*(536+10*(k+1))) := by
  interval_cases k <;> interval_cases d <;> decide

theorem quad_dispatch (t : MachineState) (d : Nat) (hd : d < 3)
    (x25 : t.getReg .x25 = BitVec.ofNat 64 d) :
    let u := ([.SLLI .x7 .x25 7, .LUI .x28 2, .ADD .x7 .x7 .x28] : List Instr).foldl execInstrBr t
    (u.getReg .x7 + signExtend12 (-1472)) &&& ~~~1#64 = BitVec.ofNat 64 (4096+4*(656+32*d)) ∧
      (∀ r, r ≠ .x7 → r ≠ .x28 → u.getReg r = t.getReg r) := by
  intro u
  constructor
  · simp only [u, List.foldl_cons, List.foldl_nil, execInstrBr, QOpening.getReg_setReg,
      MachineState.getReg_setPC, x25, reduceCtorEq, ne_eq, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, and_self]
    interval_cases d <;> decide
  · intro r h1 h2
    simp [u, execInstrBr, Ne.symm h1, Ne.symm h2]

theorem quad_back (d : Nat) (hd : d < 3) :
    BitVec.ofNat 64 (4096+4*(656+32*d+8*(1+1))) + signExtend21 (backJump (672+32*d) 597) =
      BitVec.ofNat 64 (4096+4*597) := by
  interval_cases d <;> decide

/-! ### Register arithmetic -/

theorem hyb_lui (k : Nat) (hk : k < 17) (T : Nat) :
    ((hybPage k).zeroExtend 32 <<< 12).signExtend 64 + BitVec.ofNat 64 T =
      BitVec.ofNat 64 (pentaGroupBase k+40+T) := by
  rw [hyb_page k hk, ← BitVec.ofNat_add]

theorem and_one (n : Nat) (small : n < 2^64) :
    BitVec.ofNat 64 n &&& signExtend12 1#12 = BitVec.ofNat 64 (n%2) := by
  rw [show signExtend12 1#12 = BitVec.ofNat 64 1 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, word_lt n small, word_lt 1 (by decide), word_lt _ (by omega), Nat.and_one_is_mod]

theorem shr_one (n : Nat) (small : n < 2^64) :
    BitVec.ofNat 64 n >>> (1#6).toNat = BitVec.ofNat 64 (n/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, word_lt n small, word_lt _ (by omega), Nat.shiftRight_eq_div_pow]
  rfl

theorem shl_five (m : Nat) (small : m < 2^40) : BitVec.ofNat 64 m <<< (5#6).toNat = BitVec.ofNat 64 (32*m) :=
  shift_slot m small

theorem mul368 (q : Nat) (small : q < 2^40) : BitVec.ofNat 64 q * 368#64 = BitVec.ofNat 64 (368*q) :=
  mul_width q small

theorem shr1 (n : Nat) (small : n < 2^64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n/2) := shr_one n small

theorem shr2 (n : Nat) (small : n < 2^64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n/4) := shr_two n small

theorem and1 (n : Nat) (small : n < 2^64) : BitVec.ofNat 64 n &&& 1#64 = BitVec.ofNat 64 (n%2) := by
  have := and_one n small
  rwa [show signExtend12 1#12 = 1#64 by decide] at this

theorem sub_nat (a b : Nat) (h : b ≤ a) (ha : a < 2^64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a-b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, word_lt a ha, word_lt b (by omega), word_lt _ (by omega)]
  omega

theorem add_nat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a+b) :=
  (BitVec.ofNat_add a b).symm

/-- Registers preserved through a record, apart from the scratch registers. -/
def Scratch (r : Reg) : Prop := r = .x6 ∨ r = .x7 ∨ r = .x25 ∨ r = .x28 ∨ r = .x30 ∨ r = .x31 ∨ r = .x29

/-! ### A 5-ary level -/

def pentaHead (k : Nat) : List Instr := (hybPenta k).take 6

theorem penta_head_eq (k : Nat) : pentaHead k =
    [.LUI .x28 (hybPage k), .ADD .x28 .x28 .x9, .REMU .x25 .x6 .x19, .DIVU .x6 .x6 .x19,
     .MUL .x30 .x6 .x23, .ADD .x30 .x30 .x28] := rfl

theorem penta_head_regs (k : Nat) (hk : k < 5) (t : MachineState) (n : Nat) (hn : n < 2^40)
    (x6 : t.getReg .x6 = BitVec.ofNat 64 n) (x9 : t.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (x19 : t.getReg .x19 = BitVec.ofNat 64 5) (x23 : t.getReg .x23 = BitVec.ofNat 64 368) :
    let u := (pentaHead k).foldl execInstrBr t
    u.getReg .x25 = BitVec.ofNat 64 (n%5) ∧ u.getReg .x6 = BitVec.ofNat 64 (n/5) ∧
      u.getReg .x30 = BitVec.ofNat 64 (368*(n/5)+(pentaGroupBase k+40+trapdoorBase)) ∧
      (∀ r, ¬ Scratch r → u.getReg r = t.getReg r) := by
  intro u
  have e : u = (pentaHead k).foldl execInstrBr t := rfl
  rw [penta_head_eq] at e
  simp only [List.foldl_cons, List.foldl_nil] at e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e]; simp [execInstrBr, x6, x19, remu_five n hn]
  · rw [e]; simp [execInstrBr, x6, x19, divu_five n hn]
  · rw [e]; simp [execInstrBr, x6, x9, x19, x23, divu_five n hn, mul368 (n/5) (by omega), hyb_lui k (by omega)]
    rw [add_nat]
  · intro r hr
    unfold Scratch at hr
    rw [e]
    simp only [execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    have a : r ≠ .x6 := fun h => hr (Or.inl h)
    have b : r ≠ .x25 := fun h => hr (Or.inr (Or.inr (Or.inl h)))
    have c : r ≠ .x28 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have d : r ≠ .x30 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    simp [Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

def siblingHead (j : Nat) : List Instr :=
  [.ADDI .x7 .x25 (BitVec.ofNat 12 (j+1)), .REMU .x7 .x7 .x19, .SLLI .x7 .x7 5, .ADD .x7 .x7 .x30]

theorem sibling_head_regs (j : Nat) (hj : j < 4) (t : MachineState) (d X : Nat) (hd : d < 5)
    (x25 : t.getReg .x25 = BitVec.ofNat 64 d) (x19 : t.getReg .x19 = BitVec.ofNat 64 5)
    (x30 : t.getReg .x30 = BitVec.ofNat 64 X) :
    let u := (siblingHead j).foldl execInstrBr t
    u.getReg .x7 = BitVec.ofNat 64 (32*((d+(j+1))%5)+X) ∧ (∀ r, r ≠ .x7 → u.getReg r = t.getReg r) := by
  intro u
  have e : u = (siblingHead j).foldl execInstrBr t := rfl
  simp only [siblingHead, List.foldl_cons, List.foldl_nil] at e
  refine ⟨?_, ?_⟩
  · rw [e]
    simp [execInstrBr, x25, x19, x30, sext_small (j+1) (by omega), add_nat, remu_five _ (by omega : d+(j+1) < 2^40),
      shift_slot _ (by omega : (d+(j+1))%5 < 2^40)]
  · intro r hr
    rw [e]
    simp [execInstrBr, Ne.symm hr]

/-! ### A binary level -/

def binHead (k : Nat) : List Instr := (hybBin k).take 8

theorem bin_head_eq (k : Nat) : binHead k =
    [.LUI .x28 (hybPage k), .ADD .x28 .x28 .x9, .ANDI .x7 .x6 1, .SRLI .x6 .x6 1,
     .MUL .x30 .x6 .x23, .ADD .x30 .x30 .x28, .SLLI .x7 .x7 5, .SUB .x30 .x30 .x7] := rfl

theorem bin_head_regs (k : Nat) (hk : k < 13) (t : MachineState) (n : Nat) (hn : n < 2^40)
    (x6 : t.getReg .x6 = BitVec.ofNat 64 n) (x9 : t.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (x23 : t.getReg .x23 = BitVec.ofNat 64 368) :
    let u := (binHead k).foldl execInstrBr t
    u.getReg .x6 = BitVec.ofNat 64 (n/2) ∧
      u.getReg .x30 = BitVec.ofNat 64 (368*(n/2)+(pentaGroupBase k+40+trapdoorBase)-32*(n%2)) ∧
      (∀ r, ¬ Scratch r → u.getReg r = t.getReg r) := by
  intro u
  have e : u = (binHead k).foldl execInstrBr t := rfl
  rw [bin_head_eq] at e
  simp only [List.foldl_cons, List.foldl_nil] at e
  have base : pentaGroupBase k+40+trapdoorBase < 2^40 := by
    have : pentaGroupBase k ≤ 1550966744 := by interval_cases k <;> decide
    rw [tb_val]; omega
  have mod2 : n%2 < 2 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; simp [execInstrBr, x6, shr1 n (by omega)]
  · rw [e]
    simp [execInstrBr, x6, x9, x23, shr1 n (by omega), mul368 (n/2) (by omega), hyb_lui k (by omega)]
    rw [and_one n (by omega), shift_slot (n%2) (by omega), add_nat,
      sub_nat _ _ (by rw [tb_val] at base ⊢; omega) (by omega)]
  · intro r hr
    unfold Scratch at hr
    rw [e]
    simp only [execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    have a : r ≠ .x6 := fun h => hr (Or.inl h)
    have a7 : r ≠ .x7 := fun h => hr (Or.inr (Or.inl h))
    have c : r ≠ .x28 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have d : r ≠ .x30 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    simp [Ne.symm a, Ne.symm a7, Ne.symm c, Ne.symm d]

/-! ### Level blocks -/

theorem base_bound (k : Nat) (hk : k < 22) : pentaGroupBase k+368*pentaCount (k+1) ≤ 1728786760 :=
  group_room k hk


theorem not_scratch_regs : ¬ Scratch .x8 ∧ ¬ Scratch .x9 ∧ ¬ Scratch .x15 ∧ ¬ Scratch .x18 ∧ ¬ Scratch .x19 ∧
    ¬ Scratch .x21 ∧ ¬ Scratch .x22 ∧ ¬ Scratch .x23 := by
  unfold Scratch; decide

theorem hyb_penta_split (k : Nat) : hybPenta k = pentaHead k ++
    ((siblingHead 0 ++ hybFour .x7 0 (16+128*k+32*0)) ++ ((siblingHead 1 ++ hybFour .x7 0 (16+128*k+32*1)) ++
    ((siblingHead 2 ++ hybFour .x7 0 (16+128*k+32*2)) ++ (siblingHead 3 ++ hybFour .x7 0 (16+128*k+32*3))))) := by
  simp [hybPenta, pentaHead, hybSibling, siblingHead, List.range_succ]

/-- Registers fixed during a record. -/
structure Fixed (positions : Positions) (o : Nat) (t : MachineState) : Prop where
  x8 : t.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*o)
  x9 : t.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  x15 : t.getReg .x15 = BitVec.ofNat 64 proofBase
  x18 : t.getReg .x18 = BitVec.ofNat 64 (indicesBase+8*positions.card)
  x19 : t.getReg .x19 = BitVec.ofNat 64 5
  x21 : t.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*o))
  x22 : t.getReg .x22 = BitVec.ofNat 64 nonceBase
  x23 : t.getReg .x23 = BitVec.ofNat 64 368

theorem Fixed.keep {positions : Positions} {o : Nat} {t u : MachineState} (f : Fixed positions o t)
    (same : ∀ r, ¬ Scratch r → u.getReg r = t.getReg r) : Fixed positions o u := by
  obtain ⟨a, b, c, d, e, g, h, i⟩ := not_scratch_regs
  exact ⟨(same _ a).trans f.x8, (same _ b).trans f.x9, (same _ c).trans f.x15, (same _ d).trans f.x18,
    (same _ e).trans f.x19, (same _ g).trans f.x21, (same _ h).trans f.x22, (same _ i).trans f.x23⟩

theorem scratch_of_ne {r : Reg} (h : ¬ Scratch r) : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x25 ∧ r ≠ .x28 ∧ r ≠ .x30 ∧ r ≠ .x31 ∧ r ≠ .x29 := by
  unfold Scratch at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> exact h (by simp [e])

theorem penta_d_split (k : Nat) : hybPentaD k = pentaHead k ++
    ([.SLLI .x7 .x25 8, .LUI .x28 (dispHi k), .ADD .x7 .x7 .x28] ++ [.JALR .x0 .x7 (dispLo k)]) := rfl

theorem penta_head_length (k : Nat) : (pentaHead k).length = 6 := by
  simp [pentaHead, hybPenta]

set_option maxHeartbeats 4000000 in
/-- A dispatching 5-ary level: head, dispatch, the variant's four copies and its return jump. -/
theorem penta_level (init : MachineState) (positions : Positions) (o k : Nat) (hk : k < 5)
    (present : o < positions.card) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(536+10*k)))
    (x6 : t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/5^k)) (fixed : Fixed positions o t)
    (inv : Inv init t (wordSource positions) (102*o+2+16*k)) :
    ∃ u, Runs t u 43 52 ∧ Inv init u (wordSource positions) (102*o+2+16*(k+1)) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(536+10*(k+1))) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/5^(k+1)) ∧ Fixed positions o u := by
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have codes := (hyb_codes.2.2.2.1) k hk
  rw [penta_d_split] at codes
  have headCode : CodeAt (536+10*k) (pentaHead k) := codes.left
  have restCode := codes.right
  rw [penta_head_length] at restCode
  have dispCode := restCode.left
  have jalrCode := (restCode.right) 0 (by simp)
  simp only [List.length_cons, List.length_nil] at jalrCode
  have n_small : i/5^k < 2^40 := by
    have := Nat.div_le_self i (5^k); omega
  -- the head
  let h0 := (pentaHead k).foldl execInstrBr t
  have run0 : Runs t h0 6 15 := (runs_pure _ _ t headCode pc rfl).cast rfl (by
    simp [pentaHead, hybPenta, cost, instructionCycles])
  obtain ⟨r25, r6, r30, keep0⟩ := penta_head_regs k hk t (i/5^k) n_small x6 fixed.x9 fixed.x19 fixed.x23
  have pc0 : h0.pc = BitVec.ofNat 64 (4096+4*(536+10*k+6)) := by
    rw [pure_pc _ _ rfl, pc, pc_offset, penta_head_length]
  have f0 : Fixed positions o h0 := fixed.keep keep0
  -- the dispatch
  let h1 := ([.SLLI .x7 .x25 8, .LUI .x28 (dispHi k), .ADD .x7 .x7 .x28] : List Instr).foldl execInstrBr h0
  have run1 : Runs h0 h1 3 3 := (runs_pure _ _ h0 dispCode pc0 rfl).cast rfl (by
    simp [cost, instructionCycles])
  have pc1 : h1.pc = BitVec.ofNat 64 (4096+4*(536+10*k+6+3)) := by
    rw [pure_pc _ _ rfl, pc0, pc_offset]; rfl
  obtain ⟨target, keep1⟩ := penta_dispatch k hk h0 (i/5^k%5) (Nat.mod_lt _ (by decide)) r25
  have f1 : Fixed positions o h1 := f0.keep (fun r hr => keep1 r (scratch_of_ne hr).2.1 (scratch_of_ne hr).2.2.2.1)
  let h2 := execInstrBr h1 (.JALR .x0 .x7 (dispLo k))
  have run2 : Runs h1 h2 1 1 :=
    runs_jump h1 _ (536+10*k+6+3) (by simpa using jalrCode) pc1 rfl rfl
  have pc2 : h2.pc = BitVec.ofNat 64 (4096+4*(levelVariantStart k (i/5^k%5)+8*0)) := by
    show (execInstrBr h1 (.JALR .x0 .x7 (dispLo k))).pc = _
    rw [jalr_zero, set_pc_pc, show levelVariantStart k (i/5^k%5)+8*0 = levelVariantStart k (i/5^k%5) by omega]
    exact target
  have k2 : ∀ r, h2.getReg r = h1.getReg r := by
    intro r; show (execInstrBr h1 (.JALR .x0 .x7 (dispLo k))).getReg r = _
    rw [jalr_zero]; simp
  have m2 : h2.mem = h1.mem := by
    show (execInstrBr h1 (.JALR .x0 .x7 (dispLo k))).mem = _
    rw [jalr_zero, set_pc_mem]
  have f2 : Fixed positions o h2 := f1.keep (fun r _ => k2 r)
  have x30₂ : h2.getReg .x30 = BitVec.ofNat 64 (368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase)) := by
    rw [k2, keep1 _ (by decide) (by decide), r30]
  have inv2 : Inv init h2 (wordSource positions) (102*o+2+16*k) :=
    (inv.of_mem (by rw [m2, pure_mem _ _ rfl, pure_mem _ _ rfl]))
  -- facts on the group
  have g_eq : i/5^k/5 = i/5^(k+1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  have count := div_lt_count i hi (k+1)
  rw [place_value_low (k+1) (by omega)] at count
  have room := base_bound k (by omega)
  have bk : pentaGroupBase k ≤ 1550966744 := by interval_cases k <;> decide
  obtain ⟨vc, vj⟩ := variant_codes k hk (i/5^k%5) (Nat.mod_lt _ (by decide))
  -- one copy block of the variant
  have sib (j : Nat) (hj : j < 4) (v : MachineState)
      (pcv : v.pc = BitVec.ofNat 64 (4096+4*(levelVariantStart k (i/5^k%5)+8*j)))
      (v30 : v.getReg .x30 = BitVec.ofNat 64 (368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase)))
      (v21 : v.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*o)))
      (invv : Inv init v (wordSource positions) (102*o+2+16*k+4*j)) :
      let w := (hybFour .x30 (32*((i/5^k%5+j+1)%5)) (16+128*k+32*j)).foldl execInstrBr v
      Runs v w 8 8 ∧ Inv init w (wordSource positions) (102*o+2+16*k+4*(j+1)) ∧
        w.pc = BitVec.ofNat 64 (4096+4*(levelVariantStart k (i/5^k%5)+8*(j+1))) ∧
        (∀ r, r ≠ .x31 → w.getReg r = v.getReg r) := by
    intro w
    let slot := (i/5^k%5+j+1)%5
    have slotLt : slot < 5 := Nat.mod_lt _ (by decide)
    have gLt : i/5^k/5+1 ≤ pentaCount (k+1) := by rw [g_eq]; exact count
    have gb : 368*(i/5^k/5)+368 ≤ 368*pentaCount (k+1) := by
      have := Nat.mul_le_mul_left 368 gLt; omega
    have al := group_aligned k (by omega)
    have tb := tb_val
    have pb := pb_val
    have src : 368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase)+32*slot =
        trapdoorBase+pentaGroupSlotOffset k (i/5^(k+1)) ((i/5^k%5+j+1)%5) := by
      unfold pentaGroupSlotOffset; rw [← g_eq]; omega
    obtain ⟨run, inv', pc', keep⟩ := four_run init (wordSource positions) _ .x30 (by decide) (by decide)
      (32*slot) (16+128*k+32*j) (368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase)) (proofBase+8*(102*o))
      (102*o+2+16*k+4*j) (vc j hj) (by omega) (by omega) v pcv
      v30 v21 (by omega)
      (by omega) (by omega) (by omega) (by rw [pb]; unfold MEMORY_BYTES; omega)
      (fun w hw => by rw [word_source_penta positions o k j w hk hj hw, ← src]; try omega)
      invv
    refine ⟨run, inv'.cast_count (by ring), pc'.trans (congrArg (BitVec.ofNat 64) (by omega)), keep⟩
  -- chain the four copies
  have x21₂ : h2.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*o)) := f2.x21
  obtain ⟨ra, ia, pa, ka⟩ := sib 0 (by decide) h2 pc2 x30₂ x21₂ (by simpa using inv2)
  let ha := (hybFour .x30 (32*((i/5^k%5+0+1)%5)) (16+128*k+32*0)).foldl execInstrBr h2
  obtain ⟨rb, ib, pb, kb⟩ := sib 1 (by decide) ha pa ((ka _ (by decide)).trans x30₂)
    ((ka _ (by decide)).trans x21₂) ia
  let hb := (hybFour .x30 (32*((i/5^k%5+1+1)%5)) (16+128*k+32*1)).foldl execInstrBr ha
  obtain ⟨rc, ic, pc', kc⟩ := sib 2 (by decide) hb pb ((kb _ (by decide)).trans ((ka _ (by decide)).trans x30₂))
    ((kb _ (by decide)).trans ((ka _ (by decide)).trans x21₂)) ib
  let hc := (hybFour .x30 (32*((i/5^k%5+2+1)%5)) (16+128*k+32*2)).foldl execInstrBr hb
  obtain ⟨rd, id, pd, kd⟩ := sib 3 (by decide) hc pc'
    ((kc _ (by decide)).trans ((kb _ (by decide)).trans ((ka _ (by decide)).trans x30₂)))
    ((kc _ (by decide)).trans ((kb _ (by decide)).trans ((ka _ (by decide)).trans x21₂))) ic
  let hd := (hybFour .x30 (32*((i/5^k%5+3+1)%5)) (16+128*k+32*3)).foldl execInstrBr hc
  have kall : ∀ r, r ≠ .x31 → hd.getReg r = h2.getReg r := fun r h => by
    rw [kd r h, kc r h, kb r h, ka r h]
  -- the return jump
  have jcode : program[levelVariantStart k (i/5^k%5)+8*(3+1)]? =
      some (.JAL .x0 (backJump (levelExitWord k (i/5^k%5)) (nextStart k))) := by simpa using vj
  let u := execInstrBr hd (.JAL .x0 (backJump (levelExitWord k (i/5^k%5)) (nextStart k)))
  have run5 : Runs hd u 1 1 := runs_jump hd _ _ jcode pd rfl rfl
  have ku : ∀ r, u.getReg r = hd.getReg r := by
    intro r; show (execInstrBr hd _).getReg r = _; rw [jal_zero]; simp
  have mu : u.mem = hd.mem := by show (execInstrBr hd _).mem = _; rw [jal_zero, set_pc_mem]
  refine ⟨u, (run0.trans (run1.trans (run2.trans (ra.trans (rb.trans (rc.trans (rd.trans run5))))))).cast rfl rfl,
    (id.of_mem mu).cast_count (by ring), ?_, ?_, ?_⟩
  · show (execInstrBr hd _).pc = _
    rw [jal_zero, set_pc_pc, pd]
    exact penta_back k (i/5^k%5) hk (Nat.mod_lt _ (by decide))
  · rw [ku, kall _ (by decide), k2, keep1 _ (by decide) (by decide), r6, g_eq]
  · exact f2.keep (fun r hr => by rw [ku, kall _ (scratch_of_ne hr).2.2.2.2.2.1])

/-! ### The 3-ary level 5 -/

def quadHead : List Instr := hybQuad.take 7

theorem quad_head_eq : quadHead =
    [.LUI .x28 (hybPage 5), .ADD .x28 .x28 .x9, .ADDI .x29 .x0 3, .REMU .x25 .x6 .x29, .DIVU .x6 .x6 .x29,
     .MUL .x30 .x6 .x23, .ADD .x30 .x30 .x28] := rfl

theorem divu_three (n : Nat) (small : n < 2^40) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 3) = BitVec.ofNat 64 (n/3) := by
  unfold rv64_divu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, word_lt n (by omega), word_lt 3 (by decide), word_lt _ (by omega)]

theorem remu_three (n : Nat) (small : n < 2^40) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 3) = BitVec.ofNat 64 (n%3) := by
  unfold rv64_remu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, word_lt n (by omega), word_lt 3 (by decide), word_lt _ (by omega)]

theorem three_imm : signExtend12 (3#12) = BitVec.ofNat 64 3 := by decide

theorem quad_head_regs (t : MachineState) (n : Nat) (hn : n < 2^40)
    (x6 : t.getReg .x6 = BitVec.ofNat 64 n) (x9 : t.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (x23 : t.getReg .x23 = BitVec.ofNat 64 368) :
    let u := quadHead.foldl execInstrBr t
    u.getReg .x25 = BitVec.ofNat 64 (n%3) ∧ u.getReg .x6 = BitVec.ofNat 64 (n/3) ∧
      u.getReg .x30 = BitVec.ofNat 64 (368*(n/3)+(pentaGroupBase 5+40+trapdoorBase)) ∧
      u.getReg .x29 = BitVec.ofNat 64 3 ∧
      (∀ r, ¬ Scratch r → u.getReg r = t.getReg r) := by
  intro u
  have e : u = quadHead.foldl execInstrBr t := rfl
  rw [quad_head_eq] at e
  simp only [List.foldl_cons, List.foldl_nil] at e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; simp [execInstrBr, x6, three_imm, remu_three n hn]
  · rw [e]; simp [execInstrBr, x6, three_imm, divu_three n hn]
  · rw [e]; simp [execInstrBr, x6, x9, x23, three_imm, divu_three n hn, mul368 (n/3) (by omega), hyb_lui 5 (by omega)]
    rw [add_nat]
  · rw [e]; simp [execInstrBr, three_imm]
  · intro r hr
    unfold Scratch at hr
    rw [e]
    simp only [execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    have a : r ≠ .x6 := fun h => hr (Or.inl h)
    have b : r ≠ .x25 := fun h => hr (Or.inr (Or.inr (Or.inl h)))
    have c : r ≠ .x28 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have d : r ≠ .x30 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have f : r ≠ .x29 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    simp [Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm f]

theorem quad_d_split : hybQuadD = quadHead ++
    ([.SLLI .x7 .x25 7, .LUI .x28 2, .ADD .x7 .x7 .x28] ++ [.JALR .x0 .x7 (-1472)]) := rfl

theorem quad_head_length : quadHead.length = 7 := by
  simp [quadHead, hybQuad]

set_option maxHeartbeats 4000000 in
/-- The dispatching 3-ary level 5: head, dispatch, the variant's two copies and its return jump. -/
theorem quad_level (init : MachineState) (positions : Positions) (o : Nat)
    (present : o < positions.card) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*586))
    (x6 : t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/3125)) (fixed : Fixed positions o t)
    (inv : Inv init t (wordSource positions) (102*o+82)) :
    ∃ u, Runs t u 28 37 ∧ Inv init u (wordSource positions) (102*o+90) ∧
      u.pc = BitVec.ofNat 64 (4096+4*597) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/9375) ∧ Fixed positions o u := by
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have codes := hyb_done_code.2
  rw [quad_d_split] at codes
  have headCode : CodeAt 586 quadHead := codes.left
  have restCode := codes.right
  rw [quad_head_length] at restCode
  have dispCode := restCode.left
  have jalrCode := (restCode.right) 0 (by simp)
  simp only [List.length_cons, List.length_nil] at jalrCode
  have n_small : i/3125 < 2^40 := by
    have := Nat.div_le_self i 3125; omega
  let h0 := quadHead.foldl execInstrBr t
  have run0 : Runs t h0 7 16 := (runs_pure _ _ t headCode pc rfl).cast rfl (by
    simp [quadHead, hybQuad, cost, instructionCycles])
  obtain ⟨r25, r6, r30, r29, keep0⟩ := quad_head_regs t (i/3125) n_small x6 fixed.x9 fixed.x23
  have pc0 : h0.pc = BitVec.ofNat 64 (4096+4*(586+7)) := by
    rw [pure_pc _ _ rfl, pc, pc_offset, quad_head_length]
  have f0 : Fixed positions o h0 := fixed.keep keep0
  let h1 := ([.SLLI .x7 .x25 7, .LUI .x28 2, .ADD .x7 .x7 .x28] : List Instr).foldl execInstrBr h0
  have run1 : Runs h0 h1 3 3 := (runs_pure _ _ h0 dispCode pc0 rfl).cast rfl (by
    simp [cost, instructionCycles])
  have pc1 : h1.pc = BitVec.ofNat 64 (4096+4*(586+7+3)) := by
    rw [pure_pc _ _ rfl, pc0, pc_offset]; rfl
  obtain ⟨target, keep1⟩ := quad_dispatch h0 (i/3125%3) (Nat.mod_lt _ (by decide)) r25
  have f1 : Fixed positions o h1 := f0.keep (fun r hr => keep1 r (scratch_of_ne hr).2.1 (scratch_of_ne hr).2.2.2.1)
  let h2 := execInstrBr h1 (.JALR .x0 .x7 (-1472))
  have run2 : Runs h1 h2 1 1 :=
    runs_jump h1 _ (586+7+3) (by simpa using jalrCode) pc1 rfl rfl
  have pc2 : h2.pc = BitVec.ofNat 64 (4096+4*(656+32*(i/3125%3)+8*0)) := by
    show (execInstrBr h1 (.JALR .x0 .x7 (-1472))).pc = _
    rw [jalr_zero, set_pc_pc, show 656+32*(i/3125%3)+8*0 = 656+32*(i/3125%3) by omega]
    exact target
  have k2 : ∀ r, h2.getReg r = h1.getReg r := by
    intro r; show (execInstrBr h1 (.JALR .x0 .x7 (-1472))).getReg r = _
    rw [jalr_zero]; simp
  have m2 : h2.mem = h1.mem := by
    show (execInstrBr h1 (.JALR .x0 .x7 (-1472))).mem = _
    rw [jalr_zero, set_pc_mem]
  have f2 : Fixed positions o h2 := f1.keep (fun r _ => k2 r)
  have x30₂ : h2.getReg .x30 = BitVec.ofNat 64 (368*(i/3125/3)+(pentaGroupBase 5+40+trapdoorBase)) := by
    rw [k2, keep1 _ (by decide) (by decide), r30]
  have inv2 : Inv init h2 (wordSource positions) (102*o+82) :=
    (inv.of_mem (by rw [m2, pure_mem _ _ rfl, pure_mem _ _ rfl]))
  have g_eq : i/3125/3 = i/9375 := by rw [Nat.div_div_eq_div_mul]
  have count := div_lt_count i hi 6
  rw [show placeValue 6 = 9375 from rfl] at count
  have room := base_bound 5 (by omega)
  have bk : pentaGroupBase 5 ≤ 1728786392 := by decide
  obtain ⟨vc, vj⟩ := quad_variant_codes (i/3125%3) (Nat.mod_lt _ (by decide))
  have sib (j : Nat) (hj : j < 2) (v : MachineState)
      (pcv : v.pc = BitVec.ofNat 64 (4096+4*(656+32*(i/3125%3)+8*j)))
      (v30 : v.getReg .x30 = BitVec.ofNat 64 (368*(i/3125/3)+(pentaGroupBase 5+40+trapdoorBase)))
      (v21 : v.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*o)))
      (invv : Inv init v (wordSource positions) (102*o+82+4*j)) :
      let w := (hybFour .x30 (64+32*((i/3125%3+j+1)%3)) (656+32*j)).foldl execInstrBr v
      Runs v w 8 8 ∧ Inv init w (wordSource positions) (102*o+82+4*(j+1)) ∧
        w.pc = BitVec.ofNat 64 (4096+4*(656+32*(i/3125%3)+8*(j+1))) ∧
        (∀ r, r ≠ .x31 → w.getReg r = v.getReg r) := by
    intro w
    let slot := (i/3125%3+j+1)%3
    have slotLt : slot < 3 := Nat.mod_lt _ (by decide)
    have gLt : i/3125/3+1 ≤ pentaCount 6 := by rw [g_eq]; exact count
    have gb : 368*(i/3125/3)+368 ≤ 368*pentaCount 6 := by
      have := Nat.mul_le_mul_left 368 gLt; omega
    have al := group_aligned 5 (by omega)
    have tb := tb_val
    have pb := pb_val
    have src : 368*(i/3125/3)+(pentaGroupBase 5+40+trapdoorBase)+(64+32*slot) =
        trapdoorBase+pentaGroupSlotOffset 5 (i/3125/3) (2+(i/3125%3+j+1)%3) := by
      unfold pentaGroupSlotOffset; omega
    obtain ⟨run, inv', pc', keep⟩ := four_run init (wordSource positions) _ .x30 (by decide) (by decide)
      (64+32*slot) (656+32*j) (368*(i/3125/3)+(pentaGroupBase 5+40+trapdoorBase)) (proofBase+8*(102*o))
      (102*o+82+4*j) (vc j hj) (by omega) (by omega) v pcv
      v30 v21 (by omega)
      (by omega) (by omega) (by omega) (by rw [pb]; unfold MEMORY_BYTES; omega)
      (fun w hw => by rw [word_source_quad positions o j w hj hw, ← src]; try omega)
      invv
    refine ⟨run, inv'.cast_count (by ring), pc'.trans (congrArg (BitVec.ofNat 64) (by omega)), keep⟩
  have x21₂ : h2.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*o)) := f2.x21
  obtain ⟨ra, ia, pa, ka⟩ := sib 0 (by decide) h2 pc2 x30₂ x21₂ (by simpa using inv2)
  let ha := (hybFour .x30 (64+32*((i/3125%3+0+1)%3)) (656+32*0)).foldl execInstrBr h2
  obtain ⟨rb, ib, pb, kb⟩ := sib 1 (by decide) ha pa ((ka _ (by decide)).trans x30₂)
    ((ka _ (by decide)).trans x21₂) ia
  let hb := (hybFour .x30 (64+32*((i/3125%3+1+1)%3)) (656+32*1)).foldl execInstrBr ha
  have kall : ∀ r, r ≠ .x31 → hb.getReg r = h2.getReg r := fun r h => by rw [kb r h, ka r h]
  have jcode : program[656+32*(i/3125%3)+8*(1+1)]? = some (.JAL .x0 (backJump (672+32*(i/3125%3)) 597)) := by
    rw [show 656+32*(i/3125%3)+8*(1+1) = 672+32*(i/3125%3) by omega]; exact vj
  let u := execInstrBr hb (.JAL .x0 (backJump (672+32*(i/3125%3)) 597))
  have run5 : Runs hb u 1 1 := runs_jump hb _ _ jcode pb rfl rfl
  have ku : ∀ r, u.getReg r = hb.getReg r := by
    intro r; show (execInstrBr hb _).getReg r = _; rw [jal_zero]; simp
  have mu : u.mem = hb.mem := by show (execInstrBr hb _).mem = _; rw [jal_zero, set_pc_mem]
  refine ⟨u, (run0.trans (run1.trans (run2.trans (ra.trans (rb.trans run5))))).cast rfl rfl,
    (ib.of_mem mu).cast_count (by ring), ?_, ?_, ?_⟩
  · show (execInstrBr hb _).pc = _
    rw [jal_zero, set_pc_pc, pb]
    exact quad_back (i/3125%3) (Nat.mod_lt _ (by decide))
  · rw [ku, kall _ (by decide), k2, keep1 _ (by decide) (by decide), r6, g_eq]
  · exact f2.keep (fun r hr => by rw [ku, kall _ (scratch_of_ne hr).2.2.2.2.2.1])

theorem hyb_bin_split (m : Nat) : hybBin (m+6) = binHead (m+6) ++ hybFour .x30 128 (720+32*m) := by
  simp [hybBin, binHead]

set_option maxHeartbeats 4000000 in
theorem bin_level (init : MachineState) (positions : Positions) (o m : Nat) (hm : m < 3)
    (present : o < positions.card) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(597+16*m)))
    (x6 : t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/(9375*2^m))) (fixed : Fixed positions o t)
    (inv : Inv init t (wordSource positions) (102*o+90+4*m)) :
    let u := (hybBin (m+6)).foldl execInstrBr t
    Runs t u 16 19 ∧ Inv init u (wordSource positions) (102*o+90+4*(m+1)) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(597+16*(m+1))) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/(9375*2^(m+1))) ∧ Fixed positions o u := by
  intro u
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have codes := (hyb_codes.2.2.2.2.1) m hm
  rw [hyb_bin_split] at codes
  have headCode : CodeAt (597+16*m) (binHead (m+6)) := fun j h => by
    have := codes j (by simp [binHead, hybBin, hybFour] at h ⊢; omega)
    rw [this, List.getElem?_append_left h]
  have fc : CodeAt (597+16*m+8) (hybFour .x30 128 (720+32*m)) := fun q h => by
    have := codes (8+q) (by simp [binHead, hybBin, hybFour] at h ⊢; omega)
    rw [show 597+16*m+(8+q) = 597+16*m+8+q by omega] at this
    rw [this, List.getElem?_append_right (by simp [binHead, hybBin])]
    simp [binHead, hybBin]
  let n := i/(9375*2^m)
  have n_small : n < 2^40 := by
    have := Nat.div_le_self i (9375*2^m); omega
  let h0 := (binHead (m+6)).foldl execInstrBr t
  have run0 : Runs t h0 8 11 := (runs_pure _ _ t headCode pc rfl).cast rfl (by
    simp [binHead, hybBin, cost, instructionCycles])
  obtain ⟨r6, r30, keep0⟩ := bin_head_regs (m+6) (by omega) t n n_small x6 fixed.x9 fixed.x23
  have pc0 : h0.pc = BitVec.ofNat 64 (4096+4*(597+16*m+8)) := by
    rw [pure_pc _ _ rfl, pc, pc_offset]; rfl
  have f0 : Fixed positions o h0 := fixed.keep keep0
  have g_eq : n/2 = i/(9375*2^(m+1)) := by
    show i/(9375*2^m)/2 = _
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]
  have room := base_bound (m+6) (by omega)
  have bk : pentaGroupBase (m+6) ≤ 1728786392 := by interval_cases m <;> decide
  have bit : n%2 < 2 := Nat.mod_lt _ (by decide)
  have al := group_aligned (m+6) (by omega)
  have tb := tb_val
  have pb := pb_val
  have src : 368*(n/2)+(pentaGroupBase (m+6)+40+trapdoorBase)-32*(n%2)+128 =
      trapdoorBase+pentaGroupSlotOffset (6+m) (n/2) (4-n%2) := by
    unfold pentaGroupSlotOffset; rw [show 6+m = m+6 by omega]; omega
  have gb : 368*(n/2)+368 ≤ 368*pentaCount (m+6+1) := by
    have h : n/2+1 ≤ pentaCount (m+6+1) := by
      rw [g_eq]
      have := div_lt_count i hi (6+(m+1))
      rw [place_value_bin (m+1) (by omega), show 6+(m+1) = m+6+1 by omega] at this
      omega
    have := Nat.mul_le_mul_left 368 h; omega
  obtain ⟨run2, inv2, pc2, keep2⟩ := four_run init (wordSource positions) _ .x30 (by decide) (by decide) 128
    (720+32*m) _ (proofBase+8*(102*o)) (102*o+90+4*m) fc (by omega) (by omega) h0 pc0
    r30 f0.x21 (by omega) (by omega) (by omega) (by omega) (by rw [pb]; unfold MEMORY_BYTES; omega)
    (fun w hw => by rw [word_source_bin positions o m w hm hw, src])
    (inv.of_mem (pure_mem _ _ rfl))
  have shape : u = (hybFour .x30 128 (720+32*m)).foldl execInstrBr h0 := by
    simp only [u, hyb_bin_split, List.foldl_append, h0]
  rw [shape]
  refine ⟨(run0.trans run2).cast rfl rfl, inv2.cast_count (by ring), ?_, ?_, f0.keep (fun r hr => ?_)⟩
  · exact pc2.trans (congrArg (BitVec.ofNat 64) (by omega))
  · rw [keep2 _ (by decide), r6, g_eq]
  · exact keep2 _ (scratch_of_ne hr).2.2.2.2.2.1

/-! ### One record -/

theorem hyb_salt_eq : hybSalt = [.LD .x6 .x8 0, .SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] ++
    [.LD .x31 .x7 (BitVec.ofNat 12 0), .SD .x21 .x31 (BitVec.ofNat 12 0),
     .LD .x31 .x7 (BitVec.ofNat 12 8), .SD .x21 .x31 (BitVec.ofNat 12 8)] := rfl

set_option maxHeartbeats 4000000 in
theorem salt_part (init : MachineState) (positions : Positions) (o : Nat) (present : o < positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*529)) (fixed : Fixed positions o state)
    (inv : Inv init state (wordSource positions) (102*o))
    (loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 (ordinalIndex positions o)) :
    let u := hybSalt.foldl execInstrBr state
    Runs state u 7 7 ∧ Inv init u (wordSource positions) (102*o+2) ∧ u.pc = BitVec.ofNat 64 (4096+4*536) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o) ∧ Fixed positions o u := by
  intro u
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have card := card_le positions
  have code := hyb_codes.2.2.1
  rw [hyb_salt_eq] at code
  have cl (q : Nat) (h : q < 7) := code_one code q (by simpa using h)
  -- the index load
  let s1 := execInstrBr state (.LD .x6 .x8 0)
  have addr : state.getReg .x8 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (indicesBase+8*o) := by
    rw [fixed.x8]; simp [signExtend12]
  have valid : memoryArgumentsValid state (.LD .x6 .x8 0) = true := by
    simp only [memoryArgumentsValid, memAccess, addr]
    have ib : indicesBase = 6375350304 := rfl
    exact QOpening.aligned_access _ (by rw [ib]; omega) (by rw [ib]; unfold MEMORY_BYTES; omega)
  have run1 := runs_one state _ 529 (by simpa using cl 0 (by decide)) pc rfl valid
  have x6₁ : s1.getReg .x6 = BitVec.ofNat 64 i := by
    simp only [s1, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC, addr]
    simp [loaded, i]
  have keep1 : ∀ r, r ≠ .x6 → s1.getReg r = state.getReg r := by
    intro r h; simp [s1, execInstrBr, Ne.symm h]
  have pc1 : s1.pc = BitVec.ofNat 64 (4096+4*530) := (straight_pc state _ rfl).trans (pc_next _ _ pc)
  -- the salt address
  let mid : List Instr := [.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7]
  let s2 := mid.foldl execInstrBr s1
  have midCode : CodeAt 530 mid := fun q h => by
    have hq : q < 2 := by simpa [mid] using h
    interval_cases q
    · simpa [mid] using cl 1 (by decide)
    · simpa [mid] using cl 2 (by decide)
  have run2 : Runs s1 s2 2 2 := (runs_pure _ _ s1 midCode pc1 rfl).cast rfl (by simp [mid, cost, instructionCycles])
  have x7₂ : s2.getReg .x7 = BitVec.ofNat 64 (nonceBase+16*i) := by
    simp only [s2, mid, List.foldl_cons, List.foldl_nil, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp [x6₁, keep1 .x22 (by decide), fixed.x22, shift_salt i (by omega), add_nat]
  have keep2 : ∀ r, r ≠ .x7 → s2.getReg r = s1.getReg r := by
    intro r h; simp [s2, mid, execInstrBr, Ne.symm h]
  have pc2 : s2.pc = BitVec.ofNat 64 (4096+4*532) := by rw [pure_pc _ _ rfl, pc1, pc_offset]; rfl
  have nb := nb_val
  have pb := pb_val
  have tb := tb_val
  obtain ⟨run3, inv3, pc3, keep3⟩ := copy_step init s2 (wordSource positions) 532 .x7 (by decide) 0 0
    (nonceBase+16*i) (proofBase+8*(102*o)) (102*o) (by decide) (by decide) (by simpa using cl 3 (by decide))
    (by simpa using cl 4 (by decide)) pc2 x7₂ ((keep2 _ (by decide)).trans ((keep1 _ (by decide)).trans fixed.x21))
    (by omega) (by omega) (by omega) (by omega) (by unfold MEMORY_BYTES; omega)
    (by rw [show 102*o = 102*o+0 from rfl, word_source_salt positions o 0 (by decide)])
    (inv.of_mem (by rw [pure_mem _ _ rfl]; exact mem_set_reg _ _ _))
  let s3 := execInstrBr (execInstrBr s2 (.LD .x31 .x7 (BitVec.ofNat 12 0))) (.SD .x21 .x31 (BitVec.ofNat 12 0))
  obtain ⟨run4, inv4, pc4, keep4⟩ := copy_step init s3 (wordSource positions) 534 .x7 (by decide) 8 8
    (nonceBase+16*i) (proofBase+8*(102*o)) (102*o+1) (by decide) (by decide) (by simpa using cl 5 (by decide))
    (by simpa using cl 6 (by decide)) pc3 ((keep3 _ (by decide)).trans x7₂)
    ((keep3 _ (by decide)).trans ((keep2 _ (by decide)).trans ((keep1 _ (by decide)).trans fixed.x21)))
    (by omega) (by omega) (by omega) (by omega) (by unfold MEMORY_BYTES; omega)
    (by rw [word_source_salt positions o 1 (by decide)]) inv3
  have shape : u = execInstrBr (execInstrBr s3 (.LD .x31 .x7 (BitVec.ofNat 12 8))) (.SD .x21 .x31 (BitVec.ofNat 12 8)) := by
    simp only [u, hyb_salt_eq, List.foldl_append, List.foldl_cons, List.foldl_nil, s3, s2, s1, mid]
  rw [shape]
  refine ⟨(run1.trans (run2.trans (run3.trans run4))).cast rfl rfl, inv4, pc4, ?_, fixed.keep (fun r hr => ?_)⟩
  · rw [keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), x6₁]
  · have ne := scratch_of_ne hr
    rw [keep4 _ ne.2.2.2.2.2.1, keep3 _ ne.2.2.2.2.2.1, keep2 _ ne.2.1, keep1 _ ne.1]

theorem pentas_run (init : MachineState) (positions : Positions) (o : Nat) (present : o < positions.card)
    (card : positions.card ≤ LENGTH) : ∀ n ≤ 5, ∀ t : MachineState,
    t.pc = BitVec.ofNat 64 (4096+4*536) → t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o) →
    Fixed positions o t → Inv init t (wordSource positions) (102*o+2) →
    ∃ u, Runs t u (43*n) (52*n) ∧ Inv init u (wordSource positions) (102*o+2+16*n) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(536+10*n)) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/5^n) ∧ Fixed positions o u := by
  intro n
  induction n with
  | zero =>
    intro _ t pc x6 f inv
    exact ⟨t, Runs.zero t, by simpa using inv, by simpa using pc, by simpa using x6, f⟩
  | succ n ih =>
    intro hn t pc x6 f inv
    obtain ⟨u, r, i', p', x6', f'⟩ := ih (by omega) t pc x6 f inv
    obtain ⟨u2, r2, i2, p2, x62, f2⟩ := penta_level init positions o n (by omega) present card u p' x6' f' i'
    exact ⟨u2, (r.trans r2).cast (by ring) (by ring), i2.cast_count (by ring), p2, x62, f2⟩

theorem bins_run (init : MachineState) (positions : Positions) (o : Nat) (present : o < positions.card)
    (card : positions.card ≤ LENGTH) : ∀ n ≤ 3, ∀ t : MachineState,
    t.pc = BitVec.ofNat 64 (4096+4*597) → t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/9375) →
    Fixed positions o t → Inv init t (wordSource positions) (102*o+90) →
    let u := ((List.range n).flatMap (fun m => hybBin (m+6))).foldl execInstrBr t
    Runs t u (16*n) (19*n) ∧ Inv init u (wordSource positions) (102*o+90+4*n) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(597+16*n)) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/(9375*2^n)) ∧ Fixed positions o u := by
  intro n
  induction n with
  | zero =>
    intro _ t pc x6 f inv
    exact ⟨Runs.zero t, by simpa using inv, by simpa using pc, by simpa using x6, f⟩
  | succ n ih =>
    intro hn t pc x6 f inv
    obtain ⟨r, i', p', x6', f'⟩ := ih (by omega) t pc x6 f inv
    obtain ⟨r2, i2, p2, x62, f2⟩ := bin_level init positions o n (by omega) present card _ p' x6' f' i'
    have shape : ((List.range (n+1)).flatMap (fun m => hybBin (m+6))).foldl execInstrBr t =
        (hybBin (n+6)).foldl execInstrBr (((List.range n).flatMap (fun m => hybBin (m+6))).foldl execInstrBr t) := by
      simp [List.range_succ, List.flatMap_append, List.foldl_append]
    intro u
    rw [show u = _ from shape]
    exact ⟨(r.trans r2).cast (by ring) (by ring), i2.cast_count (by ring), p2, x62, f2⟩

structure RecState (init : MachineState) (positions : Positions) (o : Nat) (state : MachineState) : Prop where
  fixed : Fixed positions o state
  pc : state.pc = BitVec.ofNat 64 (4096+4*(if o = positions.card then 648 else 529))
  inv : Inv init state (wordSource positions) (102*o)

def latchPure : List Instr := [.ADDI .x21 .x21 816, .ADDI .x8 .x8 8]

theorem latch_regs (t : MachineState) :
    (latchPure.foldl execInstrBr t).getReg .x21 = t.getReg .x21 + signExtend12 (BitVec.ofNat 12 816) ∧
    (latchPure.foldl execInstrBr t).getReg .x8 = t.getReg .x8 + signExtend12 (BitVec.ofNat 12 8) ∧
    ∀ r, r ≠ .x21 → r ≠ .x8 → (latchPure.foldl execInstrBr t).getReg r = t.getReg r := by
  refine ⟨?_, ?_, ?_⟩
  · simp [latchPure, execInstrBr]
  · simp [latchPure, execInstrBr]
  · intro r a b; simp [latchPure, execInstrBr, Ne.symm a, Ne.symm b]

set_option maxHeartbeats 4000000 in
theorem record_step (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (o : Nat) (present : o < positions.card) (state : MachineState)
    (at_ : RecState (s.initialState .opening (td, positions)) positions o state) :
    ∃ next, Runs state next 301 364 ∧ RecState (s.initialState .opening (td, positions)) positions (o+1) next := by
  let init := s.initialState .opening (td, positions)
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have notLast : o ≠ positions.card := by omega
  have pc0 : state.pc = BitVec.ofNat 64 (4096+4*529) := by simpa [notLast] using at_.pc
  have loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 (ordinalIndex positions o) := by
    have ib : indicesBase = 6375350304 := rfl
    rw [at_.inv.input _ (by rw [ib, tb_val]; omega) (by rw [ib, pb_val]; omega)
      (by rw [ib]; omega), QOpening.input_index s layout td positions o present,
      ordinal_index positions o present]
  obtain ⟨r1, i1, p1, x61, f1⟩ := salt_part init positions o present state pc0 at_.fixed at_.inv loaded
  let t1 := hybSalt.foldl execInstrBr state
  obtain ⟨t2, r2, i2, p2, x62, f2⟩ := pentas_run init positions o present card 5 le_rfl t1 p1 x61 f1 i1
  obtain ⟨tq, rq, iq, pq, x6q, fq⟩ := quad_level init positions o present card t2 (by simpa using p2)
    (by simpa using x62) f2 (by simpa using i2)
  obtain ⟨r3, i3, p3, _, f3⟩ := bins_run init positions o present card 3 le_rfl tq (by simpa using pq)
    (by simpa using x6q) fq (by simpa using iq)
  let t3 := ((List.range 3).flatMap (fun m => hybBin (m+6))).foldl execInstrBr tq
  have latchCode : CodeAt 645 latchPure := hyb_codes.2.2.2.2.2.1
  let t4 := latchPure.foldl execInstrBr t3
  have r4 : Runs t3 t4 2 2 := (runs_pure _ _ t3 latchCode (by simpa using p3) rfl).cast rfl rfl
  have p4 : t4.pc = BitVec.ofNat 64 (4096+4*647) := by rw [pure_pc _ _ rfl, p3, pc_offset]; rfl
  obtain ⟨l21, l8, keep4⟩ := latch_regs t3
  have x21₄ : t4.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*(o+1))) := by
    rw [l21, f3.x21, sext_small 816 (by decide), add_nat]
    all_goals (apply congrArg (BitVec.ofNat 64); omega)
  have x8₄ : t4.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*(o+1)) := by
    rw [l8, f3.x8, sext_small 8 (by decide), add_nat]
    all_goals (apply congrArg (BitVec.ofNat 64); omega)
  have mem4 : t4.mem = t3.mem := pure_mem _ _ rfl
  have branch := hyb_codes.2.2.2.2.2.2.1
  let next := execInstrBr t4 (.BNE .x8 .x18 7720)
  have r5 : Runs t4 next 1 1 := by
    intro fuel coins
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ 647 _ branch p4) rfl]
    rfl
  have shapeN : next = t4.setPC (if t4.getReg .x8 != t4.getReg .x18 then t4.pc + signExtend13 7720 else t4.pc + 4) :=
    bne_shape t4 _ _ _
  refine ⟨next, ((r1.trans (r2.trans (rq.trans (r3.trans r4)))).trans r5).cast rfl rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [shapeN] <;> simp only [MachineState.getReg_setPC]
    · exact x8₄
    · rw [keep4 _ (by decide) (by decide)]; exact f3.x9
    · rw [keep4 _ (by decide) (by decide)]; exact f3.x15
    · rw [keep4 _ (by decide) (by decide)]; exact f3.x18
    · rw [keep4 _ (by decide) (by decide)]; exact f3.x19
    · exact x21₄
    · rw [keep4 _ (by decide) (by decide)]; exact f3.x22
    · rw [keep4 _ (by decide) (by decide)]; exact f3.x23
  · rw [shapeN, set_pc_pc, x8₄, keep4 _ (by decide) (by decide), f3.x18, p4]
    have ib : indicesBase = 6375350304 := rfl
    by_cases last : o+1 = positions.card
    · rw [if_pos last, last]
      simp
    · rw [if_neg last]
      have ne : BitVec.ofNat 64 (indicesBase+8*(o+1)) ≠ BitVec.ofNat 64 (indicesBase+8*positions.card) := by
        intro h
        have := QOpening.nat_address_injective (by omega) (by omega) h
        omega
      simp only [bne_iff_ne, ne_eq, ne, not_false_eq_true, ite_true]
      decide
  · rw [shapeN]
    exact (i3.cast_count (by ring) : Inv init t3 (wordSource positions) (102*(o+1))).of_mem (by rw [set_pc_mem, mem4])

theorem records_run (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : ∀ n o (state : MachineState), o+n = positions.card →
    RecState (s.initialState .opening (td, positions)) positions o state →
    ∃ final, Runs state final (301*n) (364*n) ∧
      RecState (s.initialState .opening (td, positions)) positions positions.card final := by
  intro n
  induction n with
  | zero => intro o state h at_; simp at h; subst h; exact ⟨state, Runs.zero state, at_⟩
  | succ n ih =>
    intro o state h at_
    obtain ⟨next, r, a⟩ := record_step s layout td positions o (by omega) state at_
    obtain ⟨final, r', a'⟩ := ih (o+1) _ (by omega) a
    exact ⟨final, (r.trans r').cast (by ring) (by ring), a'⟩

/-! ### The level-9 table and the exit -/

/-- Initial address of table doubleword `x < 896`: doubleword `x % 4` of slot `x % 20 / 4` of
level-9 group `x / 20`. -/
def tableSource (x : Nat) : Nat := trapdoorBase+pentaGroupSlotOffset CAP_LEVEL (x/20) (x%20/4)+8*(x%4)

/-- Source of output doubleword `u`: the records, then the table. -/
def proofSource (positions : Positions) (u : Nat) : Nat :=
  if u < 102*positions.card then wordSource positions u else tableSource (u-102*positions.card)

theorem Inv.source_congr {init state : MachineState} {f g : Nat → Nat} {count : Nat}
    (inv : Inv init state f count) (same : ∀ u < count, f u = g u) : Inv init state g count :=
  ⟨inv.input, fun u h => (inv.output u h).trans (by rw [same u h])⟩

theorem hyb_slots_succ (n : Nat) : hybSlots (n+1) = hybSlots n ++ hybFour .x30 (32*n) (32*n) := by
  simp [hybSlots, List.range_succ, List.flatMap_append]

theorem hyb_four_length (x : Reg) (src off : Nat) : (hybFour x src off).length = 8 := by
  rw [hyb_four_eq]; rfl

theorem hyb_slots_length : ∀ n, (hybSlots n).length = 8*n
  | 0 => rfl
  | n+1 => by rw [hyb_slots_succ, List.length_append, hyb_slots_length n, hyb_four_length]; ring

theorem hyb_group_eq : hybGroup = hybSlots 5 ++ [.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] := rfl

theorem hyb_table_eq : hybTable = [.LUI .x30 (hybPage 9), .ADD .x30 .x30 .x9] ++ (List.replicate 44 hybGroup).flatten ++ hybHalf := rfl

theorem hyb_half_eq : hybHalf = hybSlots 4 ++ [.ADDI .x30 .x30 368, .ADDI .x21 .x21 128] := rfl

theorem table_bound : pentaGroupBase 9+40+368*45 ≤ 1728786760 := by decide

/-- Address of slot 0 of level-9 group 0. -/
def hybTableStart : Nat := pentaGroupBase 9+40+trapdoorBase

theorem hyb_table_start_value : hybTableStart = 5839253536 := rfl

theorem table_source_eq (x : Nat) : tableSource x = hybTableStart+368*(x/20)+8*(x%20) := by
  unfold tableSource hybTableStart pentaGroupSlotOffset CAP_LEVEL
  omega

/-- The first `n` slots of the group whose slot 0 is at `x30 = G`: output words `count … count + 4 n - 1`. -/
theorem slots_run (init : MachineState) (source : Nat → Nat) (start : Nat) :
    ∀ n ≤ 5, ∀ (G D count : Nat) (t : MachineState), CodeAt start (hybSlots n) →
    t.pc = BitVec.ofNat 64 (4096+4*start) →
    t.getReg .x30 = BitVec.ofNat 64 G → t.getReg .x21 = BitVec.ofNat 64 D →
    D = proofBase+8*count → G % 8 = 0 → trapdoorBase ≤ G → G+160 ≤ proofBase →
    proofBase+8*count+160 ≤ MEMORY_BYTES →
    (∀ w < 4*n, source (count+w) = G+8*w) → Inv init t source count →
    let u := (hybSlots n).foldl execInstrBr t
    Runs t u (8*n) (8*n) ∧ Inv init u source (count+4*n) ∧ u.pc = BitVec.ofNat 64 (4096+4*(start+8*n)) ∧
      ∀ r, r ≠ .x31 → u.getReg r = t.getReg r := by
  intro n
  induction n with
  | zero =>
    intro _ G D count t _ pc _ _ _ _ _ _ _ _ inv u
    rw [show u = t from rfl]
    exact ⟨Runs.zero t, by simpa using inv, by simpa using pc, fun _ _ => rfl⟩
  | succ n ih =>
    intro hn G D count t code pc x30 x21 target aligned low high fits named inv
    have codeA : CodeAt start (hybSlots n) := fun q h => by
      have hq : q < (hybSlots (n+1)).length := by
        rw [hyb_slots_succ, List.length_append]; omega
      rw [code q hq, hyb_slots_succ, List.getElem?_append_left h]
    have codeB : CodeAt (start+8*n) (hybFour .x30 (32*n) (32*n)) := fun q h => by
      have hq : 8*n+q < (hybSlots (n+1)).length := by
        rw [hyb_slots_succ, List.length_append, hyb_slots_length]; omega
      have := code (8*n+q) hq
      rw [show start+(8*n+q) = start+8*n+q by omega] at this
      rw [this, hyb_slots_succ, List.getElem?_append_right (by rw [hyb_slots_length]; omega),
        hyb_slots_length, show 8*n+q-8*n = q by omega]
    obtain ⟨r1, i1, p1, k1⟩ := ih (by omega) G D count t codeA pc x30 x21 target aligned low high fits
      (fun w hw => named w (by omega)) inv
    let v := (hybSlots n).foldl execInstrBr t
    obtain ⟨r2, i2, p2, k2⟩ := four_run init source (start+8*n) .x30 (by decide) (by decide) (32*n) (32*n)
      G D (count+4*n) codeB (by omega) (by omega) v p1 ((k1 _ (by decide)).trans x30)
      ((k1 _ (by decide)).trans x21) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun w hw => by rw [show count+4*n+w = count+(4*n+w) by omega, named _ (by omega)]; omega) i1
    have shape : (hybSlots (n+1)).foldl execInstrBr t = (hybFour .x30 (32*n) (32*n)).foldl execInstrBr v := by
      rw [hyb_slots_succ, List.foldl_append]
    intro u
    rw [show u = _ from shape]
    refine ⟨(r1.trans r2).cast (by ring) (by ring), i2.cast_count (by ring), ?_, ?_⟩
    · rw [p2]; exact congrArg (BitVec.ofNat 64) (by omega)
    · intro r h; rw [k2 r h, k1 r h]

set_option maxHeartbeats 4000000 in
theorem groups_run (init : MachineState) (positions : Positions) (card : positions.card ≤ LENGTH) :
    ∀ n ≤ 44, ∀ t : MachineState,
    t.pc = BitVec.ofNat 64 (4096+4*890) →
    t.getReg .x30 = BitVec.ofNat 64 hybTableStart →
    t.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*positions.card)) →
    Inv init t (proofSource positions) (102*positions.card) →
    let u := (List.replicate n hybGroup).flatten.foldl execInstrBr t
    Runs t u (42*n) (42*n) ∧ Inv init u (proofSource positions) (102*positions.card+20*n) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(890+42*n)) ∧
      u.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*positions.card+20*n)) ∧
      u.getReg .x30 = BitVec.ofNat 64 (hybTableStart+368*n) ∧
      (∀ r, r ≠ .x21 → r ≠ .x30 → r ≠ .x31 → u.getReg r = t.getReg r) := by
  have hL : LENGTH = 16777216 := rfl
  have tb := tb_val
  have pb := pb_val
  have ts := hyb_table_start_value
  intro n
  induction n with
  | zero =>
    intro _ t pc x30 x21 inv
    exact ⟨Runs.zero t, by simpa using inv, by simpa using pc, by simpa using x21, by simpa using x30,
      fun _ _ _ _ => rfl⟩
  | succ n ih =>
    intro hn t pc x30 x21 inv
    obtain ⟨r, i', p', d', s', k'⟩ := ih (by omega) t pc x30 x21 inv
    let v := (List.replicate n hybGroup).flatten.foldl execInstrBr t
    have gcode := (hyb_codes.2.2.2.2.2.2.2.2.1) n (by omega)
    rw [hyb_group_eq] at gcode
    have c1 : CodeAt (890+42*n) (hybSlots 5) := fun q h => by
      have := gcode q (by rw [List.length_append]; omega)
      rw [this, List.getElem?_append_left h]
    have c3 : CodeAt (890+42*n+40) [.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] := fun q h => by
      have hq : q < 2 := by simpa using h
      have := gcode (40+q) (by rw [List.length_append, hyb_slots_length]; simp; omega)
      rw [show 890+42*n+(40+q) = 890+42*n+40+q by omega] at this
      rw [this, List.getElem?_append_right (by rw [hyb_slots_length]; omega), hyb_slots_length,
        show 40+q-8*5 = q by omega]
    obtain ⟨r1, i1, p1, k1⟩ := slots_run init (proofSource positions) (890+42*n) 5 le_rfl
      (hybTableStart+368*n) (proofBase+8*(102*positions.card+20*n)) (102*positions.card+20*n) v
      c1 p' s' d' rfl (by rw [ts]; omega) (by rw [ts, tb]; omega) (by rw [ts, pb]; omega)
      (by rw [pb]; unfold MEMORY_BYTES; omega)
      (fun w hw => by
        unfold proofSource
        rw [if_neg (by omega), table_source_eq]
        rw [show 102*positions.card+20*n+w-102*positions.card = 20*n+w by omega,
          show (20*n+w)/20 = n by omega, show (20*n+w)%20 = w by omega]) i'
    let v1 := (hybSlots 5).foldl execInstrBr v
    let v3 := ([.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] : List Instr).foldl execInstrBr v1
    have r3 : Runs v1 v3 2 2 := (runs_pure _ _ v1 c3 (p1.trans (congrArg (BitVec.ofNat 64) (by omega))) rfl).cast rfl rfl
    have shape : (List.replicate (n+1) hybGroup).flatten.foldl execInstrBr t = v3 := by
      simp only [v3, v1, v, List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.foldl_append, hyb_group_eq]
    have a21 : v3.getReg .x21 = v1.getReg .x21 + signExtend12 (BitVec.ofNat 12 160) := by
      simp [v3, execInstrBr]
    have a30 : v3.getReg .x30 = v1.getReg .x30 + signExtend12 (BitVec.ofNat 12 368) := by
      simp [v3, execInstrBr]
    have a_ : ∀ q, q ≠ .x21 → q ≠ .x30 → v3.getReg q = v1.getReg q := by
      intro q a b; simp [v3, execInstrBr, Ne.symm a, Ne.symm b]
    intro u
    rw [show u = v3 from shape]
    refine ⟨((r.trans r1).trans r3).cast (by ring) (by ring), ?_, ?_, ?_, ?_, ?_⟩
    · exact (i1.of_mem (pure_mem _ _ rfl)).cast_count (by ring)
    · rw [pure_pc _ _ rfl, p1, pc_offset]; exact congrArg (BitVec.ofNat 64) (by simp; omega)
    · rw [a21, k1 .x21 (by decide), d', sext_small 160 (by decide), add_nat]
      all_goals (apply congrArg (BitVec.ofNat 64); omega)
    · rw [a30, k1 .x30 (by decide), s', sext_small 368 (by decide), add_nat]
      all_goals (apply congrArg (BitVec.ofNat 64); omega)
    · intro q a b c
      rw [a_ q a b, k1 q c, k' q a b c]

set_option maxHeartbeats 4000000 in
/-- The last table group: nodes 220-223 (slots 0-3 of group 44). -/
theorem half_run (init : MachineState) (positions : Positions) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*2738))
    (x30 : t.getReg .x30 = BitVec.ofNat 64 (hybTableStart+368*44))
    (x21 : t.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*positions.card+20*44)))
    (inv : Inv init t (proofSource positions) (102*positions.card+20*44)) :
    let u := hybHalf.foldl execInstrBr t
    Runs t u 34 34 ∧ Inv init u (proofSource positions) (102*positions.card+896) ∧
      u.pc = BitVec.ofNat 64 (4096+4*2772) ∧
      u.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(102*positions.card+896)) ∧
      (∀ r, r ≠ .x21 → r ≠ .x30 → r ≠ .x31 → u.getReg r = t.getReg r) := by
  have hL : LENGTH = 16777216 := rfl
  have tb := tb_val
  have pb := pb_val
  have ts := hyb_table_start_value
  have hcode := hyb_codes.2.2.2.2.2.2.2.2.2.1
  rw [hyb_half_eq] at hcode
  have c1 : CodeAt 2738 (hybSlots 4) := fun q h => by
    have := hcode q (by rw [List.length_append]; omega)
    rw [this, List.getElem?_append_left h]
  have c3 : CodeAt (2738+32) [.ADDI .x30 .x30 368, .ADDI .x21 .x21 128] := fun q h => by
    have hq : q < 2 := by simpa using h
    have := hcode (32+q) (by rw [List.length_append, hyb_slots_length]; simp; omega)
    rw [show 2738+(32+q) = 2738+32+q by omega] at this
    rw [this, List.getElem?_append_right (by rw [hyb_slots_length]; omega), hyb_slots_length,
      show 32+q-8*4 = q by omega]
  obtain ⟨r1, i1, p1, k1⟩ := slots_run init (proofSource positions) 2738 4 (by decide)
    (hybTableStart+368*44) (proofBase+8*(102*positions.card+20*44)) (102*positions.card+20*44) t
    c1 pc x30 x21 rfl (by rw [ts]) (by rw [ts, tb]; norm_num) (by rw [ts, pb]; norm_num)
    (by rw [pb]; unfold MEMORY_BYTES; omega)
    (fun w hw => by
      unfold proofSource
      rw [if_neg (by omega), table_source_eq]
      rw [show 102*positions.card+20*44+w-102*positions.card = 20*44+w by omega,
        show (20*44+w)/20 = 44 by omega, show (20*44+w)%20 = w by omega]) inv
  let v1 := (hybSlots 4).foldl execInstrBr t
  let v3 := ([.ADDI .x30 .x30 368, .ADDI .x21 .x21 128] : List Instr).foldl execInstrBr v1
  have r3 : Runs v1 v3 2 2 := (runs_pure _ _ v1 c3 (p1.trans (congrArg (BitVec.ofNat 64) (by omega))) rfl).cast rfl rfl
  have shape : hybHalf.foldl execInstrBr t = v3 := by
    simp only [v3, v1, hyb_half_eq, List.foldl_append]
  have a21 : v3.getReg .x21 = v1.getReg .x21 + signExtend12 (BitVec.ofNat 12 128) := by
    simp [v3, execInstrBr]
  have a_ : ∀ q, q ≠ .x21 → q ≠ .x30 → v3.getReg q = v1.getReg q := by
    intro q a b; simp [v3, execInstrBr, Ne.symm a, Ne.symm b]
  intro u
  rw [show u = v3 from shape]
  refine ⟨(r1.trans r3).cast (by ring) (by ring), ?_, ?_, ?_, ?_⟩
  · exact (i1.of_mem (pure_mem _ _ rfl)).cast_count (by ring)
  · rw [pure_pc _ _ rfl, p1, pc_offset]; rfl
  · rw [a21, k1 .x21 (by decide), x21, sext_small 128 (by decide), add_nat]
    all_goals (apply congrArg (BitVec.ofNat 64); omega)
  · intro q a b c
    rw [a_ q a b, k1 q c]

end TwoPermutationPrototype.QuadOpening
