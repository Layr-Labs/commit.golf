import CommitGolfCandidate.QuadOpeningLevel
import CommitGolfCandidate.Counting
import CommitGolfCandidate.Machine
import CommitGolfCandidate.PentaCapSpec

/-! The hybrid record writer (words 527-870) and the level-11 table copy (words 871-1986).
Word 11 jumps to word 527; the two setup words turn `x18` into the end pointer of the index list.
Each record copies the salt, the four other slots of the 5-ary levels 0-2 (rotation order) and the
binary siblings of levels 3-13 with doubleword loads and stores (94 doublewords); the table copy
appends the 66 level-14 nodes. Nothing calls the oracle. -/

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
    (∀ k < 3, CodeAt (536+54*k) (hybPenta k)) ∧ (∀ m < 8, CodeAt (740+16*m) (hybBin (m+4))) ∧
    CodeAt 868 [.ADDI .x21 .x21 752, .ADDI .x8 .x8 8] ∧ program[870]? = some (.BNE .x8 .x18 6828) ∧
    CodeAt 871 [.LUI .x30 (hybPage 12), .ADD .x30 .x30 .x9] ∧
    CodeAt 1965 hybHalf ∧ CodeAt 1983 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧
    program[1986]? = some .ECALL := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_0 : ∀ i < 4, CodeAt (873+42*(4*0+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_1 : ∀ i < 4, CodeAt (873+42*(4*1+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_2 : ∀ i < 4, CodeAt (873+42*(4*2+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_3 : ∀ i < 4, CodeAt (873+42*(4*3+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_4 : ∀ i < 4, CodeAt (873+42*(4*4+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_5 : ∀ i < 4, CodeAt (873+42*(4*5+i)) hybGroup := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hyb_groups_6 : ∀ i < 2, CodeAt (873+42*(4*6+i)) hybGroup := by
  decide +kernel

theorem hyb_groups : ∀ g < 26, CodeAt (873+42*g) hybGroup := by
  intro g hg
  have e : g = 4*(g/4)+g%4 := by omega
  have hq : g/4 < 7 := by omega
  have hi : g%4 < 4 := Nat.mod_lt _ (by decide)
  have hr : g/4*4+g%4 < 26 := by omega
  rw [e]; revert hr hi hq; generalize g/4 = q; generalize g%4 = i; intro hq hi hr
  interval_cases q <;> first
    | exact hyb_groups_0 i (by omega)
    | exact hyb_groups_1 i (by omega)
    | exact hyb_groups_2 i (by omega)
    | exact hyb_groups_3 i (by omega)
    | exact hyb_groups_4 i (by omega)
    | exact hyb_groups_5 i (by omega)
    | exact hyb_groups_6 i (by omega)

theorem hyb_codes :
    program[11]? = some hybJump ∧ CodeAt 527 hybSetup ∧ CodeAt 529 hybSalt ∧
    (∀ k < 3, CodeAt (536+54*k) (hybPenta k)) ∧ (∀ m < 8, CodeAt (740+16*m) (hybBin (m+4))) ∧
    CodeAt 868 [.ADDI .x21 .x21 752, .ADDI .x8 .x8 8] ∧ program[870]? = some (.BNE .x8 .x18 6828) ∧
    CodeAt 871 [.LUI .x30 (hybPage 12), .ADD .x30 .x30 .x9] ∧ (∀ g < 26, CodeAt (873+42*g) hybGroup) ∧
    CodeAt 1965 hybHalf ∧ CodeAt 1983 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧
    program[1986]? = some .ECALL :=
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
def Scratch (r : Reg) : Prop := r = .x6 ∨ r = .x7 ∨ r = .x25 ∨ r = .x28 ∨ r = .x30 ∨ r = .x31

/-! ### A 5-ary level -/

def pentaHead (k : Nat) : List Instr := (hybPenta k).take 6

theorem penta_head_eq (k : Nat) : pentaHead k =
    [.LUI .x28 (hybPage k), .ADD .x28 .x28 .x9, .REMU .x25 .x6 .x19, .DIVU .x6 .x6 .x19,
     .MUL .x30 .x6 .x23, .ADD .x30 .x30 .x28] := rfl

theorem penta_head_regs (k : Nat) (hk : k < 3) (t : MachineState) (n : Nat) (hn : n < 2^40)
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

theorem bin_head_regs (k : Nat) (hk : k < 15) (t : MachineState) (n : Nat) (hn : n < 2^40)
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
    have : pentaGroupBase k ≤ 1580609496 := by interval_cases k <;> decide
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
  x21 : t.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(94*o))
  x22 : t.getReg .x22 = BitVec.ofNat 64 nonceBase
  x23 : t.getReg .x23 = BitVec.ofNat 64 368

theorem Fixed.keep {positions : Positions} {o : Nat} {t u : MachineState} (f : Fixed positions o t)
    (same : ∀ r, ¬ Scratch r → u.getReg r = t.getReg r) : Fixed positions o u := by
  obtain ⟨a, b, c, d, e, g, h, i⟩ := not_scratch_regs
  exact ⟨(same _ a).trans f.x8, (same _ b).trans f.x9, (same _ c).trans f.x15, (same _ d).trans f.x18,
    (same _ e).trans f.x19, (same _ g).trans f.x21, (same _ h).trans f.x22, (same _ i).trans f.x23⟩

theorem scratch_of_ne {r : Reg} (h : ¬ Scratch r) : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x25 ∧ r ≠ .x28 ∧ r ≠ .x30 ∧ r ≠ .x31 := by
  unfold Scratch at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> exact h (by simp [e])

set_option maxHeartbeats 4000000 in
theorem penta_level (init : MachineState) (positions : Positions) (o k : Nat) (hk : k < 3)
    (present : o < positions.card) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(536+54*k)))
    (x6 : t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/5^k)) (fixed : Fixed positions o t)
    (inv : Inv init t (wordSource positions) (94*o+2+16*k)) :
    let u := (hybPenta k).foldl execInstrBr t
    Runs t u 54 75 ∧ Inv init u (wordSource positions) (94*o+2+16*(k+1)) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(536+54*(k+1))) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/5^(k+1)) ∧ Fixed positions o u := by
  intro u
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have codes := (hyb_codes.2.2.2.1) k hk
  rw [hyb_penta_split] at codes
  -- the head
  have headCode : CodeAt (536+54*k) (pentaHead k) := fun j h => by
    have := codes j (by simp [pentaHead, hybPenta] at h ⊢; omega)
    rw [this, List.getElem?_append_left h]
  have n_small : i/5^k < 2^40 := by
    have := Nat.div_le_self i (5^k); omega
  let h0 := (pentaHead k).foldl execInstrBr t
  have run0 : Runs t h0 6 15 := (runs_pure _ _ t headCode pc rfl).cast rfl (by
    simp [pentaHead, hybPenta, cost, instructionCycles])
  obtain ⟨r25, r6, r30, keep0⟩ := penta_head_regs k hk t (i/5^k) n_small x6 fixed.x9 fixed.x19 fixed.x23
  have pc0 : h0.pc = BitVec.ofNat 64 (4096+4*(536+54*k+6)) := by
    rw [pure_pc _ _ rfl, pc, pc_offset]; rfl
  have f0 : Fixed positions o h0 := fixed.keep keep0
  -- facts on the group
  have g_eq : i/5^k/5 = i/5^(k+1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  have count := div_lt_count i hi (k+1)
  rw [place_value_low (k+1) (by omega)] at count
  have room := base_bound k (by omega)
  have bk : pentaGroupBase k ≤ 1580609496 := by interval_cases k <;> decide
  -- one sibling
  have sib (j : Nat) (hj : j < 4) (v : MachineState)
      (pcv : v.pc = BitVec.ofNat 64 (4096+4*(536+54*k+6+12*j)))
      (v25 : v.getReg .x25 = BitVec.ofNat 64 (i/5^k%5))
      (v30 : v.getReg .x30 = BitVec.ofNat 64 (368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase)))
      (fv : Fixed positions o v) (invv : Inv init v (wordSource positions) (94*o+2+16*k+4*j)) :
      let w := (siblingHead j ++ hybFour .x7 0 (16+128*k+32*j)).foldl execInstrBr v
      Runs v w 12 15 ∧ Inv init w (wordSource positions) (94*o+2+16*k+4*(j+1)) ∧
        w.pc = BitVec.ofNat 64 (4096+4*(536+54*k+6+12*(j+1))) ∧
        w.getReg .x25 = v.getReg .x25 ∧ w.getReg .x30 = v.getReg .x30 ∧ w.getReg .x6 = v.getReg .x6 ∧
        (∀ r, ¬ Scratch r → w.getReg r = v.getReg r) := by
    intro w
    have off : 6+12*j < 54 := by omega
    have sc : CodeAt (536+54*k+6+12*j) (siblingHead j) := fun q h => by
      have hq : q < 4 := by simpa [siblingHead] using h
      have := codes (6+12*j+q) (by simp [pentaHead, hybPenta, siblingHead, hybFour]; omega)
      rw [show 536+54*k+(6+12*j+q) = 536+54*k+6+12*j+q by omega] at this
      rw [this]
      interval_cases j <;> interval_cases q <;> simp [pentaHead, hybPenta, siblingHead, hybFour, List.range_succ, hybSibling]
    have fc : CodeAt (536+54*k+6+12*j+4) (hybFour .x7 0 (16+128*k+32*j)) := fun q h => by
      have hq : q < 8 := by simpa [hybFour] using h
      have := codes (6+12*j+4+q) (by simp [pentaHead, hybPenta, siblingHead, hybFour]; omega)
      rw [show 536+54*k+(6+12*j+4+q) = 536+54*k+6+12*j+4+q by omega] at this
      rw [this]
      interval_cases j <;> interval_cases q <;> simp [pentaHead, hybPenta, siblingHead, hybFour, List.range_succ, hybSibling]
    let v1 := (siblingHead j).foldl execInstrBr v
    have run1 : Runs v v1 4 7 := (runs_pure _ _ v sc pcv rfl).cast rfl (by simp [siblingHead, cost, instructionCycles])
    obtain ⟨x7v, keep1⟩ := sibling_head_regs j hj v (i/5^k%5) _ (Nat.mod_lt _ (by decide)) v25 fv.x19 v30
    have pc1 : v1.pc = BitVec.ofNat 64 (4096+4*(536+54*k+6+12*j+4)) := by
      rw [pure_pc _ _ rfl, pcv, pc_offset]; rfl
    let slot := (i/5^k%5+(j+1))%5
    have slotLt : slot < 5 := Nat.mod_lt _ (by decide)
    have gLt : i/5^k/5+1 ≤ pentaCount (k+1) := by rw [g_eq]; exact count
    have gb : 368*(i/5^k/5)+368 ≤ 368*pentaCount (k+1) := by
      have := Nat.mul_le_mul_left 368 gLt; omega
    have al := group_aligned k (by omega)
    have tb := tb_val
    have pb := pb_val
    have src : 32*slot+(368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase)) =
        trapdoorBase+pentaGroupSlotOffset k (i/5^(k+1)) ((i/5^k%5+j+1)%5) := by
      unfold pentaGroupSlotOffset; rw [← g_eq, show i/5^k%5+j+1 = i/5^k%5+(j+1) by omega]; omega
    obtain ⟨run2, inv2, pc2, keep2⟩ := four_run init (wordSource positions) _ .x7 (by decide) (by decide) 0
      (16+128*k+32*j) (32*slot+(368*(i/5^k/5)+(pentaGroupBase k+40+trapdoorBase))) (proofBase+8*(94*o))
      (94*o+2+16*k+4*j) fc (by omega) (by omega) v1 pc1
      x7v ((keep1 .x21 (by decide)).trans fv.x21) (by omega)
      (by omega) (by omega) (by omega) (by rw [pb]; unfold MEMORY_BYTES; omega)
      (fun w hw => by rw [word_source_penta positions o k j w hk hj hw, ← src]; omega)
      ((invv.of_mem (pure_mem _ _ rfl)).cast_count rfl)
    have shape : w = (hybFour .x7 0 (16+128*k+32*j)).foldl execInstrBr v1 := by
      simp only [w, v1, List.foldl_append]
    rw [shape]
    refine ⟨(run1.trans run2).cast rfl rfl, inv2.cast_count (by ring), ?_, ?_, ?_, ?_, ?_⟩
    · exact pc2.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [keep2 _ (by decide), keep1 _ (by decide)]
    · rw [keep2 _ (by decide), keep1 _ (by decide)]
    · rw [keep2 _ (by decide), keep1 _ (by decide)]
    · intro r hr
      have ne := scratch_of_ne hr
      rw [keep2 _ ne.2.2.2.2.2, keep1 _ ne.2.1]
  -- chain the four siblings
  obtain ⟨ra, ia, pa, a25, a30, a6, ka⟩ := sib 0 (by decide) h0 (by simpa using pc0) r25 r30 f0
    (by simpa using inv.of_mem (pure_mem _ _ rfl))
  let ha := (siblingHead 0 ++ hybFour .x7 0 (16+128*k+32*0)).foldl execInstrBr h0
  obtain ⟨rb, ib, pb, b25, b30, b6, kb⟩ := sib 1 (by decide) ha pa (a25.trans r25) (a30.trans r30) (f0.keep ka) ia
  let hb := (siblingHead 1 ++ hybFour .x7 0 (16+128*k+32*1)).foldl execInstrBr ha
  obtain ⟨rc, ic, pc', c25, c30, c6, kc⟩ := sib 2 (by decide) hb pb (b25.trans (a25.trans r25))
    (b30.trans (a30.trans r30)) ((f0.keep ka).keep kb) ib
  let hc := (siblingHead 2 ++ hybFour .x7 0 (16+128*k+32*2)).foldl execInstrBr hb
  obtain ⟨rd, id, pd, _, _, d6, kd⟩ := sib 3 (by decide) hc pc' (c25.trans (b25.trans (a25.trans r25)))
    (c30.trans (b30.trans (a30.trans r30))) (((f0.keep ka).keep kb).keep kc) ic
  have shape : u = (siblingHead 3 ++ hybFour .x7 0 (16+128*k+32*3)).foldl execInstrBr hc := by
    simp only [u, hyb_penta_split, List.foldl_append, hc, hb, ha, h0]
  rw [shape]
  refine ⟨(run0.trans (ra.trans (rb.trans (rc.trans rd)))).cast rfl rfl, id.cast_count (by ring), ?_, ?_, ?_⟩
  · exact pd.trans (congrArg (BitVec.ofNat 64) (by omega))
  · rw [d6, c6, b6, a6, r6, g_eq]
  · exact (((f0.keep ka).keep kb).keep kc).keep kd

/-! ### The 4-ary level 3 -/

def quadHead : List Instr := hybQuad.take 6

theorem quad_head_eq : quadHead =
    [.LUI .x28 (hybPage 3), .ADD .x28 .x28 .x9, .ANDI .x25 .x6 3, .SRLI .x6 .x6 2,
     .MUL .x30 .x6 .x23, .ADD .x30 .x30 .x28] := rfl

theorem quad_head_regs (t : MachineState) (n : Nat) (hn : n < 2^40)
    (x6 : t.getReg .x6 = BitVec.ofNat 64 n) (x9 : t.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (x23 : t.getReg .x23 = BitVec.ofNat 64 368) :
    let u := quadHead.foldl execInstrBr t
    u.getReg .x25 = BitVec.ofNat 64 (n%4) ∧ u.getReg .x6 = BitVec.ofNat 64 (n/4) ∧
      u.getReg .x30 = BitVec.ofNat 64 (368*(n/4)+(pentaGroupBase 3+40+trapdoorBase)) ∧
      (∀ r, ¬ Scratch r → u.getReg r = t.getReg r) := by
  intro u
  have e : u = quadHead.foldl execInstrBr t := rfl
  rw [quad_head_eq] at e
  simp only [List.foldl_cons, List.foldl_nil] at e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e]; simp [execInstrBr, x6]; rw [and_three n (by omega)]
  · rw [e]; simp [execInstrBr, x6]; rw [shr2 n (by omega)]
  · rw [e]; simp [execInstrBr, x6, x9, x23]
    rw [shr2 n (by omega), mul368 (n/4) (by omega), hyb_lui 3 (by omega), add_nat]
  · intro r hr
    unfold Scratch at hr
    rw [e]
    simp only [execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    have a : r ≠ .x6 := fun h => hr (Or.inl h)
    have b : r ≠ .x25 := fun h => hr (Or.inr (Or.inr (Or.inl h)))
    have c : r ≠ .x28 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have d : r ≠ .x30 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    simp [Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

def quadSibHead (t : Nat) : List Instr :=
  [.ADDI .x7 .x25 (BitVec.ofNat 12 (t+1)), .ANDI .x7 .x7 3, .SLLI .x7 .x7 5, .ADD .x7 .x7 .x30]

theorem quad_sib_regs (j : Nat) (hj : j < 3) (t : MachineState) (d X : Nat) (hd : d < 4)
    (x25 : t.getReg .x25 = BitVec.ofNat 64 d) (x30 : t.getReg .x30 = BitVec.ofNat 64 X) :
    let u := (quadSibHead j).foldl execInstrBr t
    u.getReg .x7 = BitVec.ofNat 64 (32*((d+(j+1))%4)+X) ∧ (∀ r, r ≠ .x7 → u.getReg r = t.getReg r) := by
  intro u
  have e : u = (quadSibHead j).foldl execInstrBr t := rfl
  simp only [quadSibHead, List.foldl_cons, List.foldl_nil] at e
  refine ⟨?_, ?_⟩
  · rw [e]
    simp [execInstrBr, x25, x30, sext_small (j+1) (by omega), add_nat]
    rw [and_three (d+(j+1)) (by omega), shift_slot _ (by omega : (d+(j+1))%4 < 2^40), add_nat]
  · intro r hr
    rw [e]
    simp [execInstrBr, Ne.symm hr]

theorem hyb_quad_split : hybQuad = quadHead ++
    ((quadSibHead 0 ++ hybFour .x7 32 (400+32*0)) ++ ((quadSibHead 1 ++ hybFour .x7 32 (400+32*1)) ++
    (quadSibHead 2 ++ hybFour .x7 32 (400+32*2)))) := by
  simp [hybQuad, quadHead, hybQuadSib, quadSibHead, List.range_succ]

set_option maxRecDepth 100000 in
theorem hyb_quad_code : CodeAt 698 hybQuad := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem quad_level (init : MachineState) (positions : Positions) (o : Nat)
    (present : o < positions.card) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*698))
    (x6 : t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/125)) (fixed : Fixed positions o t)
    (inv : Inv init t (wordSource positions) (94*o+50)) :
    let u := hybQuad.foldl execInstrBr t
    Runs t u 42 45 ∧ Inv init u (wordSource positions) (94*o+62) ∧
      u.pc = BitVec.ofNat 64 (4096+4*740) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/500) ∧ Fixed positions o u := by
  intro u
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have codes := hyb_quad_code
  rw [hyb_quad_split] at codes
  have headCode : CodeAt 698 quadHead := fun j h => by
    have := codes j (by simp [quadHead, hybQuad] at h ⊢; omega)
    rw [this, List.getElem?_append_left h]
  have n_small : i/125 < 2^40 := by
    have := Nat.div_le_self i 25; omega
  let h0 := quadHead.foldl execInstrBr t
  have run0 : Runs t h0 6 9 := (runs_pure _ _ t headCode pc rfl).cast rfl (by
    simp [quadHead, hybQuad, cost, instructionCycles])
  obtain ⟨r25, r6, r30, keep0⟩ := quad_head_regs t (i/125) n_small x6 fixed.x9 fixed.x23
  have pc0 : h0.pc = BitVec.ofNat 64 (4096+4*(698+6)) := by
    rw [pure_pc _ _ rfl, pc, pc_offset]; rfl
  have f0 : Fixed positions o h0 := fixed.keep keep0
  have g_eq : i/125/4 = i/500 := by rw [Nat.div_div_eq_div_mul]
  have count := div_lt_count i hi 4
  rw [show placeValue 4 = 500 from rfl] at count
  have room := base_bound 3 (by omega)
  have bk : pentaGroupBase 3 ≤ 1728786392 := by decide
  have sib (j : Nat) (hj : j < 3) (v : MachineState)
      (pcv : v.pc = BitVec.ofNat 64 (4096+4*(698+6+12*j)))
      (v25 : v.getReg .x25 = BitVec.ofNat 64 (i/125%4))
      (v30 : v.getReg .x30 = BitVec.ofNat 64 (368*(i/125/4)+(pentaGroupBase 3+40+trapdoorBase)))
      (fv : Fixed positions o v) (invv : Inv init v (wordSource positions) (94*o+50+4*j)) :
      let w := (quadSibHead j ++ hybFour .x7 32 (400+32*j)).foldl execInstrBr v
      Runs v w 12 12 ∧ Inv init w (wordSource positions) (94*o+50+4*(j+1)) ∧
        w.pc = BitVec.ofNat 64 (4096+4*(698+6+12*(j+1))) ∧
        w.getReg .x25 = v.getReg .x25 ∧ w.getReg .x30 = v.getReg .x30 ∧ w.getReg .x6 = v.getReg .x6 ∧
        (∀ r, ¬ Scratch r → w.getReg r = v.getReg r) := by
    intro w
    have sc : CodeAt (698+6+12*j) (quadSibHead j) := fun q h => by
      have hq : q < 4 := by simpa [quadSibHead] using h
      have := codes (6+12*j+q) (by simp [quadHead, hybQuad, quadSibHead, hybFour]; omega)
      rw [show 698+(6+12*j+q) = 698+6+12*j+q by omega] at this
      rw [this]
      interval_cases j <;> interval_cases q <;> simp [quadHead, hybQuad, quadSibHead, hybFour, List.range_succ, hybQuadSib]
    have fc : CodeAt (698+6+12*j+4) (hybFour .x7 32 (400+32*j)) := fun q h => by
      have hq : q < 8 := by simpa [hybFour] using h
      have := codes (6+12*j+4+q) (by simp [quadHead, hybQuad, quadSibHead, hybFour]; omega)
      rw [show 698+(6+12*j+4+q) = 698+6+12*j+4+q by omega] at this
      rw [this]
      interval_cases j <;> interval_cases q <;> simp [quadHead, hybQuad, quadSibHead, hybFour, List.range_succ, hybQuadSib]
    let v1 := (quadSibHead j).foldl execInstrBr v
    have run1 : Runs v v1 4 4 := (runs_pure _ _ v sc pcv rfl).cast rfl (by simp [quadSibHead, cost, instructionCycles])
    obtain ⟨x7v, keep1⟩ := quad_sib_regs j hj v (i/125%4) _ (Nat.mod_lt _ (by decide)) v25 v30
    have pc1 : v1.pc = BitVec.ofNat 64 (4096+4*(698+6+12*j+4)) := by
      rw [pure_pc _ _ rfl, pcv, pc_offset]; rfl
    let slot := (i/125%4+(j+1))%4
    have slotLt : slot < 4 := Nat.mod_lt _ (by decide)
    have gLt : i/125/4+1 ≤ pentaCount 4 := by rw [g_eq]; exact count
    have gb : 368*(i/125/4)+368 ≤ 368*pentaCount 4 := by
      have := Nat.mul_le_mul_left 368 gLt; omega
    have al := group_aligned 3 (by omega)
    have tb := tb_val
    have pb := pb_val
    have src : 32*slot+(368*(i/125/4)+(pentaGroupBase 3+40+trapdoorBase))+32 =
        trapdoorBase+pentaGroupSlotOffset 3 (i/125/4) (1+(i/125%4+j+1)%4) := by
      unfold pentaGroupSlotOffset; rw [show i/125%4+j+1 = i/125%4+(j+1) by omega]; omega
    obtain ⟨run2, inv2, pc2, keep2⟩ := four_run init (wordSource positions) _ .x7 (by decide) (by decide) 32
      (400+32*j) (32*slot+(368*(i/125/4)+(pentaGroupBase 3+40+trapdoorBase))) (proofBase+8*(94*o))
      (94*o+50+4*j) fc (by omega) (by omega) v1 pc1
      x7v ((keep1 .x21 (by decide)).trans fv.x21) (by omega)
      (by omega) (by omega) (by omega) (by rw [pb]; unfold MEMORY_BYTES; omega)
      (fun w hw => by rw [word_source_quad positions o j w hj hw, ← src])
      ((invv.of_mem (pure_mem _ _ rfl)).cast_count rfl)
    have shape : w = (hybFour .x7 32 (400+32*j)).foldl execInstrBr v1 := by
      simp only [w, v1, List.foldl_append]
    rw [shape]
    refine ⟨(run1.trans run2).cast rfl rfl, inv2.cast_count (by ring), ?_, ?_, ?_, ?_, ?_⟩
    · exact pc2.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [keep2 _ (by decide), keep1 _ (by decide)]
    · rw [keep2 _ (by decide), keep1 _ (by decide)]
    · rw [keep2 _ (by decide), keep1 _ (by decide)]
    · intro r hr
      have ne := scratch_of_ne hr
      rw [keep2 _ ne.2.2.2.2.2, keep1 _ ne.2.1]
  obtain ⟨ra, ia, pa, a25, a30, a6, ka⟩ := sib 0 (by decide) h0 (by simpa using pc0) r25 r30 f0
    (by simpa using inv.of_mem (pure_mem _ _ rfl))
  let ha := (quadSibHead 0 ++ hybFour .x7 32 (400+32*0)).foldl execInstrBr h0
  obtain ⟨rb, ib, pb, b25, b30, b6, kb⟩ := sib 1 (by decide) ha pa (a25.trans r25) (a30.trans r30) (f0.keep ka) ia
  let hb := (quadSibHead 1 ++ hybFour .x7 32 (400+32*1)).foldl execInstrBr ha
  obtain ⟨rc, ic, pc', _, _, c6, kc⟩ := sib 2 (by decide) hb pb (b25.trans (a25.trans r25))
    (b30.trans (a30.trans r30)) ((f0.keep ka).keep kb) ib
  have shape : u = (quadSibHead 2 ++ hybFour .x7 32 (400+32*2)).foldl execInstrBr hb := by
    simp only [u, hyb_quad_split, List.foldl_append, hb, ha, h0]
  rw [shape]
  refine ⟨(run0.trans (ra.trans (rb.trans rc))).cast rfl rfl, ic.cast_count (by ring), ?_, ?_, ?_⟩
  · exact pc'.trans (congrArg (BitVec.ofNat 64) (by omega))
  · rw [c6, b6, a6, r6, g_eq]
  · exact ((f0.keep ka).keep kb).keep kc

theorem hyb_bin_split (m : Nat) : hybBin (m+4) = binHead (m+4) ++ hybFour .x30 128 (496+32*m) := by
  simp [hybBin, binHead]

set_option maxHeartbeats 4000000 in
theorem bin_level (init : MachineState) (positions : Positions) (o m : Nat) (hm : m < 8)
    (present : o < positions.card) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(740+16*m)))
    (x6 : t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/(500*2^m))) (fixed : Fixed positions o t)
    (inv : Inv init t (wordSource positions) (94*o+62+4*m)) :
    let u := (hybBin (m+4)).foldl execInstrBr t
    Runs t u 16 19 ∧ Inv init u (wordSource positions) (94*o+62+4*(m+1)) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(740+16*(m+1))) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/(500*2^(m+1))) ∧ Fixed positions o u := by
  intro u
  let i := ordinalIndex positions o
  have hi : i < LENGTH := ordinal_index_lt positions o
  have hL : LENGTH = 16777216 := rfl
  have codes := (hyb_codes.2.2.2.2.1) m hm
  rw [hyb_bin_split] at codes
  have headCode : CodeAt (740+16*m) (binHead (m+4)) := fun j h => by
    have := codes j (by simp [binHead, hybBin, hybFour] at h ⊢; omega)
    rw [this, List.getElem?_append_left h]
  have fc : CodeAt (740+16*m+8) (hybFour .x30 128 (496+32*m)) := fun q h => by
    have := codes (8+q) (by simp [binHead, hybBin, hybFour] at h ⊢; omega)
    rw [show 740+16*m+(8+q) = 740+16*m+8+q by omega] at this
    rw [this, List.getElem?_append_right (by simp [binHead, hybBin])]
    simp [binHead, hybBin]
  let n := i/(500*2^m)
  have n_small : n < 2^40 := by
    have := Nat.div_le_self i (500*2^m); omega
  let h0 := (binHead (m+4)).foldl execInstrBr t
  have run0 : Runs t h0 8 11 := (runs_pure _ _ t headCode pc rfl).cast rfl (by
    simp [binHead, hybBin, cost, instructionCycles])
  obtain ⟨r6, r30, keep0⟩ := bin_head_regs (m+4) (by omega) t n n_small x6 fixed.x9 fixed.x23
  have pc0 : h0.pc = BitVec.ofNat 64 (4096+4*(740+16*m+8)) := by
    rw [pure_pc _ _ rfl, pc, pc_offset]; rfl
  have f0 : Fixed positions o h0 := fixed.keep keep0
  have g_eq : n/2 = i/(500*2^(m+1)) := by
    show i/(500*2^m)/2 = _
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]
  have room := base_bound (m+4) (by omega)
  have bk : pentaGroupBase (m+4) ≤ 1728786392 := by interval_cases m <;> decide
  have bit : n%2 < 2 := Nat.mod_lt _ (by decide)
  have al := group_aligned (m+4) (by omega)
  have tb := tb_val
  have pb := pb_val
  have src : 368*(n/2)+(pentaGroupBase (m+4)+40+trapdoorBase)-32*(n%2)+128 =
      trapdoorBase+pentaGroupSlotOffset (4+m) (n/2) (4-n%2) := by
    unfold pentaGroupSlotOffset; rw [show 4+m = m+4 by omega]; omega
  have gb : 368*(n/2)+368 ≤ 368*pentaCount (m+4+1) := by
    have h : n/2+1 ≤ pentaCount (m+4+1) := by
      rw [g_eq]
      have := div_lt_count i hi (4+(m+1))
      rw [place_value_bin (m+1) (by omega), show 4+(m+1) = m+4+1 by omega] at this
      omega
    have := Nat.mul_le_mul_left 368 h; omega
  obtain ⟨run2, inv2, pc2, keep2⟩ := four_run init (wordSource positions) _ .x30 (by decide) (by decide) 128
    (496+32*m) _ (proofBase+8*(94*o)) (94*o+62+4*m) fc (by omega) (by omega) h0 pc0
    r30 f0.x21 (by omega) (by omega) (by omega) (by omega) (by rw [pb]; unfold MEMORY_BYTES; omega)
    (fun w hw => by rw [word_source_bin positions o m w hm hw, src])
    (inv.of_mem (pure_mem _ _ rfl))
  have shape : u = (hybFour .x30 128 (496+32*m)).foldl execInstrBr h0 := by
    simp only [u, hyb_bin_split, List.foldl_append, h0]
  rw [shape]
  refine ⟨(run0.trans run2).cast rfl rfl, inv2.cast_count (by ring), ?_, ?_, f0.keep (fun r hr => ?_)⟩
  · exact pc2.trans (congrArg (BitVec.ofNat 64) (by omega))
  · rw [keep2 _ (by decide), r6, g_eq]
  · exact keep2 _ (scratch_of_ne hr).2.2.2.2.2

/-! ### One record -/

theorem hyb_salt_eq : hybSalt = [.LD .x6 .x8 0, .SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] ++
    [.LD .x31 .x7 (BitVec.ofNat 12 0), .SD .x21 .x31 (BitVec.ofNat 12 0),
     .LD .x31 .x7 (BitVec.ofNat 12 8), .SD .x21 .x31 (BitVec.ofNat 12 8)] := rfl

set_option maxHeartbeats 4000000 in
theorem salt_part (init : MachineState) (positions : Positions) (o : Nat) (present : o < positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*529)) (fixed : Fixed positions o state)
    (inv : Inv init state (wordSource positions) (94*o))
    (loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 (ordinalIndex positions o)) :
    let u := hybSalt.foldl execInstrBr state
    Runs state u 7 7 ∧ Inv init u (wordSource positions) (94*o+2) ∧ u.pc = BitVec.ofNat 64 (4096+4*536) ∧
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
    (nonceBase+16*i) (proofBase+8*(94*o)) (94*o) (by decide) (by decide) (by simpa using cl 3 (by decide))
    (by simpa using cl 4 (by decide)) pc2 x7₂ ((keep2 _ (by decide)).trans ((keep1 _ (by decide)).trans fixed.x21))
    (by omega) (by omega) (by omega) (by omega) (by unfold MEMORY_BYTES; omega)
    (by rw [show 94*o = 94*o+0 from rfl, word_source_salt positions o 0 (by decide)])
    (inv.of_mem (by rw [pure_mem _ _ rfl]; exact mem_set_reg _ _ _))
  let s3 := execInstrBr (execInstrBr s2 (.LD .x31 .x7 (BitVec.ofNat 12 0))) (.SD .x21 .x31 (BitVec.ofNat 12 0))
  obtain ⟨run4, inv4, pc4, keep4⟩ := copy_step init s3 (wordSource positions) 534 .x7 (by decide) 8 8
    (nonceBase+16*i) (proofBase+8*(94*o)) (94*o+1) (by decide) (by decide) (by simpa using cl 5 (by decide))
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
    rw [keep4 _ ne.2.2.2.2.2, keep3 _ ne.2.2.2.2.2, keep2 _ ne.2.1, keep1 _ ne.1]

theorem pentas_run (init : MachineState) (positions : Positions) (o : Nat) (present : o < positions.card)
    (card : positions.card ≤ LENGTH) : ∀ n ≤ 3, ∀ t : MachineState,
    t.pc = BitVec.ofNat 64 (4096+4*536) → t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o) →
    Fixed positions o t → Inv init t (wordSource positions) (94*o+2) →
    let u := ((List.range n).flatMap hybPenta).foldl execInstrBr t
    Runs t u (54*n) (75*n) ∧ Inv init u (wordSource positions) (94*o+2+16*n) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(536+54*n)) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/5^n) ∧ Fixed positions o u := by
  intro n
  induction n with
  | zero =>
    intro _ t pc x6 f inv
    exact ⟨Runs.zero t, by simpa using inv, by simpa using pc, by simpa using x6, f⟩
  | succ n ih =>
    intro hn t pc x6 f inv
    obtain ⟨r, i', p', x6', f'⟩ := ih (by omega) t pc x6 f inv
    obtain ⟨r2, i2, p2, x62, f2⟩ := penta_level init positions o n (by omega) present card _ p' x6' f' i'
    have shape : ((List.range (n+1)).flatMap hybPenta).foldl execInstrBr t =
        (hybPenta n).foldl execInstrBr (((List.range n).flatMap hybPenta).foldl execInstrBr t) := by
      simp [List.range_succ, List.flatMap_append, List.foldl_append]
    intro u
    rw [show u = _ from shape]
    exact ⟨(r.trans r2).cast (by ring) (by ring), i2.cast_count (by ring), p2, x62, f2⟩

theorem bins_run (init : MachineState) (positions : Positions) (o : Nat) (present : o < positions.card)
    (card : positions.card ≤ LENGTH) : ∀ n ≤ 8, ∀ t : MachineState,
    t.pc = BitVec.ofNat 64 (4096+4*740) → t.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/500) →
    Fixed positions o t → Inv init t (wordSource positions) (94*o+62) →
    let u := ((List.range n).flatMap (fun m => hybBin (m+4))).foldl execInstrBr t
    Runs t u (16*n) (19*n) ∧ Inv init u (wordSource positions) (94*o+62+4*n) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(740+16*n)) ∧
      u.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o/(500*2^n)) ∧ Fixed positions o u := by
  intro n
  induction n with
  | zero =>
    intro _ t pc x6 f inv
    exact ⟨Runs.zero t, by simpa using inv, by simpa using pc, by simpa using x6, f⟩
  | succ n ih =>
    intro hn t pc x6 f inv
    obtain ⟨r, i', p', x6', f'⟩ := ih (by omega) t pc x6 f inv
    obtain ⟨r2, i2, p2, x62, f2⟩ := bin_level init positions o n (by omega) present card _ p' x6' f' i'
    have shape : ((List.range (n+1)).flatMap (fun m => hybBin (m+4))).foldl execInstrBr t =
        (hybBin (n+4)).foldl execInstrBr (((List.range n).flatMap (fun m => hybBin (m+4))).foldl execInstrBr t) := by
      simp [List.range_succ, List.flatMap_append, List.foldl_append]
    intro u
    rw [show u = _ from shape]
    exact ⟨(r.trans r2).cast (by ring) (by ring), i2.cast_count (by ring), p2, x62, f2⟩

structure RecState (init : MachineState) (positions : Positions) (o : Nat) (state : MachineState) : Prop where
  fixed : Fixed positions o state
  pc : state.pc = BitVec.ofNat 64 (4096+4*(if o = positions.card then 871 else 529))
  inv : Inv init state (wordSource positions) (94*o)

def latchPure : List Instr := [.ADDI .x21 .x21 752, .ADDI .x8 .x8 8]

theorem latch_regs (t : MachineState) :
    (latchPure.foldl execInstrBr t).getReg .x21 = t.getReg .x21 + signExtend12 (BitVec.ofNat 12 752) ∧
    (latchPure.foldl execInstrBr t).getReg .x8 = t.getReg .x8 + signExtend12 (BitVec.ofNat 12 8) ∧
    ∀ r, r ≠ .x21 → r ≠ .x8 → (latchPure.foldl execInstrBr t).getReg r = t.getReg r := by
  refine ⟨?_, ?_, ?_⟩
  · simp [latchPure, execInstrBr]
  · simp [latchPure, execInstrBr]
  · intro r a b; simp [latchPure, execInstrBr, Ne.symm a, Ne.symm b]

def recNext (state : MachineState) : MachineState :=
  execInstrBr ((hybBody ++ latchPure).foldl execInstrBr state) (.BNE .x8 .x18 6828)

set_option maxHeartbeats 4000000 in
theorem record_step (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (o : Nat) (present : o < positions.card) (state : MachineState)
    (at_ : RecState (s.initialState .opening (td, positions)) positions o state) :
    Runs state (recNext state) 342 432 ∧ RecState (s.initialState .opening (td, positions)) positions (o+1) (recNext state) := by
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
  obtain ⟨r2, i2, p2, x62, f2⟩ := pentas_run init positions o present card 3 le_rfl t1 p1 x61 f1 i1
  let t2 := ((List.range 3).flatMap hybPenta).foldl execInstrBr t1
  obtain ⟨rq, iq, pq, x6q, fq⟩ := quad_level init positions o present card t2 (by simpa using p2)
    (by simpa using x62) f2 (by simpa using i2)
  let tq := hybQuad.foldl execInstrBr t2
  obtain ⟨r3, i3, p3, _, f3⟩ := bins_run init positions o present card 8 le_rfl tq (by simpa using pq)
    (by simpa using x6q) fq (by simpa using iq)
  let t3 := ((List.range 8).flatMap (fun m => hybBin (m+4))).foldl execInstrBr tq
  have latchCode : CodeAt 868 latchPure := hyb_codes.2.2.2.2.2.1
  let t4 := latchPure.foldl execInstrBr t3
  have r4 : Runs t3 t4 2 2 := (runs_pure _ _ t3 latchCode (by simpa using p3) rfl).cast rfl rfl
  have p4 : t4.pc = BitVec.ofNat 64 (4096+4*870) := by rw [pure_pc _ _ rfl, p3, pc_offset]; rfl
  obtain ⟨l21, l8, keep4⟩ := latch_regs t3
  have x21₄ : t4.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(94*(o+1))) := by
    rw [l21, f3.x21, sext_small 752 (by decide), add_nat]
    all_goals (apply congrArg (BitVec.ofNat 64); omega)
  have x8₄ : t4.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*(o+1)) := by
    rw [l8, f3.x8, sext_small 8 (by decide), add_nat]
    all_goals (apply congrArg (BitVec.ofNat 64); omega)
  have mem4 : t4.mem = t3.mem := pure_mem _ _ rfl
  have shape4 : (hybBody ++ latchPure).foldl execInstrBr state = t4 := by
    simp only [t4, t3, tq, t2, t1, hybBody, List.foldl_append]
  have branch := hyb_codes.2.2.2.2.2.2.1
  have r5 : Runs t4 (recNext state) 1 1 := by
    intro fuel coins
    rw [show recNext state = execInstrBr t4 (.BNE .x8 .x18 6828) by rw [recNext, shape4],
      Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ 870 _ branch p4) rfl]
    rfl
  have shapeN : recNext state = t4.setPC (if t4.getReg .x8 != t4.getReg .x18 then t4.pc + signExtend13 6828 else t4.pc + 4) := by
    rw [recNext, shape4, bne_shape]
  refine ⟨((r1.trans (r2.trans (rq.trans (r3.trans r4)))).trans r5).cast rfl rfl, ?_, ?_, ?_⟩
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
    exact (i3.cast_count (by ring) : Inv init t3 (wordSource positions) (94*(o+1))).of_mem (by rw [set_pc_mem, mem4])

/-- `n` records. -/
def recsRun : Nat → MachineState → MachineState
  | 0, state => state
  | n+1, state => recsRun n (recNext state)

theorem records_run (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : ∀ n o (state : MachineState), o+n = positions.card →
    RecState (s.initialState .opening (td, positions)) positions o state →
    Runs state (recsRun n state) (342*n) (432*n) ∧
      RecState (s.initialState .opening (td, positions)) positions positions.card (recsRun n state) := by
  intro n
  induction n with
  | zero => intro o state h at_; simp at h; subst h; exact ⟨Runs.zero state, at_⟩
  | succ n ih =>
    intro o state h at_
    obtain ⟨r, a⟩ := record_step s layout td positions o (by omega) state at_
    obtain ⟨r', a'⟩ := ih (o+1) _ (by omega) a
    exact ⟨(r.trans r').cast (by ring) (by ring), a'⟩

/-! ### The level-11 table and the exit -/

/-- Initial address of table doubleword `x < 528`: doubleword `x % 4` of slot `x % 20 / 4` of
level-11 group `x / 20`. -/
def tableSource (x : Nat) : Nat := trapdoorBase+pentaGroupSlotOffset CAP_LEVEL (x/20) (x%20/4)+8*(x%4)

/-- Source of output doubleword `u`: the records, then the table. -/
def proofSource (positions : Positions) (u : Nat) : Nat :=
  if u < 94*positions.card then wordSource positions u else tableSource (u-94*positions.card)

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

theorem hyb_table_eq : hybTable = [.LUI .x30 (hybPage 12), .ADD .x30 .x30 .x9] ++ (List.replicate 26 hybGroup).flatten ++ hybHalf := rfl

theorem hyb_half_eq : hybHalf = hybSlots 2 ++ [.ADDI .x30 .x30 368, .ADDI .x21 .x21 64] := rfl

theorem table_bound : pentaGroupBase 12+40+368*27 ≤ 1728786760 := by decide

/-- Address of slot 0 of level-11 group 0. -/
def hybTableStart : Nat := pentaGroupBase 12+40+trapdoorBase

theorem hyb_table_start_value : hybTableStart = 5850816544 := rfl

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
    ∀ n ≤ 26, ∀ t : MachineState,
    t.pc = BitVec.ofNat 64 (4096+4*873) →
    t.getReg .x30 = BitVec.ofNat 64 hybTableStart →
    t.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(94*positions.card)) →
    Inv init t (proofSource positions) (94*positions.card) →
    let u := (List.replicate n hybGroup).flatten.foldl execInstrBr t
    Runs t u (42*n) (42*n) ∧ Inv init u (proofSource positions) (94*positions.card+20*n) ∧
      u.pc = BitVec.ofNat 64 (4096+4*(873+42*n)) ∧
      u.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(94*positions.card+20*n)) ∧
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
    have c1 : CodeAt (873+42*n) (hybSlots 5) := fun q h => by
      have := gcode q (by rw [List.length_append]; omega)
      rw [this, List.getElem?_append_left h]
    have c3 : CodeAt (873+42*n+40) [.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] := fun q h => by
      have hq : q < 2 := by simpa using h
      have := gcode (40+q) (by rw [List.length_append, hyb_slots_length]; simp; omega)
      rw [show 873+42*n+(40+q) = 873+42*n+40+q by omega] at this
      rw [this, List.getElem?_append_right (by rw [hyb_slots_length]; omega), hyb_slots_length,
        show 40+q-8*5 = q by omega]
    obtain ⟨r1, i1, p1, k1⟩ := slots_run init (proofSource positions) (873+42*n) 5 le_rfl
      (hybTableStart+368*n) (proofBase+8*(94*positions.card+20*n)) (94*positions.card+20*n) v
      c1 p' s' d' rfl (by rw [ts]; omega) (by rw [ts, tb]; omega) (by rw [ts, pb]; omega)
      (by rw [pb]; unfold MEMORY_BYTES; omega)
      (fun w hw => by
        unfold proofSource
        rw [if_neg (by omega), table_source_eq]
        rw [show 94*positions.card+20*n+w-94*positions.card = 20*n+w by omega,
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
/-- The last table group: nodes 130-131 (slots 0-1 of group 26). -/
theorem half_run (init : MachineState) (positions : Positions) (card : positions.card ≤ LENGTH) (t : MachineState)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*1965))
    (x30 : t.getReg .x30 = BitVec.ofNat 64 (hybTableStart+368*26))
    (x21 : t.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(94*positions.card+20*26)))
    (inv : Inv init t (proofSource positions) (94*positions.card+20*26)) :
    let u := hybHalf.foldl execInstrBr t
    Runs t u 18 18 ∧ Inv init u (proofSource positions) (94*positions.card+528) ∧
      u.pc = BitVec.ofNat 64 (4096+4*1983) ∧
      u.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(94*positions.card+528)) ∧
      (∀ r, r ≠ .x21 → r ≠ .x30 → r ≠ .x31 → u.getReg r = t.getReg r) := by
  have hL : LENGTH = 16777216 := rfl
  have tb := tb_val
  have pb := pb_val
  have ts := hyb_table_start_value
  have hcode := hyb_codes.2.2.2.2.2.2.2.2.2.1
  rw [hyb_half_eq] at hcode
  have c1 : CodeAt 1965 (hybSlots 2) := fun q h => by
    have := hcode q (by rw [List.length_append]; omega)
    rw [this, List.getElem?_append_left h]
  have c3 : CodeAt (1965+16) [.ADDI .x30 .x30 368, .ADDI .x21 .x21 64] := fun q h => by
    have hq : q < 2 := by simpa using h
    have := hcode (16+q) (by rw [List.length_append, hyb_slots_length]; simp; omega)
    rw [show 1965+(16+q) = 1965+16+q by omega] at this
    rw [this, List.getElem?_append_right (by rw [hyb_slots_length]; omega), hyb_slots_length,
      show 16+q-8*2 = q by omega]
  obtain ⟨r1, i1, p1, k1⟩ := slots_run init (proofSource positions) 1965 2 (by decide)
    (hybTableStart+368*26) (proofBase+8*(94*positions.card+20*26)) (94*positions.card+20*26) t
    c1 pc x30 x21 rfl (by rw [ts]) (by rw [ts, tb]; norm_num) (by rw [ts, pb]; norm_num)
    (by rw [pb]; unfold MEMORY_BYTES; omega)
    (fun w hw => by
      unfold proofSource
      rw [if_neg (by omega), table_source_eq]
      rw [show 94*positions.card+20*26+w-94*positions.card = 20*26+w by omega,
        show (20*26+w)/20 = 26 by omega, show (20*26+w)%20 = w by omega]) inv
  let v1 := (hybSlots 2).foldl execInstrBr t
  let v3 := ([.ADDI .x30 .x30 368, .ADDI .x21 .x21 64] : List Instr).foldl execInstrBr v1
  have r3 : Runs v1 v3 2 2 := (runs_pure _ _ v1 c3 (p1.trans (congrArg (BitVec.ofNat 64) (by omega))) rfl).cast rfl rfl
  have shape : hybHalf.foldl execInstrBr t = v3 := by
    simp only [v3, v1, hyb_half_eq, List.foldl_append]
  have a21 : v3.getReg .x21 = v1.getReg .x21 + signExtend12 (BitVec.ofNat 12 64) := by
    simp [v3, execInstrBr]
  have a_ : ∀ q, q ≠ .x21 → q ≠ .x30 → v3.getReg q = v1.getReg q := by
    intro q a b; simp [v3, execInstrBr, Ne.symm a, Ne.symm b]
  intro u
  rw [show u = v3 from shape]
  refine ⟨(r1.trans r3).cast (by ring) (by ring), ?_, ?_, ?_, ?_⟩
  · exact (i1.of_mem (pure_mem _ _ rfl)).cast_count (by ring)
  · rw [pure_pc _ _ rfl, p1, pc_offset]; rfl
  · rw [a21, k1 .x21 (by decide), x21, sext_small 64 (by decide), add_nat]
    all_goals (apply congrArg (BitVec.ofNat 64); omega)
  · intro q a b c
    rw [a_ q a b, k1 q c]

end TwoPermutationPrototype.QuadOpening
