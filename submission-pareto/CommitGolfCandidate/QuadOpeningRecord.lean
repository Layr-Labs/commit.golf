import CommitGolfCandidate.QuadOpeningLevel
import CommitGolfCandidate.Counting
import CommitGolfCandidate.Machine

/-! The full-group record writer (words 11-105). Setup (words 11-34), then for each record: the
index and the salt (words 35-41), seven forward permutation calls writing `P(group k)` into a
scratch area (words 42-76), seven inverse calls writing `P⁻¹(P(group k)) = group k` into the record
(words 77-103), and the loop latch (words 104-105). The latch falls through to the table jump at
word 106 after the last record. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling OracleComp
open QOpening (OpeningLayout trapdoorBase proofBase nonceBase indicesBase)
open TwoPermutationPrototype.RV64

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

/-- Word index of the record scratch area for `k` positions. -/
def recScratch (k : Nat) : Nat := proofBase/8 + 142*k + 4096

/-- Word index of the level-`j` group holding position `x`. -/
def grpWord (j x : Nat) : Nat := (trapdoorBase + pentaGroupBase j + 40)/8 + 46*(x/5^(j+1))

/-- Registers at a record boundary: about to start record `o` (or at the exit when `o = card`). -/
structure RecRegs (positions : Positions) (o : Nat) (state : MachineState) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*(if o = positions.card then 106 else 35))
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*o)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  stop : state.getReg .x18 = BitVec.ofNat 64 (indicesBase+8*positions.card)
  five : state.getReg .x19 = BitVec.ofNat 64 5
  begin : state.getReg .x15 = BitVec.ofNat 64 proofBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(142*o))
  salts : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  width : state.getReg .x23 = BitVec.ofNat 64 368
  sel : state.getReg .x5 = 0
  size : state.getReg .x11 = 200
  prim : state.getReg .x13 = 1
  scratch : state.getReg .x12 = wordAddress (recScratch positions.card)
  bases : ∀ j < 7, state.getReg (recBase j) = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase j+40)

/-- The pass hands over at word 11. -/
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

set_option maxRecDepth 100000 in
theorem rec_codes :
    CodeAt 11 recSetup ∧ CodeAt 21 recBases ∧ CodeAt 35 [.LD .x6 .x8 0] ∧
    CodeAt 36 [.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] ∧ CodeAt 38 (pairCode 2) ∧
    (∀ k < 7, CodeAt (42+5*k) (recFwd k)) ∧ CodeAt 77 recMid ∧ (∀ g < 7, CodeAt (80+3*g) recInv) ∧
    CodeAt 101 recBack ∧ CodeAt 104 [.ADDI .x8 .x8 8] ∧ program[105]? = some (.BNE .x8 .x18 7912) := by
  decide +kernel

/-! ### Setup (words 11-34) -/

def setupRun (state : MachineState) : MachineState := (recSetup ++ recBases).foldl execInstrBr state

theorem rec_base_ne (j : Nat) : recBase j ≠ .x0 ∧ recBase j ≠ .x5 ∧ recBase j ≠ .x6 ∧ recBase j ≠ .x7 ∧
    recBase j ≠ .x8 ∧ recBase j ≠ .x9 ∧ recBase j ≠ .x10 ∧ recBase j ≠ .x11 ∧ recBase j ≠ .x12 ∧
    recBase j ≠ .x13 ∧ recBase j ≠ .x15 ∧ recBase j ≠ .x18 ∧ recBase j ≠ .x19 ∧ recBase j ≠ .x21 ∧
    recBase j ≠ .x22 ∧ recBase j ≠ .x23 ∧ recBase j ≠ .x31 := by
  unfold recBase; split <;> decide

theorem rec_bases_code : recBases =
    [.LUI .x2 (BitVec.ofNat 20 (groupPage 0)), .ADD .x2 .x2 .x9,
     .LUI .x3 (BitVec.ofNat 20 (groupPage 1)), .ADD .x3 .x3 .x9,
     .LUI .x4 (BitVec.ofNat 20 (groupPage 2)), .ADD .x4 .x4 .x9,
     .LUI .x14 (BitVec.ofNat 20 (groupPage 3)), .ADD .x14 .x14 .x9,
     .LUI .x16 (BitVec.ofNat 20 (groupPage 4)), .ADD .x16 .x16 .x9,
     .LUI .x17 (BitVec.ofNat 20 (groupPage 5)), .ADD .x17 .x17 .x9,
     .LUI .x20 (BitVec.ofNat 20 (groupPage 6)), .ADD .x20 .x20 .x9] := rfl

theorem base_value (T G : Nat) (lui : Word) (hlui : lui = BitVec.ofNat 64 G) :
    lui + BitVec.ofNat 64 T = BitVec.ofNat 64 (T+G) := by
  rw [hlui, ← BitVec.ofNat_add]
  congr 1
  omega

set_option maxRecDepth 100000 in
theorem setup_post (state : MachineState) (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (c : Nat) (small : c ≤ 16777216) (count : state.getReg .x18 = BitVec.ofNat 64 c)
    (index : state.getReg .x8 = BitVec.ofNat 64 indicesBase)
    (begin : state.getReg .x15 = BitVec.ofNat 64 proofBase) :
    (∀ j < 7, (setupRun state).getReg (recBase j) = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase j+40)) ∧
    (setupRun state).getReg .x18 = BitVec.ofNat 64 (indicesBase+8*c) ∧
    (setupRun state).getReg .x12 = wordAddress (recScratch c) ∧
    (setupRun state).getReg .x5 = 0 ∧ (setupRun state).getReg .x11 = 200 ∧ (setupRun state).getReg .x13 = 1 ∧
    ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x14 → r ≠ .x16 → r ≠ .x17 → r ≠ .x20 →
      r ≠ .x5 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x18 →
      (setupRun state).getReg r = state.getReg r := by
  have pb : proofBase = 10804535392 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have page := lui_page j (by omega)
    rw [Nat.add_assoc, ← base_value _ _ _ page]
    interval_cases j <;> simp [setupRun, recSetup, rec_bases_code, recBase, execInstrBr, heap]
  · simp [setupRun, recSetup, rec_bases_code, execInstrBr, count, index]
    rw [shift_count c (by omega), ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · simp [setupRun, recSetup, rec_bases_code, execInstrBr, count, begin]
    rw [show signExtend12 1136#12 = BitVec.ofNat 64 1136 from by decide,
      show (32768#64 : Word) = BitVec.ofNat 64 32768 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
    unfold wordAddress recScratch
    apply congrArg (BitVec.ofNat 64)
    rw [pb]
    omega
  · simp [setupRun, recSetup, rec_bases_code, execInstrBr]; rfl
  · simp [setupRun, recSetup, rec_bases_code, execInstrBr]; rfl
  · simp [setupRun, recSetup, rec_bases_code, execInstrBr]; rfl
  · intro r a b c d e f g h l m n p q
    simp [setupRun, recSetup, rec_bases_code, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d,
      Ne.symm e, Ne.symm f, Ne.symm g, Ne.symm h, Ne.symm l, Ne.symm m, Ne.symm n, Ne.symm p, Ne.symm q]

set_option maxRecDepth 100000 in
theorem setup_step (init state : MachineState) (positions : Positions) (nonempty : positions.card ≠ 0)
    (at_ : EntryAt init state positions) :
    Runs state (setupRun state) 24 27 ∧ RecRegs positions 0 (setupRun state) ∧
      Inv init (setupRun state) (wordSource positions) (142*0) := by
  have pure : (recSetup ++ recBases).all pureOp = true := by decide
  obtain ⟨c₁, c₂, _⟩ := rec_codes
  have code : CodeAt 11 (recSetup ++ recBases) := by
    intro i hi
    by_cases lo : i < 10
    · rw [List.getElem?_append_left (by simpa [recSetup] using lo)]; exact c₁ i (by simpa [recSetup] using lo)
    · rw [List.getElem?_append_right (by simp [recSetup]; omega)]
      have := c₂ (i-10) (by simp [recSetup, recBases] at hi ⊢; omega)
      rw [show 21 + (i-10) = 11 + i by omega] at this
      simpa [recSetup] using this
  have run := runs_pure (recSetup ++ recBases) 11 state code at_.pc pure
  have card : positions.card ≤ LENGTH := card_le positions
  have hL : LENGTH = 16777216 := rfl
  obtain ⟨bases, stop, scr, x5, x11, x13, frame⟩ := setup_post state at_.heap positions.card (by omega)
    (by rw [at_.left]; simp) (by rw [at_.index]; simp) at_.begin
  have keep (r : Reg) (h : r ∈ [Reg.x8, .x9, .x15, .x19, .x21, .x22, .x23]) : (setupRun state).getReg r = state.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨run.cast rfl (by decide), ⟨?_, ?_, ?_, stop, ?_, ?_, ?_, ?_, ?_, x5, x11, x13, scr, bases⟩, ?_⟩
  · rw [show setupRun state = (recSetup ++ recBases).foldl execInstrBr state from rfl, pure_pc _ _ pure, at_.pc,
      if_neg (Ne.symm nonempty)]
    rfl
  · rw [keep .x8 (by simp), at_.index]
  · rw [keep .x9 (by simp), at_.heap]
  · rw [keep .x19 (by simp), at_.five]
  · rw [keep .x15 (by simp), at_.begin]
  · rw [keep .x21 (by simp), at_.dest]
  · rw [keep .x22 (by simp), at_.salts]
  · rw [keep .x23 (by simp), at_.width]
  · exact at_.inv.of_mem (pure_mem _ _ pure)

/-! ### Syscall helpers -/

theorem write_pc {bits : Nat} (st : MachineState) (d : Word) (v : BitVec bits) :
    (writeBits st d v).pc = st.pc + 4 := rfl

theorem oracle_input_inverse (state : MachineState) (src dst : Nat)
    (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 2) :
    oracleInput state = some (.inr (.inr (packBuffer (window (memoryView state) src)))) := by
  have srcValue := word_address_value (word := src) (by omega)
  have dstValue := word_address_value (word := dst) (by omega)
  have fitsSrc : 8 * src + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have fitsDst : 8 * dst + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have kind : (state.getReg .x13).toNat = 2 := by rw [primitive]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [input, output, size, srcValue, dstValue, rangeValid,
    fitsSrc, fitsDst, PERMUTATION_WIDTH, read_permutation_window]

theorem execute_inverse_call (image : Image) (fuel : Nat) (state : MachineState) (allowCoins : Bool)
    (src dst : Nat) (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (selector : state.getReg .x5 = 0) (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 2)
    (fetched : fetch image state = some (.base .ECALL)) :
    execute image (fuel + 1) state allowCoins = (do
      let answer ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView state) src)))))
      let result ← execute image fuel (writeBits state (wordAddress dst) answer) allowCoins
      pure (result.charge 8 1)) := by
  have ready := oracle_input_inverse state src dst srcBound dstBound input output size primitive
  simp only [execute, fetched, selector, ↓reduceIte, ready, output, writeOracleAnswer, oracleCycles, PERMUTATION_CYCLES]

theorem charge_merge (r : Execution) (a b c d : Nat) :
    (r.charge a b).charge c d = r.charge (c+a) (d+b) := by
  cases r; simp [Execution.charge]; omega

theorem view_of_mem {a b : MachineState} (same : a.mem = b.mem) : memoryView a = memoryView b := by
  funext w
  simp only [memoryView, MachineState.getMem, same]

theorem reply_pack' (v : BitVec 1600) : packBuffer (replyWords v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  let j : Fin 25 := ⟨k / 64, by omega⟩
  have h := congrArg (fun w : BitVec 64 => w.getLsbD (k % 64)) (packed_word (replyWords v) j)
  have b : k % 64 < 64 := by omega
  unfold replyWords at h
  dsimp only [j] at h
  change ((packBuffer _).extractLsb' (64 * (k / 64)) 64).getLsbD (k % 64) =
    (v.extractLsb' (64 * (k / 64)) 64).getLsbD (k % 64) at h
  unfold replyWords
  simpa only [BitVec.getLsbD_extractLsb', b, decide_true, Bool.true_and, Nat.div_add_mod] using h

theorem view_get (s : MachineState) (w : Nat) : s.getMem (BitVec.ofNat 64 (8*w)) = memoryView s w := rfl

/-! ### One record -/

/-- Registers and the input frame at a record boundary. -/
structure RecAt (init : MachineState) (positions : Positions) (o : Nat) (state : MachineState) : Prop where
  regs : RecRegs positions o state
  frame : ∀ a, trapdoorBase ≤ a → a < proofBase → a % 8 = 0 →
    state.getMem (BitVec.ofNat 64 a) = init.getMem (BitVec.ofNat 64 a)

def recPre (s : MachineState) : MachineState :=
  (pairCode 2).foldl execInstrBr (([.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] : List Instr).foldl execInstrBr
    (execInstrBr s (.LD .x6 .x8 0)))

def fpreCode (k : Nat) : List Instr := [.DIVU .x6 .x6 .x19, .MUL .x10 .x6 .x23, .ADD .x10 .x10 (recBase k)]
def fpre (k : Nat) (s : MachineState) : MachineState := (fpreCode k).foldl execInstrBr s
def fadv (s : MachineState) : MachineState := ([.ADDI .x12 .x12 200] : List Instr).foldl execInstrBr s
def radv (s : MachineState) : MachineState := ([.ADDI .x10 .x10 200, .ADDI .x12 .x12 160] : List Instr).foldl execInstrBr s
def recMidRun (s : MachineState) : MachineState := recMid.foldl execInstrBr s
def recFin (s : MachineState) : MachineState :=
  execInstrBr (([.ADDI .x8 .x8 8] : List Instr).foldl execInstrBr (recBack.foldl execInstrBr s)) (.BNE .x8 .x18 7912)

def recFwdTrace (x TW : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n+1, k, s => do
      let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (fpre k s)) (grpWord k x))))))
      recFwdTrace x TW n (k+1) (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y))

def recInvTrace (A D : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n+1, g, s => do
      let y ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView s) (A+25*g))))))
      recInvTrace A D n (g+1) (radv (writeBits s (wordAddress (D+20*g)) y))

def recordTrace (x TW D : Nat) (s : MachineState) : OracleComp World MachineState := do
  let t ← recFwdTrace x TW 7 0 (recPre s)
  let u ← recInvTrace TW D 7 0 (recMidRun t)
  pure (recFin u)

/-- Registers at forward block `k` of a record. -/
structure RFwd (x TW k : Nat) (s : MachineState) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*(42+5*k))
  x6 : s.getReg .x6 = BitVec.ofNat 64 (x/5^k)
  x12 : s.getReg .x12 = wordAddress (TW+25*k)
  sel : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  prim : s.getReg .x13 = 1
  five : s.getReg .x19 = BitVec.ofNat 64 5
  width : s.getReg .x23 = BitVec.ofNat 64 368
  bases : ∀ j < 7, s.getReg (recBase j) = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase j+40)

/-- Registers at inverse block `g` of a record. -/
structure RInv (A D g : Nat) (s : MachineState) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*(80+3*g))
  src : s.getReg .x10 = wordAddress (A+25*g)
  dst : s.getReg .x12 = wordAddress (D+20*g)
  sel : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  prim : s.getReg .x13 = 2

def fwdScratch : List Reg := [.x6, .x10, .x12]

theorem grp_word_address (j x : Nat) (hj : j < 7) :
    8*grpWord j x = trapdoorBase+pentaGroupBase j+40+368*(x/5^(j+1)) := by
  have a := group_aligned j (by omega)
  have tb : trapdoorBase = 4294971424 := rfl
  unfold grpWord; omega

theorem grp_word_bound (j x : Nat) (hj : j < 7) (hx : x < LENGTH) : 8*(grpWord j x + 25) ≤ proofBase := by
  have room := group_room j (by omega)
  have count := div_lt_count x hx (j+1)
  have tb : trapdoorBase = 4294971424 := rfl
  have pb : proofBase = 10804535392 := rfl
  rw [show 8*(grpWord j x + 25) = 8*grpWord j x + 200 by ring, grp_word_address j x hj]
  have : 368 * (x / 5 ^ (j + 1)) + 368 ≤ 368 * pentaCount (j+1) := by
    have := Nat.mul_le_mul_left 368 (show x / 5 ^ (j + 1) + 1 ≤ pentaCount (j+1) by omega)
    omega
  omega

set_option maxRecDepth 100000 in
theorem fpre_regs (s : MachineState) (x k : Nat) (hk : k < 7) (hx : x < LENGTH)
    (x6 : s.getReg .x6 = BitVec.ofNat 64 (x/5^k)) (five : s.getReg .x19 = BitVec.ofNat 64 5)
    (width : s.getReg .x23 = BitVec.ofNat 64 368)
    (base : s.getReg (recBase k) = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40)) :
    (fpre k s).getReg .x6 = BitVec.ofNat 64 (x/5^(k+1)) ∧
    (fpre k s).getReg .x10 = wordAddress (grpWord k x) ∧
    (fpre k s).mem = s.mem ∧
    ∀ r, r ≠ .x6 → r ≠ .x10 → (fpre k s).getReg r = s.getReg r := by
  obtain ⟨_, _, n6, _, _, _, n10, _, _, _, _, _, _, _, _, n23, _⟩ := rec_base_ne k
  have hL : LENGTH = 16777216 := rfl
  have q : x/5^k < 2^40 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have quot : rv64_divu (BitVec.ofNat 64 (x/5^k)) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (x/5^(k+1)) := by
    rw [divu_five _ q, pow_succ, Nat.div_div_eq_div_mul]
  have q' : x/5^(k+1) < 2^40 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  refine ⟨?_, ?_, pure_mem _ _ rfl, ?_⟩
  · simp [fpre, fpreCode, execInstrBr, x6, five, quot, Ne.symm n6]
  · simp [fpre, fpreCode, execInstrBr, x6, five, quot, width, base, Ne.symm n6, Ne.symm n10, n6, n10]
    rw [mul_width _ q', ← BitVec.ofNat_add]
    unfold wordAddress
    rw [grp_word_address k x hk]
    congr 1; omega
  · intro r a b
    simp [fpre, fpreCode, execInstrBr, Ne.symm a, Ne.symm b]

theorem fpre_runs (s : MachineState) (k : Nat) (hk : k < 7) (pc : s.pc = BitVec.ofNat 64 (4096+4*(42+5*k))) :
    Runs s (fpre k s) 3 9 ∧ (fpre k s).pc = BitVec.ofNat 64 (4096+4*(42+5*k+3)) := by
  obtain ⟨_, _, _, _, _, fwd, _⟩ := rec_codes
  have code : CodeAt (42+5*k) (fpreCode k) := by
    intro i hi
    have := fwd k hk i (by simp [recFwd]; simp [fpreCode] at hi; omega)
    rw [this]
    have hi' : i < 3 := by simpa [fpreCode] using hi
    interval_cases i <;> rfl
  have pure : (fpreCode k).all pureOp = true := by simp [fpreCode, pureOp]
  refine ⟨(runs_pure _ _ s code pc pure).cast rfl (by simp [fpreCode, cost, instructionCycles]), ?_⟩
  rw [fpre, pure_pc _ _ pure, pc, pc_offset]; rfl

theorem fwd_step_rec (x TW k fuel : Nat) (s : MachineState) (hk : k < 7) (hx : x < LENGTH)
    (at_ : RFwd x TW k s) (sb : grpWord k x + 25 ≤ 2^33) (tb : TW+25*k+25 ≤ 2^33) :
    execute openingImage (5+fuel) s true = (do
      let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (fpre k s)) (grpWord k x))))))
      let r ← execute openingImage fuel (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)) true
      pure (r.charge 18 1)) := by
  obtain ⟨_, _, _, _, _, fwd, _⟩ := rec_codes
  obtain ⟨run₁, pc₁⟩ := fpre_runs s k hk at_.pc
  obtain ⟨x6', x10', _, keep'⟩ := fpre_regs s x k hk hx at_.x6 at_.five at_.width (at_.bases k hk)
  have fetched : fetch openingImage (fpre k s) = some (.base .ECALL) :=
    fetch_program _ (42+5*k+3) .ECALL (by have := fwd k hk 3 (by simp [recFwd]); simpa [recFwd] using this) pc₁
  rw [show 5+fuel = 3+((1+fuel)+1) by omega, run₁ _ true,
    execute_permutation_call openingImage (1+fuel) (fpre k s) true (grpWord k x) (TW+25*k) sb tb x10'
      ((keep' .x12 (by decide) (by decide)).trans at_.x12) ((keep' .x5 (by decide) (by decide)).trans at_.sel)
      ((keep' .x11 (by decide) (by decide)).trans at_.size) ((keep' .x13 (by decide) (by decide)).trans at_.prim) fetched]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro y
  have pcw : (writeBits (fpre k s) (wordAddress (TW+25*k)) y).pc = BitVec.ofNat 64 (4096+4*(42+5*k+4)) := by
    rw [write_pc, pc_next _ _ pc₁]
  have code : CodeAt (42+5*k+4) [.ADDI .x12 .x12 200] := by
    intro i hi
    have i0 : i = 0 := by simpa using hi
    subst i0
    have := fwd k hk 4 (by simp [recFwd])
    simpa [recFwd] using this
  have run₂ : Runs _ (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)) 1 1 :=
    (runs_pure _ _ _ code pcw rfl).cast rfl rfl
  rw [run₂ fuel true]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro r
  rw [charge_merge, charge_merge]

theorem fwd_next_rec {bits : Nat} (x TW k : Nat) (hk : k < 7) (hx : x < LENGTH) (s : MachineState)
    (at_ : RFwd x TW k s) (y : BitVec bits) :
    RFwd x TW (k+1) (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)) ∧
      ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)).getReg r = s.getReg r := by
  obtain ⟨run₁, pc₁⟩ := fpre_runs s k hk at_.pc
  obtain ⟨x6', _, _, keep'⟩ := fpre_regs s x k hk hx at_.x6 at_.five at_.width (at_.bases k hk)
  have w (r : Reg) := writeBits_register (fpre k s) (wordAddress (TW+25*k)) y r
  have adv12 : (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)).getReg .x12 =
      (writeBits (fpre k s) (wordAddress (TW+25*k)) y).getReg .x12 + signExtend12 200 := by
    simp [fadv, execInstrBr]
  have advKeep (r : Reg) (a : r ≠ .x12) : (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)).getReg r =
      (writeBits (fpre k s) (wordAddress (TW+25*k)) y).getReg r := by simp [fadv, execInstrBr, Ne.symm a]
  have all (r : Reg) (a : r ≠ .x6) (b : r ≠ .x10) (c : r ≠ .x12) :
      (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)).getReg r = s.getReg r := by
    rw [advKeep r c, w, keep' r a b]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, all⟩
  · rw [fadv, pure_pc _ _ rfl, write_pc, pc₁, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
    congr 1
  · rw [advKeep _ (by decide), w, x6']
  · rw [adv12, w, keep' _ (by decide) (by decide), at_.x12, show signExtend12 (200 : BitVec 12) = wordAddress 25 by decide,
      ← wordAddress_add]; congr 1
  · rw [all _ (by decide) (by decide) (by decide), at_.sel]
  · rw [all _ (by decide) (by decide) (by decide), at_.size]
  · rw [all _ (by decide) (by decide) (by decide), at_.prim]
  · rw [all _ (by decide) (by decide) (by decide), at_.five]
  · rw [all _ (by decide) (by decide) (by decide), at_.width]
  · intro j hj
    obtain ⟨_, _, a, _, _, _, b, _, c, _⟩ := rec_base_ne j
    rw [all _ a b c, at_.bases j hj]

theorem fwd_run_rec (x TW : Nat) (hx : x < LENGTH) (tb : TW+25*7 ≤ 2^33) (sb : ∀ k < 7, grpWord k x + 25 ≤ 2^33) :
    ∀ n k fuel (s : MachineState), k+n ≤ 7 → RFwd x TW k s →
      execute openingImage (5*n+fuel) s true = (do
        let t ← recFwdTrace x TW n k s
        let r ← execute openingImage fuel t true
        pure (r.charge (18*n) n)) := by
  intro n
  induction n with
  | zero =>
    intro k fuel s _ _
    simp only [recFwdTrace, pure_bind, Nat.mul_zero, Nat.zero_add]
    conv => lhs; rw [← bind_pure (execute openingImage fuel s true)]
    apply bind_congr; intro r; cases r; simp [Execution.charge]
  | succ n ih =>
    intro k fuel s le at_
    rw [show 5*(n+1)+fuel = 5+(5*n+fuel) by omega, fwd_step_rec x TW k _ s (by omega) hx at_ (sb k (by omega)) (by omega)]
    simp only [recFwdTrace, bind_assoc]
    apply bind_congr; intro y
    rw [ih (k+1) fuel _ (by omega) (fwd_next_rec x TW k (by omega) hx s at_ y).1]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro r
    rw [charge_merge, show 18 + 18*n = 18*(n+1) by omega, show 1 + n = n+1 by omega]

theorem fwd_post_rec (x TW : Nat) (hx : x < LENGTH) : ∀ n k (s t : MachineState), k+n ≤ 7 → RFwd x TW k s →
    t ∈ support (recFwdTrace x TW n k s) →
      RFwd x TW (k+n) t ∧ ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r := by
  intro n
  induction n with
  | zero =>
    intro k s t _ at_ hit
    simp only [recFwdTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; exact ⟨at_, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    intro k s t le at_ hit
    simp only [recFwdTrace, mem_support_bind_iff] at hit
    obtain ⟨y, _, rest⟩ := hit
    obtain ⟨next, keep⟩ := fwd_next_rec x TW k (by omega) hx s at_ y
    obtain ⟨fin, keep'⟩ := ih (k+1) _ t (by omega) next rest
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using fin,
      fun r a b c => (keep' r a b c).trans (keep r a b c)⟩

theorem radv_regs (t : MachineState) :
    (radv t).getReg .x10 = t.getReg .x10 + wordAddress 25 ∧
    (radv t).getReg .x12 = t.getReg .x12 + wordAddress 20 ∧
    (radv t).mem = t.mem ∧ (radv t).pc = t.pc + 8 ∧
    ∀ r, r ≠ .x10 → r ≠ .x12 → (radv t).getReg r = t.getReg r := by
  refine ⟨?_, ?_, pure_mem _ _ rfl, ?_, ?_⟩
  · simp [radv, execInstrBr, signExtend12]; rfl
  · simp [radv, execInstrBr, signExtend12]; rfl
  · rw [radv, pure_pc _ _ rfl]; rfl
  · intro r a b
    simp [radv, execInstrBr, Ne.symm a, Ne.symm b]

theorem inv_step_rec (A D g fuel : Nat) (s : MachineState) (hg : g < 7) (at_ : RInv A D g s)
    (ab : A+25*g+25 ≤ 2^33) (db : D+20*g+25 ≤ 2^33) :
    execute openingImage (3+fuel) s true = (do
      let y ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView s) (A+25*g))))))
      let r ← execute openingImage fuel (radv (writeBits s (wordAddress (D+20*g)) y)) true
      pure (r.charge 10 1)) := by
  obtain ⟨_, _, _, _, _, _, _, inv, _⟩ := rec_codes
  have code := inv g hg
  have fetched : fetch openingImage s = some (.base .ECALL) :=
    fetch_program s (80+3*g) .ECALL (by have := code 0 (by simp [recInv]); simpa [recInv] using this) at_.pc
  rw [show 3+fuel = (2+fuel)+1 by omega,
    execute_inverse_call openingImage (2+fuel) s true (A+25*g) (D+20*g) ab db at_.src at_.dst
      at_.sel at_.size at_.prim fetched]
  apply bind_congr; intro y
  have pcw : (writeBits s (wordAddress (D+20*g)) y).pc = BitVec.ofNat 64 (4096+4*(80+3*g+1)) := by
    rw [write_pc, pc_next _ _ at_.pc]
  have tail : CodeAt (80+3*g+1) [.ADDI .x10 .x10 200, .ADDI .x12 .x12 160] := by
    intro i hi
    have := code (i+1) (by simp [recInv] at hi ⊢; omega)
    rw [show 80+3*g+1+i = 80+3*g+(i+1) by omega, this]
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> rfl
  have run : Runs _ (radv (writeBits s (wordAddress (D+20*g)) y)) 2 2 :=
    (runs_pure _ _ _ tail pcw rfl).cast rfl rfl
  rw [run fuel true]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro r
  rw [charge_merge]

theorem inv_next_rec {bits : Nat} (A D g : Nat) (s : MachineState) (at_ : RInv A D g s) (y : BitVec bits) :
    RInv A D (g+1) (radv (writeBits s (wordAddress (D+20*g)) y)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → (radv (writeBits s (wordAddress (D+20*g)) y)).getReg r = s.getReg r := by
  obtain ⟨a10, a12, _, apc, keep⟩ := radv_regs (writeBits s (wordAddress (D+20*g)) y)
  have w (r : Reg) := writeBits_register s (wordAddress (D+20*g)) y r
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r a b => (keep r a b).trans (w r)⟩
  · rw [apc, write_pc, at_.pc, BitVec.add_assoc]
    rw [show (4 : Word) + 8 = BitVec.ofNat 64 12 from rfl, ← BitVec.ofNat_add]
    congr 1
  · rw [a10, w, at_.src, ← wordAddress_add]; congr 1
  · rw [a12, w, at_.dst, ← wordAddress_add]; congr 1
  · rw [keep _ (by decide) (by decide), w, at_.sel]
  · rw [keep _ (by decide) (by decide), w, at_.size]
  · rw [keep _ (by decide) (by decide), w, at_.prim]

theorem inv_run_rec (A D : Nat) (ab : A+25*7 ≤ 2^33) (db : D+20*7+5 ≤ 2^33) :
    ∀ n g fuel (s : MachineState), g+n ≤ 7 → RInv A D g s →
      execute openingImage (3*n+fuel) s true = (do
        let t ← recInvTrace A D n g s
        let r ← execute openingImage fuel t true
        pure (r.charge (10*n) n)) := by
  intro n
  induction n with
  | zero =>
    intro g fuel s _ _
    simp only [recInvTrace, pure_bind, Nat.mul_zero, Nat.zero_add]
    conv => lhs; rw [← bind_pure (execute openingImage fuel s true)]
    apply bind_congr; intro r; cases r; simp [Execution.charge]
  | succ n ih =>
    intro g fuel s le at_
    rw [show 3*(n+1)+fuel = 3+(3*n+fuel) by omega, inv_step_rec A D g _ s (by omega) at_ (by omega) (by omega)]
    simp only [recInvTrace, bind_assoc]
    apply bind_congr; intro y
    rw [ih (g+1) fuel _ (by omega) (inv_next_rec A D g s at_ y).1]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro r
    rw [charge_merge, show 10 + 10*n = 10*(n+1) by omega, show 1 + n = n+1 by omega]

theorem inv_post_rec (A D : Nat) : ∀ n g (s t : MachineState), RInv A D g s →
    t ∈ support (recInvTrace A D n g s) →
      RInv A D (g+n) t ∧ ∀ r, r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r := by
  intro n
  induction n with
  | zero =>
    intro g s t at_ hit
    simp only [recInvTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; exact ⟨at_, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro g s t at_ hit
    simp only [recInvTrace, mem_support_bind_iff] at hit
    obtain ⟨y, _, rest⟩ := hit
    obtain ⟨next, keep⟩ := inv_next_rec A D g s at_ y
    obtain ⟨fin, keep'⟩ := ih (g+1) _ t next rest
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using fin, fun r a b => (keep' r a b).trans (keep r a b)⟩

/-! ### Fixed-oracle semantics of one record -/

def fixedRecFwd (o : Oracle) (x TW : Nat) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, k, s => fixedRecFwd o x TW n (k+1)
      (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) (o.permutation (packBuffer (window (memoryView (fpre k s)) (grpWord k x))))))

def fixedRecInv (o : Oracle) (A D : Nat) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, g, s => fixedRecInv o A D n (g+1)
      (radv (writeBits s (wordAddress (D+20*g)) (o.permutation.symm (packBuffer (window (memoryView s) (A+25*g))))))

theorem rec_fwd_fixed (o : Oracle) (x TW : Nat) : ∀ n k (s : MachineState),
    o.run (recFwdTrace x TW n k s) = pure (fixedRecFwd o x TW n k s, n) := by
  intro n
  induction n with
  | zero => intro k s; exact oracle_run_pure ..
  | succ n ih =>
    intro k s
    rw [recFwdTrace, oracle_run_public_bind]
    simp only [Oracle.answer]
    rw [ih]
    simp [fixedRecFwd, Nat.add_comm]
    rfl

theorem rec_inv_fixed (o : Oracle) (A D : Nat) : ∀ n g (s : MachineState),
    o.run (recInvTrace A D n g s) = pure (fixedRecInv o A D n g s, n) := by
  intro n
  induction n with
  | zero => intro g s; exact oracle_run_pure ..
  | succ n ih =>
    intro g s
    rw [recInvTrace, oracle_run_public_bind]
    simp only [Oracle.answer]
    rw [ih]
    simp [fixedRecInv, Nat.add_comm]
    rfl

theorem rec_fwd_mem (o : Oracle) (x TW : Nat) (s0 : MachineState) (hx : x < LENGTH) (tb : TW+25*7 ≤ 2^33)
    (sep : ∀ k < 7, grpWord k x + 25 ≤ TW) :
    ∀ n k (s : MachineState), k+n ≤ 7 →
      (∀ w < TW, memoryView s w = memoryView s0 w) →
      (∀ h < k, window (memoryView s) (TW+25*h) =
        (replyWords (o.permutation (packBuffer (window (memoryView s0) (grpWord h x)))) : Words 25)) →
      (∀ w < TW, memoryView (fixedRecFwd o x TW n k s) w = memoryView s0 w) ∧
      (∀ h < k+n, window (memoryView (fixedRecFwd o x TW n k s)) (TW+25*h) =
        (replyWords (o.permutation (packBuffer (window (memoryView s0) (grpWord h x)))) : Words 25)) := by
  intro n
  induction n with
  | zero => intro k s _ low done; exact ⟨low, done⟩
  | succ n ih =>
    intro k s le low done
    have pm : memoryView (fpre k s) = memoryView s := view_of_mem (pure_mem _ _ rfl)
    let y := o.permutation (packBuffer (window (memoryView (fpre k s)) (grpWord k x)))
    let s' := fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)
    have view : ∀ w < 2^33, memoryView s' w = writeWindow (memoryView s) (TW+25*k) (replyWords y) w := by
      intro w big
      have fm : s'.mem = (writeBits (fpre k s) (wordAddress (TW+25*k)) y).mem := pure_mem _ _ rfl
      rw [view_of_mem fm, ← pm]
      exact permutation_write_memory _ (TW+25*k) w y (by omega) big
    have srcSame : window (memoryView (fpre k s)) (grpWord k x) = (window (memoryView s0) (grpWord k x) : Words 25) := by
      rw [pm]; funext j; exact low _ (by have := j.isLt; have := sep k (by omega); omega)
    have low' : ∀ w < TW, memoryView s' w = memoryView s0 w := by
      intro w hw
      rw [view w (by omega), writeWindow, dite_eq_right (by omega)]
      exact low w hw
    have done' : ∀ h < k+1, window (memoryView s') (TW+25*h) =
        (replyWords (o.permutation (packBuffer (window (memoryView s0) (grpWord h x)))) : Words 25) := by
      intro h hh
      funext j
      have jb := j.isLt
      by_cases last : h = k
      · subst h
        simp only [window]
        rw [view _ (by omega), writeWindow, dite_eq_left (by omega)]
        simp only [y, srcSame]
        congr 2
        first | omega | (apply Fin.ext; simp; omega)
      · have old := congrFun (done h (by omega)) j
        simp only [window] at old ⊢
        rw [view _ (by omega), writeWindow, dite_eq_right (by omega)]
        exact old
    have rest := ih (k+1) s' (by omega) low' done'
    simpa [fixedRecFwd, Nat.add_assoc, Nat.add_comm 1 n] using rest

theorem rec_inv_mem (o : Oracle) (A D : Nat) (src : Nat → BitVec 1600) (s0 : MachineState)
    (sep : D+20*7+5 ≤ A) (ab : A+25*7 ≤ 2^33) :
    ∀ n g (s : MachineState), g+n ≤ 7 →
      (∀ w < D, memoryView s w = memoryView s0 w) →
      (∀ h, g ≤ h → h < 7 → window (memoryView s) (A+25*h) = (replyWords (o.permutation (src h)) : Words 25)) →
      (∀ h < g, ∀ m < 20, memoryView s (D+20*h+m) = (src h).extractLsb' (64*m) 64) →
      (∀ w < D, memoryView (fixedRecInv o A D n g s) w = memoryView s0 w) ∧
      (∀ h < g+n, ∀ m < 20, memoryView (fixedRecInv o A D n g s) (D+20*h+m) = (src h).extractLsb' (64*m) 64) := by
  intro n
  induction n with
  | zero => intro g s _ low _ done; exact ⟨low, done⟩
  | succ n ih =>
    intro g s le low pending done
    let y := o.permutation.symm (packBuffer (window (memoryView s) (A+25*g)))
    have answer : y = src g := by
      have rp := reply_pack' (o.permutation (src g))
      simp only [y, pending g le_rfl (by omega)]
      rw [rp]
      exact Equiv.symm_apply_apply _ _
    let s' := radv (writeBits s (wordAddress (D+20*g)) y)
    have view : ∀ w < 2^33, memoryView s' w = writeWindow (memoryView s) (D+20*g) (replyWords y) w := by
      intro w big
      rw [view_of_mem (radv_regs _).2.2.1]
      exact permutation_write_memory s (D+20*g) w y (by omega) big
    have low' : ∀ w < D, memoryView s' w = memoryView s0 w := by
      intro w hw
      rw [view w (by omega), writeWindow, dite_eq_right (by omega)]
      exact low w hw
    have pending' : ∀ h, g+1 ≤ h → h < 7 →
        window (memoryView s') (A+25*h) = (replyWords (o.permutation (src h)) : Words 25) := by
      intro h lo hi
      funext j
      have jb := j.isLt
      have old := congrFun (pending h (by omega) hi) j
      simp only [window] at old ⊢
      rw [view _ (by omega), writeWindow, dite_eq_right (by omega)]
      exact old
    have done' : ∀ h < g+1, ∀ m < 20, memoryView s' (D+20*h+m) = (src h).extractLsb' (64*m) 64 := by
      intro h hh m hm
      by_cases last : h = g
      · subst h
        rw [view _ (by omega), writeWindow, dite_eq_left (by omega), answer]
        simp only [replyWords]
        congr 2
        omega
      · rw [view _ (by omega), writeWindow, dite_eq_right (by omega)]
        exact done h (by omega) m hm
    have rest := ih (g+1) s' (by omega) low' pending' done'
    simpa [fixedRecInv, Nat.add_assoc, Nat.add_comm 1 n] using rest

/-! ### Loads and stores of the opener -/

theorem run_ld (state : MachineState) (rd rs : Reg) (imm : BitVec 12) (index : Nat)
    (code : program[index]? = some (.LD rd rs imm)) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (A : Nat) (addr : state.getReg rs + signExtend12 imm = BitVec.ofNat 64 A) (al : A % 8 = 0)
    (bound : A + 8 ≤ MEMORY_BYTES) (nz : rd ≠ .x0) :
    Runs state (execInstrBr state (.LD rd rs imm)) 1 1 ∧
      (execInstrBr state (.LD rd rs imm)).getReg rd = state.getMem (BitVec.ofNat 64 A) ∧
      (∀ r, r ≠ rd → (execInstrBr state (.LD rd rs imm)).getReg r = state.getReg r) ∧
      (execInstrBr state (.LD rd rs imm)).mem = state.mem ∧
      (execInstrBr state (.LD rd rs imm)).pc = BitVec.ofNat 64 (4096+4*(index+1)) := by
  have valid : memoryArgumentsValid state (.LD rd rs imm) = true := by
    simp only [memoryArgumentsValid, memAccess, addr]
    exact QOpening.aligned_access _ al bound
  refine ⟨runs_one state _ index code pc rfl valid, ?_, ?_, mem_set_reg _ _ _, ?_⟩
  · simp [execInstrBr, addr, nz]
  · intro r a; simp [execInstrBr, Ne.symm a]
  · exact (straight_pc state _ rfl).trans (pc_next _ _ pc)

theorem run_sd (state : MachineState) (base value : Reg) (imm : BitVec 12) (index : Nat)
    (code : program[index]? = some (.SD base value imm)) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (W : Nat) (addr : state.getReg base + signExtend12 imm = wordAddress W) (bound : 8*W + 8 ≤ MEMORY_BYTES) :
    Runs state (execInstrBr state (.SD base value imm)) 1 1 ∧
      (∀ r, (execInstrBr state (.SD base value imm)).getReg r = state.getReg r) ∧
      (∀ w < 2^61, memoryView (execInstrBr state (.SD base value imm)) w =
        if w = W then state.getReg value else memoryView state w) ∧
      (execInstrBr state (.SD base value imm)).pc = BitVec.ofNat 64 (4096+4*(index+1)) := by
  have valid : memoryArgumentsValid state (.SD base value imm) = true := by
    simp only [memoryArgumentsValid, memAccess, addr]
    exact QOpening.aligned_access _ (by omega) (by omega)
  refine ⟨runs_one state _ index code pc rfl valid, ?_, ?_, ?_⟩
  · intro r; simp [execInstrBr, MachineState.getReg_setPC]; cases r <;> rfl
  · intro w hw
    have stored := memory_at_store (state := state) (value := state.getReg value) (address := W) (index := w)
      (by unfold MEMORY_BYTES at bound; omega) hw
    simp only [execInstrBr, addr]
    rw [show memoryView ((state.setMem (wordAddress W) (state.getReg value)).setPC (state.pc + 4)) w =
      memoryView (state.setMem (wordAddress W) (state.getReg value)) w from rfl, stored]
    simp [writeWord]
  · exact (straight_pc state _ rfl).trans (pc_next _ _ pc)

/-- The index and the salt of record `o`. -/
theorem pre_run (state : MachineState) (o x : Nat) (hx : x < LENGTH) (ho : o < LENGTH)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*35))
    (index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*o))
    (loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 x)
    (salts : state.getReg .x22 = BitVec.ofNat 64 nonceBase)
    (dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(142*o))) :
    Runs state (recPre state) 7 7 ∧ (recPre state).getReg .x6 = BitVec.ofNat 64 x ∧
      (recPre state).pc = BitVec.ofNat 64 (4096+4*42) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x31 → (recPre state).getReg r = state.getReg r) ∧
      (∀ w < 2^61, memoryView (recPre state) w =
        if w = proofBase/8 + 142*o + 1 then memoryView state ((nonceBase+16*x)/8 + 1)
        else if w = proofBase/8 + 142*o then memoryView state ((nonceBase+16*x)/8)
        else memoryView state w) := by
  have hL : LENGTH = 16777216 := rfl
  have nb : nonceBase = 6106914848 := rfl
  have ib : indicesBase = 6375350304 := rfl
  have pb : proofBase = 10804535392 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨_, _, c₁, c₂, c₃, _⟩ := rec_codes
  obtain ⟨run₁, x6₁, keep₁, mem₁, pc₁⟩ := run_ld state .x6 .x8 0 35 (by simpa using c₁ 0 (by simp)) pc
    (indicesBase+8*o) (by rw [index, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]) (by omega) (by omega) (by decide)
  generalize h₁ : execInstrBr state (.LD .x6 .x8 0) = s₁ at run₁ x6₁ keep₁ mem₁ pc₁
  rw [loaded] at x6₁
  have pure₂ : ([.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] : List Instr).all pureOp = true := rfl
  have run₂ := runs_pure _ 36 s₁ c₂ pc₁ pure₂
  generalize h₂ : ([.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] : List Instr).foldl execInstrBr s₁ = s₂ at run₂
  have x7₂ : s₂.getReg .x7 = BitVec.ofNat 64 (nonceBase+16*x) := by
    rw [← h₂]; simp [execInstrBr, x6₁, keep₁ .x22 (by decide), salts]
    rw [shift_salt x (by omega), ← BitVec.ofNat_add]
  have keep₂ (r : Reg) (a : r ≠ .x7) : s₂.getReg r = s₁.getReg r := by
    rw [← h₂]; simp [execInstrBr, Ne.symm a]
  have mem₂ : s₂.mem = s₁.mem := by rw [← h₂]; exact pure_mem _ _ pure₂
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*38) := by rw [← h₂, pure_pc _ _ pure₂, pc₁, pc_offset]; rfl
  have pcodes : ∀ i < 4, program[38+i]? = (pairCode 2)[i]? := c₃
  have p0 : program[38]? = some (.LD .x31 .x7 0) := by rw [pcodes 0 (by decide)]; rfl
  have p1 : program[39]? = some (.SD .x21 .x31 0) := by rw [pcodes 1 (by decide)]; rfl
  have p2 : program[40]? = some (.LD .x31 .x7 8) := by rw [pcodes 2 (by decide)]; rfl
  have p3 : program[41]? = some (.SD .x21 .x31 8) := by rw [pcodes 3 (by decide)]; rfl
  have o0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have o8 : signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 := by decide
  obtain ⟨run₃, v₃, keep₃, mem₃, pc₃⟩ := run_ld s₂ .x31 .x7 0 38 p0 pc₂ (nonceBase+16*x)
    (by rw [x7₂, o0, BitVec.add_zero]) (by omega) (by omega) (by decide)
  generalize h₃ : execInstrBr s₂ (.LD .x31 .x7 0) = s₃ at run₃ v₃ keep₃ mem₃ pc₃
  obtain ⟨run₄, keep₄, view₄, pc₄⟩ := run_sd s₃ .x21 .x31 0 39 p1 pc₃ (proofBase/8 + 142*o)
    (by rw [keep₃ _ (by decide), keep₂ _ (by decide), keep₁ _ (by decide), dest, o0, BitVec.add_zero]
        unfold wordAddress; congr 1; omega) (by omega)
  generalize h₄ : execInstrBr s₃ (.SD .x21 .x31 0) = s₄ at run₄ keep₄ view₄ pc₄
  have src1 : s₄.getMem (BitVec.ofNat 64 (nonceBase+16*x+8)) = memoryView state ((nonceBase+16*x)/8 + 1) := by
    have e : s₄.getMem (BitVec.ofNat 64 (nonceBase+16*x+8)) = memoryView s₄ ((nonceBase+16*x)/8 + 1) := by
      rw [← view_get]; congr 2; omega
    rw [e, view₄ _ (by omega), if_neg (by omega), view_of_mem mem₃, view_of_mem mem₂, view_of_mem mem₁]
  obtain ⟨run₅, v₅, keep₅, mem₅, pc₅⟩ := run_ld s₄ .x31 .x7 8 40 p2 pc₄ (nonceBase+16*x+8)
    (by rw [keep₄, keep₃ _ (by decide), x7₂, o8, ← BitVec.ofNat_add]) (by omega) (by omega) (by decide)
  generalize h₅ : execInstrBr s₄ (.LD .x31 .x7 8) = s₅ at run₅ v₅ keep₅ mem₅ pc₅
  obtain ⟨run₆, keep₆, view₆, pc₆⟩ := run_sd s₅ .x21 .x31 8 41 p3 pc₅ (proofBase/8 + 142*o + 1)
    (by rw [keep₅ _ (by decide), keep₄, keep₃ _ (by decide), keep₂ _ (by decide), keep₁ _ (by decide), dest, o8,
          ← BitVec.ofNat_add]
        unfold wordAddress; congr 1; omega) (by omega)
  generalize h₆ : execInstrBr s₅ (.SD .x21 .x31 8) = s₆ at run₆ keep₆ view₆ pc₆
  have shape : recPre state = s₆ := by
    rw [← h₆, ← h₅, ← h₄, ← h₃, ← h₂, ← h₁]; rfl
  rw [shape]
  have w0 : s₃.getReg .x31 = memoryView state ((nonceBase+16*x)/8) := by
    rw [v₃, ← view_of_mem mem₁, ← view_of_mem mem₂]; rw [← view_get]; congr 2; omega
  refine ⟨(run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆))))).cast rfl
      (by simp [cost, instructionCycles]), ?_, pc₆, ?_, ?_⟩
  · rw [keep₆, keep₅ _ (by decide), keep₄, keep₃ _ (by decide), keep₂ _ (by decide), x6₁]
  · intro r a b c
    rw [keep₆, keep₅ r c, keep₄, keep₃ r c, keep₂ r b, keep₁ r a]
  · intro w hw
    rw [view₆ w hw, v₅, src1, view_of_mem mem₅, view₄ w hw, w0, view_of_mem mem₃, view_of_mem mem₂,
      view_of_mem mem₁]

/-! ### One whole record -/

theorem minus_1400 (W : Nat) (h : W < 2^60) :
    wordAddress (W+175) + signExtend12 (-1400 : BitVec 12) = wordAddress W := by
  rw [show signExtend12 (-1400 : BitVec 12) = BitVec.ofNat 64 (2^64-1400) by decide]
  unfold wordAddress
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem mid_regs (t : MachineState) (TW W21 : Nat) (h : TW < 2^60)
    (x12 : t.getReg .x12 = wordAddress (TW+175)) (x21 : t.getReg .x21 = BitVec.ofNat 64 (8*W21)) :
    (recMidRun t).getReg .x10 = wordAddress TW ∧ (recMidRun t).getReg .x12 = wordAddress (W21+2) ∧
    (recMidRun t).getReg .x13 = 2 ∧ (recMidRun t).mem = t.mem ∧
    ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x13 → (recMidRun t).getReg r = t.getReg r := by
  refine ⟨?_, ?_, ?_, pure_mem _ _ rfl, ?_⟩
  · simp [recMidRun, recMid, execInstrBr, x12]; exact minus_1400 TW h
  · simp [recMidRun, recMid, execInstrBr, x21]
    unfold wordAddress
    rw [show signExtend12 16#12 = BitVec.ofNat 64 16 by decide, ← BitVec.ofNat_add]
    congr 1
  · simp [recMidRun, recMid, execInstrBr]; rfl
  · intro r a b c
    simp [recMidRun, recMid, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

def recBackRun (u : MachineState) : MachineState :=
  ([.ADDI .x8 .x8 8] : List Instr).foldl execInstrBr (recBack.foldl execInstrBr u)

theorem back_regs (u : MachineState) (TW W : Nat) (h : TW < 2^60)
    (x10 : u.getReg .x10 = wordAddress (TW+175)) (x12 : u.getReg .x12 = wordAddress W) :
    (recBackRun u).getReg .x12 = wordAddress TW ∧ (recBackRun u).getReg .x21 = wordAddress W ∧
    (recBackRun u).getReg .x13 = 1 ∧ (recBackRun u).getReg .x8 = u.getReg .x8 + signExtend12 8 ∧
    (recBackRun u).mem = u.mem ∧
    ∀ r, r ≠ .x8 → r ≠ .x12 → r ≠ .x13 → r ≠ .x21 → (recBackRun u).getReg r = u.getReg r := by
  have pure : (recBack ++ ([.ADDI .x8 .x8 8] : List Instr)).all pureOp = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [recBackRun, recBack, execInstrBr, x10]; exact minus_1400 TW h
  · simp [recBackRun, recBack, execInstrBr, x12, show signExtend12 0#12 = 0#64 by decide]
  · simp [recBackRun, recBack, execInstrBr]; rfl
  · simp [recBackRun, recBack, execInstrBr]
  · rw [recBackRun, ← List.foldl_append]; exact pure_mem _ _ pure
  · intro r a b c d
    simp [recBackRun, recBack, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

theorem rec_fin_shape (u : MachineState) : recFin u = (recBackRun u).setPC
    (if (recBackRun u).getReg .x8 != (recBackRun u).getReg .x18 then (recBackRun u).pc + signExtend13 7912
     else (recBackRun u).pc + 4) := bne_shape _ _ _ _

theorem record_exec (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (o : Nat) (present : o < positions.card) (state : MachineState)
    (at_ : RecAt (s.initialState .opening (td, positions)) positions o state) (fuel : Nat) :
    execute openingImage (71+fuel) state true = (do
      let t ← recordTrace (ordinalIndex positions o) (recScratch positions.card) (proofBase/8+142*o+2) state
      let r ← execute openingImage fuel t true
      pure (r.charge 211 14)) := by
  let x := ordinalIndex positions o
  let TW := recScratch positions.card
  let D := proofBase/8+142*o+2
  have hx : x < LENGTH := ordinal_index_lt positions o
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have pb : proofBase = 10804535392 := rfl
  have ib : indicesBase = 6375350304 := rfl
  have tw : TW = proofBase/8 + 142*positions.card + 4096 := rfl
  obtain ⟨_, _, _, _, _, _, cm, _, cb, cl, cn⟩ := rec_codes
  have r := at_.regs
  have loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 x := by
    rw [at_.frame _ (by unfold trapdoorBase; omega) (by omega) (by omega),
      QOpening.input_index s layout td positions o present]
    show _ = BitVec.ofNat 64 (ordinalIndex positions o)
    rw [ordinal_index positions o present]
  have notLast : o ≠ positions.card := by omega
  have pc₀ : state.pc = BitVec.ofNat 64 (4096+4*35) := by simpa [notLast] using r.pc
  obtain ⟨run₁, x6₁, pc₁, keep₁, _⟩ := pre_run state o x hx (by omega) pc₀ r.index loaded r.salts r.dest
  have k₁ (reg : Reg) (h : reg ∈ [Reg.x5, .x11, .x12, .x13, .x19, .x21, .x23, .x8, .x9, .x15, .x18, .x22, .x2, .x3, .x4, .x14, .x16, .x17, .x20]) :
      (recPre state).getReg reg = state.getReg reg :=
    keep₁ reg (by intro e; subst e; simp at h) (by intro e; subst e; simp at h) (by intro e; subst e; simp at h)
  have fwd0 : RFwd x TW 0 (recPre state) := by
    refine ⟨by simpa using pc₁, by simpa using x6₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k₁ .x12 (by simp), r.scratch]; simp [TW]
    · rw [k₁ .x5 (by simp), r.sel]
    · rw [k₁ .x11 (by simp), r.size]
    · rw [k₁ .x13 (by simp), r.prim]
    · rw [k₁ .x19 (by simp), r.five]
    · rw [k₁ .x23 (by simp), r.width]
    · intro j hj
      rw [keep₁ _ (rec_base_ne j).2.2.1 (rec_base_ne j).2.2.2.1 (rec_base_ne j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, r.bases j hj]
  have sb : ∀ k < 7, grpWord k x + 25 ≤ 2^33 := by
    intro k hk; have := grp_word_bound k x hk hx; omega
  rw [show 71+fuel = 7+(5*7+(3+(3*7+(3+(1+(1+fuel)))))) by omega, run₁ _ true,
    fwd_run_rec x TW hx (by omega) sb 7 0 _ (recPre state) (by omega) fwd0]
  simp only [recordTrace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support; intro t ht
  obtain ⟨fwd7, keepF⟩ := fwd_post_rec x TW hx 7 0 _ t (by omega) fwd0 ht
  have x21t : t.getReg .x21 = BitVec.ofNat 64 (8*(proofBase/8+142*o)) := by
    rw [keepF _ (by decide) (by decide) (by decide), k₁ .x21 (by simp), r.dest]; congr 1; omega
  obtain ⟨m10, m12, m13, _, mkeep⟩ := mid_regs t TW (proofBase/8+142*o) (by omega) (by simpa using fwd7.x12) x21t
  have runM : Runs t (recMidRun t) 3 3 := (runs_pure _ 77 t cm (by simpa using fwd7.pc) rfl).cast rfl rfl
  have inv0 : RInv TW D 0 (recMidRun t) := by
    refine ⟨?_, by simpa using m10, by simpa [D] using m12, ?_, ?_, m13⟩
    · rw [recMidRun, pure_pc _ _ rfl, fwd7.pc, show (4*recMid.length) = 12 from rfl, ← BitVec.ofNat_add]
    · rw [mkeep _ (by decide) (by decide) (by decide), fwd7.sel]
    · rw [mkeep _ (by decide) (by decide) (by decide), fwd7.size]
  rw [runM, inv_run_rec TW D (by omega) (by omega) 7 0 _ (recMidRun t) (by omega) inv0]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support; intro u hu
  obtain ⟨inv7, _⟩ := inv_post_rec TW D 7 0 _ u inv0 hu
  have pure₃ : (recBack ++ ([.ADDI .x8 .x8 8] : List Instr)).all pureOp = true := rfl
  have code₃ : CodeAt 101 (recBack ++ ([.ADDI .x8 .x8 8] : List Instr)) := by
    intro i hi
    have hi' : i < 4 := by simpa [recBack] using hi
    by_cases lo : i < 3
    · rw [List.getElem?_append_left (by simpa [recBack] using lo)]; exact cb i (by simpa [recBack] using lo)
    · have i3 : i = 3 := by omega
      subst i3
      simpa [recBack] using cl 0 (by simp)
  have runB : Runs u (recBackRun u) 4 4 := by
    have := (runs_pure _ 101 u code₃ (by simpa using inv7.pc) pure₃).cast rfl rfl
    rwa [List.foldl_append] at this
  have pcB : (recBackRun u).pc = BitVec.ofNat 64 (4096+4*105) := by
    rw [recBackRun, ← List.foldl_append, pure_pc _ _ pure₃, inv7.pc]; rfl
  have runL : Runs (recBackRun u) (recFin u) 1 1 := by
    intro fuel coins
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ 105 _ cn pcB) rfl]
    rfl
  rw [show 3+(1+(1+fuel)) = 4+(1+fuel) by omega, runB, runL]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro z
  apply congrArg pure
  cases z; simp [Execution.charge]; omega

theorem fwd_frame_rec (x TW : Nat) (tb : TW + 25*7 ≤ 2^33) : ∀ n k (s t : MachineState), k+n ≤ 7 →
    t ∈ support (recFwdTrace x TW n k s) → ∀ w < TW, memoryView t w = memoryView s w := by
  intro n
  induction n with
  | zero =>
    intro k s t _ hit w _
    simp only [recFwdTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; rfl
  | succ n ih =>
    intro k s t le hit w hw
    simp only [recFwdTrace, mem_support_bind_iff] at hit
    obtain ⟨y, _, rest⟩ := hit
    rw [ih (k+1) _ t (by omega) rest w hw]
    have fm : (fadv (writeBits (fpre k s) (wordAddress (TW+25*k)) y)).mem =
        (writeBits (fpre k s) (wordAddress (TW+25*k)) y).mem := pure_mem _ _ rfl
    have pw : memoryView (writeBits (fpre k s) (wordAddress (TW+25*k)) y) w =
        writeWindow (memoryView (fpre k s)) (TW+25*k) (replyWords y) w :=
      permutation_write_memory _ _ w y (by omega) (by omega)
    have fpm : (fpre k s).mem = s.mem := pure_mem _ _ rfl
    rw [view_of_mem fm, pw, writeWindow, dite_eq_right (by omega), view_of_mem fpm]

theorem inv_frame_rec (A D : Nat) (db : D + 20*7 + 5 ≤ 2^33) : ∀ n g (s t : MachineState), g+n ≤ 7 →
    t ∈ support (recInvTrace A D n g s) → ∀ w < D, memoryView t w = memoryView s w := by
  intro n
  induction n with
  | zero =>
    intro g s t _ hit w _
    simp only [recInvTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; rfl
  | succ n ih =>
    intro g s t le hit w hw
    simp only [recInvTrace, mem_support_bind_iff] at hit
    obtain ⟨y, _, rest⟩ := hit
    have pw : memoryView (writeBits s (wordAddress (D+20*g)) y) w =
        writeWindow (memoryView s) (D+20*g) (replyWords y) w :=
      permutation_write_memory _ _ w y (by omega) (by omega)
    rw [ih (g+1) _ t (by omega) rest w hw, view_of_mem (radv_regs _).2.2.1, pw, writeWindow, dite_eq_right (by omega)]

/-- After any reply sequence, the record leaves the registers of record `o + 1` and the input frame. -/
theorem record_post (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (o : Nat) (present : o < positions.card) (state : MachineState)
    (at_ : RecAt (s.initialState .opening (td, positions)) positions o state) (t : MachineState)
    (hit : t ∈ support (recordTrace (ordinalIndex positions o) (recScratch positions.card) (proofBase/8+142*o+2) state)) :
    RecAt (s.initialState .opening (td, positions)) positions (o+1) t := by
  let x := ordinalIndex positions o
  let TW := recScratch positions.card
  let D := proofBase/8+142*o+2
  have hx : x < LENGTH := ordinal_index_lt positions o
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have pb : proofBase = 10804535392 := rfl
  have ib : indicesBase = 6375350304 := rfl
  have tw : TW = proofBase/8 + 142*positions.card + 4096 := rfl
  have r := at_.regs
  have loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 x := by
    rw [at_.frame _ (by unfold trapdoorBase; omega) (by omega) (by omega),
      QOpening.input_index s layout td positions o present]
    show _ = BitVec.ofNat 64 (ordinalIndex positions o)
    rw [ordinal_index positions o present]
  have notLast : o ≠ positions.card := by omega
  have pc₀ : state.pc = BitVec.ofNat 64 (4096+4*35) := by simpa [notLast] using r.pc
  obtain ⟨_, x6₁, pc₁, keep₁, view₁⟩ := pre_run state o x hx (by omega) pc₀ r.index loaded r.salts r.dest
  have k₁ (reg : Reg) (h : reg ∈ [Reg.x5, .x11, .x12, .x13, .x19, .x21, .x23, .x8, .x9, .x15, .x18, .x22, .x2, .x3, .x4, .x14, .x16, .x17, .x20]) :
      (recPre state).getReg reg = state.getReg reg :=
    keep₁ reg (by intro e; subst e; simp at h) (by intro e; subst e; simp at h) (by intro e; subst e; simp at h)
  have fwd0 : RFwd x TW 0 (recPre state) := by
    refine ⟨by simpa using pc₁, by simpa using x6₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k₁ .x12 (by simp), r.scratch]; simp [TW]
    · rw [k₁ .x5 (by simp), r.sel]
    · rw [k₁ .x11 (by simp), r.size]
    · rw [k₁ .x13 (by simp), r.prim]
    · rw [k₁ .x19 (by simp), r.five]
    · rw [k₁ .x23 (by simp), r.width]
    · intro j hj
      rw [keep₁ _ (rec_base_ne j).2.2.1 (rec_base_ne j).2.2.2.1 (rec_base_ne j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, r.bases j hj]
  simp only [recordTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  obtain ⟨t₁, ht₁, u, hu, rfl⟩ := hit
  obtain ⟨fwd7, keepF⟩ := fwd_post_rec x TW hx 7 0 _ t₁ (by omega) fwd0 ht₁
  have x21t : t₁.getReg .x21 = BitVec.ofNat 64 (8*(proofBase/8+142*o)) := by
    rw [keepF _ (by decide) (by decide) (by decide), k₁ .x21 (by simp), r.dest]; congr 1; omega
  obtain ⟨m10, m12, m13, mmem, mkeep⟩ := mid_regs t₁ TW (proofBase/8+142*o) (by omega) (by simpa using fwd7.x12) x21t
  have inv0 : RInv TW D 0 (recMidRun t₁) := by
    refine ⟨?_, by simpa using m10, by simpa [D] using m12, ?_, ?_, m13⟩
    · rw [recMidRun, pure_pc _ _ rfl, fwd7.pc, show (4*recMid.length) = 12 from rfl, ← BitVec.ofNat_add]
    · rw [mkeep _ (by decide) (by decide) (by decide), fwd7.sel]
    · rw [mkeep _ (by decide) (by decide) (by decide), fwd7.size]
  obtain ⟨inv7, keepI⟩ := inv_post_rec TW D 7 0 _ u inv0 hu
  obtain ⟨b12, b21, b13, b8, bmem, bkeep⟩ := back_regs u TW (D+20*7) (by omega) (by simpa using inv7.src)
    (by simpa using inv7.dst)
  have pure₃ : (recBack ++ ([.ADDI .x8 .x8 8] : List Instr)).all pureOp = true := rfl
  have pcB : (recBackRun u).pc = BitVec.ofNat 64 (4096+4*105) := by
    rw [recBackRun, ← List.foldl_append, pure_pc _ _ pure₃, inv7.pc]; rfl
  -- registers kept through the whole record
  have all (reg : Reg) (n6 : reg ≠ .x6) (n7 : reg ≠ .x7) (n31 : reg ≠ .x31) (n8 : reg ≠ .x8) (n10 : reg ≠ .x10)
      (n12 : reg ≠ .x12) (n13 : reg ≠ .x13) (n21 : reg ≠ .x21) :
      (recBackRun u).getReg reg = state.getReg reg := by
    rw [bkeep reg n8 n12 n13 n21, keepI reg n10 n12, mkeep reg n10 n12 n13, keepF reg n6 n10 n12, keep₁ reg n6 n7 n31]
  have x8B : (recBackRun u).getReg .x8 = BitVec.ofNat 64 (indicesBase+8*(o+1)) := by
    rw [b8, keepI _ (by decide) (by decide), mkeep _ (by decide) (by decide) (by decide), keepF _ (by decide) (by decide) (by decide),
      k₁ .x8 (by simp), r.index, show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 by decide, ← BitVec.ofNat_add]
    congr 1
  have stopB : (recBackRun u).getReg .x18 = BitVec.ofNat 64 (indicesBase+8*positions.card) := by
    rw [all .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.stop]
  have regsFin (reg : Reg) : (recFin u).getReg reg = (recBackRun u).getReg reg := by
    rw [rec_fin_shape, MachineState.getReg_setPC]
  have memFin : (recFin u).mem = (recBackRun u).mem := by rw [rec_fin_shape]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [rec_fin_shape, set_pc_pc, pcB, x8B, stopB]
    by_cases last : o+1 = positions.card
    · rw [show indicesBase+8*(o+1) = indicesBase+8*positions.card by omega, if_pos last]
      simp
    · have different : BitVec.ofNat 64 (indicesBase+8*(o+1)) ≠ BitVec.ofNat 64 (indicesBase+8*positions.card) := by
        intro same
        have := QOpening.nat_address_injective (by omega) (by omega) same
        omega
      rw [if_neg last]
      simp [different]
      decide
  · rw [regsFin, x8B]
  · rw [regsFin, all .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.heap]
  · rw [regsFin, stopB]
  · rw [regsFin, all .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.five]
  · rw [regsFin, all .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.begin]
  · rw [regsFin, b21]; unfold wordAddress; apply congrArg (BitVec.ofNat 64); simp only [D]; omega
  · rw [regsFin, all .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.salts]
  · rw [regsFin, all .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.width]
  · rw [regsFin, all .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.sel]
  · rw [regsFin, all .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.size]
  · rw [regsFin, b13]
  · rw [regsFin, b12]
  · intro j hj
    obtain ⟨_, _, a6, a7, a8, _, a10, _, a12, a13, _, _, _, a21, _, _, a31⟩ := rec_base_ne j
    rw [regsFin, all _ a6 a7 a31 a8 a10 a12 a13 a21, r.bases j hj]
  · intro a lo hi al
    obtain ⟨w, rfl⟩ : ∃ w, a = 8*w := ⟨a/8, by omega⟩
    rw [view_get, view_of_mem memFin, view_of_mem bmem, inv_frame_rec TW D (by omega) 7 0 _ u (by omega) hu w (by omega),
      view_of_mem mmem, fwd_frame_rec x TW (by omega) 7 0 _ t₁ (by omega) ht₁ w (by omega),
      view₁ w (by omega), if_neg (by omega), if_neg (by omega), ← view_get]
    exact at_.frame _ lo hi al

/-! ### Fixed oracle -/

def fixedRecord (o : Oracle) (x TW D : Nat) (s : MachineState) : MachineState :=
  recFin (fixedRecInv o TW D 7 0 (recMidRun (fixedRecFwd o x TW 7 0 (recPre s))))

theorem record_fixed (o : Oracle) (x TW D : Nat) (s : MachineState) :
    o.run (recordTrace x TW D s) = pure (fixedRecord o x TW D s, 14) := by
  unfold recordTrace
  rw [oracle_run_bind, rec_fwd_fixed]
  simp only [pure_bind]
  rw [oracle_run_bind, rec_inv_fixed]
  simp only [pure_bind, oracle_run_pure]
  rfl

set_option maxRecDepth 1000000 in
theorem record_member (o : Oracle) (x TW D : Nat) (s : MachineState) :
    fixedRecord o x TW D s ∈ support (recordTrace x TW D s) := by
  apply writer_support (o.world.withAddCost Oracle.callCost) _ (fixedRecord o x TW D s, (14 : Nat))
  change (_, _) ∈ support (o.run (recordTrace x TW D s))
  rw [record_fixed]; simp

/-- With the fixed oracle the record emits the salt and the seven groups of its position. -/
theorem record_inv (orc : Oracle) (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (o : Nat) (present : o < positions.card) (state : MachineState)
    (at_ : RecAt (s.initialState .opening (td, positions)) positions o state)
    (inv : Inv (s.initialState .opening (td, positions)) state (wordSource positions) (142*o)) :
    Inv (s.initialState .opening (td, positions))
      (fixedRecord orc (ordinalIndex positions o) (recScratch positions.card) (proofBase/8+142*o+2) state)
      (wordSource positions) (142*(o+1)) := by
  let init := s.initialState .opening (td, positions)
  let x := ordinalIndex positions o
  let TW := recScratch positions.card
  let D := proofBase/8+142*o+2
  have hx : x < LENGTH := ordinal_index_lt positions o
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have pb : proofBase = 10804535392 := rfl
  have ib : indicesBase = 6375350304 := rfl
  have nb : nonceBase = 6106914848 := rfl
  have tb : trapdoorBase = 4294971424 := rfl
  have tw : TW = proofBase/8 + 142*positions.card + 4096 := rfl
  have r := at_.regs
  have loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 x := by
    rw [at_.frame _ (by unfold trapdoorBase; omega) (by omega) (by omega),
      QOpening.input_index s layout td positions o present]
    show _ = BitVec.ofNat 64 (ordinalIndex positions o)
    rw [ordinal_index positions o present]
  have notLast : o ≠ positions.card := by omega
  have pc₀ : state.pc = BitVec.ofNat 64 (4096+4*35) := by simpa [notLast] using r.pc
  obtain ⟨_, _, _, _, view₁⟩ := pre_run state o x hx (by omega) pc₀ r.index loaded r.salts r.dest
  let s₁ := recPre state
  let src : Nat → BitVec 1600 := fun h => packBuffer (window (memoryView s₁) (grpWord h x))
  have sep : ∀ k < 7, grpWord k x + 25 ≤ TW := by
    intro k hk; have := grp_word_bound k x hk hx; omega
  obtain ⟨fLow, fWin⟩ := rec_fwd_mem orc x TW s₁ hx (by omega) sep 7 0 s₁ (by omega) (fun _ _ => rfl)
    (fun h hh => absurd hh (Nat.not_lt_zero _))
  let t := fixedRecFwd orc x TW 7 0 s₁
  have vm : memoryView (recMidRun t) = memoryView t := view_of_mem (pure_mem _ _ rfl)
  obtain ⟨iLow, iOut⟩ := rec_inv_mem orc TW D src (recMidRun t) (by omega) (by omega) 7 0 (recMidRun t) (by omega)
    (fun _ _ => rfl) (fun h _ hh => by rw [vm]; exact fWin h hh) (fun h hh => absurd hh (Nat.not_lt_zero _))
  let u := fixedRecInv orc TW D 7 0 (recMidRun t)
  have pure₃ : (recBack ++ ([.ADDI .x8 .x8 8] : List Instr)).all pureOp = true := rfl
  have vf : memoryView (recFin u) = memoryView u := by
    rw [rec_fin_shape]
    apply view_of_mem
    show (recBackRun u).mem = u.mem
    rw [recBackRun, ← List.foldl_append]; exact pure_mem _ _ pure₃
  have low : ∀ w, w < D → memoryView (recFin u) w = memoryView s₁ w := by
    intro w hw
    rw [vf, iLow w hw, vm, fLow w (by omega)]
  have fin : fixedRecord orc x TW D state = recFin u := rfl
  show Inv init (fixedRecord orc x TW D state) (wordSource positions) (142*(o+1))
  rw [fin]
  refine ⟨fun a lo hi al => ?_, fun v hv => ?_⟩
  · obtain ⟨w, rfl⟩ : ∃ w, a = 8*w := ⟨a/8, by omega⟩
    rw [view_get, low w (by omega), view₁ w (by omega), if_neg (by omega), if_neg (by omega), ← view_get]
    exact inv.input _ lo hi al
  · by_cases old : v < 142*o
    · rw [show proofBase + 8*v = 8*(proofBase/8+v) by omega, view_get, low _ (by omega), view₁ _ (by omega),
        if_neg (by omega), if_neg (by omega), ← view_get, ← show proofBase + 8*v = 8*(proofBase/8+v) by omega]
      exact inv.output v old
    by_cases salt : v < 142*o + 2
    · have e : v - 142*o < 2 := by omega
      rw [show proofBase + 8*v = 8*(proofBase/8+v) by omega, view_get, low _ (by omega), view₁ _ (by omega)]
      have src_eq : wordSource positions v = 8*((nonceBase+16*x)/8 + (v - 142*o)) := by
        rw [show v = 142*o + (v - 142*o) by omega, word_source_salt positions o _ e]
        simp only [x]; omega
      by_cases one : proofBase/8+v = proofBase/8 + 142*o + 1
      · rw [if_pos one, ← view_get, src_eq, show v - 142*o = 1 by omega]
        exact inv.input _ (by omega) (by omega) (by omega)
      · rw [if_neg one, if_pos (by omega), ← view_get, src_eq, show v - 142*o = 0 by omega, Nat.add_zero]
        exact inv.input _ (by omega) (by omega) (by omega)
    · let e := v - (142*o + 2)
      let h := e / 20
      let m := e % 20
      have hh : h < 7 := by omega
      have hm : m < 20 := by omega
      have addr : proofBase + 8*v = 8*(D + 20*h + m) := by simp only [D, h, m, e]; omega
      have out := iOut h hh m hm
      have packed := packed_word (window (memoryView s₁) (grpWord h x)) ⟨m, by omega⟩
      rw [addr, view_get, vf, out]
      simp only [src] at packed ⊢
      rw [packed]
      simp only [window]
      rw [view₁ _ (by have := grp_word_bound h x hh hx; omega), if_neg (by have := grp_word_bound h x hh hx; omega),
        if_neg (by have := grp_word_bound h x hh hx; omega)]
      have srcAddr : wordSource positions v = 8*(grpWord h x + m) := by
        rw [show v = 142*o + 2 + 20*h + m by simp only [h, m, e]; omega, word_source_level positions o h m hh hm]
        have := grp_word_address h x hh
        simp only [x] at this ⊢
        omega
      rw [srcAddr, ← view_get]
      have gb := grp_word_bound h x hh hx
      have ga := grp_word_address h x hh
      have lo : trapdoorBase ≤ 8*(grpWord h x + m) := by omega
      have hi : 8*(grpWord h x + m) < proofBase := by omega
      exact inv.input _ lo hi (by omega)

/-! ### All records -/

def recordsTrace (positions : Positions) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n+1, o, s => do
      let t ← recordTrace (ordinalIndex positions o) (recScratch positions.card) (proofBase/8+142*o+2) s
      recordsTrace positions n (o+1) t

def fixedRecords (orc : Oracle) (positions : Positions) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, o, s => fixedRecords orc positions n (o+1)
      (fixedRecord orc (ordinalIndex positions o) (recScratch positions.card) (proofBase/8+142*o+2) s)

theorem records_exec (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) :
    ∀ n o fuel (state : MachineState), o+n ≤ positions.card →
      RecAt (s.initialState .opening (td, positions)) positions o state →
      execute openingImage (71*n+fuel) state true = (do
        let t ← recordsTrace positions n o state
        let r ← execute openingImage fuel t true
        pure (r.charge (211*n) (14*n))) := by
  intro n
  induction n with
  | zero =>
    intro o fuel state _ _
    simp only [recordsTrace, pure_bind, Nat.mul_zero, Nat.zero_add]
    conv => lhs; rw [← bind_pure (execute openingImage fuel state true)]
    apply bind_congr; intro r; cases r; simp [Execution.charge]
  | succ n ih =>
    intro o fuel state le at_
    rw [show 71*(n+1)+fuel = 71+(71*n+fuel) by omega,
      record_exec s layout td positions o (by omega) state at_]
    simp only [recordsTrace, bind_assoc]
    apply bind_congr_of_forall_mem_support; intro t ht
    rw [ih (o+1) fuel t (by omega) (record_post s layout td positions o (by omega) state at_ t ht)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro u
    apply bind_congr; intro z
    rw [charge_merge, show 211 + 211*n = 211*(n+1) by omega, show 14 + 14*n = 14*(n+1) by omega]

theorem records_post (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) :
    ∀ n o (state t : MachineState), o+n ≤ positions.card →
      RecAt (s.initialState .opening (td, positions)) positions o state →
      t ∈ support (recordsTrace positions n o state) →
      RecAt (s.initialState .opening (td, positions)) positions (o+n) t := by
  intro n
  induction n with
  | zero =>
    intro o state t _ at_ hit
    simp only [recordsTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; exact at_
  | succ n ih =>
    intro o state t le at_ hit
    simp only [recordsTrace, mem_support_bind_iff] at hit
    obtain ⟨u, hu, rest⟩ := hit
    have h := ih (o+1) u t (by omega) (record_post s layout td positions o (by omega) state at_ u hu) rest
    simpa [Nat.add_assoc, Nat.add_comm 1 n] using h

theorem records_fixed (orc : Oracle) (positions : Positions) :
    ∀ n o (state : MachineState),
      orc.run (recordsTrace positions n o state) = pure (fixedRecords orc positions n o state, 14*n) := by
  intro n
  induction n with
  | zero => intro o state; exact oracle_run_pure ..
  | succ n ih =>
    intro o state
    rw [recordsTrace, oracle_run_bind, record_fixed]
    simp only [pure_bind]
    rw [ih]
    simp only [pure_bind, fixedRecords]
    congr 2
    omega

theorem records_inv (orc : Oracle) (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) :
    ∀ n o (state : MachineState), o+n ≤ positions.card →
      RecAt (s.initialState .opening (td, positions)) positions o state →
      Inv (s.initialState .opening (td, positions)) state (wordSource positions) (142*o) →
      RecAt (s.initialState .opening (td, positions)) positions (o+n) (fixedRecords orc positions n o state) ∧
      Inv (s.initialState .opening (td, positions)) (fixedRecords orc positions n o state)
        (wordSource positions) (142*(o+n)) := by
  intro n
  induction n with
  | zero => intro o state _ at_ inv; exact ⟨at_, inv⟩
  | succ n ih =>
    intro o state le at_ inv
    have at' := record_post s layout td positions o (by omega) state at_ _ (record_member orc _ _ _ state)
    have inv' := record_inv orc s layout td positions o (by omega) state at_ inv
    have h := ih (o+1) _ (by omega) at' inv'
    simpa [fixedRecords, Nat.add_assoc, Nat.add_comm 1 n] using h

end TwoPermutationPrototype.QuadOpening
