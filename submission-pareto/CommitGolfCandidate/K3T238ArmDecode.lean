import CommitGolfCandidate.TwoPermutationPackedPair
import CommitGolfCandidate.K3T238ArmMask

/-! # T238 lower-loop arm, before the call (loop levels 5..13, `x29 = 9..1`)

Words 63..231 (the K1x copy paths, unchanged) put the child digest and the 30-byte sibling in the pair at 12544.
Word 232 jumps to the block `S` (577..620): `x29 = 9` goes straight to the call; otherwise `x28` points at the
sibling's halfword 14 in the pair, and `x29 ∈ 2..8` clears the sibling's bits 238..255 (588..592) while `x29 = 1`
gathers the last packed sibling's bits 224..237 from the seven earlier slots (593..620). Word 621 sets the call
output. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! ### Small facts -/

theorem ult_word (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  unfold BitVec.ult
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem beq_word (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases same : a = b
  · subst same; simp
  · have ne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
      intro eq
      have n := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at n
      exact same n
    simp [ne, same]

theorem read_mem {s t : MachineState} (same : t.mem = s.mem) (a n : Nat) : readBuffer t a n = readBuffer s a n := by
  unfold readBuffer
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem view_mem {s t : MachineState} (same : t.mem = s.mem) (w : Nat) : memoryView t w = memoryView s w := by
  simp only [memoryView, MachineState.getMem, same]

/-- A branch at word `w` that lands at word `target`. -/
theorem arm_branch (s : MachineState) (w target : Nat) (i : Instr) (bound : w < 705)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*w))
    (decoded : (packedImage.code[w]?).bind decodeInstruction = some (.base i))
    (step : execInstrBr s i = s.setPC (BitVec.ofNat 64 (4096+4*target)))
    (plain : ordinaryStep s (.base i) = some (execInstrBr s i)) (cost : instructionCycles (.base i) = 1) :
    GroupHop s (s.setPC (BitVec.ofNat 64 (4096+4*target))) 1 := by
  rw [← step]
  exact arm_hop s w i bound pc decoded plain cost

/-! ### Words 63..231: the copy paths -/

/-- The state at word 232 after K1x's dispatch, child and sibling copies (30-byte sibling path). -/
def t238Copy (s : MachineState) (even : Bool) : MachineState :=
  route (merge (dispatch s false even) false even) false even

structure CopyFacts (s c : MachineState) (even : Bool) (proof : Nat) : Prop where
  run : GroupHop s c 45
  pc : c.pc = BitVec.ofNat 64 (4096+4*232)
  regs : ∀ r, r ≠ .x31 → r ≠ .x7 → r ≠ .x30 → c.getReg r = s.getReg r
  width : c.getReg .x30 = BitVec.ofNat 64 30
  child : readBuffer c (8*slotWord (!even)) 32 = readBuffer s 12288 32
  sibling : readBuffer c (8*slotWord even) 32 = 0#16 ++ readBuffer s proof 30
  frame : ∀ w < 2^61, (w < 1568 ∨ 1576 ≤ w) → memoryView c w = memoryView s w

theorem t238_copy (s : MachineState) (node proof left : Nat) (even : Bool)
    (pc : s.pc = 4348) (nodeReg : s.getReg .x6 = BitVec.ofNat 64 node) (nodeBound : node < 2^64)
    (parity : even = decide (node % 2 = 0)) (proofReg : s.getReg .x21 = BitVec.ofNat 64 proof)
    (counter : s.getReg .x29 = BitVec.ofNat 64 left) (narrow : left < 13)
    (digest : s.getReg .x23 = 12288) (pair : s.getReg .x24 = 12544)
    (above : 32768 ≤ proof) (aligned : proof % 2 = 0) (room : proof + 30 ≤ MEMORY_BYTES) :
    CopyFacts s (t238Copy s even) even proof := by
  have cnt : (false = true) ↔ BitVec.ult (s.getReg .x29) 13 = false := by
    have low : BitVec.ult (s.getReg .x29) 13 = true := by
      rw [counter, show (13 : Word) = BitVec.ofNat 64 13 from rfl, ult_word _ _ (by omega) (by decide)]
      exact decide_eq_true narrow
    rw [low]
    exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  have par : (even = true) ↔ s.getReg .x6 &&& 1 = 0 := by
    rw [nodeReg, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt nodeBound, parity]
    change (decide (node % 2 = 0) = true) ↔ node &&& 1 = 0
    rw [Nat.and_one_is_mod, decide_eq_true_iff]
  have dp := execute_dispatch s false even pc cnt par
  let d := dispatch s false even
  have dreg (r : Reg) (a : r ≠ .x7) (b : r ≠ .x30) : d.getReg r = s.getReg r := by
    simp only [d, dispatch, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]
  have dmem : d.mem = s.mem := rfl
  have mg := merge_facts d false even proof rfl ((dreg _ (by decide) (by decide)).trans proofReg)
    ((dreg _ (by decide) (by decide)).trans digest) ((dreg _ (by decide) (by decide)).trans pair) above aligned
    (by simpa using room)
  let m := merge d false even
  have rr := route_run m false even mg.pc
  have rpc := route_pc m false even mg.pc
  have cm : (t238Copy s even).mem = m.mem := rfl
  refine ⟨(dp.thenDo mg.run).thenDo rr, rpc, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b c
    show (m.setPC 5024).getReg r = _
    rw [MachineState.getReg_setPC, mg.register r a]
    exact dreg r b c
  · show (m.setPC 5024).getReg .x30 = _
    rw [MachineState.getReg_setPC, mg.register _ (by decide)]
    simp only [d, dispatch, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x7 ≠ .x30 by decide),
      MachineState.getReg_setReg_eq (show Reg.x30 ≠ .x0 by decide), width]
    rfl
  · rw [read_mem cm, mg.child, read_mem dmem]
  · rw [read_mem cm, mg.sibling]
    simp only [wire, Bool.false_eq_true, ite_false]
    rw [read_mem dmem]
  · intro w hw outside
    rw [view_mem cm, mg.frame w hw outside, view_mem dmem]

/-! ### Doublewords of a 32-byte buffer -/

theorem dwords_concat (x : BitVec 256) :
    ((x.extractLsb' 192 64 ++ x.extractLsb' 128 64) ++ x.extractLsb' 64 64) ++ x.extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases a : i < 64
  · simp [a]
  · by_cases b : i - 64 < 64
    · simp [a, b, show 64 + (i - 64) = i by omega]
    · by_cases c : i - 64 - 64 < 64
      · simp [a, b, c, show 128 + (i - 64 - 64) = i by omega]
      · simp [a, b, c, show 192 + (i - 64 - 64 - 64) = i by omega, show i - 64 - 64 - 64 < 64 by omega]

theorem read_of_dwords (s : MachineState) (base : Nat) (aligned : base % 8 = 0) (x : BitVec 256)
    (w0 : s.getMem (BitVec.ofNat 64 base) = x.extractLsb' 0 64)
    (w1 : s.getMem (BitVec.ofNat 64 (base+8)) = x.extractLsb' 64 64)
    (w2 : s.getMem (BitVec.ofNat 64 (base+16)) = x.extractLsb' 128 64)
    (w3 : s.getMem (BitVec.ofNat 64 (base+24)) = x.extractLsb' 192 64) :
    readBuffer s base 32 = x := by
  rw [read_digest_words s base aligned, w0, w1, w2, w3]
  exact dwords_concat x

/-- The doublewords of a buffer read as `x`. -/
theorem dwords_of_read (s : MachineState) (base : Nat) (aligned : base % 8 = 0) (x : BitVec 256)
    (read : readBuffer s base 32 = x) :
    s.getMem (BitVec.ofNat 64 base) = x.extractLsb' 0 64 ∧
    s.getMem (BitVec.ofNat 64 (base+8)) = x.extractLsb' 64 64 ∧
    s.getMem (BitVec.ofNat 64 (base+16)) = x.extractLsb' 128 64 ∧
    s.getMem (BitVec.ofNat 64 (base+24)) = x.extractLsb' 192 64 := by
  have d0 := read_digest_word s base 0 aligned (by decide)
  have d1 := read_digest_word s base 1 aligned (by decide)
  have d2 := read_digest_word s base 2 aligned (by decide)
  have d3 := read_digest_word s base 3 aligned (by decide)
  rw [read] at d0 d1 d2 d3
  exact ⟨by simpa using d0.symm, by simpa using d1.symm, by simpa using d2.symm, by simpa using d3.symm⟩

theorem agree_dword (x y : BitVec 256) (start : Nat) (fits : start + 64 ≤ 192)
    (agree : ∀ i < 192, x.getLsbD i = y.getLsbD i) : x.extractLsb' start 64 = y.extractLsb' start 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', agree _ (by omega)]

/-- The 30-byte sibling, the 238-bit sibling and the gathered last sibling agree below bit 192. -/
theorem wide_low (R : BitVec 240) (i : Nat) (low : i < 192) : ((0#16) ++ R).getLsbD i = R.getLsbD i := by
  rw [BitVec.getLsbD_append, if_pos (by omega)]

theorem mid_low (R : BitVec 240) (i : Nat) (low : i < 192) :
    ((0#18) ++ R.extractLsb' 0 238).getLsbD i = R.getLsbD i := by
  rw [BitVec.getLsbD_append, if_pos (by omega), BitVec.getLsbD_extractLsb']
  simp [show i < 238 by omega]

theorem short_low (R : BitVec 240) (T : BitVec 14) (i : Nat) (low : i < 192) :
    ((0#18) ++ (T ++ R.extractLsb' 0 224)).getLsbD i = R.getLsbD i := by
  rw [BitVec.getLsbD_append, if_pos (by omega), BitVec.getLsbD_append, if_pos (by omega), BitVec.getLsbD_extractLsb']
  simp [show i < 224 by omega]

theorem mid_top (R : BitVec 240) :
    ((((0#16) ++ R).extractLsb' 192 64) <<< 18) >>> 18 = ((0#18) ++ R.extractLsb' 0 238).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_append] <;> simp

theorem short_top (R : BitVec 240) (T : BitVec 14) :
    replaceWord32 (((0#16) ++ R).extractLsb' 192 64) 1 ((T.zeroExtend 64).truncate 32) =
      ((0#18) ++ (T ++ R.extractLsb' 0 224)).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [replaceWord32, BitVec.zeroExtend, BitVec.truncate, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_append] <;> simp

/-! ### Words 232, 577..581: into `S`, `x10 := x24`, the level split -/

/-- Word 232 `jal S`, 577 `addi x10,x24,0`, 578 `addi x7,x0,10`, 579 `bgeu x29,x7` (not taken), 580 `addi x7,x0,9`. -/
def t238Entry (c : MachineState) : MachineState :=
  execInstrBr ((execInstrBr (execInstrBr (execInstrBr c (.JAL .x0 1380)) (.ADDI .x10 .x24 0))
    (.ADDI .x7 .x0 10)).setPC (BitVec.ofNat 64 (4096+4*580))) (.ADDI .x7 .x0 9)

theorem execute_entry (c : MachineState) (left : Nat) (pc : c.pc = BitVec.ofNat 64 (4096+4*232))
    (counter : c.getReg .x29 = BitVec.ofNat 64 left) (small : left < 10) :
    GroupHop c (t238Entry c) 5 := by
  let e1 := execInstrBr c (.JAL .x0 1380)
  let e2 := execInstrBr e1 (.ADDI .x10 .x24 0)
  let e3 := execInstrBr e2 (.ADDI .x7 .x0 10)
  have p1 : e1.pc = BitVec.ofNat 64 (4096+4*577) := by
    show c.pc + signExtend21 1380 = _
    rw [pc]; rfl
  have p2 : e2.pc = BitVec.ofNat 64 (4096+4*(577+1)) := pc_next p1 rfl
  have p3 : e3.pc = BitVec.ofNat 64 (4096+4*(577+1+1)) := pc_next p2 rfl
  have x29 : e3.getReg .x29 = BitVec.ofNat 64 left := by
    simp only [e3, e2, e1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x7 ≠ .x29 by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x10 ≠ .x29 by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x0 ≠ .x29 by decide)]
    exact counter
  have x7 : e3.getReg .x7 = BitVec.ofNat 64 10 := by
    simp only [e3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x7 ≠ .x0 by decide)]
    rfl
  have cond : BitVec.ult (e3.getReg .x29) (e3.getReg .x7) = true := by
    rw [x29, x7, ult_word _ _ (by omega) (by decide)]
    exact decide_eq_true small
  have h0 := arm_hop c 232 _ (by decide) pc rfl rfl rfl
  have h1 := arm_hop e1 577 _ (by decide) p1 rfl rfl rfl
  have h2 := arm_hop e2 (577+1) _ (by decide) p2 rfl rfl rfl
  have h3 := arm_branch e3 (577+1+1) 580 (.BGEU .x29 .x7 6808) (by decide) p3 rfl (by
    show (if ¬ BitVec.ult (e3.getReg .x29) (e3.getReg .x7) = true then e3.setPC (e3.pc + signExtend13 6808)
      else e3.setPC (e3.pc + 4)) = _
    rw [if_neg (by rw [cond]; decide), p3]
    rfl) rfl rfl
  have h4 := arm_hop (e3.setPC (BitVec.ofNat 64 (4096+4*580))) 580 (.ADDI .x7 .x0 9) (by decide) rfl rfl rfl rfl
  exact (((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4

theorem entry_facts (c : MachineState) (pair : c.getReg .x24 = 12544) :
    let e := t238Entry c
    e.pc = BitVec.ofNat 64 (4096+4*581) ∧ e.mem = c.mem ∧ e.getReg .x7 = BitVec.ofNat 64 9 ∧
      e.getReg .x10 = BitVec.ofNat 64 12544 ∧
      ∀ r, r ≠ .x7 → r ≠ .x10 → e.getReg r = c.getReg r := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp only [t238Entry, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x7 ≠ .x0 by decide)]
    rfl
  · simp only [t238Entry, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x7 ≠ .x10 by decide),
      MachineState.getReg_setReg_eq (show Reg.x10 ≠ .x0 by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x0 ≠ .x24 by decide), pair]
    rfl
  · intro r a b
    simp only [t238Entry, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]
    by_cases z : r = .x0
    · subst z; rfl
    · exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm z)

/-! ### Words 581..587: the sibling's halfword 14 in the pair, and the last level -/

def pcAt (w : Nat) : Word := BitVec.ofNat 64 (4096+4*w)

/-- 582 `andi x7,x6,1`, 583 `addi x28,x24,60`, 584 `beq x7,x0,+8` (taken for an even node),
585 `addi x28,x24,28` (odd node), 586 `addi x7,x0,1`. -/
def t238Parity (y : MachineState) (even : Bool) : MachineState :=
  let g := execInstrBr (execInstrBr y (.ANDI .x7 .x6 1)) (.ADDI .x28 .x24 60)
  execInstrBr (if even then g.setPC (pcAt 586) else execInstrBr (g.setPC (pcAt 585)) (.ADDI .x28 .x24 28))
    (.ADDI .x7 .x0 1)

def parityCost (even : Bool) : Nat := if even then 4 else 5

theorem execute_parity (y : MachineState) (node : Nat) (even : Bool) (pc : y.pc = pcAt 582)
    (nodeReg : y.getReg .x6 = BitVec.ofNat 64 node) (nodeBound : node < 2^64)
    (parity : even = decide (node % 2 = 0)) :
    GroupHop y (t238Parity y even) (parityCost even) := by
  let g1 := execInstrBr y (.ANDI .x7 .x6 1)
  let g := execInstrBr g1 (.ADDI .x28 .x24 60)
  have p1 : g1.pc = BitVec.ofNat 64 (4096+4*(582+1)) := pc_next pc rfl
  have p2 : g.pc = BitVec.ofNat 64 (4096+4*(582+1+1)) := pc_next p1 rfl
  have x7 : g.getReg .x7 = BitVec.ofNat 64 (node % 2) := by
    simp only [g, g1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x28 ≠ .x7 by decide),
      MachineState.getReg_setReg_eq (show Reg.x7 ≠ .x0 by decide), nodeReg]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt nodeBound,
      Nat.mod_eq_of_lt (by omega : node % 2 < 2^64)]
    exact Nat.and_one_is_mod node
  have h0 := arm_hop y 582 _ (by decide) pc rfl rfl rfl
  have h1 := arm_hop g1 (582+1) _ (by decide) p1 rfl rfl rfl
  cases even with
  | true =>
    have e : node % 2 = 0 := of_decide_eq_true parity.symm
    have h2 := arm_branch g (582+1+1) 586 (.BEQ .x7 .x0 8) (by decide) p2 rfl (by
      show (if (g.getReg .x7 == g.getReg .x0) = true then g.setPC (g.pc + signExtend13 8) else g.setPC (g.pc + 4)) = _
      rw [if_pos (by rw [x7, e]; rfl), p2]; rfl) rfl rfl
    have h3 := arm_hop (g.setPC (pcAt 586)) 586 (.ADDI .x7 .x0 1) (by decide) rfl rfl rfl rfl
    exact ((h0.thenDo h1).thenDo h2).thenDo h3
  | false =>
    have o : node % 2 = 1 := by
      have := of_decide_eq_false parity.symm; omega
    have h2 := arm_branch g (582+1+1) 585 (.BEQ .x7 .x0 8) (by decide) p2 rfl (by
      show (if (g.getReg .x7 == g.getReg .x0) = true then g.setPC (g.pc + signExtend13 8) else g.setPC (g.pc + 4)) = _
      rw [if_neg (by rw [x7, o, show g.getReg .x0 = 0 from rfl]; decide), p2]; rfl) rfl rfl
    have h3 := arm_hop (g.setPC (pcAt 585)) 585 (.ADDI .x28 .x24 28) (by decide) rfl rfl rfl rfl
    have h4 := arm_hop (execInstrBr (g.setPC (pcAt 585)) (.ADDI .x28 .x24 28)) 586 (.ADDI .x7 .x0 1) (by decide)
      (pc_next (rfl : (g.setPC (pcAt 585)).pc = BitVec.ofNat 64 (4096+4*585)) rfl) rfl rfl rfl
    exact (((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4

theorem parity_facts (y : MachineState) (even : Bool) (pair : y.getReg .x24 = 12544) :
    let f := t238Parity y even
    f.pc = pcAt 587 ∧ f.mem = y.mem ∧ f.getReg .x7 = BitVec.ofNat 64 1 ∧
      f.getReg .x28 = BitVec.ofNat 64 (8*slotWord even+28) ∧
      ∀ r, r ≠ .x7 → r ≠ .x28 → f.getReg r = y.getReg r := by
  cases even <;> refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [t238Parity, execInstrBr, MachineState.getReg_setPC, ite_true, ite_false, Bool.false_eq_true,
        MachineState.getReg_setReg_eq (show Reg.x7 ≠ .x0 by decide)]; rfl)
    | (simp only [t238Parity, execInstrBr, MachineState.getReg_setPC, ite_true, ite_false, Bool.false_eq_true,
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x7 ≠ .x28 by decide),
        MachineState.getReg_setReg_eq (show Reg.x28 ≠ .x0 by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x7 ≠ .x24 by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x28 ≠ .x24 by decide), pair]; rfl)
    | (intro r a b
       simp only [t238Parity, execInstrBr, MachineState.getReg_setPC, ite_true, ite_false, Bool.false_eq_true,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)])

/-! ### Words 588..592 (`x29 ∈ 2..8`): clear the sibling's bits 238..255, jump to the call -/

def sibByte (even : Bool) : Nat := 8*slotWord even

theorem sib_room (even : Bool) : sibByte even + 32 ≤ MEMORY_BYTES ∧ sibByte even % 8 = 0 ∧ 12544 ≤ sibByte even ∧
    sibByte even ≤ 12576 := by
  cases even <;> decide

def t238Mid (z : MachineState) : MachineState := execInstrBr (maskAfter z .x28 0) (.JAL .x0 116)

theorem execute_mid (z : MachineState) (even : Bool) (pc : z.pc = pcAt 588)
    (x28 : z.getReg .x28 = BitVec.ofNat 64 (sibByte even+28)) :
    GroupHop z (t238Mid z) 5 ∧ MaskPost z (maskAfter z .x28 0) (sibByte even+24) := by
  have room := sib_room even
  have address : z.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (sibByte even+24+4) := by
    rw [x28, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 from rfl, ← BitVec.ofNat_add]
    try exact congrArg _ (by omega)
  have post := mask_post z .x28 0 (sibByte even+24) address (by omega) (by decide)
  have run := execute_mask z 588 .x28 0 (sibByte even+24) (by decide) pc rfl rfl rfl rfl address (by omega)
    (by omega) (by decide)
  have pm : (maskAfter z .x28 0).pc = pcAt 592 := by rw [post.pc, pc]; rfl
  have jump := arm_hop (maskAfter z .x28 0) 592 (.JAL .x0 116) (by decide) pm rfl rfl rfl
  exact ⟨run.thenDo jump, post⟩

theorem mid_pc (z : MachineState) (even : Bool) (pc : z.pc = pcAt 588)
    (x28 : z.getReg .x28 = BitVec.ofNat 64 (sibByte even+28)) : (t238Mid z).pc = pcAt 621 := by
  have room := sib_room even
  have address : z.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (sibByte even+24+4) := by
    rw [x28, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 from rfl, ← BitVec.ofNat_add]
    try exact congrArg _ (by omega)
  have post := mask_post z .x28 0 (sibByte even+24) address (by omega) (by decide)
  show (maskAfter z .x28 0).pc + signExtend21 116 = _
  rw [post.pc, pc]; rfl

/-! ### Words 593..620 (`x29 = 1`): gather the last sibling's top bits into its halfword 14 -/

def gatherState (z : MachineState) : Nat → MachineState
  | 0 => gatherStart z .x21
  | j+1 => chunkAfter (gatherState z j) .x21 .x7 (j+1)

def gatherVal (z : MachineState) (P : Nat) : Nat → Word
  | 0 => (spareHalf z P 0).zeroExtend 64 >>> 14
  | j+1 => gatherVal z P j ||| (((spareHalf z P (j+1)).zeroExtend 64 >>> 14) <<< (2*(j+1)))

theorem spare_half_congr {s t : MachineState} (same : ∀ a, t.getMem a = s.getMem a) (P j : Nat) :
    spareHalf t P j = spareHalf s P j := by
  simp only [spareHalf, MachineState.getHalfword, same]

theorem gather_state_facts (z : MachineState) (P : Nat) (pc : z.pc = pcAt 593)
    (baseReg : z.getReg .x21 = BitVec.ofNat 64 P) (room : 182 ≤ P) (even : P % 2 = 0) (fits : P ≤ MEMORY_BYTES)
    (j : Nat) (small : j ≤ 6) :
    GroupHop z (gatherState z j) (2+4*j) ∧ (gatherState z j).pc = pcAt (595+4*j) ∧
      (∀ a, (gatherState z j).getMem a = z.getMem a) ∧
      (∀ q, q ≠ .x31 → q ≠ .x7 → (gatherState z j).getReg q = z.getReg q) ∧
      (gatherState z j).getReg .x31 = gatherVal z P j := by
  induction j with
  | zero =>
    have post := gather_start_post z .x21 P baseReg room
    refine ⟨execute_gather_start z 593 .x21 P (by decide) pc rfl rfl baseReg room even fits, ?_, post.2.1,
      fun q a _ => post.2.2.1 q a, post.2.2.2⟩
    show (gatherStart z .x21).pc = _
    rw [post.1, pc]; rfl
  | succ j ih =>
    obtain ⟨run, pcj, mem, regs, val⟩ := ih (by omega)
    have base : (gatherState z j).getReg .x21 = BitVec.ofNat 64 P := (regs _ (by decide) (by decide)).trans baseReg
    have post := chunk_post (gatherState z j) .x21 .x7 (j+1) P base (by omega) room (by decide) (by decide)
    have jb : j < 6 := by omega
    have step := execute_chunk (gatherState z j) (595+4*j) .x21 .x7 (j+1) P (by omega) pcj
      (by interval_cases j <;> rfl) (by interval_cases j <;> rfl) (by interval_cases j <;> rfl)
      (by interval_cases j <;> rfl) base (by omega) room even fits
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := run.thenDo step
      rwa [show 2+4*j+4 = 2+4*(j+1) by omega] at this
    · show (chunkAfter (gatherState z j) .x21 .x7 (j+1)).pc = _
      rw [post.1, pcj, show pcAt (595+4*(j+1)) = pcAt (595+4*j) + 4 + 4 + 4 + 4 from ?_]
      simp only [pcAt, BitVec.add_assoc]
      rw [show (4 : Word) + (4 + (4 + 4)) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
      exact congrArg _ (by omega)
    · intro a
      exact (post.2.1 a).trans (mem a)
    · intro q a b
      exact (post.2.2.1 q a b).trans (regs q a b)
    · show (chunkAfter (gatherState z j) .x21 .x7 (j+1)).getReg .x31 = _
      rw [post.2.2.2, val, spare_half_congr mem]
      rfl

structure ShortPost (z t : MachineState) (dword : Nat) (value : Word) : Prop where
  pc : t.pc = pcAt 621
  x30 : t.getReg .x30 = BitVec.ofNat 64 28
  regs : ∀ q, q ≠ .x31 → q ≠ .x7 → q ≠ .x30 → t.getReg q = z.getReg q
  word : t.getMem (BitVec.ofNat 64 dword) = replaceWord32 (z.getMem (BitVec.ofNat 64 dword)) 1 (value.truncate 32)
  other : ∀ a, a ≠ BitVec.ofNat 64 dword → t.getMem a = z.getMem a

/-- Words 619..620 from any state: `sw x31,0(x28); addi x30,x0,28`. -/
def shortTail (g : MachineState) : MachineState :=
  execInstrBr (execInstrBr g (.SW .x28 .x31 0)) (.ADDI .x30 .x0 28)

theorem execute_short_tail (g : MachineState) (even : Bool) (pc : g.pc = pcAt 619)
    (x28 : g.getReg .x28 = BitVec.ofNat 64 (sibByte even+28)) :
    GroupHop g (shortTail g) 2 ∧ ShortPost g (shortTail g) (sibByte even+24) (g.getReg .x31) := by
  have sr := sib_room even
  have address : g.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (sibByte even+24+4) := by
    rw [x28, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 from rfl, ← BitVec.ofNat_add]
    try exact congrArg _ (by omega)
  have al := arm_align (sibByte even+24) 4 (by omega) (by decide)
  have off := arm_byte_offset (sibByte even+24) 4 (by omega) (by decide)
  have sw := arm_hop g 619 (.SW .x28 .x31 0) (by decide) pc rfl
    (sw_step g .x28 .x31 0 (by rw [address]; exact access_ofNat _ 4 (by omega) (by omega))) rfl
  let g1 := execInstrBr g (.SW .x28 .x31 0)
  have p1 : g1.pc = BitVec.ofNat 64 (4096+4*(619+1)) := pc_next pc rfl
  have last := arm_hop g1 (619+1) (.ADDI .x30 .x0 28) (by decide) p1 rfl rfl rfl
  have stored : g1 = (g.setMem (BitVec.ofNat 64 (sibByte even+24))
      (replaceWord32 (g.getMem (BitVec.ofNat 64 (sibByte even+24))) 1 ((g.getReg .x31).truncate 32))).setPC (g.pc + 4) := by
    show (g.setWord32 (g.getReg .x28 + signExtend12 0) ((g.getReg .x31).truncate 32)).setPC (g.pc + 4) = _
    rw [address]
    simp only [MachineState.setWord32, al, off]
  have outer : shortTail g = (g1.setReg .x30 (g1.getReg .x0 + signExtend12 28)).setPC (g1.pc + 4) := rfl
  refine ⟨sw.thenDo last, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [outer, arm_pc_set_pc, p1]; rfl
  · rw [outer, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x30 ≠ .x0 by decide)]
    rfl
  · intro q a b c
    rw [outer, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c), stored,
      MachineState.getReg_setPC, arm_getReg_set_mem]
  · rw [outer, arm_getMem_set_pc, arm_getMem_set_reg, stored, arm_getMem_set_pc, MachineState.getMem_setMem_eq]
  · intro a ha
    rw [outer, arm_getMem_set_pc, arm_getMem_set_reg, stored, arm_getMem_set_pc, MachineState.getMem_setMem_ne ha]

def t238Short (z : MachineState) : MachineState := shortTail (gatherState z 6)

theorem execute_short (z : MachineState) (even : Bool) (P : Nat) (pc : z.pc = pcAt 593)
    (baseReg : z.getReg .x21 = BitVec.ofNat 64 P) (room : 182 ≤ P) (evenP : P % 2 = 0) (fits : P ≤ MEMORY_BYTES)
    (x28 : z.getReg .x28 = BitVec.ofNat 64 (sibByte even+28)) :
    GroupHop z (t238Short z) 28 ∧ ShortPost z (t238Short z) (sibByte even+24) (gatherVal z P 6) := by
  obtain ⟨run, pcg, mem, regs, val⟩ := gather_state_facts z P pc baseReg room evenP fits 6 (by decide)
  show GroupHop z (shortTail (gatherState z 6)) 28 ∧
    ShortPost z (shortTail (gatherState z 6)) (sibByte even+24) (gatherVal z P 6)
  generalize gatherState z 6 = g at run pcg mem regs val ⊢
  have tail := execute_short_tail g even (by rw [pcg]; try rfl) ((regs _ (by decide) (by decide)).trans x28)
  obtain ⟨hop, post⟩ := tail
  refine ⟨run.thenDo hop, ⟨post.pc, post.x30, ?_, ?_, ?_⟩⟩
  · intro q a b c
    exact (post.regs q a b c).trans (regs q a b)
  · rw [post.word, mem, val]
  · intro a ha
    exact (post.other a ha).trans (mem a)

end TwoPermutationPrototype.Packed.Checker
