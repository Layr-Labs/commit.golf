import CommitGolfCandidate.GroupOpenWideCopy
import CommitGolfCandidate.GroupOpenShifted30

/-! The shared 30-byte copy stub (opening words 1062..1096) of writer levels 2..12.

Rows `225+35k` (`k = 0..10`, the sites `CopySite.sibling l` with `l = k+1`) hold `jal x29,<1062>`. The stub tests
`x21 & 3`: a destination that is 2 mod 4 enters the shifted-load path at row 1867 (27 cycles).
Otherwise it tests `x21 & 7`: 4 mod 8 copies seven words and the last halfword (22 cycles),
0 mod 8 three dwords, a word and the last halfword (16 cycles). The source (`x7`, a heap node) is 8-aligned. Every
path ends at the site's word `start+30` with only `x29` and `x31` changed. Built on the width-generic pairs of
`GroupOpenWideCopy`. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
set_option maxRecDepth 8192

/-! ### Code -/

/-- The stub's words, from row 1062, and the site's own pairs 1..14. -/
structure Stub30Code (site : CopySite) : Prop where
  entry : Decodes site.start (.JAL .x29 (BitVec.ofNat 21 (4*(1062-site.start))))
  test4 : Decodes 1062 (.ANDI .x31 .x21 3)
  four : Decodes (1062+1) (.BEQ .x31 .x0 16)
  shiftJump : Decodes (1062+2) (.JAL .x0 3212)
  shiftBack : Decodes 1889 (.JALR .x0 .x29 116)
  test8 : Decodes (1062+5) (.ANDI .x31 .x21 7)
  eight : Decodes (1062+6) (.BEQ .x31 .x0 72)
  words : PairsAt (1062+7) 7 4 .x7 0 0
  wordsHalf : PairsAt (1062+21) 1 2 .x7 28 28
  wordsBack : Decodes (1062+23) (.JALR .x0 .x29 116)
  dwords : PairsAt (1062+24) 3 8 .x7 0 0
  dwordsWord : PairsAt (1062+30) 1 4 .x7 24 24
  dwordsHalf : PairsAt (1062+32) 1 2 .x7 28 28
  dwordsBack : Decodes (1062+34) (.JALR .x0 .x29 116)

set_option maxHeartbeats 4000000 in
theorem stub30_code_all : ∀ l : Fin 13, 0 < l.val → l.val < 12 → Stub30Code (.sibling l) := by
  intro l h1 h2
  constructor <;> revert l <;> decide

theorem wide30_sibling (site : CopySite) (wide : site.wide30 = true) :
    ∃ l : Fin 13, site = .sibling l ∧ 0 < l.val ∧ l.val < 12 := by
  cases site with
  | sibling l =>
    simp only [CopySite.wide30, Bool.and_eq_true, decide_eq_true_eq] at wide
    exact ⟨l, rfl, wide.1, wide.2⟩
  | _ => simp [CopySite.wide30] at wide

theorem stub30_code (site : CopySite) (wide : site.wide30 = true) : Stub30Code site := by
  obtain ⟨l, rfl, h1, h2⟩ := wide30_sibling site wide
  exact stub30_code_all l h1 h2

structure SiteFacts30 (site : CopySite) : Prop where
  startFit : site.start+30 ≤ 1062
  jump : BitVec.ofNat 64 (4096+4*site.start) + signExtend21 (BitVec.ofNat 21 (4*(1062-site.start))) =
    BitVec.ofNat 64 (4096+4*1062)
  back116 : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 116) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+30))
  back4 : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 4) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+2))
  source : site.source = .x7
  offset : site.destOffset = 0
  halfwords : site.halfwords = 15
  notWide : site.wide = false

theorem site_facts30_all : ∀ l : Fin 13, 0 < l.val → l.val < 12 → SiteFacts30 (.sibling l) := by
  intro l h1 h2
  constructor <;> revert l <;> decide

theorem site_facts30 (site : CopySite) (wide : site.wide30 = true) : SiteFacts30 site := by
  obtain ⟨l, rfl, h1, h2⟩ := wide30_sibling site wide
  exact site_facts30_all l h1 h2

/-! ### Small facts -/

private theorem mem_setReg30 (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem getMem_eq30 {a b : MachineState} (same : a.mem = b.mem) (q : Word) : a.getMem q = b.getMem q := by
  unfold MachineState.getMem; rw [same]

theorem andi_imm_facts (u : MachineState) (imm : BitVec 12) :
    let v := execInstrBr u (.ANDI .x31 .x21 imm)
    v.pc = u.pc + 4 ∧ v.getReg .x31 = u.getReg .x21 &&& signExtend12 imm ∧ Moves u v .x31 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg30]

theorem and_three (T : Nat) (fit : T < 2^64) :
    BitVec.ofNat 64 T &&& signExtend12 3 = BitVec.ofNat 64 (T % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [show signExtend12 3 = (3#64 : Word) from rfl, BitVec.toNat_and,
    show (3#64 : Word).toNat = 2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  omega

theorem and_seven (T : Nat) (fit : T < 2^64) :
    BitVec.ofNat 64 T &&& signExtend12 7 = BitVec.ofNat 64 (T % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [show signExtend12 7 = (7#64 : Word) from rfl, BitVec.toNat_and,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  omega

/-! ### The stub paths -/

def entryJump30 (site : CopySite) : Instr := .JAL .x29 (BitVec.ofNat 21 (4*(1062-site.start)))

def enter30 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (entryJump30 site)) (.ANDI .x31 .x21 3)) (.BEQ .x31 .x0 16)

def slow30 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (enter30 site s) (.ANDI .x31 .x21 7)) (.BEQ .x31 .x0 72)

def half30Path (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (Shifted30.copy30 (execInstrBr (enter30 site s) (.JAL .x0 3212))) (.JALR .x0 .x29 116)

def word30Path (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 2 .x7 28 28 0 1 (pairsRun 4 .x7 0 0 0 7 (slow30 site s))) (.JALR .x0 .x29 116)

def dword30Path (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 2 .x7 28 28 0 1 (pairsRun 4 .x7 24 24 0 1 (pairsRun 8 .x7 0 0 0 3 (slow30 site s))))
    (.JALR .x0 .x29 116)

/-- The state after a 30-byte site's copy: the stub path picked by the destination's alignment. -/
def wide30State (site : CopySite) (s : MachineState) : MachineState :=
  if (s.getReg .x21).toNat % 4 = 0 then
    (if (s.getReg .x21).toNat % 8 = 0 then dword30Path site s else word30Path site s)
  else half30Path site s

/-- Cycles of a 30-byte site's copy into `target`: 16 (8-aligned), 22 (4 mod 8) or 27 (2 mod 4). -/
def wide30Cost (target : Nat) : Nat := if target % 4 = 0 then (if target % 8 = 0 then 16 else 22) else 27

structure Wide30Inputs (site : CopySite) (s : MachineState) (S T : Nat) : Prop where
  wide30 : site.wide30 = true
  pc : s.pc = BitVec.ofNat 64 (4096+4*site.start)
  src : s.getReg .x7 = BitVec.ofNat 64 S
  dst : s.getReg .x21 = BitVec.ofNat 64 T
  srcAligned : S % 8 = 0
  dstEven : T % 2 = 0
  apart : S+30 ≤ T
  room : T+30 ≤ MEMORY_BYTES

structure Entered30 (site : CopySite) (s e : MachineState) (S T : Nat) : Prop where
  x29 : e.getReg .x29 = BitVec.ofNat 64 (4096+4*(site.start+1))
  src : e.getReg .x7 = BitVec.ofNat 64 S
  dst : e.getReg .x21 = BitVec.ofNat 64 T
  mem : e.mem = s.mem
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → e.getReg r = s.getReg r

theorem enter30_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T) :
    RunsOpeningBlock s (enter30 site s) 3 ∧ Entered30 site s (enter30 site s) S T ∧
    (enter30 site s).pc = (if T % 4 = 0 then BitVec.ofNat 64 (4096+4*(1062+5))
      else BitVec.ofNat 64 (4096+4*(1062+2))) := by
  have facts := site_facts30 site input.wide30
  have code := stub30_code site input.wide30
  have sf := facts.startFit
  have fitT : T < 2^64 := by have := input.room; unfold MEMORY_BYTES at this; omega
  have run1 := run_step s site.start _ (by omega) input.pc code.entry rfl rfl
  obtain ⟨p1, x29a, m1⟩ := jal_facts s (BitVec.ofNat 21 (4*(1062-site.start)))
  generalize he1 : execInstrBr s (.JAL .x29 (BitVec.ofNat 21 (4*(1062-site.start)))) = e1 at p1 x29a m1
  have run1' : RunsOpeningBlock s e1 1 := by rw [← he1]; exact run1
  have pc1 : e1.pc = BitVec.ofNat 64 (4096+4*1062) := by rw [p1, input.pc]; exact facts.jump
  have run2 := run_step e1 1062 _ (by omega) pc1 code.test4 rfl rfl
  obtain ⟨p2, x31b, m2⟩ := andi_imm_facts e1 3
  generalize he2 : execInstrBr e1 (.ANDI .x31 .x21 3) = e2 at p2 x31b m2 run2
  have pc2 : e2.pc = BitVec.ofNat 64 (4096+4*(1062+1)) := by rw [p2, pc1, ofNat_four]
  have v31 : e2.getReg .x31 = BitVec.ofNat 64 (T % 4) := by
    rw [x31b, m1.regs .x21 (by decide), input.dst, and_three T fitT]
  have run3 := run_step e2 (1062+1) _ (by omega) pc2 code.four rfl rfl
  obtain ⟨p3, m3⟩ := beq_facts e2 16
  generalize he3 : execInstrBr e2 (.BEQ .x31 .x0 16) = e3 at p3 m3 run3
  have same : enter30 site s = e3 := by rw [← he3, ← he2, ← he1]; unfold enter30 entryJump30; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) (b : r ≠ .x29) : e3.getReg r = s.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m3.regs r z, m2.regs r a, m1.regs r b]
  have total := (run1'.next run2).next run3
  rw [show 1+1+1 = 3 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, keep⟩, ?_⟩
  · rw [m3.regs .x29 (by decide), m2.regs .x29 (by decide), x29a, input.pc, ofNat_four]
  · rw [keep .x7 (by decide) (by decide), input.src]
  · rw [keep .x21 (by decide) (by decide)]; exact input.dst
  · rw [m3.mem, m2.mem, m1.mem]
  · rw [p3, v31, pc2]
    have cls : T % 4 = 0 ∨ T % 4 = 2 := by have := input.dstEven; omega
    rcases cls with h | h <;> rw [h]
    · rw [if_pos rfl, if_pos rfl, show signExtend13 16 = BitVec.ofNat 64 (4*4) from rfl, ofNat_step]
    · rw [if_neg (by decide), if_neg (by decide), ofNat_four]

theorem slow30_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T)
    (fast : T % 4 = 0) :
    RunsOpeningBlock s (slow30 site s) 5 ∧ Entered30 site s (slow30 site s) S T ∧
    (slow30 site s).pc = (if T % 8 = 0 then BitVec.ofNat 64 (4096+4*(1062+24))
      else BitVec.ofNat 64 (4096+4*(1062+7))) := by
  have fitT : T < 2^64 := by have := input.room; unfold MEMORY_BYTES at this; omega
  have code := stub30_code site input.wide30
  obtain ⟨run3, entered, pc3⟩ := enter30_facts site s S T input
  rw [if_pos fast] at pc3
  generalize he3 : enter30 site s = e3 at run3 entered pc3
  have run4 := run_step e3 (1062+5) _ (by omega) pc3 code.test8 rfl rfl
  obtain ⟨p4, x31c, m4⟩ := andi_imm_facts e3 7
  generalize he4 : execInstrBr e3 (.ANDI .x31 .x21 7) = e4 at p4 x31c m4 run4
  have pc4 : e4.pc = BitVec.ofNat 64 (4096+4*(1062+6)) := by rw [p4, pc3, ofNat_four]
  have v31 : e4.getReg .x31 = BitVec.ofNat 64 (T % 8) := by
    rw [x31c, entered.dst, and_seven T fitT]
  have run5 := run_step e4 (1062+6) _ (by omega) pc4 code.eight rfl rfl
  obtain ⟨p5, m5⟩ := beq_facts e4 72
  generalize he5 : execInstrBr e4 (.BEQ .x31 .x0 72) = e5 at p5 m5 run5
  have same : slow30 site s = e5 := by rw [← he5, ← he4, ← he3]; unfold slow30; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) : e5.getReg r = e3.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m5.regs r z, m4.regs r a]
  have total := (run3.next run4).next run5
  rw [show 3+1+1 = 5 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keep .x29 (by decide)]; exact entered.x29
  · rw [keep .x7 (by decide)]; exact entered.src
  · rw [keep .x21 (by decide)]; exact entered.dst
  · rw [m5.mem, m4.mem]; exact entered.mem
  · intro r a b; rw [keep r a]; exact entered.regs r a b
  · rw [p5, v31, pc4]
    have cls : T % 8 = 0 ∨ T % 8 = 4 := by omega
    rcases cls with h | h <;> rw [h]
    · rw [if_pos rfl, if_pos rfl, show signExtend13 72 = BitVec.ofNat 64 (4*18) from rfl, ofNat_step]
    · rw [if_neg (by decide), if_neg (by decide), ofNat_four]

structure Wide30Done (site : CopySite) (s t : MachineState) (S T cost : Nat) : Prop where
  run : RunsOpeningBlock s t cost
  pc : t.pc = BitVec.ofNat 64 (4096+4*(site.start+30))
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 30
  below : ∀ q : Word, q.toNat < T - T % 8 → t.getMem q = s.getMem q

theorem half30_done (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T)
    (h : T % 4 ≠ 0) : Wide30Done site s (half30Path site s) S T 27 := by
  have facts := site_facts30 site input.wide30
  have code := stub30_code site input.wide30
  have room := input.room
  have apart := input.apart
  have ram : MEMORY_BYTES < 2^64 := by decide
  obtain ⟨run3, entered, pc3⟩ := enter30_facts site s S T input
  rw [if_neg h] at pc3
  let e := enter30 site s
  let j := execInstrBr e (.JAL .x0 3212)
  have runJ := run_step e 1064 _ (by decide) pc3 code.shiftJump rfl rfl
  have jpc : j.pc = BitVec.ofNat 64 (4096+4*1867) := by
    change e.pc + signExtend21 3212 = _
    rw [pc3]
    rfl
  have jregs (r : Reg) : j.getReg r = e.getReg r := by
    simp only [j, execInstrBr, MachineState.getReg_setPC, MachineState.setReg]
  have jmem : j.mem = e.mem := rfl
  have done := Shifted30.copy30_done j S T jpc
    ((jregs .x7).trans entered.src) ((jregs .x21).trans entered.dst)
    input.srcAligned (by have := input.dstEven; omega) apart (by omega) room
  let c := Shifted30.copy30 j
  have runBack := run_step c 1889 _ (by decide) done.pc code.shiftBack rfl rfl
  obtain ⟨pBack, mBack⟩ := jalr_facts c 116
  have same : half30Path site s = execInstrBr c (.JALR .x0 .x29 116) := rfl
  rw [same]
  refine ⟨((run3.next runJ).next done.run).next runBack, ?_, ?_, ?_, ?_⟩
  · rw [pBack, done.regs .x29 (by decide), jregs .x29, entered.x29]
    exact facts.back116
  · intro r a b
    rw [keep_x0 mBack, done.regs r a, jregs r, entered.regs r a b]
  · have copied := copy_congr_before (jmem.trans entered.mem).symm done.bytes
    exact copy_congr_mem mBack.mem copied
  · intro q below
    rw [getMem_eq30 mBack.mem, done.below q below]
    exact getMem_eq30 (jmem.trans entered.mem) q

theorem word30_done (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T)
    (h : T % 8 = 4) : Wide30Done site s (word30Path site s) S T 22 := by
  have facts := site_facts30 site input.wide30
  have code := stub30_code site input.wide30
  have sf := facts.startFit
  have room := input.room
  have apart := input.apart
  have sa := input.srcAligned
  obtain ⟨run5, entered, pc5⟩ := slow30_facts site s S T input (by omega)
  rw [if_neg (by omega)] at pc5
  generalize he5 : slow30 site s = e5 at run5 entered pc5
  have dst0 : e5.getReg .x21 + BitVec.ofNat 64 0 = BitVec.ofNat 64 T := by
    rw [entered.dst]; exact BitVec.add_zero _
  obtain ⟨runW, pcW, regsW, copyW, belowW⟩ := run_pairs 4 (by decide) .x7 (by decide) (1062+7) 0 0 S T
    (by omega) (by omega) 7 0 e5 (by simpa using code.words) (by omega) (by simpa using pc5) entered.src dst0
    (by omega) (by omega) (by omega) (by omega)
  generalize hw : pairsRun 4 .x7 0 0 0 7 e5 = w at runW pcW regsW copyW belowW
  have pcW' : w.pc = BitVec.ofNat 64 (4096+4*(1062+21+2*0)) := by rw [pcW]
  have srcW : w.getReg .x7 = BitVec.ofNat 64 S := by rw [regsW .x7 (by decide)]; exact entered.src
  have dstW : w.getReg .x21 + BitVec.ofNat 64 28 = BitVec.ofNat 64 (T+28) := by
    rw [regsW .x21 (by decide), entered.dst, ← BitVec.ofNat_add]
  obtain ⟨runH, pcH, regsH, copyH, belowH⟩ := run_pairs 2 (by decide) .x7 (by decide) (1062+21) 28 28 S (T+28)
    (by omega) (by omega) 1 0 w (by simpa using code.wordsHalf) (by omega) pcW' srcW dstW
    (by omega) (by omega) (by omega) (by omega)
  generalize hh : pairsRun 2 .x7 28 28 0 1 w = c at runH pcH regsH copyH belowH
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(1062+23)) := by rw [pcH]
  have runJ := run_step c (1062+23) _ (by omega) pcC code.wordsBack rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 116
  generalize hf : execInstrBr c (.JALR .x0 .x29 116) = f at pJ mJ runJ
  have same : word30Path site s = f := by rw [← hf, ← hh, ← hw, ← he5]; unfold word30Path; exact Eq.refl _
  rw [same]
  have total := ((run5.next runW).next runH).next runJ
  rw [show 5+2*7+2*1+1 = 22 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pJ, regsH .x29 (by decide), regsW .x29 (by decide), entered.x29]; exact facts.back116
  · intro r a b; rw [keep_x0 mJ r, regsH r a, regsW r a, entered.regs r a b]
  · have head : ByteCopy e5 w S T 28 := by simpa using copyW
    have tail : ByteCopy w c (S+28) (T+28) 2 := by simpa using copyH
    have whole := copy_extend head tail (by omega) (by unfold MEMORY_BYTES at room; omega)
    exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm whole)
  · intro q below
    rw [getMem_eq30 mJ.mem, belowH q (by omega), belowW q below, getMem_eq30 entered.mem]

theorem dword30_done (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T)
    (h : T % 8 = 0) : Wide30Done site s (dword30Path site s) S T 16 := by
  have facts := site_facts30 site input.wide30
  have code := stub30_code site input.wide30
  have sf := facts.startFit
  have room := input.room
  have apart := input.apart
  have sa := input.srcAligned
  obtain ⟨run5, entered, pc5⟩ := slow30_facts site s S T input (by omega)
  rw [if_pos h] at pc5
  generalize he5 : slow30 site s = e5 at run5 entered pc5
  have dst0 : e5.getReg .x21 + BitVec.ofNat 64 0 = BitVec.ofNat 64 T := by
    rw [entered.dst]; exact BitVec.add_zero _
  obtain ⟨runD, pcD, regsD, copyD, belowD⟩ := run_pairs 8 (by decide) .x7 (by decide) (1062+24) 0 0 S T
    (by omega) h 3 0 e5 (by simpa using code.dwords) (by omega) (by simpa using pc5) entered.src dst0
    (by omega) (by omega) (by omega) (by omega)
  generalize hd : pairsRun 8 .x7 0 0 0 3 e5 = d at runD pcD regsD copyD belowD
  have pcD' : d.pc = BitVec.ofNat 64 (4096+4*(1062+30+2*0)) := by rw [pcD]
  have srcD : d.getReg .x7 = BitVec.ofNat 64 S := by rw [regsD .x7 (by decide)]; exact entered.src
  have dstD : d.getReg .x21 + BitVec.ofNat 64 24 = BitVec.ofNat 64 (T+24) := by
    rw [regsD .x21 (by decide), entered.dst, ← BitVec.ofNat_add]
  obtain ⟨runW, pcW, regsW, copyW, belowW⟩ := run_pairs 4 (by decide) .x7 (by decide) (1062+30) 24 24 S (T+24)
    (by omega) (by omega) 1 0 d (by simpa using code.dwordsWord) (by omega) pcD' srcD dstD
    (by omega) (by omega) (by omega) (by omega)
  generalize hw : pairsRun 4 .x7 24 24 0 1 d = w at runW pcW regsW copyW belowW
  have pcW' : w.pc = BitVec.ofNat 64 (4096+4*(1062+32+2*0)) := by rw [pcW]
  have srcW : w.getReg .x7 = BitVec.ofNat 64 S := by rw [regsW .x7 (by decide), regsD .x7 (by decide)]; exact entered.src
  have dstW : w.getReg .x21 + BitVec.ofNat 64 28 = BitVec.ofNat 64 (T+28) := by
    rw [regsW .x21 (by decide), regsD .x21 (by decide), entered.dst, ← BitVec.ofNat_add]
  obtain ⟨runH, pcH, regsH, copyH, belowH⟩ := run_pairs 2 (by decide) .x7 (by decide) (1062+32) 28 28 S (T+28)
    (by omega) (by omega) 1 0 w (by simpa using code.dwordsHalf) (by omega) pcW' srcW dstW
    (by omega) (by omega) (by omega) (by omega)
  generalize hh : pairsRun 2 .x7 28 28 0 1 w = c at runH pcH regsH copyH belowH
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(1062+34)) := by rw [pcH]
  have runJ := run_step c (1062+34) _ (by omega) pcC code.dwordsBack rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 116
  generalize hf : execInstrBr c (.JALR .x0 .x29 116) = f at pJ mJ runJ
  have same : dword30Path site s = f := by
    rw [← hf, ← hh, ← hw, ← hd, ← he5]; unfold dword30Path; exact Eq.refl _
  rw [same]
  have total := (((run5.next runD).next runW).next runH).next runJ
  rw [show 5+2*3+2*1+2*1+1 = 16 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pJ, regsH .x29 (by decide), regsW .x29 (by decide), regsD .x29 (by decide), entered.x29]
    exact facts.back116
  · intro r a b; rw [keep_x0 mJ r, regsH r a, regsW r a, regsD r a, entered.regs r a b]
  · have head : ByteCopy e5 d S T 24 := by simpa using copyD
    have mid : ByteCopy d w (S+24) (T+24) 4 := by simpa using copyW
    have tail : ByteCopy w c (S+28) (T+28) 2 := by simpa using copyH
    have first := copy_extend head mid (by omega) (by unfold MEMORY_BYTES at room; omega)
    have whole := copy_extend first tail (by omega) (by unfold MEMORY_BYTES at room; omega)
    exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm whole)
  · intro q below
    rw [getMem_eq30 mJ.mem, belowH q (by omega), belowW q (by omega), belowD q below, getMem_eq30 entered.mem]

/-- A 30-byte site's copy: the cycles depend on the destination's alignment, everything else is as for the
halfword copy it replaces (`x29` is clobbered too). -/
theorem wide30_copy (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T) :
    Wide30Done site s (wide30State site s) S T (wide30Cost T) := by
  have fitT : T < 2^64 := by have := input.room; unfold MEMORY_BYTES at this; omega
  have low : (s.getReg .x21).toNat = T := by rw [input.dst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fitT]
  unfold wide30State wide30Cost
  rw [low]
  by_cases h4 : T % 4 = 0
  · rw [if_pos h4, if_pos h4]
    by_cases h8 : T % 8 = 0
    · rw [if_pos h8, if_pos h8]; exact dword30_done site s S T input h8
    · rw [if_neg h8, if_neg h8]; exact word30_done site s S T input (by omega)
  · rw [if_neg h4, if_neg h4]; exact half30_done site s S T input h4

/-- Whatever the inputs, a 30-byte site's copy changes no register but `x29` and `x31`. -/
theorem wide30_regs (site : CopySite) (s : MachineState) (r : Reg) (a : r ≠ .x31) (b : r ≠ .x29) :
    (wide30State site s).getReg r = s.getReg r := by
  have enter : (enter30 site s).getReg r = s.getReg r := by
    unfold enter30 entryJump30
    rw [keep_x0 (beq_facts _ 16).2, (andi_imm_facts _ 3).2.2.regs r a, (jal_facts _ _).2.2.regs r b]
  have slow : (slow30 site s).getReg r = s.getReg r := by
    unfold slow30
    rw [keep_x0 (beq_facts _ 72).2, (andi_imm_facts _ 7).2.2.regs r a, enter]
  unfold wide30State
  split
  · split
    · unfold dword30Path
      rw [keep_x0 (jalr_facts _ 116).2, pairs_regs _ _ _ _ r a, pairs_regs _ _ _ _ r a, pairs_regs _ _ _ _ r a, slow]
    · unfold word30Path
      rw [keep_x0 (jalr_facts _ 116).2, pairs_regs _ _ _ _ r a, pairs_regs _ _ _ _ r a, slow]
  · unfold half30Path
    rw [keep_x0 (jalr_facts _ 116).2, Shifted30.copy30_regs _ r a]
    change (enter30 site s).getReg r = s.getReg r
    exact enter

end TwoPermutationPrototype.GroupedOpening
