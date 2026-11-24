import CommitGolfCandidate.GroupOpenWideCopy28

/-! Inline aligned 30-byte writer copies, with a shared shifted path for halfword destinations. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
open Wide Shifted30 CapCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def entryJump30 (site : CopySite) : BitVec 21 :=
  BitVec.ofNat 21 (4*(1067-(site.start+2)))

structure Stub30Code (site : CopySite) : Prop where
  test4 : Decodes site.start (.ANDI .x31 .x21 3)
  four : Decodes (site.start+1) (.BEQ .x31 .x0 8)
  enter : Decodes (site.start+2) (.JAL .x29 (entryJump30 site))
  test8 : Decodes (site.start+3) (.ANDI .x31 .x21 7)
  eight : Decodes (site.start+4) (.BEQ .x31 .x0 64)
  words : PairsAt (site.start+5) 7 4 .x7 0 0
  wordsBack : Decodes (site.start+19) (.JAL .x0 36)
  dwords : PairsAt (site.start+20) 3 8 .x7 0 0
  dwordsWord : PairsAt (site.start+26) 1 4 .x7 24 24
  half : PairsAt (site.start+28) 1 2 .x7 28 28

private theorem sibling30_code : ∀ l : Fin 13, 0 < l.val → l.val < 12 →
    Stub30Code (.sibling l) := by
  intro l low high
  constructor <;> revert l <;> decide +kernel

theorem stub30_code (site : CopySite) (wide : site.wide30 = true) : Stub30Code site := by
  cases site with
  | nonce => simp [CopySite.wide30] at wide
  | cap => simp [CopySite.wide30] at wide
  | quartet j => simp [CopySite.wide30] at wide
  | firstSibling => simp [CopySite.wide30] at wide
  | sibling l =>
    have h : 0 < l.val ∧ l.val < 12 := by simpa [CopySite.wide30] using wide
    exact sibling30_code l h.1 h.2

structure SiteFacts30 (site : CopySite) : Prop where
  startFit : site.start+30 ≤ 1062
  source : site.source = .x7
  offset : site.destOffset = 0
  halfwords : site.halfwords = 15
  enter : BitVec.ofNat 64 (4096+4*(site.start+2))+signExtend21 (entryJump30 site) =
    BitVec.ofNat 64 (4096+4*1067)
  back : (BitVec.ofNat 64 (4096+4*(site.start+2))+4+signExtend12 108) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+30))

private theorem sibling30_facts : ∀ l : Fin 13, 0 < l.val → l.val < 12 →
    SiteFacts30 (.sibling l) := by
  intro l low high
  constructor <;> revert l <;> decide +kernel

theorem site_facts30 (site : CopySite) (wide : site.wide30 = true) : SiteFacts30 site := by
  cases site with
  | nonce => simp [CopySite.wide30] at wide
  | cap => simp [CopySite.wide30] at wide
  | quartet j => simp [CopySite.wide30] at wide
  | firstSibling => simp [CopySite.wide30] at wide
  | sibling l =>
    have h : 0 < l.val ∧ l.val < 12 := by simpa [CopySite.wide30] using wide
    exact sibling30_facts l h.1 h.2

private theorem shifted30_code : ∀ k : Fin 4,
    CodeAt (1067+6*k.val) (chunkCode (8*k.val) (decide (k.val=3))) := by
  unfold CodeAt; decide +kernel

def enter30 (_site : CopySite) (s : MachineState) := Writer28.testState s 3 8
def aligned30 (site : CopySite) (s : MachineState) := Writer28.testState (enter30 site s) 7 64
def word30Path (site : CopySite) (s : MachineState) :=
  pairsRun 2 .x7 28 28 0 1
    (execInstrBr (pairsRun 4 .x7 0 0 0 7 (aligned30 site s)) (.JAL .x0 36))
def dword30Path (site : CopySite) (s : MachineState) :=
  pairsRun 2 .x7 28 28 0 1
    (pairsRun 4 .x7 24 24 0 1 (pairsRun 8 .x7 0 0 0 3 (aligned30 site s)))
def half30Path (site : CopySite) (s : MachineState) :=
  execInstrBr (copy30 (execInstrBr (enter30 site s) (.JAL .x29 (entryJump30 site)))) (.JALR .x0 .x29 108)
def wide30State (site : CopySite) (s : MachineState) : MachineState :=
  if (s.getReg .x21).toNat % 4 = 0 then
    if (s.getReg .x21).toNat % 8 = 0 then dword30Path site s else word30Path site s
  else half30Path site s

def wide30Cost (target : Nat) : Nat :=
  if target % 4 = 0 then (if target % 8 = 0 then 14 else 21) else 26

structure Wide30Inputs (site : CopySite) (s : MachineState) (S T : Nat) : Prop where
  wide30 : site.wide30 = true
  pc : s.pc = BitVec.ofNat 64 (4096+4*site.start)
  src : s.getReg .x7 = BitVec.ofNat 64 S
  dst : s.getReg .x21 = BitVec.ofNat 64 T
  srcAligned : S % 8 = 0
  dstEven : T % 2 = 0
  apart : S+30 ≤ T
  room : T+30 ≤ MEMORY_BYTES

structure Wide30Done (site : CopySite) (s t : MachineState) (S T n : Nat) : Prop where
  run : RunsOpeningBlock s t n
  pc : t.pc = BitVec.ofNat 64 (4096+4*(site.start+30))
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 30
  below : ∀ q : Word, q.toNat < T-T%8 → t.getMem q = s.getMem q

theorem word30_done (site : CopySite) (s : MachineState) (S T : Nat)
    (input : Wide30Inputs site s S T)
    (pc : (aligned30 site s).pc=BitVec.ofNat 64 (4096+4*(site.start+5)))
    (regs : ∀ r, r ≠ .x31 → (aligned30 site s).getReg r=s.getReg r)
    (ta : T%4=0) : Done (aligned30 site s) (word30Path site s) S T 30 17 (site.start+30) := by
  have f := site_facts30 site input.wide30
  have bound := f.startFit
  have c := stub30_code site input.wide30
  have src : (aligned30 site s).getReg .x7=BitVec.ofNat 64 S := by
    rw [regs _ (by decide)]; exact input.src
  have dst : (aligned30 site s).getReg .x21=BitVec.ofNat 64 T := by
    rw [regs _ (by decide)]; exact input.dst
  have a := pairs (aligned30 site s) S T (site.start+5) 0 4 7 (by omega) c.words
    (by omega) pc src dst (by have := input.srcAligned; omega) (by omega)
    (by decide) (by have := input.apart; omega) (by have := input.room; omega)
  generalize hw : pairsRun 4 .x7 0 0 0 7 (aligned30 site s) = w at a
  have apc : w.pc=BitVec.ofNat 64 (4096+4*(site.start+19)) := by
    simpa [Nat.add_assoc] using a.pc
  have jr := run_step w (site.start+19) _ (by omega) apc c.wordsBack rfl rfl
  have jp : (execInstrBr w (.JAL .x0 36)).pc =
      BitVec.ofNat 64 (4096+4*(site.start+28)) := by
    change w.pc+signExtend21 36=_
    rw [apc, show signExtend21 36=BitVec.ofNat 64 (4*9) from rfl, ofNat_step]
  have b : Done (aligned30 site s) (execInstrBr w (.JAL .x0 36)) S T 28 15 (site.start+28) := by
    have mem : (execInstrBr w (.JAL .x0 36)).mem=w.mem := rfl
    refine ⟨a.run.next jr, jp, ?_, copy_congr_mem mem a.bytes, ?_⟩
    · intro r h
      have keep : (execInstrBr w (.JAL .x0 36)).getReg r=w.getReg r := by cases r <;> rfl
      exact keep.trans (a.regs r h)
    · intro q low; rw [getMem_congr mem, a.below q low]
  have h := pairs _ S T (site.start+28) 28 2 1 (by omega) c.half (by omega) b.pc
    ((b.regs _ (by decide)).trans src) ((b.regs _ (by decide)).trans dst)
    (by have := input.srcAligned; omega) (by omega) (by decide) input.apart input.room
  unfold word30Path
  rw [hw]
  simpa [Nat.add_assoc] using append b h input.apart input.room

theorem dword30_done (site : CopySite) (s : MachineState) (S T : Nat)
    (input : Wide30Inputs site s S T)
    (pc : (aligned30 site s).pc=BitVec.ofNat 64 (4096+4*(site.start+20)))
    (regs : ∀ r, r ≠ .x31 → (aligned30 site s).getReg r=s.getReg r)
    (ta : T%8=0) : Done (aligned30 site s) (dword30Path site s) S T 30 10 (site.start+30) := by
  have f := site_facts30 site input.wide30
  have bound := f.startFit
  have c := stub30_code site input.wide30
  have src : (aligned30 site s).getReg .x7=BitVec.ofNat 64 S := by
    rw [regs _ (by decide)]; exact input.src
  have dst : (aligned30 site s).getReg .x21=BitVec.ofNat 64 T := by
    rw [regs _ (by decide)]; exact input.dst
  have a := pairs (aligned30 site s) S T (site.start+20) 0 8 3 (by omega) c.dwords
    (by omega) pc src dst input.srcAligned (by omega) (by decide)
    (by have := input.apart; omega) (by have := input.room; omega)
  have b := pairs _ S T (site.start+26) 24 4 1 (by omega) c.dwordsWord (by omega)
    (by simpa [Nat.add_assoc] using a.pc) ((a.regs _ (by decide)).trans src)
    ((a.regs _ (by decide)).trans dst) (by have := input.srcAligned; omega) (by omega)
    (by decide) (by have := input.apart; omega) (by have := input.room; omega)
  have ab := append a b (by have := input.apart; omega) (by have := input.room; omega)
  have h := pairs _ S T (site.start+28) 28 2 1 (by omega) c.half (by omega)
    (by simpa [Nat.add_assoc] using b.pc) ((ab.regs _ (by decide)).trans src)
    ((ab.regs _ (by decide)).trans dst) (by have := input.srcAligned; omega) (by omega)
    (by decide) input.apart input.room
  simpa [dword30Path, Nat.add_assoc] using append ab h input.apart input.room

theorem half30_done (site : CopySite) (s : MachineState) (S T : Nat)
    (input : Wide30Inputs site s S T) (ta : T%4=2)
    (ran : RunsOpeningBlock s (enter30 site s) 2)
    (pc : (enter30 site s).pc=BitVec.ofNat 64 (4096+4*(site.start+2)))
    (regs : ∀ r, r ≠ .x31 → (enter30 site s).getReg r=s.getReg r)
    (mem : (enter30 site s).mem=s.mem) : Wide30Done site s (half30Path site s) S T 26 := by
  have f := site_facts30 site input.wide30
  have bound := f.startFit
  have c := stub30_code site input.wide30
  let a := execInstrBr (enter30 site s) (.JAL .x29 (entryJump30 site))
  have ja := run_step _ (site.start+2) _ (by omega) pc c.enter rfl rfl
  obtain ⟨pa, va, ma⟩ := jal_facts (enter30 site s) (entryJump30 site)
  have apc : a.pc=BitVec.ofNat 64 (4096+4*1067) := by rw [pa, pc, f.enter]
  have ar (r : Reg) (h : r ≠ .x29) : a.getReg r=(enter30 site s).getReg r := ma.regs r h
  have am : a.mem=(enter30 site s).mem := ma.mem
  have asrc : a.getReg .x7=BitVec.ofNat 64 S := by
    rw [ar _ (by decide), regs _ (by decide)]; exact input.src
  have adst : a.getReg .x21=BitVec.ofNat 64 T := by
    rw [ar _ (by decide), regs _ (by decide)]; exact input.dst
  have d := copy30_done 1067 a S T (by decide) shifted30_code apc asrc adst input.srcAligned ta
    input.apart (by have := input.apart; have := input.room; omega) input.room
  have back := run_step _ 1089 _ (by decide) d.pc (by decide +kernel : Decodes 1089 (.JALR .x0 .x29 108)) rfl rfl
  obtain ⟨pb, mb⟩ := jalr_facts (copy30 a) 108
  change Wide30Done site s (execInstrBr (copy30 a) (.JALR .x0 .x29 108)) S T 26
  refine ⟨((ran.next ja).next d.run).next back, ?_, ?_, ?_, ?_⟩
  · rw [pb, d.regs .x29 (by decide), va, pc, f.back]
  · intro r h k
    rw [keep_x0 mb r, d.regs r h, ar r k, regs r h]
  · exact copy_congr_mem mb.mem (copy_congr_before ((am.trans mem).symm) d.bytes)
  · intro q low
    rw [getMem_congr mb.mem, d.below q low, getMem_congr am, getMem_congr mem]

theorem wide30_copy (site : CopySite) (s : MachineState) (S T : Nat) (input : Wide30Inputs site s S T) :
    Wide30Done site s (wide30State site s) S T (wide30Cost T) := by
  have f := site_facts30 site input.wide30
  have bound := f.startFit
  have c := stub30_code site input.wide30
  have fit : T<2^64 := by have := input.room; unfold MEMORY_BYTES at this; omega
  have dst : s.getReg .x21=BitVec.ofNat 64 T := input.dst
  have low : (s.getReg .x21).toNat=T := by rw [dst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  obtain ⟨ra, pa, ga, ma⟩ := Writer28.test s T site.start 4 3 8 (by omega) input.pc c.test4 c.four
    (by decide) (mask_bits s T 3 (by simp) dst fit)
  change RunsOpeningBlock s (enter30 site s) 2 at ra
  change (enter30 site s).pc=_ at pa
  change (∀ r, r ≠ .x31 → (enter30 site s).getReg r=s.getReg r) at ga
  change (enter30 site s).mem=s.mem at ma
  unfold wide30State wide30Cost
  rw [low]
  by_cases four : T%4=0
  · rw [if_pos four, if_pos four]
    have pca : (enter30 site s).pc=BitVec.ofNat 64 (4096+4*(site.start+3)) := by
      rw [if_pos four, show signExtend13 8=BitVec.ofNat 64 (4*2) from rfl, ofNat_step] at pa
      simpa [Nat.add_assoc] using pa
    obtain ⟨rb, pb, gb, mb⟩ := Writer28.test (enter30 site s) T (site.start+3) 8 7 64
      (by omega) pca c.test8 (by simpa [Nat.add_assoc] using c.eight) (by decide)
      (mask_bits _ T 7 (by simp) ((ga _ (by decide)).trans dst) fit)
    have regs (r : Reg) (h : r ≠ .x31) : (aligned30 site s).getReg r=s.getReg r :=
      (gb r h).trans (ga r h)
    by_cases eight : T%8=0
    · rw [if_pos eight, if_pos eight]
      have pcb : (aligned30 site s).pc=BitVec.ofNat 64 (4096+4*(site.start+20)) := by
        rw [if_pos eight, show signExtend13 64=BitVec.ofNat 64 (4*16) from rfl, ofNat_step] at pb
        simpa [aligned30, Nat.add_assoc] using pb
      have d := dword30_done site s S T input pcb regs eight
      have total := before ra ga ma (before rb gb mb d)
      exact ⟨total.run, total.pc, fun r h _ => total.regs r h, total.bytes, total.below⟩
    · rw [if_neg eight, if_neg eight]
      have pcb : (aligned30 site s).pc=BitVec.ofNat 64 (4096+4*(site.start+5)) := by
        rw [if_neg eight] at pb
        simpa [aligned30, Nat.add_assoc] using pb
      have d := word30_done site s S T input pcb regs four
      have total := before ra ga ma (before rb gb mb d)
      exact ⟨total.run, total.pc, fun r h _ => total.regs r h, total.bytes, total.below⟩
  · rw [if_neg four, if_neg four]
    exact half30_done site s S T input (by have := input.dstEven; omega) ra (by simpa [four] using pa) ga ma

theorem wide30_regs (site : CopySite) (s : MachineState) (r : Reg) (h : r ≠ .x31) (k : r ≠ .x29) :
    (wide30State site s).getReg r=s.getReg r := by
  have test (s : MachineState) (mask : BitVec 12) (off : BitVec 13) :
      (Writer28.testState s mask off).getReg r=s.getReg r := by
    unfold Writer28.testState
    rw [keep_x0 (beq_facts _ off).2, (andi_facts _ mask).2.2.regs r h]
  have enter : (enter30 site s).getReg r=s.getReg r := test s 3 8
  have aligned : (aligned30 site s).getReg r=s.getReg r := (test _ 7 64).trans enter
  have jump (u : MachineState) : (execInstrBr u (.JAL .x0 36)).getReg r=u.getReg r := by cases r <;> rfl
  unfold wide30State
  split
  · split
    · unfold dword30Path
      rw [pairs_regs _ _ _ _ r h, pairs_regs _ _ _ _ r h, pairs_regs _ _ _ _ r h, aligned]
    · unfold word30Path
      rw [pairs_regs _ _ _ _ r h, jump, pairs_regs _ _ _ _ r h, aligned]
  · unfold half30Path
    rw [keep_x0 (jalr_facts _ 108).2 r, copy30_regs _ r h,
      (jal_facts _ (entryJump30 site)).2.2.regs r k, enter]

end TwoPermutationPrototype.GroupedOpening
