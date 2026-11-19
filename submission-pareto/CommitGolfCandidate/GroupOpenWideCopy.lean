import CommitGolfCandidate.GroupOpenWideCopyCore
import CommitGolfCandidate.GroupOpenShifted32

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
set_option maxRecDepth 8192
open Wide

/-! ### The stub paths -/

def entryJump (site : CopySite) : Instr := .JAL .x29 (BitVec.ofNat 21 (4*(site.stub-site.start)))

def enterState (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (entryJump site)) (.ANDI .x31 .x21 3)) (.BNE .x31 .x0 (BitVec.ofNat 13 (8192+4*(site.start+1)-4*(site.stub+1))))

def slowState (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (enterState site s) (.ANDI .x31 .x21 7)) (.BNE .x31 .x0 52)

def dwordPath (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 8 site.source 0 site.destOffset 0 4 (slowState site s)) (.JALR .x0 .x29 124)

def wordPath (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 4 site.source 0 site.destOffset 0 8 (slowState site s)) (.JALR .x0 .x29 124)

def halfPath (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (Shifted32.copy32 site (enterState site s)) (.JAL .x0 28)

/-- The state after a wide site's copy: the stub path picked by the destination's alignment. -/
def wideState (site : CopySite) (s : MachineState) : MachineState :=
  if (s.getReg .x21).toNat % 8 = 0 then dwordPath site s
  else if (s.getReg .x21).toNat % 8 = 4 then wordPath site s else halfPath site s

/-- Cycles of a wide copy: 14 (8-aligned), 22 (4-aligned), or 28. -/
def wideCost (target : Nat) : Nat := if target % 8 = 0 then 14 else if target % 8 = 4 then 22 else 28

structure WideInputs (site : CopySite) (s : MachineState) (S T : Nat) : Prop where
  wide : site.wide = true
  pc : s.pc = BitVec.ofNat 64 (4096+4*site.start)
  src : s.getReg site.source = BitVec.ofNat 64 S
  dst : s.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 T
  srcAligned : S % 8 = 0
  dstEven : T % 2 = 0
  apart : S+32 ≤ T
  room : T+32 ≤ MEMORY_BYTES

structure SiteFacts (site : CopySite) : Prop where
  startFit : site.start+32 ≤ 1062
  stubFit : site.stub+33 ≤ 1062
  jump : BitVec.ofNat 64 (4096+4*site.start) + signExtend21 (BitVec.ofNat 21 (4*(site.stub-site.start))) =
    BitVec.ofNat 64 (4096+4*site.stub)
  back124 : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 124) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+32))
  slowTarget : BitVec.ofNat 64 (4096+4*(site.stub+1)) +
    signExtend13 (BitVec.ofNat 13 (8192+4*(site.start+1)-4*(site.stub+1))) =
      BitVec.ofNat 64 (4096+4*(site.start+1))
  back4 : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 4) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+2))
  src31 : site.source ≠ .x31
  src29 : site.source ≠ .x29
  src0 : site.source ≠ .x0
  offAligned : site.destOffset % 8 = 0
  offSmall : site.destOffset+32 ≤ 2000

theorem site_facts (site : CopySite) (wide : site.wide = true) : SiteFacts site := by
  cases site with
  | quartet j => clear wide; constructor <;> revert j <;> decide
  | firstSibling => constructor <;> decide
  | _ => simp [CopySite.wide] at wide

private theorem low_bits (x : Word) (d T : Nat) (fit : T < 2^64) (aligned : d % 8 = 0)
    (sum : x + BitVec.ofNat 64 d = BitVec.ofNat 64 T) :
    x.toNat % 8 = T % 8 ∧ x &&& signExtend12 7 = BitVec.ofNat 64 (T % 8) := by
  have total := congrArg BitVec.toNat sum
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit] at total
  have low : x.toNat % 8 = T % 8 := by
    have dm : d % 2^64 % 8 = 0 := by rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2^64)]; exact aligned
    rw [← total, Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2^64)]
    omega
  refine ⟨low, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [show signExtend12 7 = (7#64 : Word) from rfl, BitVec.toNat_and,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

private theorem zero_reg (u : MachineState) : u.getReg .x0 = 0#64 := rfl

private theorem plain_valid (u : MachineState) (i : Instr) (none : memAccess u i = none) :
    memoryArgumentsValid u i = true := by
  unfold memoryArgumentsValid; rw [none]

structure Moves (u v : MachineState) (changed : Reg) : Prop where
  regs : ∀ r, r ≠ changed → v.getReg r = u.getReg r
  mem : v.mem = u.mem

theorem jal_facts (u : MachineState) (off : BitVec 21) :
    let v := execInstrBr u (.JAL .x29 off)
    v.pc = u.pc + signExtend21 off ∧ v.getReg .x29 = u.pc + 4 ∧ Moves u v .x29 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem andi_facts (u : MachineState) (imm : BitVec 12) :
    let v := execInstrBr u (.ANDI .x31 .x21 imm)
    v.pc = u.pc + 4 ∧ v.getReg .x31 = u.getReg .x21 &&& signExtend12 imm ∧ Moves u v .x31 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem addi_facts (u : MachineState) :
    let v := execInstrBr u (.ADDI .x31 .x31 4092)
    v.pc = u.pc + 4 ∧ v.getReg .x31 = u.getReg .x31 + signExtend12 4092 ∧ Moves u v .x31 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem beq_facts (u : MachineState) (off : BitVec 13) :
    let v := execInstrBr u (.BEQ .x31 .x0 off)
    v.pc = (if u.getReg .x31 = 0#64 then u.pc + signExtend13 off else u.pc + 4) ∧ Moves u v .x0 := by
  refine ⟨?_, fun r _ => ?_, ?_⟩
  · simp only [execInstrBr, zero_reg]
    by_cases h : u.getReg .x31 = 0#64 <;> simp [h, MachineState.setPC]
  · simp only [execInstrBr]; split <;> rfl
  · simp only [execInstrBr]; split <;> rfl

theorem bne_facts (u : MachineState) (off : BitVec 13) :
    let v := execInstrBr u (.BNE .x31 .x0 off)
    v.pc = (if u.getReg .x31 = 0#64 then u.pc + 4 else u.pc + signExtend13 off) ∧ Moves u v .x0 := by
  refine ⟨?_, fun r _ => ?_, ?_⟩
  · simp only [execInstrBr, zero_reg]
    by_cases h : u.getReg .x31 = 0#64 <;> simp [h, MachineState.setPC]
  · simp only [execInstrBr]; split <;> rfl
  · simp only [execInstrBr]; split <;> rfl

theorem jalr_facts (u : MachineState) (off : BitVec 12) :
    let v := execInstrBr u (.JALR .x0 .x29 off)
    v.pc = (u.getReg .x29 + signExtend12 off) &&& ~~~1#64 ∧ Moves u v .x0 := by
  refine ⟨rfl, fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem copy_zero (s : MachineState) (S T : Nat) : ByteCopy s s S T 0 :=
  ⟨fun i h => absurd h (by omega), fun _ _ => rfl⟩

theorem copy_after {s t u : MachineState} {S T n : Nat} (copy : ByteCopy s t S T n) (same : u.mem = t.mem) :
    ByteCopy s u S T n := copy_congr_mem same copy

structure Entered (site : CopySite) (s e : MachineState) (S T : Nat) : Prop where
  x29 : e.getReg .x29 = BitVec.ofNat 64 (4096+4*(site.start+1))
  src : e.getReg site.source = BitVec.ofNat 64 S
  dst : e.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 T
  mem : e.mem = s.mem
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → e.getReg r = s.getReg r

theorem moves_reg {u v : MachineState} {changed : Reg} (m : Moves u v changed) (r : Reg) (h : r ≠ changed)
    (zero : changed = .x0 → r ≠ .x0 ∨ True := fun _ => Or.inr trivial) : v.getReg r = u.getReg r := m.regs r h

theorem x0_any (u v : MachineState) : v.getReg .x0 = u.getReg .x0 := rfl

theorem enter_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T) :
    RunsOpeningBlock s (enterState site s) 3 ∧ Entered site s (enterState site s) S T ∧
    (enterState site s).getReg .x31 = BitVec.ofNat 64 (T % 4) ∧
    (enterState site s).pc = (if T % 4 = 0 then BitVec.ofNat 64 (4096+4*(site.stub+2))
      else BitVec.ofNat 64 (4096+4*(site.start+1))) := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  obtain ⟨low, andBits⟩ := low_bits (s.getReg .x21) site.destOffset T
    (by have := input.room; unfold MEMORY_BYTES at this; omega) facts.offAligned input.dst
  have andBits4 : s.getReg .x21 &&& signExtend12 3 = BitVec.ofNat 64 (T % 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [show signExtend12 3 = (3#64 : Word) from rfl, BitVec.toNat_and,
      show (3#64 : Word).toNat = 2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
    omega
  have run1 := run_step s site.start _ (by omega) input.pc code.entry rfl rfl
  obtain ⟨p1, x29a, m1⟩ := jal_facts s (BitVec.ofNat 21 (4*(site.stub-site.start)))
  generalize he1 : execInstrBr s (.JAL .x29 (BitVec.ofNat 21 (4*(site.stub-site.start)))) = e1 at p1 x29a m1
  have run1' : RunsOpeningBlock s e1 1 := by rw [← he1]; exact run1
  have pc1 : e1.pc = BitVec.ofNat 64 (4096+4*site.stub) := by rw [p1, input.pc]; exact facts.jump
  have run2 := run_step e1 site.stub _ (by omega) pc1 code.test rfl rfl
  obtain ⟨p2, x31b, m2⟩ := andi_facts e1 3
  generalize he2 : execInstrBr e1 (.ANDI .x31 .x21 3) = e2 at p2 x31b m2 run2
  have pc2 : e2.pc = BitVec.ofNat 64 (4096+4*(site.stub+1)) := by rw [p2, pc1, ofNat_four]
  have v31 : e2.getReg .x31 = BitVec.ofNat 64 (T % 4) := by rw [x31b, m1.regs .x21 (by decide), andBits4]
  have run3 := run_step e2 (site.stub+1) _ (by omega) pc2 code.shifted rfl rfl
  obtain ⟨p3, m3⟩ := bne_facts e2 (BitVec.ofNat 13 (8192+4*(site.start+1)-4*(site.stub+1)))
  generalize he3 : execInstrBr e2 (.BNE .x31 .x0 (BitVec.ofNat 13 (8192+4*(site.start+1)-4*(site.stub+1)))) = e3 at p3 m3 run3
  have same : enterState site s = e3 := by rw [← he3, ← he2, ← he1]; unfold enterState entryJump; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) (b : r ≠ .x29) : e3.getReg r = s.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m3.regs r z, m2.regs r a, m1.regs r b]
  have total := (run1'.next run2).next run3
  rw [show 1+1+1 = 3 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, keep⟩, by rw [m3.regs .x31 (by decide), v31], ?_⟩
  · rw [m3.regs .x29 (by decide), m2.regs .x29 (by decide), x29a, input.pc, ofNat_four]
  · rw [keep _ facts.src31 facts.src29, input.src]
  · rw [keep .x21 (by decide) (by decide)]; exact input.dst
  · rw [m3.mem, m2.mem, m1.mem]
  · rw [p3, v31, pc2]
    have cls : T % 4 = 0 ∨ T % 4 = 2 := by have := input.dstEven; omega
    rcases cls with h | h <;> rw [h]
    · rw [if_pos rfl, if_pos rfl, ofNat_four]
    · rw [if_neg (by decide), if_neg (by decide)]
      exact facts.slowTarget

theorem slow_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (fast : T % 4 = 0) :
    RunsOpeningBlock s (slowState site s) 5 ∧ Entered site s (slowState site s) S T ∧
    (slowState site s).pc = (if T % 8 = 4 then BitVec.ofNat 64 (4096+4*(site.stub+16))
      else BitVec.ofNat 64 (4096+4*(site.stub+4))) := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have bf := facts.stubFit
  obtain ⟨run3, entered, x31e, pc3⟩ := enter_facts site s S T input
  rw [if_pos fast] at pc3
  generalize he3 : enterState site s = e3 at run3 entered pc3 x31e
  have run4 := run_step e3 (site.stub+2) _ (by omega) pc3 code.test8 rfl rfl
  obtain ⟨p4, x31c, m4⟩ := andi_facts e3 7
  generalize he4 : execInstrBr e3 (.ANDI .x31 .x21 7) = e4 at p4 x31c m4 run4
  have pc4 : e4.pc = BitVec.ofNat 64 (4096+4*(site.stub+3)) := by rw [p4, pc3, ofNat_four]
  have run5 := run_step e4 (site.stub+3) _ (by omega) pc4 code.four rfl rfl
  obtain ⟨p5, m5⟩ := bne_facts e4 52
  generalize he5 : execInstrBr e4 (.BNE .x31 .x0 52) = e5 at p5 m5 run5
  have same : slowState site s = e5 := by rw [← he5, ← he4, ← he3]; unfold slowState; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) : e5.getReg r = e3.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m5.regs r z, m4.regs r a]
  have total := (run3.next run4).next run5
  rw [show 3+1+1 = 5 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keep .x29 (by decide)]; exact entered.x29
  · rw [keep _ facts.src31]; exact entered.src
  · rw [keep .x21 (by decide)]; exact entered.dst
  · rw [m5.mem, m4.mem]; exact entered.mem
  · intro r a b; rw [keep r a]; exact entered.regs r a b
  · obtain ⟨_, andBits⟩ := low_bits (s.getReg .x21) site.destOffset T
      (by have := input.room; unfold MEMORY_BYTES at this; omega) facts.offAligned input.dst
    rw [p5, x31c, entered.regs .x21 (by decide) (by decide), andBits, pc4]
    have cls : T % 8 = 0 ∨ T % 8 = 4 := by omega
    rcases cls with h | h <;> rw [h]
    · rw [if_pos (by decide), if_neg (by decide), ofNat_four]
    · rw [if_neg (by decide), if_pos rfl, show signExtend13 52 = BitVec.ofNat 64 (4*13) from rfl, ofNat_step]

structure WideDone (site : CopySite) (s t : MachineState) (S T cost : Nat) : Prop where
  run : RunsOpeningBlock s t cost
  pc : t.pc = BitVec.ofNat 64 (4096+4*(site.start+32))
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 32
  below : ∀ q : Word, q.toNat < T - T % 8 → t.getMem q = s.getMem q

theorem keep_x0 {u v : MachineState} (m : Moves u v .x0) (r : Reg) : v.getReg r = u.getReg r := by
  by_cases z : r = .x0
  · subst z; exact x0_any _ _
  · exact m.regs r z

theorem dword_path_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (h : T % 8 = 0) : WideDone site s (dwordPath site s) S T 14 := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  have off := facts.offSmall
  have room := input.room
  obtain ⟨run3, entered, pc3⟩ := slow_facts site s S T input (by omega)
  rw [if_neg (by omega : T % 8 ≠ 4)] at pc3
  generalize he3 : slowState site s = e3 at run3 entered pc3
  obtain ⟨runP, pcP, regsP, copyP, belowP⟩ := run_pairs 8 (by decide) site.source facts.src31 (site.stub+4) 0
    site.destOffset S T (by have := input.srcAligned; omega) h 4 0 e3 (by simpa using code.dwords) (by omega)
    (by simpa using pc3) entered.src entered.dst (by omega) (by omega) (by have := input.apart; omega) (by omega)
  generalize hc : pairsRun 8 site.source 0 site.destOffset 0 4 e3 = c at runP pcP regsP copyP belowP
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(site.stub+12)) := by rw [pcP]
  have runJ := run_step c (site.stub+12) _ (by omega) pcC code.dwordsBack rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 124
  generalize hf : execInstrBr c (.JALR .x0 .x29 124) = f at pJ mJ runJ
  have same : dwordPath site s = f := by rw [← hf, ← hc, ← he3]; unfold dwordPath; exact Eq.refl _
  rw [same]
  have total := (run3.next runP).next runJ
  rw [show 5+2*4+1 = 14 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pJ, regsP .x29 (by decide), entered.x29]; exact facts.back124
  · intro r a b; rw [keep_x0 mJ r, regsP r a, entered.regs r a b]
  · have c32 : ByteCopy e3 c S T 32 := by simpa using copyP
    exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm c32)
  · intro q below
    rw [getMem_congr mJ.mem, belowP q below, getMem_congr entered.mem]

theorem word_path_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (h : T % 8 = 4) : WideDone site s (wordPath site s) S T 22 := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  have off := facts.offSmall
  have room := input.room
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input (by omega)
  rw [if_pos h] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runP, pcP, regsP, copyP, belowP⟩ := run_pairs 4 (by decide) site.source facts.src31 (site.stub+16) 0
    site.destOffset S T (by have := input.srcAligned; omega) (by omega) 8 0 e5 (by simpa using code.words) (by omega)
    (by simpa using pc5) entered.src entered.dst (by omega) (by omega) (by have := input.apart; omega) (by omega)
  generalize hc : pairsRun 4 site.source 0 site.destOffset 0 8 e5 = c at runP pcP regsP copyP belowP
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(site.stub+32)) := by rw [pcP]
  have runJ := run_step c (site.stub+32) _ (by omega) pcC code.wordsBack rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 124
  generalize hf : execInstrBr c (.JALR .x0 .x29 124) = f at pJ mJ runJ
  have same : wordPath site s = f := by rw [← hf, ← hc, ← he5]; unfold wordPath; exact Eq.refl _
  rw [same]
  have total := (run5.next runP).next runJ
  rw [show 5+2*8+1 = 22 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pJ, regsP .x29 (by decide), entered.x29]; exact facts.back124
  · intro r a b; rw [keep_x0 mJ r, regsP r a, entered.regs r a b]
  · have c32 : ByteCopy e5 c S T 32 := by simpa using copyP
    exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm c32)
  · intro q below
    rw [getMem_congr mJ.mem, belowP q below, getMem_congr entered.mem]

theorem jump28_facts (u : MachineState) :
    let v := execInstrBr u (.JAL .x0 28)
    v.pc = u.pc + signExtend21 28 ∧ (∀ r, v.getReg r = u.getReg r) ∧ v.mem = u.mem := by
  refine ⟨rfl, ?_, rfl⟩
  intro r
  cases r <;> rfl

set_option maxHeartbeats 2000000 in
theorem half_path_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (h : T % 8 ≠ 0) (h4 : T % 8 ≠ 4) : WideDone site s (halfPath site s) S T 28 := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have ta : T % 4 = 2 := by have := input.dstEven; omega
  obtain ⟨run3, entered, _, pc3⟩ := enter_facts site s S T input
  rw [if_neg (by omega : T % 4 ≠ 0)] at pc3
  have copied := Shifted32.copy32_done site input.wide facts.src31 (enterState site s) S T
    pc3 entered.src entered.dst input.srcAligned ta input.apart
    (by have := input.room; have := input.apart; omega) input.room
  let c := Shifted32.copy32 site (enterState site s)
  have runJ := run_step c (site.start+25) (.JAL .x0 28) (by have := facts.startFit; omega)
    copied.pc code.shiftedBack rfl rfl
  obtain ⟨pcJ, regsJ, memJ⟩ := jump28_facts c
  refine ⟨(run3.next copied.run).next runJ, ?_, ?_, ?_, ?_⟩
  · change (execInstrBr c (.JAL .x0 28)).pc = _
    rw [pcJ, copied.pc, show signExtend21 28 = BitVec.ofNat 64 (4*7) from rfl, ofNat_step]
  · intro r a b
    rw [show halfPath site s = execInstrBr c (.JAL .x0 28) from rfl, regsJ r,
      copied.regs r a, entered.regs r a b]
  · exact copy_congr_mem memJ (copy_congr_before entered.mem.symm copied.bytes)
  · intro q below
    change (execInstrBr c (.JAL .x0 28)).getMem q = s.getMem q
    rw [getMem_congr memJ, copied.below q below, getMem_congr entered.mem]

/-- A wide site's copy: the cycles depend on the destination's alignment, everything else is as for the
halfword copy it replaces (`x29` is clobbered too). -/
theorem wide_copy (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T) :
    WideDone site s (wideState site s) S T (wideCost T) := by
  have facts := site_facts site input.wide
  obtain ⟨low, _⟩ := low_bits (s.getReg .x21) site.destOffset T
    (by have := input.room; unfold MEMORY_BYTES at this; omega) facts.offAligned input.dst
  unfold wideState wideCost
  rw [low]
  by_cases h0 : T % 8 = 0
  · rw [if_pos h0, if_pos h0]; exact dword_path_done site s S T input h0
  · rw [if_neg h0, if_neg h0]
    by_cases h4 : T % 8 = 4
    · rw [if_pos h4, if_pos h4]; exact word_path_done site s S T input h4
    · rw [if_neg h4, if_neg h4]; exact half_path_done site s S T input h0 h4

theorem pair_regs (width : Nat) (src : Reg) (load store k : Nat) (s : MachineState) (r : Reg) (h : r ≠ .x31) :
    (pairStep width src load store k s).getReg r = s.getReg r := by
  have keep (u : MachineState) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  unfold pairStep wideLoad wideStore
  by_cases h8 : width = 8
  · simp only [h8, ite_true, execInstrBr, MachineState.getReg_setPC, reg_setMem, keep]
  · by_cases h4 : width = 4
    · simp only [h4, show (4 = 8) = False from by decide, ite_true, ite_false, execInstrBr,
        MachineState.getReg_setPC, reg_setWord32, keep]
    · simp only [h8, h4, ite_false, execInstrBr, MachineState.getReg_setPC, reg_setHalfword, keep]

theorem pairs_regs (width : Nat) (src : Reg) (load store : Nat) (r : Reg) (h : r ≠ .x31) :
    ∀ n k (s : MachineState), (pairsRun width src load store k n s).getReg r = s.getReg r := by
  intro n
  induction n with
  | zero => intro k s; rfl
  | succ n ih => intro k s; exact (ih (k+1) _).trans (pair_regs width src load store k s r h)

/-- Whatever the inputs, a wide site's copy changes no register but `x29` and `x31`. -/
theorem wide_regs (site : CopySite) (s : MachineState) (r : Reg) (a : r ≠ .x31) (b : r ≠ .x29) :
    (wideState site s).getReg r = s.getReg r := by
  have enter : (enterState site s).getReg r = s.getReg r := by
    unfold enterState entryJump
    rw [keep_x0 (bne_facts _ _).2, (andi_facts _ 3).2.2.regs r a, (jal_facts _ _).2.2.regs r b]
  have slow : (slowState site s).getReg r = s.getReg r := by
    unfold slowState
    rw [keep_x0 (bne_facts _ 52).2, (andi_facts _ 7).2.2.regs r a, enter]
  unfold wideState
  split
  · unfold dwordPath; rw [keep_x0 (jalr_facts _ 124).2, pairs_regs _ _ _ _ r a, slow]
  · split
    · unfold wordPath; rw [keep_x0 (jalr_facts _ 124).2, pairs_regs _ _ _ _ r a, slow]
    · unfold halfPath
      have jump (u : MachineState) : (execInstrBr u (.JAL .x0 28)).getReg r = u.getReg r := by cases r <;> rfl
      rw [jump]
      unfold Shifted32.copy32
      rw [Shifted32.chunk_regs _ _ _ _ r a, Shifted32.chunk_regs _ _ _ _ r a,
        Shifted32.chunk_regs _ _ _ _ r a, Shifted32.chunk_regs _ _ _ _ r a, enter]

end TwoPermutationPrototype.GroupedOpening
