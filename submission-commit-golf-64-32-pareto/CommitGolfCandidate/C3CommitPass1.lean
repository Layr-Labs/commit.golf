import CommitGolfCandidate.C3CommitFetch
import CommitGolfCandidate.C3CommitMemory

/-! # Pass 1 of the 3c1p commit loop: three compressions per leaf, in place

With `a0` at `B - 112` (`B` the leaf's message address, i.e. word `base`):
`addi a0,a0,304 ; addi a2,a0,0 ; ecall` (t1 = C(v[192..256)) written at B+192),
`addi a0,a0,-32 ; addi a2,a0,8 ; ecall` (t2 = C(v[160..192) | t1) at B+168),
`addi a0,a0,-16 ; ecall` (t3 = C(v[144..168) | t2 | t1[8..16)) at B+168). 29 cycles, 3 calls. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false

/-- Message word index of leaf `i` (`4096 + 256 i` bytes). -/
def leafBase (i : Nat) : Nat := 512 + 32 * i

def p1a (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x10 .x10 304)) (.ADDI .x12 .x10 0)

def p1b (s : MachineState) (base : Nat) (t1 : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (writeBits (p1a s) (wordAddress (base + 24)) t1) (.ADDI .x10 .x10 4064))
    (.ADDI .x12 .x10 8)

def p1c (s : MachineState) (base : Nat) (t1 t2 : BitVec 256) : MachineState :=
  execInstrBr (writeBits (p1b s base t1) (wordAddress (base + 21)) t2) (.ADDI .x10 .x10 4080)

def p1d (s : MachineState) (base : Nat) (t1 t2 t3 : BitVec 256) : MachineState :=
  writeBits (p1c s base t1 t2) (wordAddress (base + 21)) t3

def p1Trace (s : MachineState) (base : Nat) : OracleComp World MachineState := do
  let t1 ← World.query (.inr (.inl (readBuffer (p1a s) (8 * (base + 24)) 64)))
  let t2 ← World.query (.inr (.inl (readBuffer (p1b s base t1) (8 * (base + 20)) 64)))
  let t3 ← World.query (.inr (.inl (readBuffer (p1c s base t1 t2) (8 * (base + 18)) 64)))
  return p1d s base t1 t2 t3

structure P1Ready (s : MachineState) (base : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (base - 14)
  low : 14 ≤ base
  bound : base + 32 ≤ 2 ^ 33
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0

private theorem imm304 : signExtend12 (304 : BitVec 12) = BitVec.ofNat 64 (8 * 38) := by decide
private theorem imm0 : signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) := by decide
private theorem imm8 : signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 (8 * 1) := by decide

private theorem immm32 : signExtend12 (4064 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 4) := by decide
private theorem immm16 : signExtend12 (4080 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 2) := by decide

theorem p1a_mem (s : MachineState) : (p1a s).mem = s.mem := by
  rw [p1a, addi_mem, addi_mem]

theorem p1a_regs (s : MachineState) (base : Nat) (ready : P1Ready s base) :
    (p1a s).getReg .x10 = wordAddress (base + 24) ∧ (p1a s).getReg .x12 = wordAddress (base + 24) ∧
      (p1a s).pc = s.pc + 4 + 4 := by
  have low := ready.low
  let first := execInstrBr s (.ADDI .x10 .x10 304)
  have up : first.getReg .x10 = wordAddress (base + 24) := by
    rw [addi_self s .x10 304 (by decide), ready.source, imm304, address_up]; congr 1; omega
  have a10 : (p1a s).getReg .x10 = first.getReg .x10 := addi_other first .x12 .x10 .x10 0 (by decide)
  have a12 : (p1a s).getReg .x12 = first.getReg .x10 + signExtend12 0 := addi_from first .x12 .x10 0 (by decide)
  refine ⟨a10.trans up, a12.trans ?_, ?_⟩
  · rw [up, imm0, address_up]
  · rw [p1a, addi_pc, addi_pc]

theorem p1a_keeps (s : MachineState) (r : Reg) (a : r ≠ .x10) (b : r ≠ .x12) :
    (p1a s).getReg r = s.getReg r := by
  rw [p1a, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a]

theorem p1b_regs (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 : BitVec 256) :
    (p1b s base t1).getReg .x10 = wordAddress (base + 20) ∧ (p1b s base t1).getReg .x12 = wordAddress (base + 21) ∧
      (p1b s base t1).pc = s.pc + 4 + 4 + 4 + 4 + 4 := by
  have prior := p1a_regs s base ready
  let w := writeBits (p1a s) (wordAddress (base + 24)) t1
  let first := execInstrBr w (.ADDI .x10 .x10 4064)
  have wx : w.getReg .x10 = wordAddress (base + 24) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans prior.1
  have down : first.getReg .x10 = wordAddress (base + 20) := by
    rw [addi_self w .x10 4064 (by decide), wx, address_down (base + 24) 4 4064 immm32 (by omega) (by norm_num)]
    congr 1
  have b10 : (p1b s base t1).getReg .x10 = first.getReg .x10 := addi_other first .x12 .x10 .x10 8 (by decide)
  have b12 : (p1b s base t1).getReg .x12 = first.getReg .x10 + signExtend12 8 := addi_from first .x12 .x10 8 (by decide)
  refine ⟨b10.trans down, b12.trans ?_, ?_⟩
  · rw [down, imm8, address_up]
  · rw [p1b, addi_pc, addi_pc, written_pc, prior.2.2]

theorem p1b_keeps (s : MachineState) (base : Nat) (t1 : BitVec 256) (r : Reg) (a : r ≠ .x10) (b : r ≠ .x12) :
    (p1b s base t1).getReg r = s.getReg r := by
  rw [p1b, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register, p1a_keeps s r a b]

theorem p1c_regs (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 t2 : BitVec 256) :
    (p1c s base t1 t2).getReg .x10 = wordAddress (base + 18) ∧
      (p1c s base t1 t2).getReg .x12 = wordAddress (base + 21) ∧
      (p1c s base t1 t2).pc = s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 := by
  have prior := p1b_regs s base ready t1
  let w := writeBits (p1b s base t1) (wordAddress (base + 21)) t2
  have wx : w.getReg .x10 = wordAddress (base + 20) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans prior.1
  have wy : w.getReg .x12 = wordAddress (base + 21) :=
    (CommitGolfCandidate.writeBits_register _ _ _ _).trans prior.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [p1c, addi_self w .x10 4080 (by decide), wx, address_down (base + 20) 2 4080 immm16 (by omega) (by norm_num)]
    congr 1
  · rw [p1c, addi_other w .x10 .x10 .x12 4080 (by decide), wy]
  · rw [p1c, addi_pc, written_pc, prior.2.2]

theorem p1c_keeps (s : MachineState) (base : Nat) (t1 t2 : BitVec 256) (r : Reg) (a : r ≠ .x10) (b : r ≠ .x12) :
    (p1c s base t1 t2).getReg r = s.getReg r := by
  rw [p1c, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register, p1b_keeps s base t1 r a b]

theorem p1d_regs (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 t2 t3 : BitVec 256) :
    (p1d s base t1 t2 t3).getReg .x10 = wordAddress (base + 18) ∧
      (p1d s base t1 t2 t3).getReg .x12 = wordAddress (base + 21) ∧
      (p1d s base t1 t2 t3).pc = s.pc + BitVec.ofNat 64 32 := by
  have prior := p1c_regs s base ready t1 t2
  refine ⟨(CommitGolfCandidate.writeBits_register _ _ _ _).trans prior.1,
    (CommitGolfCandidate.writeBits_register _ _ _ _).trans prior.2.1, ?_⟩
  rw [p1d, written_pc, prior.2.2]
  simp only [BitVec.add_assoc]
  congr 1

theorem p1d_keeps (s : MachineState) (base : Nat) (t1 t2 t3 : BitVec 256) (r : Reg) (a : r ≠ .x10) (b : r ≠ .x12) :
    (p1d s base t1 t2 t3).getReg r = s.getReg r := by
  rw [p1d, CommitGolfCandidate.writeBits_register, p1c_keeps s base t1 t2 r a b]

/-! ### Memory -/

def p1Mem (M : Memory) (base : Nat) (t1 t2 t3 : BitVec 256) : Memory :=
  writeWindow (writeWindow (writeWindow M (base + 24) (digestWords t1)) (base + 21) (digestWords t2))
    (base + 21) (digestWords t3)

theorem p1b_memory (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 : BitVec 256) (w : Nat)
    (bounded : w < 2 ^ 33) :
    memoryView (p1b s base t1) w = writeWindow (memoryView s) (base + 24) (digestWords t1) w := by
  have room := ready.bound
  have same : (p1b s base t1).mem = (writeBits (p1a s) (wordAddress (base + 24)) t1).mem := by
    rw [p1b, addi_mem, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) bounded, memoryView_congr (p1a_mem s)]

theorem p1c_memory (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 t2 : BitVec 256) (w : Nat)
    (bounded : w < 2 ^ 33) :
    memoryView (p1c s base t1 t2) w =
      writeWindow (writeWindow (memoryView s) (base + 24) (digestWords t1)) (base + 21) (digestWords t2) w := by
  have room := ready.bound
  have same : (p1c s base t1 t2).mem = (writeBits (p1b s base t1) (wordAddress (base + 21)) t2).mem := by
    rw [p1c, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) bounded]
  by_cases inside : base + 21 ≤ w ∧ w < base + 21 + 4
  · simp only [writeWindow, dite_eq_left inside]
  · simp only [writeWindow, dite_eq_right inside]
    exact (p1b_memory s base ready t1 w bounded).trans (by simp only [writeWindow])

theorem p1d_memory (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 t2 t3 : BitVec 256) (w : Nat)
    (bounded : w < 2 ^ 33) :
    memoryView (p1d s base t1 t2 t3) w = p1Mem (memoryView s) base t1 t2 t3 w := by
  have room := ready.bound
  rw [p1d, compression_write_memory _ _ _ _ (by omega) bounded]
  unfold p1Mem
  by_cases inside : base + 21 ≤ w ∧ w < base + 21 + 4
  · simp only [writeWindow, dite_eq_left inside]
  · rw [show ∀ X : Memory, writeWindow X (base + 21) (digestWords t3) w = X w from
      fun X => by simp only [writeWindow, dite_eq_right inside]]
    rw [show ∀ X : Memory, writeWindow X (base + 21) (digestWords t3) w = X w from
      fun X => by simp only [writeWindow, dite_eq_right inside]]
    exact p1c_memory s base ready t1 t2 w bounded

theorem p1_first_input (s : MachineState) (base : Nat) :
    readBuffer (p1a s) (8 * (base + 24)) 64 = packWords8 (c3FirstWords (window (memoryView s) base)) := by
  rw [c3_read_compression, memoryView_congr (p1a_mem s)]
  congr 1
  funext k
  simp only [window, c3FirstWords]
  congr 1
  omega

theorem p1_second_input (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 : BitVec 256) :
    readBuffer (p1b s base t1) (8 * (base + 20)) 64 =
      packWords8 (c3SecondWords (window (memoryView s) base) (digestWords t1)) := by
  rw [c3_read_compression]
  have room := ready.bound
  congr 1
  funext k
  simp only [window]
  rw [p1b_memory s base ready t1 _ (by omega)]
  by_cases low : k.val < 4
  · have outside : ¬ (base + 24 ≤ base + 20 + k.val ∧ base + 20 + k.val < base + 24 + 4) := by omega
    simp only [writeWindow, dite_eq_right outside, c3SecondWords, low, dite_true, window]
    rw [Nat.add_assoc]
  · have inside : base + 24 ≤ base + 20 + k.val ∧ base + 20 + k.val < base + 24 + 4 := by omega
    simp only [writeWindow, dite_eq_left inside, c3SecondWords, low, dite_false]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega

theorem p1_third_input (s : MachineState) (base : Nat) (ready : P1Ready s base) (t1 t2 : BitVec 256) :
    readBuffer (p1c s base t1 t2) (8 * (base + 18)) 64 =
      packWords8 (c3ThirdWords (window (memoryView s) base) (digestWords t1) (digestWords t2)) := by
  rw [c3_read_compression]
  have room := ready.bound
  congr 1
  funext k
  simp only [window]
  rw [p1c_memory s base ready t1 t2 _ (by omega)]
  by_cases low : k.val < 3
  · have a : ¬ (base + 21 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 21 + 4) := by omega
    have b : ¬ (base + 24 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 24 + 4) := by omega
    simp only [writeWindow, dite_eq_right a, dite_eq_right b, c3ThirdWords, low, dite_true, window]
    rw [Nat.add_assoc]
  by_cases mid : k.val < 7
  · have a : base + 21 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 21 + 4 := by omega
    simp only [writeWindow, dite_eq_left a, c3ThirdWords, low, mid, dite_true, dite_false]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega
  · have k7 : k.val = 7 := by omega
    have a : ¬ (base + 21 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 21 + 4) := by omega
    have b : base + 24 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 24 + 4 := by omega
    simp only [writeWindow, dite_eq_right a, dite_eq_left b, c3ThirdWords, low, mid, dite_false]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega

/-! ### Execution -/

attribute [local irreducible] packedWideCommitImage

theorem word_pc_add (index k : Nat) : wordPC index + BitVec.ofNat 64 (4 * k) = wordPC (index + k) := by
  unfold wordPC
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem execute_p1_leaf (s : MachineState) (j : Nat) (hj : j < 2048) (base : Nat) (ready : P1Ready s base)
    (pc : s.pc = wordPC (p1Index j)) (fuel : Nat) :
    execute packedWideCommitImage (8 + fuel) s true =
      (do let d ← p1Trace s base
          let r ← execute packedWideCommitImage fuel d true
          return r.charge 29 3) := by
  have room := ready.bound
  have aRegs := p1a_regs s base ready
  -- two ordinary steps
  have stepA : execute packedWideCommitImage (2 + (6 + fuel)) s true =
      (do let r ← execute packedWideCommitImage (6 + fuel) (p1a s) true; return r.charge 2 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := fun i =>
      if i = 0 then s else if i = 1 then execInstrBr s (.ADDI .x10 .x10 304) else p1a s)
    intro i hi
    interval_cases i
    · refine ⟨.base (opAt p1Ops 0), fetch_p1 j hj 0 (by decide) _ (by simpa using pc), rfl, rfl⟩
    · refine ⟨.base (opAt p1Ops 1), fetch_p1 j hj 1 (by decide) _ ?_, rfl, rfl⟩
      change s.pc + 4 = _
      rw [pc, show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
  rw [show 8 + fuel = 2 + (6 + fuel) by omega, stepA]
  -- first call
  have fetchA : fetch packedWideCommitImage (p1a s) = some (.base .ECALL) := by
    have := fetch_p1 j hj 2 (by decide) (p1a s) (by
      rw [aRegs.2.2, pc, BitVec.add_assoc, show (4 : Word) + 4 = BitVec.ofNat 64 (4 * 2) by rfl, word_pc_add])
    simpa [opAt, p1Ops] using this
  rw [show 6 + fuel = (5 + fuel) + 1 by omega,
    execute_compression_on _ _ (p1a s) true (base + 24) (base + 24) (by omega) (by omega) aRegs.1 aRegs.2.1
      ((p1a_keeps s .x5 (by decide) (by decide)).trans ready.selector)
      ((p1a_keeps s .x11 (by decide) (by decide)).trans ready.size)
      ((p1a_keeps s .x13 (by decide) (by decide)).trans ready.primitive) fetchA]
  simp only [p1Trace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t1 _
  let w1 := writeBits (p1a s) (wordAddress (base + 24)) t1
  have w1pc : w1.pc = wordPC (p1Index j + 3) := by
    change (p1a s).pc + 4 = _
    rw [aRegs.2.2, pc, BitVec.add_assoc, BitVec.add_assoc, show (4 : Word) + (4 + 4) = BitVec.ofNat 64 (4 * 3) by rfl,
      word_pc_add]
  have stepB : execute packedWideCommitImage (2 + (3 + fuel)) w1 true =
      (do let r ← execute packedWideCommitImage (3 + fuel) (p1b s base t1) true; return r.charge 2 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := fun i =>
      if i = 0 then w1 else if i = 1 then execInstrBr w1 (.ADDI .x10 .x10 4064) else p1b s base t1)
    intro i hi
    interval_cases i
    · refine ⟨.base (opAt p1Ops 3), fetch_p1 j hj 3 (by decide) _ (by simpa using w1pc), rfl, rfl⟩
    · refine ⟨.base (opAt p1Ops 4), fetch_p1 j hj 4 (by decide) _ ?_, rfl, rfl⟩
      change w1.pc + 4 = _
      rw [w1pc, show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
  rw [show 5 + fuel = 2 + (3 + fuel) by omega, stepB]
  have bRegs := p1b_regs s base ready t1
  have fetchB : fetch packedWideCommitImage (p1b s base t1) = some (.base .ECALL) := by
    have := fetch_p1 j hj 5 (by decide) (p1b s base t1) (by
      rw [bRegs.2.2, pc]
      simp only [BitVec.add_assoc]
      rw [show (4 : Word) + (4 + (4 + (4 + 4))) = BitVec.ofNat 64 (4 * 5) by rfl, word_pc_add])
    simpa [opAt, p1Ops] using this
  rw [show 3 + fuel = (2 + fuel) + 1 by omega,
    execute_compression_on _ _ (p1b s base t1) true (base + 20) (base + 21) (by omega) (by omega) bRegs.1 bRegs.2.1
      ((p1b_keeps s base t1 .x5 (by decide) (by decide)).trans ready.selector)
      ((p1b_keeps s base t1 .x11 (by decide) (by decide)).trans ready.size)
      ((p1b_keeps s base t1 .x13 (by decide) (by decide)).trans ready.primitive) fetchB]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t2 _
  let w2 := writeBits (p1b s base t1) (wordAddress (base + 21)) t2
  have w2pc : w2.pc = wordPC (p1Index j + 6) := by
    change (p1b s base t1).pc + 4 = _
    rw [bRegs.2.2, pc]
    simp only [BitVec.add_assoc]
    rw [show (4 : Word) + (4 + (4 + (4 + (4 + 4)))) = BitVec.ofNat 64 (4 * 6) by rfl, word_pc_add]
  have stepC : execute packedWideCommitImage (1 + (1 + fuel)) w2 true =
      (do let r ← execute packedWideCommitImage (1 + fuel) (p1c s base t1 t2) true; return r.charge 1 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := fun i => if i = 0 then w2 else p1c s base t1 t2)
    intro i hi
    interval_cases i
    exact ⟨.base (opAt p1Ops 6), fetch_p1 j hj 6 (by decide) _ (by simpa using w2pc), rfl, rfl⟩
  rw [show 2 + fuel = 1 + (1 + fuel) by omega, stepC]
  have cRegs := p1c_regs s base ready t1 t2
  have fetchC : fetch packedWideCommitImage (p1c s base t1 t2) = some (.base .ECALL) := by
    have := fetch_p1 j hj 7 (by decide) (p1c s base t1 t2) (by
      rw [cRegs.2.2, pc]
      simp only [BitVec.add_assoc]
      rw [show (4 : Word) + (4 + (4 + (4 + (4 + (4 + 4))))) = BitVec.ofNat 64 (4 * 7) by rfl, word_pc_add])
    simpa [opAt, p1Ops] using this
  rw [show 1 + fuel = fuel + 1 by omega,
    execute_compression_on _ _ (p1c s base t1 t2) true (base + 18) (base + 21) (by omega) (by omega) cRegs.1 cRegs.2.1
      ((p1c_keeps s base t1 t2 .x5 (by decide) (by decide)).trans ready.selector)
      ((p1c_keeps s base t1 t2 .x11 (by decide) (by decide)).trans ready.size)
      ((p1c_keeps s base t1 t2 .x13 (by decide) (by decide)).trans ready.primitive) fetchC]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t3 _
  simp [Execution.charge, p1d]
  congr 1
  funext a
  congr 1 <;> omega

end TwoPermutationPrototype.RV64.C3Leaves
