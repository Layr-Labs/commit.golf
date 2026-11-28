import CommitGolfCandidate.TwoPermutationPackedDecode
import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.TwoPermutationPackedRecordGeometry
import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.C3CommitMemory
import CommitGolfCandidate.TwoPermutationCheckerRecordSetup
import CommitGolfCandidate.TwoPermutationPackedCheckRecordData
import CommitGolfCandidate.TwoPermutationPackedInputFrame
import CommitGolfCandidate.TwoPermutationOpeningBlocks

/-! # The checker's 3c1p leaf block (check image words 22..62)

With `src = checkSourceWord ordinal` (the claimed value is at words `src+5 .. src+37`):
`ld t1,0(s0) ; slli t3,t1,8 ; add t3,gp,t3 ; addi a1,zero,64 ; addi a3,zero,0 ; addi a0,s3,232 ;
addi a2,a0,0 ; ecall` (t1 at src+29), `addi a0,a0,-32 ; addi a2,a0,8 ; ecall` (t2 at src+26),
`addi a0,a0,-16 ; ecall` (t3 at src+26), `addi t6,t3,40 ; sd t6,0(a0)` (tag at src+23), eight
halfword copies of the salt from the proof to src+24..src+26, `addi a1,zero,200 ; addi a3,zero,1 ;
addi a0,a0,-144 ; addi a2,s7,0 ; ecall` (the leaf digest at 12288), then the leader's lower setup.
41 steps, 91 cycles, 4 public calls. -/
namespace TwoPermutationPrototype.Packed.C3RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.C3Leaves TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (checkIndexWord checkSourceWord checker_positions_bound RecordInputFrame
  honestIndex record_input_index record_input_value beginLower beginLowerCode lower_setup_post
  lower_setup_register lower_setup_mem check_recorded_bind check_recorded_map checker_value_data buffer_window)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false

/-! ### Pure window algebra of the chain -/

theorem c3_first_window (M : Memory) (base : Nat) :
    (window M (base + 24) : Words 8) = c3FirstWords (window M base) := by
  funext k; simp only [window, c3FirstWords]; congr 1; omega

theorem c3_second_window (M : Memory) (base : Nat) (t1 : BitVec 256) :
    (window (writeWindow M (base + 24) (digestWords t1)) (base + 20) : Words 8) =
      c3SecondWords (window M base) (digestWords t1) := by
  funext k
  have kt := k.isLt
  simp only [window]
  by_cases low : k.val < 4
  · have outside : ¬ (base + 24 ≤ base + 20 + k.val ∧ base + 20 + k.val < base + 24 + 4) := by omega
    simp only [writeWindow, dite_eq_right outside, c3SecondWords, low, dite_true, window]
    rw [Nat.add_assoc]
  · have inside : base + 24 ≤ base + 20 + k.val ∧ base + 20 + k.val < base + 24 + 4 := by omega
    simp only [writeWindow, dite_eq_left inside, c3SecondWords, low, dite_false]
    congr 1; ext; simp only [Fin.val_mk]; omega

theorem c3_third_window (M : Memory) (base : Nat) (t1 t2 : BitVec 256) :
    (window (writeWindow (writeWindow M (base + 24) (digestWords t1)) (base + 21) (digestWords t2)) (base + 18) :
      Words 8) = c3ThirdWords (window M base) (digestWords t1) (digestWords t2) := by
  funext k
  have kt := k.isLt
  simp only [window]
  by_cases low : k.val < 3
  · have a : ¬ (base + 21 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 21 + 4) := by omega
    have b : ¬ (base + 24 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 24 + 4) := by omega
    simp only [writeWindow, dite_eq_right a, dite_eq_right b, c3ThirdWords, low, dite_true, window]
    rw [Nat.add_assoc]
  by_cases mid : k.val < 7
  · have a : base + 21 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 21 + 4 := by omega
    simp only [writeWindow, dite_eq_left a, c3ThirdWords, low, mid, dite_true, dite_false]
    congr 1; ext; simp only [Fin.val_mk]; omega
  · have a : ¬ (base + 21 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 21 + 4) := by omega
    have b : base + 24 ≤ base + 18 + k.val ∧ base + 18 + k.val < base + 24 + 4 := by omega
    simp only [writeWindow, dite_eq_right a, dite_eq_left b, c3ThirdWords, low, mid, dite_false]
    congr 1; ext; simp only [Fin.val_mk]; omega

/-! ### States -/

def c3RecordOps : List Instr :=
  [.LD .x6 .x8 0, .SLLI .x28 .x6 8, .ADD .x28 .x3 .x28, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0,
   .ADDI .x10 .x19 232, .ADDI .x12 .x10 0]

def ckPrefix (s : MachineState) (count : Nat) : MachineState := (c3RecordOps.take count).foldl execInstrBr s
def ck1 (s : MachineState) : MachineState := ckPrefix s 7

def ck2 (s : MachineState) (src : Nat) (t1 : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (writeBits (ck1 s) (wordAddress (src + 29)) t1) (.ADDI .x10 .x10 4064))
    (.ADDI .x12 .x10 8)

def ck3 (s : MachineState) (src : Nat) (t1 t2 : BitVec 256) : MachineState :=
  execInstrBr (writeBits (ck2 s src t1) (wordAddress (src + 26)) t2) (.ADDI .x10 .x10 4080)

def ck4 (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3) (.ADDI .x31 .x28 40))
    (.SD .x10 .x31 0)

def ck5 (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) : MachineState :=
  copyField (fieldCode .nonce) (ck4 s src t1 t2 t3)

def ck6 (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (ck5 s src t1 t2 t3) (.ADDI .x11 .x0 200))
    (.ADDI .x13 .x0 1)) (.ADDI .x10 .x10 3952)) (.ADDI .x12 .x23 0)

def ck7 (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) (y : BitVec 1600) : MachineState :=
  writeBits (ck6 s src t1 t2 t3) (wordAddress 1536) y

/-- The precondition: the record cursor's registers, named by their word indices. -/
structure CkReady (s : MachineState) (src proof : Nat) (index : Index) : Prop where
  pc : s.pc = 0x1058
  indexAccess : accessValid (s.getReg .x8) 8 = true
  indexValue : s.getMem (s.getReg .x8) = BitVec.ofNat 64 index.val
  source : s.getReg .x19 = wordAddress src
  proofPointer : s.getReg .x21 = BitVec.ofNat 64 proof
  tagBase : s.getReg .x3 = 4056
  digest : s.getReg .x23 = wordAddress 1536
  selector : s.getReg .x5 = 0
  sourceBound : src + 37 ≤ 2 ^ 33
  sourceLow : 1576 ≤ src
  proofAligned : proof % 2 = 0
  proofBound : proof + 16 ≤ MEMORY_BYTES
  apart : 8 * (src + 37) ≤ proof

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem set_pc_pc (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem mem_set_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
@[local simp] private theorem mem_set_pc (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl

private theorem addr_shift (i : Nat) : (BitVec.ofNat 64 i <<< 8) = BitVec.ofNat 64 (256 * i) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 i * BitVec.ofNat 64 256 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm i]

theorem ck1_facts (s : MachineState) :
    let t := ck1 s
    t.mem = s.mem ∧ t.getReg .x6 = s.getMem (s.getReg .x8) ∧
    t.getReg .x28 = s.getReg .x3 + (s.getMem (s.getReg .x8) <<< 8) ∧ t.getReg .x11 = 64 ∧ t.getReg .x13 = 0 ∧
    t.getReg .x10 = s.getReg .x19 + 232 ∧ t.getReg .x12 = s.getReg .x19 + 232 ∧ t.pc = s.pc + 28 := by
  simp [ck1, ckPrefix, c3RecordOps, execInstrBr, signExtend12, BitVec.add_assoc] <;> rfl

theorem ck1_keeps (s : MachineState) (r : Reg) (a : r ≠ .x6) (b : r ≠ .x28) (c : r ≠ .x11) (d : r ≠ .x13)
    (e : r ≠ .x10) (f : r ≠ .x12) : (ck1 s).getReg r = s.getReg r := by
  simp [ck1, ckPrefix, c3RecordOps, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f]

theorem ck1_regs (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index) :
    (ck1 s).getReg .x10 = wordAddress (src + 29) ∧ (ck1 s).getReg .x12 = wordAddress (src + 29) ∧
    (ck1 s).getReg .x28 = BitVec.ofNat 64 (4056 + 256 * index.val) := by
  obtain ⟨_, _, h28, _, _, h10, h12, _⟩ := ck1_facts s
  have up : s.getReg .x19 + 232 = wordAddress (src + 29) := by
    rw [ready.source, show (232 : Word) = BitVec.ofNat 64 (8 * 29) by rfl, address_up]
  refine ⟨h10.trans up, h12.trans up, ?_⟩
  rw [h28, ready.tagBase, ready.indexValue, addr_shift, show (4056 : Word) = BitVec.ofNat 64 4056 by rfl,
    ← BitVec.ofNat_add]

private theorem immm32 : signExtend12 (4064 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 4) := by decide
private theorem immm16 : signExtend12 (4080 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 2) := by decide
private theorem immm144 : signExtend12 (3952 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 18) := by decide
private theorem imm8 : signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 (8 * 1) := by decide

theorem ck2_regs (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 : BitVec 256) :
    (ck2 s src t1).getReg .x10 = wordAddress (src + 25) ∧ (ck2 s src t1).getReg .x12 = wordAddress (src + 26) ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → (ck2 s src t1).getReg r = (ck1 s).getReg r) ∧
      (ck2 s src t1).pc = (ck1 s).pc + 4 + 4 + 4 := by
  have prior := ck1_regs s src proof index ready
  let w := writeBits (ck1 s) (wordAddress (src + 29)) t1
  let first := execInstrBr w (.ADDI .x10 .x10 4064)
  have wx : w.getReg .x10 = wordAddress (src + 29) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans prior.1
  have down : first.getReg .x10 = wordAddress (src + 25) := by
    rw [addi_self w .x10 4064 (by decide), wx, address_down (src + 29) 4 4064 immm32 (by omega) (by norm_num),
      show src + 29 - 4 = src + 25 by omega]
  refine ⟨(addi_other first .x12 .x10 .x10 8 (by decide)).trans down, ?_, ?_, ?_⟩
  · rw [ck2, addi_from _ _ _ _ (by decide), down, imm8, address_up]
  · intro r a b
    rw [ck2, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register]
  · rw [ck2, addi_pc, addi_pc, written_pc]

theorem ck3_regs (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 : BitVec 256) :
    (ck3 s src t1 t2).getReg .x10 = wordAddress (src + 23) ∧ (ck3 s src t1 t2).getReg .x12 = wordAddress (src + 26) ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → (ck3 s src t1 t2).getReg r = (ck1 s).getReg r) ∧
      (ck3 s src t1 t2).pc = (ck1 s).pc + 4 + 4 + 4 + 4 + 4 := by
  obtain ⟨b10, b12, bkeep, bpc⟩ := ck2_regs s src proof index ready t1
  let w := writeBits (ck2 s src t1) (wordAddress (src + 26)) t2
  have wx : w.getReg .x10 = wordAddress (src + 25) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans b10
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ck3, addi_self w .x10 4080 (by decide), wx, address_down (src + 25) 2 4080 immm16 (by omega) (by norm_num),
      show src + 25 - 2 = src + 23 by omega]
  · rw [ck3, addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, b12]
  · intro r a b
    rw [ck3, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register, bkeep r a b]
  · rw [ck3, addi_pc, written_pc, bpc]

theorem ck4_regs (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) :
    (ck4 s src t1 t2 t3).getReg .x10 = wordAddress (src + 23) ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x31 → (ck4 s src t1 t2 t3).getReg r = (ck1 s).getReg r) ∧
      (ck4 s src t1 t2 t3).pc = (ck1 s).pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 := by
  obtain ⟨c10, _, ckeep, cpc⟩ := ck3_regs s src proof index ready t1 t2
  refine ⟨?_, ?_, ?_⟩
  · rw [ck4, sd_reg, addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, c10]
  · intro r a b c
    rw [ck4, sd_reg, addi_other _ _ _ _ _ c, CommitGolfCandidate.writeBits_register, ckeep r a b]
  · rw [ck4, sd_pc, addi_pc, written_pc, cpc]

theorem ck2_memory (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ck2 s src t1) w = writeWindow (memoryView s) (src + 29) (digestWords t1) w := by
  have room := ready.sourceBound
  have same : (ck2 s src t1).mem = (writeBits (ck1 s) (wordAddress (src + 29)) t1).mem := by
    rw [ck2, addi_mem, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw,
    memoryView_congr (ck1_facts s).1]

theorem ck3_memory (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ck3 s src t1 t2) w =
      writeWindow (writeWindow (memoryView s) (src + 29) (digestWords t1)) (src + 26) (digestWords t2) w := by
  have room := ready.sourceBound
  have same : (ck3 s src t1 t2).mem = (writeBits (ck2 s src t1) (wordAddress (src + 26)) t2).mem := by
    rw [ck3, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  by_cases inside : src + 26 ≤ w ∧ w < src + 26 + 4
  · simp only [writeWindow, dite_eq_left inside]
  · rw [show ∀ X : Memory, writeWindow X (src + 26) (digestWords t2) w = X w from
      fun X => by simp only [writeWindow, dite_eq_right inside]]
    rw [show ∀ X : Memory, writeWindow X (src + 26) (digestWords t2) w = X w from
      fun X => by simp only [writeWindow, dite_eq_right inside]]
    exact ck2_memory s src proof index ready t1 w hw

/-- Memory after the chain and the tag store, as a pure function of the memory before the leaf. -/
def ckMem (M : Memory) (src : Nat) (t1 t2 t3 : BitVec 256) (tag : Word) : Memory :=
  writeWord (writeWindow (writeWindow (writeWindow M (src + 29) (digestWords t1)) (src + 26) (digestWords t2))
    (src + 26) (digestWords t3)) (src + 23) tag

theorem ck4_memory (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ck4 s src t1 t2 t3) w = ckMem (memoryView s) src t1 t2 t3 (c3Tag index) w := by
  have room := ready.sourceBound
  obtain ⟨c10, _, ckeep, _⟩ := ck3_regs s src proof index ready t1 t2
  let w3 := writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3
  let w5 := execInstrBr w3 (.ADDI .x31 .x28 40)
  have x10 : w5.getReg .x10 = wordAddress (src + 23) := by
    rw [addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, c10]
  have x31 : w5.getReg .x31 = c3Tag index := by
    rw [addi_from _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, ckeep _ (by decide) (by decide),
      (ck1_regs s src proof index ready).2.2, show signExtend12 (40 : BitVec 12) = BitVec.ofNat 64 40 by decide,
      ← BitVec.ofNat_add]
    unfold c3Tag; congr 1; omega
  have same : (ck4 s src t1 t2 t3).mem = (w5.setMem (w5.getReg .x10 + signExtend12 0) (w5.getReg .x31)).mem := by
    rw [ck4, sd_mem]
  rw [memoryView_congr same, x10, x31, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) by decide,
    address_up, view_store _ (src + 23) w _ (by omega) (by omega)]
  unfold ckMem
  simp only [writeWord]
  split
  · rfl
  · have mem5 : memoryView w5 w = memoryView w3 w := by rw [memoryView_congr (addi_mem _ _ _ _)]
    rw [mem5, compression_write_memory _ _ _ _ (by omega) hw]
    by_cases inside : src + 26 ≤ w ∧ w < src + 26 + 4
    · simp only [writeWindow, dite_eq_left inside]
    · rw [show ∀ X : Memory, writeWindow X (src + 26) (digestWords t3) w = X w from
        fun X => by simp only [writeWindow, dite_eq_right inside]]
      rw [show ∀ X : Memory, writeWindow X (src + 26) (digestWords t3) w = X w from
        fun X => by simp only [writeWindow, dite_eq_right inside]]
      exact ck3_memory s src proof index ready t1 t2 w hw

/-! ### Execution -/


theorem pc_word (k : Nat) : (0x1058 : Word) + BitVec.ofNat 64 (4 * k) = BitVec.ofNat 64 (4096 + 4 * (22 + k)) := by
  rw [show (0x1058 : Word) = BitVec.ofNat 64 4184 by rfl, ← BitVec.ofNat_add]; congr 1; omega

theorem ck1_pc (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index) :
    (ck1 s).pc = BitVec.ofNat 64 (4096 + 4 * 29) := by
  rw [(ck1_facts s).2.2.2.2.2.2.2, ready.pc, show (28 : Word) = BitVec.ofNat 64 (4 * 7) by rfl, pc_word]

theorem execute_ck1 (s : MachineState) (pc : s.pc = 0x1058) (index : accessValid (s.getReg .x8) 8 = true)
    (fuel : Nat) :
    execute packedImage (7 + fuel) s false =
      (do let result ← execute packedImage fuel (ck1 s) false; return result.charge 7 0) := by
  apply execute_unit_steps (states := ckPrefix s)
  intro i bounded
  refine ⟨.base (c3RecordOps[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (22 + i) _ (by omega)
    · interval_cases i <;> simp [ckPrefix, c3RecordOps, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, ckPrefix, c3RecordOps,
      signExtend12, index] <;> assumption
  · interval_cases i <;> rfl

theorem execute_lower_setup_packed (state : MachineState) (pc : state.pc = 0x10e8) (fuel : Nat) :
    execute packedImage (5 + fuel) state false =
      (do let result ← execute packedImage fuel (beginLower state 5) false
          return result.charge 5 0) := by
  apply execute_unit_steps (states := beginLower state)
  intro i bounded
  refine ⟨.base (beginLowerCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (58 + i) _ (by omega)
    · interval_cases i <;> simp [beginLower, beginLowerCode, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem ordinary_one (st next : MachineState) (instr : Instr) (fuel : Nat)
    (fetched : fetch packedImage st = some (.base instr)) (stepped : ordinaryStep st (.base instr) = some next)
    (unit : instructionCycles (.base instr) = 1) :
    execute packedImage (1 + fuel) st false =
      (do let result ← execute packedImage fuel next false; return result.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped, unit]

theorem charge_charge (r : Execution) (a b c d : Nat) : (r.charge a b).charge c d = r.charge (c + a) (d + b) := by
  simp only [Execution.charge, Nat.add_assoc]

def c3CheckQueries (s : MachineState) (src : Nat) : OracleComp World MachineState := do
  let t1 ← World.query (.inr (.inl (readBuffer (ck1 s) (8 * (src + 29)) 64)))
  let t2 ← World.query (.inr (.inl (readBuffer (ck2 s src t1) (8 * (src + 25)) 64)))
  let t3 ← World.query (.inr (.inl (readBuffer (ck3 s src t1 t2) (8 * (src + 23)) 64)))
  let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (ck6 s src t1 t2 t3)) (src + 5))))))
  return ck7 s src t1 t2 t3 y

theorem ck4_copy_ready (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) :
    CopyReady (fieldCode .nonce) (ck4 s src t1 t2 t3) proof (8 * (src + 24)) 0 := by
  obtain ⟨d10, dkeep, dpc⟩ := ck4_regs s src proof index ready t1 t2 t3
  have pb := ready.proofBound
  have sb := ready.sourceBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ready.proofAligned, ?_⟩
  · change (ck4 s src t1 t2 t3).pc = BitVec.ofNat 64 (4096 + 4 * (37 + 2 * 0))
    rw [dpc, ck1_pc s src proof index ready]
    try rfl
  · change (ck4 s src t1 t2 t3).getReg .x21 = _
    rw [dkeep .x21 (by decide) (by decide) (by decide),
      ck1_keeps s .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ready.proofPointer]
  · change (ck4 s src t1 t2 t3).getReg .x10 + BitVec.ofNat 64 (8 * 1) = _
    rw [d10, address_up]
    try rfl
  · change proof + 2 * 8 ≤ MEMORY_BYTES; omega
  · change 8 * (src + 24) + 2 * 8 ≤ MEMORY_BYTES; unfold MEMORY_BYTES; omega
  · change 8 * (src + 24) % 2 = 0; omega

theorem ck5_pc (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) : (ck5 s src t1 t2 t3).pc = BitVec.ofNat 64 (4096 + 4 * 53) :=
  copy_field_pc _ _ _ _ (ck4_copy_ready s src proof index ready t1 t2 t3)

theorem ck5_reg (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) (r : Reg) (h : r ≠ .x31) :
    (ck5 s src t1 t2 t3).getReg r = (ck4 s src t1 t2 t3).getReg r :=
  copy_field_register _ _ r h

theorem ck6_mem (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) :
    (ck6 s src t1 t2 t3).mem = (ck5 s src t1 t2 t3).mem := by
  rw [ck6, addi_mem, addi_mem, addi_mem, addi_mem]

theorem ck6_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) :
    (ck6 s src t1 t2 t3).getReg .x10 = wordAddress (src + 5) ∧
    (ck6 s src t1 t2 t3).getReg .x12 = wordAddress 1536 ∧
    (ck6 s src t1 t2 t3).getReg .x5 = 0 ∧
    (ck6 s src t1 t2 t3).getReg .x11 = 200 ∧
    (ck6 s src t1 t2 t3).getReg .x13 = 1 ∧
    (ck6 s src t1 t2 t3).pc = BitVec.ofNat 64 (4096 + 4 * 57) := by
  have sb := ready.sourceBound
  obtain ⟨d10, dkeep, _⟩ := ck4_regs s src proof index ready t1 t2 t3
  have p5 := ck5_pc s src proof index ready t1 t2 t3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ck6, addi_other _ .x12 .x23 .x10 0 (by decide), addi_self _ .x10 3952 (by decide),
      addi_other _ .x13 .x0 .x10 1 (by decide), addi_other _ .x11 .x0 .x10 200 (by decide),
      ck5_reg _ _ _ _ _ .x10 (by decide), d10,
      address_down (src + 23) 18 3952 immm144 (by omega) (by norm_num), show src + 23 - 18 = src + 5 by omega]
  · rw [ck6, addi_from _ .x12 .x23 0 (by decide), addi_other _ .x10 .x10 .x23 3952 (by decide),
      addi_other _ .x13 .x0 .x23 1 (by decide), addi_other _ .x11 .x0 .x23 200 (by decide),
      ck5_reg _ _ _ _ _ .x23 (by decide), dkeep .x23 (by decide) (by decide) (by decide),
      ck1_keeps s .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ready.digest,
      show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) by decide, address_up]
  · rw [ck6, addi_other _ .x12 .x23 .x5 0 (by decide), addi_other _ .x10 .x10 .x5 3952 (by decide),
      addi_other _ .x13 .x0 .x5 1 (by decide), addi_other _ .x11 .x0 .x5 200 (by decide),
      ck5_reg _ _ _ _ _ .x5 (by decide), dkeep .x5 (by decide) (by decide) (by decide),
      ck1_keeps s .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ready.selector]
  · rw [ck6, addi_other _ .x12 .x23 .x11 0 (by decide), addi_other _ .x10 .x10 .x11 3952 (by decide),
      addi_other _ .x13 .x0 .x11 1 (by decide), addi_from _ .x11 .x0 200 (by decide)]
    try rfl
  · rw [ck6, addi_other _ .x12 .x23 .x13 0 (by decide), addi_other _ .x10 .x10 .x13 3952 (by decide),
      addi_from _ .x13 .x0 1 (by decide)]
    try rfl
  · rw [ck6, addi_pc, addi_pc, addi_pc, addi_pc, p5]
    try rfl

theorem execute_c3_check_leaf (s : MachineState) (src proof : Nat) (index : Index)
    (ready : CkReady s src proof index) (fuel : Nat) :
    execute packedImage (36 + fuel) s false =
      (do let d ← c3CheckQueries s src
          let r ← execute packedImage fuel d false
          return r.charge 86 4) := by
  have sb := ready.sourceBound
  have pa := ck1_pc s src proof index ready
  obtain ⟨_, _, _, h11, h13, _, _, _⟩ := ck1_facts s
  have r1 := ck1_regs s src proof index ready
  have sel1 : (ck1 s).getReg .x5 = 0 :=
    (ck1_keeps s .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.selector
  -- seven ordinary steps and the first compression
  rw [show 36 + fuel = 7 + ((28 + fuel) + 1) by omega, execute_ck1 s ready.pc ready.indexAccess,
    execute_compression_on packedImage (28 + fuel) (ck1 s) false (src + 29) (src + 29) (by omega) (by omega)
      r1.1 r1.2.1 sel1 h11 h13 (fetch_at _ 29 .ECALL (by decide) pa rfl)]
  simp only [c3CheckQueries, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t1 _
  -- two ordinary steps and the second compression
  have w1pc : (writeBits (ck1 s) (wordAddress (src + 29)) t1).pc = BitVec.ofNat 64 (4096 + 4 * 30) := by
    rw [written_pc, pa]; try rfl
  have m1pc : (execInstrBr (writeBits (ck1 s) (wordAddress (src + 29)) t1) (.ADDI .x10 .x10 4064)).pc =
      BitVec.ofNat 64 (4096 + 4 * 31) := by
    rw [addi_pc, w1pc]; try rfl
  obtain ⟨b10, b12, bkeep, bpc⟩ := ck2_regs s src proof index ready t1
  have pb : (ck2 s src t1).pc = BitVec.ofNat 64 (4096 + 4 * 32) := by rw [bpc, pa]; try rfl
  rw [show 28 + fuel = 1 + (1 + ((25 + fuel) + 1)) by omega,
    ordinary_one _ _ (.ADDI .x10 .x10 4064) _ (fetch_at _ 30 _ (by decide) w1pc rfl) rfl rfl,
    ordinary_one _ (ck2 s src t1) (.ADDI .x12 .x10 8) _ (fetch_at _ 31 _ (by decide) m1pc rfl) rfl rfl,
    execute_compression_on packedImage (25 + fuel) (ck2 s src t1) false (src + 25) (src + 26) (by omega) (by omega)
      b10 b12 ((bkeep .x5 (by decide) (by decide)).trans sel1) ((bkeep .x11 (by decide) (by decide)).trans h11)
      ((bkeep .x13 (by decide) (by decide)).trans h13) (fetch_at _ 32 .ECALL (by decide) pb rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t2 _
  -- one ordinary step and the third compression
  obtain ⟨c10, c12, ckeep, cpc⟩ := ck3_regs s src proof index ready t1 t2
  have w2pc : (writeBits (ck2 s src t1) (wordAddress (src + 26)) t2).pc = BitVec.ofNat 64 (4096 + 4 * 33) := by
    rw [written_pc, pb]; try rfl
  have pc3 : (ck3 s src t1 t2).pc = BitVec.ofNat 64 (4096 + 4 * 34) := by rw [cpc, pa]; try rfl
  rw [show 25 + fuel = 1 + ((23 + fuel) + 1) by omega,
    ordinary_one _ (ck3 s src t1 t2) (.ADDI .x10 .x10 4080) _ (fetch_at _ 33 _ (by decide) w2pc rfl) rfl rfl,
    execute_compression_on packedImage (23 + fuel) (ck3 s src t1 t2) false (src + 23) (src + 26) (by omega) (by omega)
      c10 c12 ((ckeep .x5 (by decide) (by decide)).trans sel1) ((ckeep .x11 (by decide) (by decide)).trans h11)
      ((ckeep .x13 (by decide) (by decide)).trans h13) (fetch_at _ 34 .ECALL (by decide) pc3 rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t3 _
  -- tag, salt copy, permutation setup and the permutation call
  have w3pc : (writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3).pc = BitVec.ofNat 64 (4096 + 4 * 35) := by
    rw [written_pc, pc3]; try rfl
  have w4pc : (execInstrBr (writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3) (.ADDI .x31 .x28 40)).pc =
      BitVec.ofNat 64 (4096 + 4 * 36) := by
    rw [addi_pc, w3pc]; try rfl
  have w4x10 : (execInstrBr (writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3) (.ADDI .x31 .x28 40)).getReg
      .x10 = wordAddress (src + 23) := by
    rw [addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, c10]
  have sdStep : ordinaryStep (execInstrBr (writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3)
      (.ADDI .x31 .x28 40)) (.base (.SD .x10 .x31 0)) = some (ck4 s src t1 t2 t3) := by
    have valid : memoryArgumentsValid (execInstrBr (writeBits (ck3 s src t1 t2) (wordAddress (src + 26)) t3)
        (.ADDI .x31 .x28 40)) (.SD .x10 .x31 0) = true := by
      change accessValid (_ + signExtend12 0) 8 = true
      rw [w4x10, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) by decide]
      exact word_access _ _ (by omega)
    change (if memoryArgumentsValid _ (.SD .x10 .x31 0) = true then
      some (execInstrBr _ (.SD .x10 .x31 0)) else none) = _
    rw [valid]
    rfl
  have copyRun : ∀ X, execute packedImage (16 + X) (ck4 s src t1 t2 t3) false =
      (do let r ← execute packedImage X (ck5 s src t1 t2 t3) false; return r.charge 16 0) := fun X =>
    copy_field_execute (fieldCode .nonce) _ _ _ (ck4_copy_ready s src proof index ready t1 t2 t3) X false
  have p5 := ck5_pc s src proof index ready t1 t2 t3
  have q1 : (execInstrBr (ck5 s src t1 t2 t3) (.ADDI .x11 .x0 200)).pc = BitVec.ofNat 64 (4096 + 4 * 54) := by
    rw [addi_pc, p5]; try rfl
  have q2 : (execInstrBr (execInstrBr (ck5 s src t1 t2 t3) (.ADDI .x11 .x0 200)) (.ADDI .x13 .x0 1)).pc =
      BitVec.ofNat 64 (4096 + 4 * 55) := by
    rw [addi_pc, q1]; try rfl
  have q3 : (execInstrBr (execInstrBr (execInstrBr (ck5 s src t1 t2 t3) (.ADDI .x11 .x0 200)) (.ADDI .x13 .x0 1))
      (.ADDI .x10 .x10 3952)).pc = BitVec.ofNat 64 (4096 + 4 * 56) := by
    rw [addi_pc, q2]; try rfl
  obtain ⟨e10, e12, e5, e11, e13, e6pc⟩ := ck6_facts s src proof index ready t1 t2 t3
  rw [show 23 + fuel = 1 + (1 + (16 + (1 + (1 + (1 + (1 + (fuel + 1))))))) by omega,
    ordinary_one _ _ (.ADDI .x31 .x28 40) _ (fetch_at _ 35 _ (by decide) w3pc rfl) rfl rfl,
    ordinary_one _ (ck4 s src t1 t2 t3) (.SD .x10 .x31 0) _ (fetch_at _ 36 _ (by decide) w4pc rfl) sdStep rfl,
    copyRun,
    ordinary_one _ _ (.ADDI .x11 .x0 200) _ (fetch_at _ 53 _ (by decide) p5 rfl) rfl rfl,
    ordinary_one _ _ (.ADDI .x13 .x0 1) _ (fetch_at _ 54 _ (by decide) q1 rfl) rfl rfl,
    ordinary_one _ _ (.ADDI .x10 .x10 3952) _ (fetch_at _ 55 _ (by decide) q2 rfl) rfl rfl,
    ordinary_one _ (ck6 s src t1 t2 t3) (.ADDI .x12 .x23 0) _ (fetch_at _ 56 _ (by decide) q3 rfl) rfl rfl,
    execute_permutation_call packedImage fuel (ck6 s src t1 t2 t3) false (src + 5) 1536 (by omega) (by decide)
      e10 e12 e5 e11 e13 (fetch_at _ 57 .ECALL (by decide) e6pc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro y _
  simp only [charge_charge]
  rfl

/-! ### Rows under a fixed oracle -/

section rows
attribute [local irreducible] execute readBuffer writeBits packBuffer

theorem c3_check_rows (oracle : Oracle) (s : MachineState) (src : Nat) :
    let q1 := readBuffer (ck1 s) (8 * (src + 29)) 64
    let t1 := oracle.compression q1
    let q2 := readBuffer (ck2 s src t1) (8 * (src + 25)) 64
    let t2 := oracle.compression q2
    let q3 := readBuffer (ck3 s src t1 t2) (8 * (src + 23)) 64
    let t3 := oracle.compression q3
    let q4 := packBuffer (window (memoryView (ck6 s src t1 t2 t3)) (src + 5))
    let y := oracle.permutation q4
    checkEvaluation oracle (recordRows (c3CheckQueries s src)) =
      ((ck7 s src t1 t2 t3 y, [.compression q1 t1, .compression q2 t2, .compression q3 t3, .permutation q4 y]), 4) := by
  simp only [c3CheckQueries, record_rows_query, check_evaluation_public_bind, check_evaluation_map,
    record_rows_pure, check_evaluation_pure]
  rfl

end rows

/-! ### Memory meaning -/

/-- The salt words copied from the proof. -/
def ckNonce (s : MachineState) (proof : Nat) : Words 2 := fun i => (readBuffer s proof 16).extractLsb' (64 * i.val) 64

theorem ck_mem_outside (M : Memory) (src : Nat) (t1 t2 t3 : BitVec 256) (tag : Word) (w : Nat)
    (outside : w < src + 23 ∨ src + 33 ≤ w) : ckMem M src t1 t2 t3 tag w = M w := by
  simp only [ckMem, writeWord, writeWindow]
  split_ifs <;> first | omega | rfl

theorem ck_first (s : MachineState) (src : Nat) :
    readBuffer (ck1 s) (8 * (src + 29)) 64 = c3FirstInput (window (memoryView s) (src + 5)) := by
  rw [c3_read_compression, memoryView_congr (ck1_facts s).1, show src + 29 = src + 5 + 24 by omega,
    c3_first_window]
  try rfl

theorem ck_second (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 : BitVec 256) :
    readBuffer (ck2 s src t1) (8 * (src + 25)) 64 =
      packWords8 (c3SecondWords (window (memoryView s) (src + 5)) (digestWords t1)) := by
  have sb := ready.sourceBound
  have same : (window (memoryView (ck2 s src t1)) (src + 25) : Words 8) =
      window (writeWindow (memoryView s) (src + 29) (digestWords t1)) (src + 25) := by
    funext k
    exact ck2_memory s src proof index ready t1 (src + 25 + k.val) (by have := k.isLt; omega)
  have shifted := c3_second_window (memoryView s) (src + 5) t1
  rw [show src + 5 + 24 = src + 29 by omega, show src + 5 + 20 = src + 25 by omega] at shifted
  rw [c3_read_compression, same, shifted]

theorem ck_third (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 : BitVec 256) :
    readBuffer (ck3 s src t1 t2) (8 * (src + 23)) 64 =
      packWords8 (c3ThirdWords (window (memoryView s) (src + 5)) (digestWords t1) (digestWords t2)) := by
  have sb := ready.sourceBound
  have same : (window (memoryView (ck3 s src t1 t2)) (src + 23) : Words 8) =
      window (writeWindow (writeWindow (memoryView s) (src + 29) (digestWords t1)) (src + 26) (digestWords t2))
        (src + 23) := by
    funext k
    exact ck3_memory s src proof index ready t1 t2 (src + 23 + k.val) (by have := k.isLt; omega)
  have shifted := c3_third_window (memoryView s) (src + 5) t1 t2
  rw [show src + 5 + 24 = src + 29 by omega, show src + 5 + 21 = src + 26 by omega,
    show src + 5 + 18 = src + 23 by omega] at shifted
  rw [c3_read_compression, same, shifted]

theorem ck5_frame (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) (w : Nat) (bound : w < 2 ^ 33) (outside : w < src + 24 ∨ src + 26 ≤ w) :
    memoryView (ck5 s src t1 t2 t3) w = memoryView (ck4 s src t1 t2 t3) w := by
  have sb := ready.sourceBound
  have frame := (field_bytes .nonce (ck4 s src t1 t2 t3) _ _ (ck4_copy_ready s src proof index ready t1 t2 t3)
    (by have := ready.apart; omega)).2
  apply word_eq_of_byte_frame
  intro i hi
  apply frame
  intro j hj eq
  have same := congrArg BitVec.toNat eq
  have one : 8 * w + i < 2 ^ 64 := by omega
  change j < 16 at hj
  have two : 8 * (src + 24) + j < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt two] at same
  omega

theorem ck4_proof_read (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) : readBuffer (ck4 s src t1 t2 t3) proof 16 = readBuffer s proof 16 := by
  have ap := ready.apart
  have pb := ready.proofBound
  apply buffer_byte_frame
  intro j hj
  rw [ck4_memory s src proof index ready t1 t2 t3 _ (by unfold MEMORY_BYTES at pb; omega),
    ck_mem_outside _ _ _ _ _ _ _ (by omega)]

theorem ck_perm_input (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) :
    (window (memoryView (ck6 s src t1 t2 t3)) (src + 5) : Words 25) =
      c3PermWords index (ckNonce s proof) (window (memoryView s) (src + 5)) (digestWords t3) := by
  have sb := ready.sourceBound
  have ap := ready.apart
  funext k
  have kt := k.isLt
  change memoryView (ck6 s src t1 t2 t3) (src + 5 + k.val) = _
  rw [memoryView_congr (ck6_mem s src t1 t2 t3)]
  by_cases nonceWord : k.val = 19 ∨ k.val = 20
  · have fr : readBuffer (ck5 s src t1 t2 t3) (8 * (src + 24)) 16 = readBuffer (ck4 s src t1 t2 t3) proof 16 :=
      field_read .nonce _ _ _ (ck4_copy_ready s src proof index ready t1 t2 t3) (by omega)
    have win := congrFun (buffer_window (ck5 s src t1 t2 t3) (src + 24) 2) ⟨k.val - 19, by omega⟩
    change memoryView (ck5 s src t1 t2 t3) (src + 24 + (k.val - 19)) =
      (readBuffer (ck5 s src t1 t2 t3) (8 * (src + 24)) (8 * 2)).extractLsb' (64 * (k.val - 19)) 64 at win
    rw [show src + 5 + k.val = src + 24 + (k.val - 19) by omega, win, show 8 * 2 = 16 by rfl, fr,
      ck4_proof_read s src proof index ready t1 t2 t3]
    simp only [c3PermWords]
    rw [dite_eq_right (show ¬ k.val < 18 by omega), ite_eq_right (show k.val ≠ 18 by omega), dite_eq_left (show k.val < 21 by omega)]
    rfl
  · rw [ck5_frame s src proof index ready t1 t2 t3 _ (by omega) (by omega),
      ck4_memory s src proof index ready t1 t2 t3 _ (by omega)]
    by_cases low : k.val < 18
    · rw [ck_mem_outside _ _ _ _ _ _ _ (by omega)]
      simp only [c3PermWords]
      rw [dite_eq_left low]
      rfl
    · by_cases tagWord : k.val = 18
      · rw [show src + 5 + k.val = src + 23 by omega]
        simp only [c3PermWords]
        rw [dite_eq_right low, ite_eq_left tagWord]
        unfold ckMem
        rw [writeWord, ite_eq_left rfl]
      · simp only [c3PermWords]
        rw [dite_eq_right low, ite_eq_right tagWord, dite_eq_right (show ¬ k.val < 21 by omega)]
        unfold ckMem
        rw [writeWord, ite_eq_right (show src + 5 + k.val ≠ src + 23 by omega), writeWindow,
          dite_eq_left (show src + 26 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 26 + 4 by omega)]
        congr 1
        ext
        simp only [Fin.val_mk]
        omega

/-! ### The final state -/

theorem ck7_keeps (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) (y : Block) (r : Reg) (a : r ≠ .x6) (b : r ≠ .x28) (c : r ≠ .x11)
    (d : r ≠ .x13) (e : r ≠ .x10) (f : r ≠ .x12) (g : r ≠ .x31) :
    (ck7 s src t1 t2 t3 y).getReg r = s.getReg r := by
  obtain ⟨_, dkeep, _⟩ := ck4_regs s src proof index ready t1 t2 t3
  unfold ck7
  refine (CommitGolfCandidate.writeBits_register _ _ _ _).trans ?_
  rw [ck6, addi_other _ _ _ _ _ f, addi_other _ _ _ _ _ e,
    addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ c, ck5_reg _ _ _ _ _ _ g, dkeep r e f g,
    ck1_keeps s r a b c d e f]

theorem ck7_index (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) (y : Block) :
    (ck7 s src t1 t2 t3 y).getReg .x6 = BitVec.ofNat 64 index.val := by
  obtain ⟨_, dkeep, _⟩ := ck4_regs s src proof index ready t1 t2 t3
  unfold ck7
  refine (CommitGolfCandidate.writeBits_register _ _ _ _).trans ?_
  rw [ck6, addi_other _ .x12 .x23 .x6 0 (by decide),
    addi_other _ .x10 .x10 .x6 3952 (by decide), addi_other _ .x13 .x0 .x6 1 (by decide),
    addi_other _ .x11 .x0 .x6 200 (by decide), ck5_reg _ _ _ _ _ .x6 (by decide),
    dkeep .x6 (by decide) (by decide) (by decide), (ck1_facts s).2.1, ready.indexValue]

theorem ck7_pc (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) (y : Block) : (ck7 s src t1 t2 t3 y).pc = 0x10e8 := by
  unfold ck7
  refine (written_pc _ _ _).trans ?_
  rw [(ck6_facts s src proof index ready t1 t2 t3).2.2.2.2.2]
  try rfl

theorem ck7_digest (s : MachineState) (src : Nat) (t1 t2 t3 : BitVec 256) (y : Block) :
    readBuffer (ck7 s src t1 t2 t3 y) 12288 32 = outputDigest y := by
  unfold ck7
  exact write_bits_digest (bits := 1600) (ck6 s src t1 t2 t3) 12288 0 y (by decide) (by decide)

theorem ck7_frame (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (t1 t2 t3 : BitVec 256) (y : Block) (w : Nat) (bound : w < 2 ^ 33)
    (inputOutside : w < src ∨ src + 37 ≤ w) (scratchOutside : w < 1534 ∨ 1576 ≤ w) :
    memoryView (ck7 s src t1 t2 t3 y) w = memoryView s w := by
  unfold ck7
  rw [permutation_write_memory _ 1536 w y (by decide) bound, writeWindow,
    dite_eq_right (show ¬(1536 ≤ w ∧ w < 1536 + 25) by omega), memoryView_congr (ck6_mem s src t1 t2 t3),
    ck5_frame s src proof index ready t1 t2 t3 w bound (by omega),
    ck4_memory s src proof index ready t1 t2 t3 w bound, ck_mem_outside _ _ _ _ _ _ _ (by omega)]

/-- The leaf calls under a fixed oracle: the final state and the recorded rows. -/
def c3Raw (oracle : Oracle) (s : MachineState) (src : Nat) : MachineState × List PublicRow :=
  (checkEvaluation oracle (recordRows (c3CheckQueries s src))).1

theorem c3_raw_spec (oracle : Oracle) (s : MachineState) (src proof : Nat) (index : Index)
    (ready : CkReady s src proof index) (v : Words 32) (hv : window (memoryView s) (src + 5) = v) :
    (∃ t1 t2 t3 : BitVec 256, (c3Raw oracle s src).1 =
        ck7 s src t1 t2 t3 (oracle.permutation (c3PermInput oracle.compression index (ckNonce s proof) v))) ∧
      (c3Raw oracle s src).2 =
        [.compression (c3FirstInput v) (c3T1 oracle.compression v),
         .compression (c3SecondInput oracle.compression v) (c3T2 oracle.compression v),
         .compression (c3ThirdInput oracle.compression v) (c3T3 oracle.compression v),
         .permutation (c3PermInput oracle.compression index (ckNonce s proof) v)
           (oracle.permutation (c3PermInput oracle.compression index (ckNonce s proof) v))] := by
  subst hv
  have rows := c3_check_rows oracle s src
  dsimp only at rows
  rw [ck_first] at rows
  generalize ht1 : oracle.compression (c3FirstInput (window (memoryView s) (src + 5))) = t1 at rows
  rw [ck_second s src proof index ready t1] at rows
  generalize ht2 : oracle.compression (packWords8 (c3SecondWords (window (memoryView s) (src + 5))
    (digestWords t1))) = t2 at rows
  rw [ck_third s src proof index ready t1 t2] at rows
  generalize ht3 : oracle.compression (packWords8 (c3ThirdWords (window (memoryView s) (src + 5))
    (digestWords t1) (digestWords t2))) = t3 at rows
  rw [ck_perm_input s src proof index ready t1 t2 t3] at rows
  subst ht1 ht2 ht3
  exact ⟨⟨_, _, _, congrArg (fun r => r.1.1) rows⟩, congrArg (fun r => r.1.2) rows⟩

theorem c3_calls (oracle : Oracle) (s : MachineState) (src : Nat) :
    (checkEvaluation oracle (recordRows (c3CheckQueries s src))).2 = 4 := by
  rw [c3_check_rows]

/-! ### The record block -/

def c3Block (oracle : Oracle) (ordinal : Nat) (_index : Index) (s : MachineState) : RecordBlock :=
  let raw := c3Raw oracle s (checkSourceWord ordinal)
  ⟨beginLower raw.1 5, 41, 91, raw.2⟩

theorem ck_ready (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    CkReady s (checkSourceWord ordinal) (checkProofByte ordinal) (honestIndex input.positions ordinal present).val := by
  obtain ⟨aligned, _, _, room, _⟩ := packed_record_geometry input ordinal present fits
  have card := checker_positions_bound input
  have acc := word_access (checkIndexWord ordinal) 0 (by unfold checkIndexWord; omega)
  rw [address_up, Nat.add_zero] at acc
  refine ⟨cursor.pc.trans (ite_eq_right (show ¬ ordinal = input.positions.card by omega)), ?_, ?_, cursor.value,
    cursor.proof, cursor.tag, cursor.digest, cursor.selector, ?_, ?_, aligned, ?_, ?_⟩
  · rw [cursor.index]; exact acc
  · rw [cursor.index]; exact record_input_index input ordinal present s framed
  · unfold checkSourceWord; omega
  · unfold checkSourceWord; omega
  · omega
  · unfold checkSourceWord checkProofByte; omega

private theorem saved_ordinary (r : Reg) (keep : RecordSaved r) :
    r≠.x6 ∧ r≠.x28 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x13 ∧ r≠.x12 ∧ r≠.x31 ∧ r≠.x21 ∧ r≠.x29 := by
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem c3_exact_run (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) (proof : Nat)
    (ready : CkReady s (checkSourceWord ordinal) proof index) (fuel : Nat) :
    let out := c3Block oracle ordinal index s
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel out.state false))
    checkEvaluation oracle (recordRows (execute packedImage (out.steps + fuel) s false)) =
      ((tail.1.1.charge out.cycles 4, out.rows ++ tail.1.2), 4 + tail.2) := by
  let src := checkSourceWord ordinal
  let raw := c3Raw oracle s src
  have pc : raw.1.pc = 0x10e8 := by
    obtain ⟨⟨t1, t2, t3, eq⟩, _⟩ := c3_raw_spec oracle s src proof index ready _ rfl
    change (c3Raw oracle s src).1.pc = _
    rw [eq]
    exact ck7_pc s src proof index ready _ _ _ _
  change checkEvaluation oracle (recordRows (execute packedImage (41 + fuel) s false)) = _
  rw [show 41 + fuel = 36 + (5 + fuel) by omega, execute_c3_check_leaf s src proof index ready, check_recorded_bind]
  simp only [bind_pure_comp, check_recorded_map]
  erw [execute_lower_setup_packed raw.1 pc]
  simp only [bind_pure_comp, check_recorded_map]
  change (let tail := checkEvaluation oracle (recordRows (execute packedImage fuel (beginLower raw.1 5) false))
          ((((tail.1.1.charge 5 0).charge 86 4), raw.2 ++ tail.1.2),
            (checkEvaluation oracle (recordRows (c3CheckQueries s src))).2 + tail.2)) = _
  rw [c3_calls]
  simp only [Execution.charge, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  rfl

theorem c3_leaf_block : LeafBlockRefines c3Block := by
  intro oracle input ordinal present s fits cursor framed
  let item := honestIndex input.positions ordinal present
  let src := checkSourceWord ordinal
  let proof := checkProofByte ordinal
  have ready : CkReady s src proof item.val := ck_ready input ordinal present s fits cursor framed
  have values : window (memoryView s) (src + 5) = entryWords (input.values item) :=
    checker_value_data (fun _ => input.values item) item.val (record_input_value input ordinal present s framed)
  obtain ⟨⟨t1, t2, t3, finalEq⟩, rowsEq⟩ := c3_raw_spec oracle s src proof item.val ready _ values
  let raw := (c3Raw oracle s src).1
  have rawEq : raw = ck7 s src t1 t2 t3 _ := finalEq
  have params := lower_setup_post raw
  have value (r : Reg) (g6 : r≠.x6) (g28 : r≠.x28) (g10 : r≠.x10) (g11 : r≠.x11)
      (g13 : r≠.x13) (g12 : r≠.x12) (g31 : r≠.x31) : raw.getReg r = s.getReg r := by
    rw [rawEq]; exact ck7_keeps s src proof item.val ready _ _ _ _ r g6 g28 g11 g13 g10 g12 g31
  have finalSaved : LowerSaved s (beginLower raw 5) := by
    intro r safe
    obtain ⟨h6, h28, h10, h11, h13, h12, h31, h21, h29⟩ := saved_ordinary r safe
    exact (lower_setup_register raw r h21 h6 h11 h13 h29).trans (value r h6 h28 h10 h11 h13 h12 h31)
  have digest : readBuffer (c3Block oracle ordinal item.val s).state 12288 32 =
      c3LeafDigest oracle.compression oracle.permutation item.val (ckNonce s proof) (entryWords (input.values item)) := by
    change readBuffer (beginLower raw 5) 12288 32 = _
    rw [read_buffer_memory_congr _ _ (lower_setup_mem raw), rawEq, ck7_digest]
    rfl
  refine ⟨by change 41 ≤ 169; decide, c3_exact_run oracle ordinal item.val s proof ready, ?_, finalSaved, ?_, ?_, ?_⟩
  · change LowerCursor ordinal item.val 0 (beginLower raw 5)
    refine ⟨?_, ?_, ?_, params.2.2.2.2.1, (finalSaved .x23 (by decide)).trans cursor.digest,
      (finalSaved .x24 (by decide)).trans cursor.pair, (finalSaved .x5 (by decide)).trans cursor.selector,
      params.2.2.1, params.2.2.2.1, (finalSaved .x20 (by decide)).trans cursor.challengeLength⟩
    · change (beginLower raw 5).pc = 4348
      rw [params.2.2.2.2.2, rawEq, ck7_pc s src proof item.val ready]
      rfl
    · rw [params.2.1, rawEq, ck7_index s src proof item.val ready,
        ← rawEq, value .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        cursor.challengeLength, ← BitVec.ofNat_add]
      simp only [Opening.lowerNode, Nat.pow_zero, Nat.div_one, Nat.add_comm]
    · rw [params.1, value .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        cursor.proof]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 16 = BitVec.ofNat 64 (_ + 16)
      rw [← BitVec.ofNat_add]
  · intro w bound inputOutside scratchOutside
    change memoryView (beginLower raw 5) w = _
    rw [memoryView_congr (lower_setup_mem raw), rawEq]
    exact ck7_frame s src proof item.val ready _ _ _ _ w bound inputOutside scratchOutside
  · refine ⟨⟨ckNonce s proof, ?_, digest.symm⟩⟩
    change C3LeafRows (c3Raw oracle s src).2 _ _ _ _ _
    rw [rowsEq]
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  · intro message salts canonical
    rw [digest]
    have loaded : RecordInputFrame (honestCheckInput oracle message input.positions salts) ordinal s :=
      Eq.mp (congrArg (fun data => RecordInputFrame data ordinal s) canonical) framed
    have salt := packed_record_nonce oracle message input.positions salts ordinal present s loaded
    have nonce : ckNonce s proof = saltWords (salts item.val) := by
      funext i
      change (readBuffer s (checkProofByte ordinal) 16).extractLsb' (64 * i.val) 64 = _
      rw [salt]
      rfl
    have entry : input.values item = message item.val := by
      let lookup (record : CheckInput) : Entry :=
        if h : item.val ∈ record.positions then record.values ⟨item.val, h⟩ else 0
      have transported := congrArg lookup canonical
      have inside : item.val ∈ (honestCheckInput oracle message input.positions salts).positions := item.property
      dsimp only [lookup] at transported
      rw [dite_eq_left item.property, dite_eq_left inside] at transported
      exact transported
    rw [nonce, entry]
    rfl

end TwoPermutationPrototype.Packed.C3RecordLeaf
