import CommitGolfCandidate.MoonOpenCopy29

/-! Verified subroutine specifications for all six slow-path copy families (`copy32_r`, `copy30_r`,
`copy29_r`, `copy32_x3_r`, `copy30_x4_r`, `copy29_x2_r`), plus `writerState_advance_base`. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Proof Pointer Advance & Helper Lemmas -/

theorem setReg_x0_eq (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl

theorem writerState_of_mem_eq {clean : Prop} {s s' : MachineState}
    {r : Fin 8} {flushedR4 : Bool} {base dstOff : Nat} {written : List Byte}
    (hw : WriterState clean s r flushedR4 base dstOff written)
    (hmem : ∀ a, s'.getMem a = s.getMem a)
    (hx25 : s'.getReg .x25 = s.getReg .x25)
    (hx12 : s'.getReg .x12 = s.getReg .x12) :
    WriterState clean s' r flushedR4 base dstOff written := by
  have hbyte : ∀ a, s'.getByte a = s.getByte a := fun a => by simp only [MachineState.getByte, hmem]
  refine ⟨hw.hbase8, hw.hdst8, hw.hlen, hw.hbound, hx25.trans hw.rx25, hw.hflushed_ok,
    fun hcl j hj => (hbyte _).trans (hw.hbytes hcl j hj), fun hcl => ?_⟩
  have hrem := hw.hrem hcl
  cases flushedR4 with
  | true =>
    simp only [↓reduceIte] at hrem ⊢
    intro j hj; exact (hbyte _).trans (hrem j hj)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
    by_cases hr0 : r.val = 0
    · simp [hr0]
    · simp only [hr0, ↓reduceIte] at hrem ⊢
      exact ⟨fun j hj => by rw [hx12]; exact hrem.1 j hj, fun j h1 h2 => by rw [hx12]; exact hrem.2 j h1 h2⟩

/-- Advancing `x25` by `dstOff` (a multiple of 8) folds `dstOff` into `base` and resets `dstOff` to `0`. -/
theorem writerState_advance_base {clean : Prop} {s : MachineState} {r : Fin 8}
    {base dstOff : Nat} {written : List Byte}
    (hw : WriterState clean s r false base dstOff written)
    (hdst_off : dstOff < 2048) (hnext_pc : Word) :
    WriterState clean ((s.setReg .x25 (s.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff))).setPC hnext_pc)
      r false (base + dstOff) 0 written := by
  have hbase8 := hw.hbase8
  have hdst8 := hw.hdst8
  have hrx25 : ((s.setReg .x25 (s.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff))).setPC hnext_pc).getReg .x25 =
      BitVec.ofNat 64 (11341403200 + (base + dstOff)) := by
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hw.rx25, signExtend12_nonneg dstOff hdst_off, ← BitVec.ofNat_add]
    congr 1; omega
  have hbyte : ∀ a, ((s.setReg .x25 (s.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff))).setPC hnext_pc).getByte a =
      s.getByte a := fun a => by simp [getByte_setPC, getByte_setReg]
  have hx12 : ((s.setReg .x25 (s.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff))).setPC hnext_pc).getReg .x12 =
      s.getReg .x12 := by simp [getReg_setReg_ne']
  refine ⟨by omega, by omega, by have := hw.hlen; omega, by have := hw.hbound; omega,
    hrx25, by simp, fun hcl j hj => by rw [hbyte]; exact hw.hbytes hcl j (by omega), fun hcl => ?_⟩
  have hrem := hw.hrem hcl
  simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
  by_cases hr0 : r.val = 0
  · simp [hr0]
  · simp only [hr0, ↓reduceIte] at hrem ⊢
    simpa only [hx12, Nat.add_zero] using hrem

/-! ### 2. Subroutine PC Tables & Lengths -/

def pcCopy32 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_copy32_r0 | 1 => PC_copy32_r1 | 2 => PC_copy32_r2 | 3 => PC_copy32_r3
  | 4 => PC_copy32_r4 | 5 => PC_copy32_r5 | 6 => PC_copy32_r6 | _ => PC_copy32_r7

def pcCopy30 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_copy30_r0 | 1 => PC_copy30_r1 | 2 => PC_copy30_r2 | 3 => PC_copy30_r3
  | 4 => PC_copy30_r4 | 5 => PC_copy30_r5 | 6 => PC_copy30_r6 | _ => PC_copy30_r7

def pcCopy29 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_copy29_r0 | 1 => PC_copy29_r1 | 2 => PC_copy29_r2 | 3 => PC_copy29_r3
  | 4 => PC_copy29_r4 | 5 => PC_copy29_r5 | 6 => PC_copy29_r6 | _ => PC_copy29_r7

def pcCopy32x3 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_copy32_x3_r0 | 1 => PC_copy32_x3_r1 | 2 => PC_copy32_x3_r2 | 3 => PC_copy32_x3_r3
  | 4 => PC_copy32_x3_r4 | 5 => PC_copy32_x3_r5 | 6 => PC_copy32_x3_r6 | _ => PC_copy32_x3_r7

def pcCopy30x4 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_copy30_x4_r0 | 1 => PC_copy30_x4_r1 | 2 => PC_copy30_x4_r2 | 3 => PC_copy30_x4_r3
  | 4 => PC_copy30_x4_r4 | 5 => PC_copy30_x4_r5 | 6 => PC_copy30_x4_r6 | _ => PC_copy30_x4_r7

def pcCopy29x2 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_copy29_x2_r0 | 1 => PC_copy29_x2_r1 | 2 => PC_copy29_x2_r2 | 3 => PC_copy29_x2_r3
  | 4 => PC_copy29_x2_r4 | 5 => PC_copy29_x2_r5 | 6 => PC_copy29_x2_r6 | _ => PC_copy29_x2_r7

def copy32SubCode (r : Fin 8) : List Instruction :=
  dwordsCode r 4 .x10 0 0 false false ++
  [.base (.ADDI .x25 .x25 (32#12)), .base (.JALR .x0 .x1 (0#12))]

def copy30SubCode (r : Fin 8) : List Instruction :=
  copy30Code r .x10 0 false ++
  [.base (.ADDI .x25 .x25 (BitVec.ofNat 12 (copy30NextDstOff r 0))),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * (copy30NextR r).val))),
   .base (.JALR .x0 .x1 (0#12))]

def copy29SubCode (r : Fin 8) : List Instruction :=
  copy29Code r .x10 0 .x5 0 false false false ++
  [.base (.ADDI .x25 .x25 (BitVec.ofNat 12 (copy29NextDstOff r 0))),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * (copy29NextR r).val))),
   .base (.JALR .x0 .x1 (0#12))]

def copy32x3SubCode (r : Fin 8) : List Instruction :=
  dwordsCode r 4 .x10 0 0 false (r.val == 4) ++
  dwordsCode r 4 .x28 0 32 (r.val == 4) (r.val == 4) ++
  dwordsCode r 4 .x8 0 64 (r.val == 4) false ++
  [.base (.ADDI .x25 .x25 (96#12)), .base (.JALR .x0 .x1 (0#12))]

def copy30x4SubCode (r : Fin 8) : List Instruction :=
  let r1 := copy30NextR r; let d1 := copy30NextDstOff r 0
  let r2 := copy30NextR r1; let d2 := copy30NextDstOff r1 d1
  let r3 := copy30NextR r2; let d3 := copy30NextDstOff r2 d2
  copy30Code r .x10 0 false ++
  copy30Code r1 .x28 d1 false ++
  copy30Code r2 .x8 d2 false ++
  copy30Code r3 .x19 d3 false ++
  [.base (.ADDI .x25 .x25 (120#12)), .base (.JALR .x0 .x1 (0#12))]

def copy29x2NextR (r : Fin 8) : Fin 8 := copy29NextR (copy29NextR r)

def copy29x2NextDstOff (r : Fin 8) : Nat :=
  copy29NextDstOff (copy29NextR r) (copy29NextDstOff r 0)

def copy29x2SubCode (r : Fin 8) : List Instruction :=
  let r1 := copy29NextR r; let d1 := copy29NextDstOff r 0; let f1 := copy29NextFlushedR4 r true
  let r2 := copy29NextR r1; let d2 := copy29NextDstOff r1 d1
  copy29Code r .x10 0 .x19 0 true false true ++
  copy29Code r1 .x28 d1 .x19 6 false f1 false ++
  [.base (.ADDI .x5 .x19 (0#12)),
   .base (.ADDI .x25 .x25 (BitVec.ofNat 12 d2)),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r2.val))),
   .base (.JALR .x0 .x1 (0#12))]

private theorem codeAt_copy32 (r : Fin 8) : CodeAt (pcCopy32 r) (copy32SubCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_copy30 (r : Fin 8) : CodeAt (pcCopy30 r) (copy30SubCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_copy29 (r : Fin 8) : CodeAt (pcCopy29 r) (copy29SubCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_copy32x3 (r : Fin 8) : CodeAt (pcCopy32x3 r) (copy32x3SubCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_copy30x4 (r : Fin 8) : CodeAt (pcCopy30x4 r) (copy30x4SubCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_copy29x2 (r : Fin 8) : CodeAt (pcCopy29x2 r) (copy29x2SubCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

/-! ### 3. Subroutine Execution Specifications -/

/-- `copy32_r`: copy 32 B from `x10`, advance `x25 += 32`, return via `x1`. -/
theorem openRuns_sub_copy32 {clean : Prop} {s : MachineState} {r : Fin 8}
    {retPc srcBase base : Nat} {written : List Byte} {d : Digest}
    (hpc : s.pc = pcAt (pcCopy32 r))
    (hx1 : s.getReg .x1 = pcAt retPc)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 srcBase)
    (hsrc_al : srcBase % 8 = 0)
    (hsrc_bd : srcBase + 32 ≤ 11341403200)
    (hsrc_mem : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (srcBase + 8 * k)) = d.extractLsb' (64 * k) 64)
    (hbase_bd : base + 40 ≤ 8556390424)
    (hw : WriterState clean s r false base 0 written) :
    let cyc := (copy32SubCode r).length
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt retPc ∧
      RegsEqExcept [.x5, .x6, .x12, .x25] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' r false (base + 32) 0 (written ++ bitsToBytes d 32) := by
  have hcode := codeAt_copy32 r
  have hcodeL := hcode.left
  have hcodeR := hcode.right
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_dwords 4 (s := s) (r := r)
    (vals := fun k => d.extractLsb' (64 * k) 64)
    (by omega) hcodeL hpc (by decide) hx10 (by omega) (by omega) (by omega)
    (fun hcl k hk => by simpa only [Nat.add_zero] using hsrc_mem hcl k hk)
    (by omega) (by omega) hw
  rw [(bitsToBytes_take_dwords d 4).symm] at hw1
  simp only [Bool.and_false] at hw1
  set pc1 := pcCopy32 r + (dwordsCode r 4 .x10 0 0 false false).length
  have hbdR : pc1 + 2 ≤ OPEN_CODE_LEN := by have := hcodeR.1; simpa using this
  have hi0 : openInstr pc1 = .base (.ADDI .x25 .x25 (32#12)) := by have h := hcodeR.2 0 (by simp); simpa using h
  have hi1 : openInstr (pc1 + 1) = .base (.JALR .x0 .x1 (0#12)) := by have h := hcodeR.2 1 (by simp); simpa using h
  have ha1 := step_ADDI (s := s1) (by omega) hpc1 hi0
  set s2 := (s1.setReg .x25 (s1.getReg .x25 + signExtend12 (32#12))).setPC (pcAt (pc1 + 1))
  have hs2_x1 : s2.getReg .x1 = pcAt retPc := by
    simp [s2, getReg_setReg_ne', (hregs1 .x1 (by simp)).trans hx1]
  have ha2 := step_JALR (s := s2) (by omega) rfl hi1 hs2_x1
  set s3 := (s2.setReg .x0 (pcAt (pc1 + 1 + 1))).setPC (pcAt retPc)
  have hlen : (copy32SubCode r).length = (dwordsCode r 4 .x10 0 0 false false).length + 2 := by
    simp [copy32SubCode]
  refine ⟨s3, by rw [hlen]; exact (hr1.trans ha1).trans ha2, rfl, ?_, hp1.trans (fun _ _ => by simp [s3, s2]), ?_⟩
  · intro reg hreg
    have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
    have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
    have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
    have hne25 : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h0 : s3.getReg reg = s2.getReg reg := by
      cases reg <;> simp [s3, setReg_x0_eq]
    exact h0.trans ((by simp [s2, getReg_setReg_ne' .x25 reg hne25.symm] : s2.getReg reg = s1.getReg reg).trans
      (hregs1 reg (by simp [hne5, hne6, hne12])))
  · have hw2 : WriterState clean s2 r false (base + 32) 0 (written ++ bitsToBytes d 32) :=
      writerState_advance_base (dstOff := 32) hw1 (by omega) (pcAt (pc1 + 1))
    exact writerState_of_mem_eq hw2 (fun _ => by simp [s3])
      (by simp [s3, getReg_setReg_ne']) (by simp [s3, getReg_setReg_ne'])

/-- `copy30_r`: copy 30 B from `x10`, advance `x25`, set `x14 = 8 * nr`, return via `x1`. -/
theorem openRuns_sub_copy30 {clean : Prop} {s : MachineState} {r : Fin 8}
    {retPc srcBase base : Nat} {written : List Byte} {d : Digest}
    (hpc : s.pc = pcAt (pcCopy30 r))
    (hx1 : s.getReg .x1 = pcAt retPc)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 srcBase)
    (hsrc_al : srcBase % 8 = 0)
    (hsrc_bd : srcBase + 32 ≤ 11341403200)
    (hsrc_mem : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (srcBase + 8 * k)) = d.extractLsb' (64 * k) 64)
    (hd_clean : clean → mask240 d = d)
    (hbase_bd : base + 40 ≤ 8556390424)
    (hw : WriterState clean s r false base 0 written) :
    let cyc := (copy30SubCode r).length
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt retPc ∧
      s'.getReg .x14 = BitVec.ofNat 64 (8 * (copy30NextR r).val) ∧
      RegsEqExcept [.x5, .x6, .x12, .x14, .x25] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' (copy30NextR r) false (base + copy30NextDstOff r 0) 0 (written ++ bitsToBytes d 30) := by
  have hcode := codeAt_copy30 r
  have hcodeL := hcode.left
  have hcodeR := hcode.right
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_copy30 hcodeL hpc (by decide) hx10 hsrc_al hsrc_bd
    hsrc_mem hd_clean (by omega) (by omega) hw
  set pc1 := pcCopy30 r + (copy30Code r .x10 0 false).length
  have hbdR : pc1 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; simpa using this
  have hi0 : openInstr pc1 = .base (.ADDI .x25 .x25 (BitVec.ofNat 12 (copy30NextDstOff r 0))) := by have h := hcodeR.2 0 (by simp); simpa using h
  have hi1 : openInstr (pc1 + 1) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * (copy30NextR r).val))) := by have h := hcodeR.2 1 (by simp); simpa using h
  have hi2 : openInstr (pc1 + 2) = .base (.JALR .x0 .x1 (0#12)) := by have h := hcodeR.2 2 (by simp); simpa using h
  have ha1 := step_ADDI (s := s1) (by omega) hpc1 hi0
  set s2 := (s1.setReg .x25 (s1.getReg .x25 + signExtend12 (BitVec.ofNat 12 (copy30NextDstOff r 0)))).setPC (pcAt (pc1 + 1))
  have ha2 := step_ADDI (s := s2) (by omega) rfl hi1
  set s3 := (s2.setReg .x14 (s2.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * (copy30NextR r).val)))).setPC (pcAt (pc1 + 1 + 1))
  have hs3_x1 : s3.getReg .x1 = pcAt retPc := by
    simp [s3, s2, getReg_setReg_ne', (hregs1 .x1 (by simp)).trans hx1]
  have ha3 := step_JALR (s := s3) (by omega) (by congr 1) hi2 hs3_x1
  set s4 := (s3.setReg .x0 (pcAt (pc1 + 2 + 1))).setPC (pcAt retPc)
  have hlen : (copy30SubCode r).length = (copy30Code r .x10 0 false).length + 3 := by simp [copy30SubCode]
  have hdst_lt : copy30NextDstOff r 0 < 2048 := by unfold copy30NextDstOff; split_ifs <;> omega
  have hnr_lt : 8 * (copy30NextR r).val < 2048 := by have := (copy30NextR r).isLt; omega
  refine ⟨s4, by rw [hlen]; exact ((hr1.trans ha1).trans ha2).trans ha3, rfl, ?_, ?_,
    hp1.trans (fun _ _ => by simp [s4, s3, s2]), ?_⟩
  · simp [s4, s3, getReg_setReg_ne', show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg _ hnr_lt]
  · intro reg hreg
    have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
    have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
    have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
    have hne14 : reg ≠ .x14 := fun h => hreg (by simp [h])
    have hne25 : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h0 : s4.getReg reg = s3.getReg reg := by cases reg <;> simp [s4, setReg_x0_eq]
    exact h0.trans ((by simp [s3, s2, getReg_setReg_ne' .x14 reg hne14.symm,
      getReg_setReg_ne' .x25 reg hne25.symm] : s3.getReg reg = s1.getReg reg).trans
      (hregs1 reg (by simp [hne5, hne6, hne12])))
  · have hw2 : WriterState clean s2 (copy30NextR r) false (base + copy30NextDstOff r 0) 0 (written ++ bitsToBytes d 30) :=
      writerState_advance_base hw1 hdst_lt (pcAt (pc1 + 1))
    exact writerState_of_mem_eq hw2 (fun _ => by simp [s4, s3, setReg_x0_eq])
      (by simp [s4, s3, setReg_x0_eq, getReg_setReg_ne']) (by simp [s4, s3, setReg_x0_eq, getReg_setReg_ne'])

/-- `copy29_r`: copy 29 B from `x10`, return 6-bit tail in `x5`, advance `x25`, set `x14 = 8 * nr`, return via `x1`. -/
theorem openRuns_sub_copy29 {clean : Prop} {s : MachineState} {r : Fin 8}
    {retPc srcBase base : Nat} {written : List Byte} {d : Digest}
    (hpc : s.pc = pcAt (pcCopy29 r))
    (hx1 : s.getReg .x1 = pcAt retPc)
    (hx11 : s.getReg .x11 = mask40Word)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 srcBase)
    (hsrc_al : srcBase % 8 = 0)
    (hsrc_bd : srcBase + 32 ≤ 11341403200)
    (hsrc_mem : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (srcBase + 8 * k)) = d.extractLsb' (64 * k) 64)
    (hd_clean : clean → mask238 d = d)
    (hbase_bd : base + 40 ≤ 8556390424)
    (hw : WriterState clean s r false base 0 written) :
    let cyc := (copy29SubCode r).length
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt retPc ∧
      s'.getReg .x14 = BitVec.ofNat 64 (8 * (copy29NextR r).val) ∧
      (clean → s'.getReg .x5 = BitVec.ofNat 64 (tail6 d).toNat) ∧
      RegsEqExcept [.x5, .x6, .x10, .x12, .x14, .x25] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' (copy29NextR r) false (base + copy29NextDstOff r 0) 0 (written ++ bitsToBytes d 29) := by
  have hcode := codeAt_copy29 r
  have hcodeL := hcode.left
  have hcodeR := hcode.right
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1, hpost1⟩ := openRuns_copy29 (tailDst := .x5) (tailShift := 0)
    (tailInit := false) (prevVal := 0) (flushR7 := false)
    hcodeL hpc (by decide) (by decide) (fun _ h => absurd rfl h) (by omega)
    hx11 hx10 hsrc_al hsrc_bd hsrc_mem hd_clean (by omega) (by omega) hw (fun _ => by simp)
  simp only [copy29NextFlushedR4, Bool.and_false] at hw1
  set pc1 := pcCopy29 r + (copy29Code r .x10 0 .x5 0 false false false).length
  have hbdR : pc1 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; simpa using this
  have hi0 : openInstr pc1 = .base (.ADDI .x25 .x25 (BitVec.ofNat 12 (copy29NextDstOff r 0))) := by have h := hcodeR.2 0 (by simp); simpa using h
  have hi1 : openInstr (pc1 + 1) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * (copy29NextR r).val))) := by have h := hcodeR.2 1 (by simp); simpa using h
  have hi2 : openInstr (pc1 + 2) = .base (.JALR .x0 .x1 (0#12)) := by have h := hcodeR.2 2 (by simp); simpa using h
  have ha1 := step_ADDI (s := s1) (by omega) hpc1 hi0
  set s2 := (s1.setReg .x25 (s1.getReg .x25 + signExtend12 (BitVec.ofNat 12 (copy29NextDstOff r 0)))).setPC (pcAt (pc1 + 1))
  have ha2 := step_ADDI (s := s2) (by omega) rfl hi1
  set s3 := (s2.setReg .x14 (s2.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * (copy29NextR r).val)))).setPC (pcAt (pc1 + 1 + 1))
  have hs3_x1 : s3.getReg .x1 = pcAt retPc := by
    simp [s3, s2, getReg_setReg_ne', (hregs1 .x1 (by simp)).trans hx1]
  have ha3 := step_JALR (s := s3) (by omega) (by congr 1) hi2 hs3_x1
  set s4 := (s3.setReg .x0 (pcAt (pc1 + 2 + 1))).setPC (pcAt retPc)
  have hlen : (copy29SubCode r).length = (copy29Code r .x10 0 .x5 0 false false false).length + 3 := by simp [copy29SubCode]
  have hdst_lt : copy29NextDstOff r 0 < 2048 := by unfold copy29NextDstOff; split_ifs <;> omega
  have hnr_lt : 8 * (copy29NextR r).val < 2048 := by have := (copy29NextR r).isLt; omega
  refine ⟨s4, by rw [hlen]; exact ((hr1.trans ha1).trans ha2).trans ha3, rfl, ?_, ?_, ?_,
    hp1.trans (fun _ _ => by simp [s4, s3, s2]), ?_⟩
  · simp [s4, s3, getReg_setReg_ne', show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg _ hnr_lt]
  · intro hcl
    have h5 := hpost1 hcl; simp at h5
    simp [s4, s3, s2, getReg_setReg_ne', h5]
  · intro reg hreg
    have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
    have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
    have hne10 : reg ≠ .x10 := fun h => hreg (by simp [h])
    have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
    have hne14 : reg ≠ .x14 := fun h => hreg (by simp [h])
    have hne25 : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h0 : s4.getReg reg = s3.getReg reg := by cases reg <;> simp [s4, setReg_x0_eq]
    exact h0.trans ((by simp [s3, s2, getReg_setReg_ne' .x14 reg hne14.symm,
      getReg_setReg_ne' .x25 reg hne25.symm] : s3.getReg reg = s1.getReg reg).trans
      (hregs1 reg (by simp [hne5, hne6, hne10, hne12])))
  · have hw2 : WriterState clean s2 (copy29NextR r) false (base + copy29NextDstOff r 0) 0 (written ++ bitsToBytes d 29) :=
      writerState_advance_base hw1 hdst_lt (pcAt (pc1 + 1))
    exact writerState_of_mem_eq hw2 (fun _ => by simp [s4, s3, setReg_x0_eq])
      (by simp [s4, s3, setReg_x0_eq, getReg_setReg_ne']) (by simp [s4, s3, setReg_x0_eq, getReg_setReg_ne'])

/-- `copy32_x3_r`: batched 3×32 B copy from `(x10, x28, x8)`, `r` unchanged, `x25 += 96`, return via `x1`. -/
theorem openRuns_sub_copy32x3 {clean : Prop} {s : MachineState} {r : Fin 8}
    {retPc src0 src1 src2 base : Nat} {written : List Byte} {d0 d1 d2 : Digest}
    (hpc : s.pc = pcAt (pcCopy32x3 r))
    (hx1 : s.getReg .x1 = pcAt retPc)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src0)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 src1)
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 src2)
    (hal0 : src0 % 8 = 0) (hal1 : src1 % 8 = 0) (hal2 : src2 % 8 = 0)
    (hbd0 : src0 + 32 ≤ 11341403200) (hbd1 : src1 + 32 ≤ 11341403200) (hbd2 : src2 + 32 ≤ 11341403200)
    (hm0 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src0 + 8 * k)) = d0.extractLsb' (64 * k) 64)
    (hm1 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src1 + 8 * k)) = d1.extractLsb' (64 * k) 64)
    (hm2 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src2 + 8 * k)) = d2.extractLsb' (64 * k) 64)
    (hbase_bd : base + 104 ≤ 8556390424)
    (hw : WriterState clean s r false base 0 written) :
    let cyc := (copy32x3SubCode r).length
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt retPc ∧
      RegsEqExcept [.x5, .x6, .x12, .x25] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' r false (base + 96) 0
        (written ++ bitsToBytes d0 32 ++ bitsToBytes d1 32 ++ bitsToBytes d2 32) := by
  have hcode := codeAt_copy32x3 r
  have hcodeD0 := hcode.left.left.left
  have hcodeD1 := hcode.left.left.right
  have hcodeD2 := hcode.left.right
  have hcodeR := hcode.right
  have hmem_pres : ∀ {sa sb : MachineState} {src : Nat} {d : Digest},
      ProofWritePreserves sa sb → src + 32 ≤ 11341403200 →
      (clean → ∀ k < 4, sa.getMem (BitVec.ofNat 64 (src + 8 * k)) = d.extractLsb' (64 * k) 64) →
      (clean → ∀ k < 4, sb.getMem (BitVec.ofNat 64 (src + 8 * k)) = d.extractLsb' (64 * k) 64) := by
    intro sa sb src d hp hbd hm hcl k hk
    have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (src + 8 * k)).toNat ∧
        (BitVec.ofNat 64 (src + 8 * k)).toNat < 19897793624) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hp _ hnot]; exact hm hcl k hk
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_dwords 4 (s := s) (r := r)
    (vals := fun k => d0.extractLsb' (64 * k) 64)
    (by omega) hcodeD0 hpc (by decide) hx10 (by omega) (by omega) (by omega)
    (fun hcl k hk => by simpa only [Nat.add_zero] using hm0 hcl k hk) (by omega) (by omega) hw
  rw [(bitsToBytes_take_dwords d0 4).symm] at hw1
  simp only [Bool.and_self] at hw1
  obtain ⟨s2, hr2, hpc2, hregs2, hp2, hw2⟩ := openRuns_dwords 4 (s := s1) (r := r)
    (vals := fun k => d1.extractLsb' (64 * k) 64)
    (by omega) hcodeD1 hpc1 (by decide) ((hregs1 .x28 (by simp)).trans hx28) (by omega) (by omega) (by omega)
    (fun hcl k hk => by simpa only [Nat.add_zero] using hmem_pres hp1 hbd1 hm1 hcl k hk) (by omega) (by omega) hw1
  rw [(bitsToBytes_take_dwords d1 4).symm] at hw2
  simp only [Bool.and_self] at hw2
  have hpc2' : s2.pc = pcAt (pcCopy32x3 r + (dwordsCode r 4 .x10 0 0 false (r.val == 4) ++
      dwordsCode r 4 .x28 0 32 (r.val == 4) (r.val == 4)).length) := by
    rw [hpc2]; simp only [List.length_append]; congr 1; omega
  obtain ⟨s3, hr3, hpc3, hregs3, hp3, hw3⟩ := openRuns_dwords 4 (s := s2) (r := r)
    (vals := fun k => d2.extractLsb' (64 * k) 64)
    (by omega) hcodeD2 hpc2' (by decide) ((hregs2 .x8 (by simp)).trans ((hregs1 .x8 (by simp)).trans hx8))
    (by omega) (by omega) (by omega)
    (fun hcl k hk => by simpa only [Nat.add_zero] using hmem_pres (hp1.trans hp2) hbd2 hm2 hcl k hk)
    (by omega) (by omega) hw2
  rw [(bitsToBytes_take_dwords d2 4).symm] at hw3
  simp only [Bool.and_false] at hw3
  set pc3 := pcCopy32x3 r + ((dwordsCode r 4 .x10 0 0 false (r.val == 4) ++
      dwordsCode r 4 .x28 0 32 (r.val == 4) (r.val == 4)) ++
      dwordsCode r 4 .x8 0 64 (r.val == 4) false).length
  have hpc3' : s3.pc = pcAt pc3 := by rw [hpc3]; simp only [List.length_append, pc3]; congr 1; omega
  have hbdR : pc3 + 2 ≤ OPEN_CODE_LEN := by have := hcodeR.1; simpa [pc3] using this
  have hi0 : openInstr pc3 = .base (.ADDI .x25 .x25 (96#12)) := by have h := hcodeR.2 0 (by simp); simpa [pc3] using h
  have hi1 : openInstr (pc3 + 1) = .base (.JALR .x0 .x1 (0#12)) := by have h := hcodeR.2 1 (by simp); simpa [pc3] using h
  have ha1 := step_ADDI (s := s3) (by omega) hpc3' hi0
  set s4 := (s3.setReg .x25 (s3.getReg .x25 + signExtend12 (96#12))).setPC (pcAt (pc3 + 1))
  have hs4_x1 : s4.getReg .x1 = pcAt retPc := by
    simp [s4, getReg_setReg_ne', (hregs3 .x1 (by simp)).trans ((hregs2 .x1 (by simp)).trans ((hregs1 .x1 (by simp)).trans hx1))]
  have ha2 := step_JALR (s := s4) (by omega) rfl hi1 hs4_x1
  set s5 := (s4.setReg .x0 (pcAt (pc3 + 1 + 1))).setPC (pcAt retPc)
  have hlen : (copy32x3SubCode r).length =
      (dwordsCode r 4 .x10 0 0 false (r.val == 4)).length +
      (dwordsCode r 4 .x28 0 32 (r.val == 4) (r.val == 4)).length +
      (dwordsCode r 4 .x8 0 64 (r.val == 4) false).length + 2 := by
    simp [copy32x3SubCode]; omega
  refine ⟨s5, by rw [hlen]; exact (((hr1.trans hr2).trans hr3).trans ha1).trans ha2, rfl, ?_,
    ((hp1.trans hp2).trans hp3).trans (fun _ _ => by simp [s5, s4]), ?_⟩
  · intro reg hreg
    have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
    have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
    have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
    have hne25 : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h0 : s5.getReg reg = s4.getReg reg := by cases reg <;> simp [s5, setReg_x0_eq]
    exact h0.trans ((by simp [s4, getReg_setReg_ne' .x25 reg hne25.symm] : s4.getReg reg = s3.getReg reg).trans
      ((hregs3 reg (by simp [hne5, hne6, hne12])).trans
       ((hregs2 reg (by simp [hne5, hne6, hne12])).trans (hregs1 reg (by simp [hne5, hne6, hne12])))))
  · have hw4 : WriterState clean s4 r false (base + 96) 0
        (written ++ bitsToBytes d0 32 ++ bitsToBytes d1 32 ++ bitsToBytes d2 32) :=
      writerState_advance_base (dstOff := 96) hw3 (by omega) (pcAt (pc3 + 1))
    exact writerState_of_mem_eq hw4 (fun _ => by simp [s5, setReg_x0_eq])
      (by simp [s5, setReg_x0_eq, getReg_setReg_ne']) (by simp [s5, setReg_x0_eq, getReg_setReg_ne'])

private theorem copy30x4_end_r (r : Fin 8) :
    copy30NextR (copy30NextR (copy30NextR (copy30NextR r))) = r := by
  fin_cases r <;> rfl

private theorem copy30x4_end_dst (r : Fin 8) :
    copy30NextDstOff (copy30NextR (copy30NextR (copy30NextR r)))
      (copy30NextDstOff (copy30NextR (copy30NextR r))
        (copy30NextDstOff (copy30NextR r) (copy30NextDstOff r 0))) = 120 := by
  fin_cases r <;> rfl

/-- `copy30_x4_r`: batched 4×30 B copy from `(x10, x28, x8, x19)`, `r` unchanged, `x25 += 120`, return via `x1`. -/
theorem openRuns_sub_copy30x4 {clean : Prop} {s : MachineState} {r : Fin 8}
    {retPc src0 src1 src2 src3 base : Nat} {written : List Byte} {d0 d1 d2 d3 : Digest}
    (hpc : s.pc = pcAt (pcCopy30x4 r))
    (hx1 : s.getReg .x1 = pcAt retPc)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src0)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 src1)
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 src2)
    (hx19 : s.getReg .x19 = BitVec.ofNat 64 src3)
    (hal0 : src0 % 8 = 0) (hal1 : src1 % 8 = 0) (hal2 : src2 % 8 = 0) (hal3 : src3 % 8 = 0)
    (hbd0 : src0 + 32 ≤ 11341403200) (hbd1 : src1 + 32 ≤ 11341403200)
    (hbd2 : src2 + 32 ≤ 11341403200) (hbd3 : src3 + 32 ≤ 11341403200)
    (hm0 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src0 + 8 * k)) = d0.extractLsb' (64 * k) 64)
    (hm1 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src1 + 8 * k)) = d1.extractLsb' (64 * k) 64)
    (hm2 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src2 + 8 * k)) = d2.extractLsb' (64 * k) 64)
    (hm3 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src3 + 8 * k)) = d3.extractLsb' (64 * k) 64)
    (hc0 : clean → mask240 d0 = d0) (hc1 : clean → mask240 d1 = d1)
    (hc2 : clean → mask240 d2 = d2) (hc3 : clean → mask240 d3 = d3)
    (hbase_bd : base + 136 ≤ 8556390424)
    (hw : WriterState clean s r false base 0 written) :
    let cyc := (copy30x4SubCode r).length
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt retPc ∧
      RegsEqExcept [.x5, .x6, .x12, .x25] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' r false (base + 120) 0
        (written ++ bitsToBytes d0 30 ++ bitsToBytes d1 30 ++ bitsToBytes d2 30 ++ bitsToBytes d3 30) := by
  have hcode := codeAt_copy30x4 r
  set r1 := copy30NextR r; set d1o := copy30NextDstOff r 0
  set r2 := copy30NextR r1; set d2o := copy30NextDstOff r1 d1o
  set r3 := copy30NextR r2; set d3o := copy30NextDstOff r2 d2o
  have hd1o : copy30NextDstOff r 0 ≤ 32 := by unfold copy30NextDstOff; split_ifs <;> omega
  have hd2o : copy30NextDstOff (copy30NextR r) (copy30NextDstOff r 0) ≤ 64 := by unfold copy30NextDstOff; split_ifs <;> omega
  have hd3o : copy30NextDstOff (copy30NextR (copy30NextR r)) (copy30NextDstOff (copy30NextR r) (copy30NextDstOff r 0)) ≤ 96 := by
    unfold copy30NextDstOff; split_ifs <;> omega
  have hcode0 := hcode.left.left.left.left
  have hcode1 := hcode.left.left.left.right
  have hcode2 := hcode.left.left.right
  have hcode3 := hcode.left.right
  have hcodeR := hcode.right
  have hmem_pres : ∀ {sa sb : MachineState} {src : Nat} {d : Digest},
      ProofWritePreserves sa sb → src + 32 ≤ 11341403200 →
      (clean → ∀ k < 4, sa.getMem (BitVec.ofNat 64 (src + 8 * k)) = d.extractLsb' (64 * k) 64) →
      (clean → ∀ k < 4, sb.getMem (BitVec.ofNat 64 (src + 8 * k)) = d.extractLsb' (64 * k) 64) := by
    intro sa sb src d hp hbd hm hcl k hk
    have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (src + 8 * k)).toNat ∧
        (BitVec.ofNat 64 (src + 8 * k)).toNat < 19897793624) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hp _ hnot]; exact hm hcl k hk
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_copy30 hcode0 hpc (by decide) hx10 hal0 hbd0
    hm0 hc0 (by omega) (by omega) hw
  obtain ⟨s2, hr2, hpc2, hregs2, hp2, hw2⟩ := openRuns_copy30 hcode1 hpc1 (by decide)
    ((hregs1 .x28 (by simp)).trans hx28) hal1 hbd1 (hmem_pres hp1 hbd1 hm1) hc1 (by omega) (by omega) hw1
  have hpc2' : s2.pc = pcAt (pcCopy30x4 r + (copy30Code r .x10 0 false ++ copy30Code r1 .x28 d1o false).length) := by
    rw [hpc2]; simp only [List.length_append, r1, d1o, Nat.add_assoc]
  obtain ⟨s3, hr3, hpc3, hregs3, hp3, hw3⟩ := openRuns_copy30 hcode2 hpc2' (by decide)
    ((hregs2 .x8 (by simp)).trans ((hregs1 .x8 (by simp)).trans hx8)) hal2 hbd2
    (hmem_pres (hp1.trans hp2) hbd2 hm2) hc2 (by omega) (by omega) hw2
  have hpc3' : s3.pc = pcAt (pcCopy30x4 r + ((copy30Code r .x10 0 false ++ copy30Code r1 .x28 d1o false) ++
      copy30Code r2 .x8 d2o false).length) := by
    rw [hpc3]; simp only [List.length_append, r1, r2, d1o, d2o, Nat.add_assoc]
  obtain ⟨s4, hr4, hpc4, hregs4, hp4, hw4⟩ := openRuns_copy30 hcode3 hpc3' (by decide)
    ((hregs3 .x19 (by simp)).trans ((hregs2 .x19 (by simp)).trans ((hregs1 .x19 (by simp)).trans hx19)))
    hal3 hbd3 (hmem_pres ((hp1.trans hp2).trans hp3) hbd3 hm3) hc3 (by omega) (by omega) hw3
  rw [copy30x4_end_r r, copy30x4_end_dst r] at hw4
  set pc4 := pcCopy30x4 r + (((copy30Code r .x10 0 false ++ copy30Code r1 .x28 d1o false) ++
      copy30Code r2 .x8 d2o false) ++ copy30Code r3 .x19 d3o false).length
  have hpc4' : s4.pc = pcAt pc4 := by rw [hpc4]; simp only [List.length_append, pc4, r1, r2, r3, d1o, d2o, d3o, Nat.add_assoc]
  have hbdR : pc4 + 2 ≤ OPEN_CODE_LEN := by have := hcodeR.1; simpa [pc4] using this
  have hi0 : openInstr pc4 = .base (.ADDI .x25 .x25 (120#12)) := by have h := hcodeR.2 0 (by simp); simpa [pc4] using h
  have hi1 : openInstr (pc4 + 1) = .base (.JALR .x0 .x1 (0#12)) := by have h := hcodeR.2 1 (by simp); simpa [pc4] using h
  have ha1 := step_ADDI (s := s4) (by omega) hpc4' hi0
  set s5 := (s4.setReg .x25 (s4.getReg .x25 + signExtend12 (120#12))).setPC (pcAt (pc4 + 1))
  have hs5_x1 : s5.getReg .x1 = pcAt retPc := by
    simp [s5, getReg_setReg_ne', (hregs4 .x1 (by simp)).trans ((hregs3 .x1 (by simp)).trans
      ((hregs2 .x1 (by simp)).trans ((hregs1 .x1 (by simp)).trans hx1)))]
  have ha2 := step_JALR (s := s5) (by omega) rfl hi1 hs5_x1
  set s6 := (s5.setReg .x0 (pcAt (pc4 + 1 + 1))).setPC (pcAt retPc)
  have htot := ((((hr1.trans hr2).trans hr3).trans hr4).trans ha1).trans ha2
  have hlen : (copy30Code r .x10 0 false).length + (copy30Code (copy30NextR r) .x28 (copy30NextDstOff r 0) false).length +
      (copy30Code (copy30NextR (copy30NextR r)) .x8 (copy30NextDstOff (copy30NextR r) (copy30NextDstOff r 0)) false).length +
      (copy30Code (copy30NextR (copy30NextR (copy30NextR r))) .x19
        (copy30NextDstOff (copy30NextR (copy30NextR r)) (copy30NextDstOff (copy30NextR r) (copy30NextDstOff r 0))) false).length + 1 + 1 =
      (copy30x4SubCode r).length := by
    simp only [copy30x4SubCode, List.length_append, List.length_cons, List.length_nil]
  refine ⟨s6, by simpa only [hlen] using htot, rfl, ?_,
    (((hp1.trans hp2).trans hp3).trans hp4).trans (fun _ _ => by simp [s6, s5]), ?_⟩
  · intro reg hreg
    have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
    have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
    have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
    have hne25 : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h0 : s6.getReg reg = s5.getReg reg := by cases reg <;> simp [s6, setReg_x0_eq]
    exact h0.trans ((by simp [s5, getReg_setReg_ne' .x25 reg hne25.symm] : s5.getReg reg = s4.getReg reg).trans
      ((hregs4 reg (by simp [hne5, hne6, hne12])).trans
       ((hregs3 reg (by simp [hne5, hne6, hne12])).trans
        ((hregs2 reg (by simp [hne5, hne6, hne12])).trans (hregs1 reg (by simp [hne5, hne6, hne12]))))))
  · have hw5 : WriterState clean s5 r false (base + 120) 0
        (written ++ bitsToBytes d0 30 ++ bitsToBytes d1 30 ++ bitsToBytes d2 30 ++ bitsToBytes d3 30) :=
      writerState_advance_base (dstOff := 120) hw4 (by omega) (pcAt (pc4 + 1))
    exact writerState_of_mem_eq hw5 (fun _ => by simp [s6, setReg_x0_eq])
      (by simp [s6, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, setReg_x0_eq, getReg_setReg_ne'])

/-- `copy29_x2_r`: batched 2×29 B copy from `(x10, x28)`, returning 12-bit tail in `x5` (preserving `x8`). -/
theorem openRuns_sub_copy29x2 {clean : Prop} {s : MachineState} {r : Fin 8}
    {retPc src0 src1 base : Nat} {written : List Byte} {d0 d1 : Digest}
    (hpc : s.pc = pcAt (pcCopy29x2 r))
    (hx1 : s.getReg .x1 = pcAt retPc)
    (hx11 : s.getReg .x11 = mask40Word)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src0)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 src1)
    (hal0 : src0 % 8 = 0) (hal1 : src1 % 8 = 0)
    (hbd0 : src0 + 32 ≤ 11341403200) (hbd1 : src1 + 32 ≤ 11341403200)
    (hm0 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src0 + 8 * k)) = d0.extractLsb' (64 * k) 64)
    (hm1 : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (src1 + 8 * k)) = d1.extractLsb' (64 * k) 64)
    (hc0 : clean → mask238 d0 = d0) (hc1 : clean → mask238 d1 = d1)
    (hbase_bd : base + 72 ≤ 8556390424)
    (hw : WriterState clean s r false base 0 written) :
    let cyc := (copy29x2SubCode r).length
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt retPc ∧
      s'.getReg .x14 = BitVec.ofNat 64 (8 * (copy29x2NextR r).val) ∧
      (clean → s'.getReg .x5 = BitVec.ofNat 64 (bitsOf6 [tail6 d0, tail6 d1])) ∧
      RegsEqExcept [.x5, .x6, .x10, .x12, .x14, .x19, .x25] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' (copy29x2NextR r) false (base + copy29x2NextDstOff r) 0
        (written ++ bitsToBytes d0 29 ++ bitsToBytes d1 29) := by
  have hcode := codeAt_copy29x2 r
  set r1 := copy29NextR r; set d1o := copy29NextDstOff r 0; set f1 := copy29NextFlushedR4 r true
  set r2 := copy29x2NextR r; set d2o := copy29x2NextDstOff r
  have hd1o : copy29NextDstOff r 0 ≤ 32 := by unfold copy29NextDstOff; split_ifs <;> omega
  have hd2o : copy29NextDstOff (copy29NextR r) (copy29NextDstOff r 0) ≤ 64 := by unfold copy29NextDstOff; split_ifs <;> omega
  have hcode0 := hcode.left.left
  have hcode1 := hcode.left.right
  have hcodeR := hcode.right
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1, hpost1⟩ := openRuns_copy29 (tailDst := .x19) (tailShift := 0)
    (tailInit := true) (prevVal := 0) (flushR7 := true)
    hcode0 hpc (by decide) (by decide) (fun h _ => by simp at h) (by omega)
    hx11 hx10 hal0 hbd0 hm0 hc0 (by omega) (by omega) hw (fun _ => by simp)
  have hm1' : clean → ∀ k < 4, s1.getMem (BitVec.ofNat 64 (src1 + 8 * k)) = d1.extractLsb' (64 * k) 64 := by
    intro hcl k hk
    have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (src1 + 8 * k)).toNat ∧
        (BitVec.ofNat 64 (src1 + 8 * k)).toNat < 19897793624) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hp1 _ hnot]; exact hm1 hcl k hk
  have hpre1 : TailAccumPre clean s1 .x19 6 false (tail6 d0).toNat := by
    intro hcl
    have h19 := hpost1 hcl; simp only [↓reduceIte] at h19
    simp only [Bool.false_eq_true, ↓reduceIte, show (6 == 0) = false from rfl]
    exact ⟨(tail6 d0).isLt, h19⟩
  obtain ⟨s2, hr2, hpc2, hregs2, hp2, hw2, hpost2⟩ := openRuns_copy29 (tailDst := .x19) (tailShift := 6)
    (tailInit := false) (prevVal := (tail6 d0).toNat) (flushR7 := false)
    hcode1 hpc1 (by decide) (by decide) (fun _ _ => by decide) (by omega)
    ((hregs1 .x11 (by simp)).trans hx11) ((hregs1 .x28 (by simp)).trans hx28)
    hal1 hbd1 hm1' hc1 (by omega) (by omega) hw1 hpre1
  simp only [copy29NextFlushedR4, Bool.and_false] at hw2
  set pc2 := pcCopy29x2 r + (copy29Code r .x10 0 .x19 0 true false true ++
      copy29Code r1 .x28 d1o .x19 6 false f1 false).length
  have hpc2' : s2.pc = pcAt pc2 := by rw [hpc2]; simp only [List.length_append, pc2, r1, d1o, f1, Nat.add_assoc]
  have hbdR : pc2 + 4 ≤ OPEN_CODE_LEN := by have := hcodeR.1; simpa [pc2] using this
  have hi0 : openInstr pc2 = .base (.ADDI .x5 .x19 (0#12)) := by have h := hcodeR.2 0 (by simp); simpa [pc2] using h
  have hi1 : openInstr (pc2 + 1) = .base (.ADDI .x25 .x25 (BitVec.ofNat 12 d2o)) := by have h := hcodeR.2 1 (by simp); simpa [pc2, d2o, copy29x2NextDstOff] using h
  have hi2 : openInstr (pc2 + 2) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r2.val))) := by have h := hcodeR.2 2 (by simp); simpa [pc2, r2, copy29x2NextR] using h
  have hi3 : openInstr (pc2 + 3) = .base (.JALR .x0 .x1 (0#12)) := by have h := hcodeR.2 3 (by simp); simpa [pc2] using h
  have ha1 := step_ADDI (s := s2) (by omega) hpc2' hi0
  set s3 := (s2.setReg .x5 (s2.getReg .x19 + signExtend12 (0#12))).setPC (pcAt (pc2 + 1))
  have ha2 := step_ADDI (s := s3) (by omega) rfl hi1
  set s4 := (s3.setReg .x25 (s3.getReg .x25 + signExtend12 (BitVec.ofNat 12 d2o))).setPC (pcAt (pc2 + 1 + 1))
  have ha3 := step_ADDI (s := s4) (by omega) (by congr 1) hi2
  set s5 := (s4.setReg .x14 (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * r2.val)))).setPC (pcAt (pc2 + 2 + 1))
  have hs5_x1 : s5.getReg .x1 = pcAt retPc := by
    simp [s5, s4, s3, getReg_setReg_ne', (hregs2 .x1 (by simp)).trans ((hregs1 .x1 (by simp)).trans hx1)]
  have ha4 := step_JALR (s := s5) (by omega) (by congr 1) hi3 hs5_x1
  set s6 := (s5.setReg .x0 (pcAt (pc2 + 3 + 1))).setPC (pcAt retPc)
  have htot := ((((hr1.trans hr2).trans ha1).trans ha2).trans ha3).trans ha4
  have hlen : (copy29Code r .x10 0 .x19 0 true false true).length +
      (copy29Code (copy29NextR r) .x28 (copy29NextDstOff r 0) .x19 6 false (copy29NextFlushedR4 r true) false).length +
      1 + 1 + 1 + 1 = (copy29x2SubCode r).length := by
    simp only [copy29x2SubCode, List.length_append, List.length_cons, List.length_nil]
  have hnr_lt : 8 * r2.val < 2048 := by have := r2.isLt; omega
  refine ⟨s6, by simpa only [hlen] using htot, rfl, ?_, ?_, ?_,
    (hp1.trans hp2).trans (fun _ _ => by simp [s6, s5, s4, s3]), ?_⟩
  · simp [s6, s5, getReg_setReg_ne', show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg _ hnr_lt]
  · intro hcl
    have h19 := hpost2 hcl
    simp only [Bool.false_eq_true, ↓reduceIte, show (6 == 0) = false from rfl] at h19
    have hbits : bitsOf6 [tail6 d0, tail6 d1] = (tail6 d0).toNat + (tail6 d1).toNat * 2 ^ 6 := by
      simp [bitsOf6]; ring
    simp [s6, s5, s4, s3, getReg_setReg_ne', h19, signExtend12_nonneg 0 (by omega), hbits]
  · intro reg hreg
    have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
    have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
    have hne10 : reg ≠ .x10 := fun h => hreg (by simp [h])
    have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
    have hne14 : reg ≠ .x14 := fun h => hreg (by simp [h])
    have hne19 : reg ≠ .x19 := fun h => hreg (by simp [h])
    have hne25 : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h0 : s6.getReg reg = s5.getReg reg := by cases reg <;> simp [s6, setReg_x0_eq]
    exact h0.trans ((by simp [s5, s4, s3, getReg_setReg_ne' .x14 reg hne14.symm,
      getReg_setReg_ne' .x25 reg hne25.symm, getReg_setReg_ne' .x5 reg hne5.symm] : s5.getReg reg = s2.getReg reg).trans
      ((hregs2 reg (by simp [hne5, hne6, hne10, hne12, hne19])).trans
       (hregs1 reg (by simp [hne5, hne6, hne10, hne12, hne19]))))
  · have hw3 := writerState_of_mem_eq hw2 (s' := s3) (fun _ => by simp [s3])
      (by simp [s3, getReg_setReg_ne']) (by simp [s3, getReg_setReg_ne'])
    have hw4 : WriterState clean s4 (copy29x2NextR r) false (base + copy29x2NextDstOff r) 0
        (written ++ bitsToBytes d0 29 ++ bitsToBytes d1 29) :=
      writerState_advance_base hw3 (by omega) (pcAt (pc2 + 1 + 1))
    exact writerState_of_mem_eq hw4 (fun _ => by simp [s6, s5])
      (by simp [s6, s5, getReg_setReg_ne']) (by simp [s6, s5, getReg_setReg_ne'])

end CommitGolfCandidate.MoonOpen
