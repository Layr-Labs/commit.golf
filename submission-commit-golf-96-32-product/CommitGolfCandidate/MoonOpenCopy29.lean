import CommitGolfCandidate.MoonOpenBlocks

/-! Universal 29-byte + 6-bit-tail copy lemma (`copy29Code`, all 8 residues + `r = 7 → r = 4`
early flush + 3 tail-extraction modes) and 6-bit cap-frontier tail-push lemma (`tailPush6Code`). -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Byte-Extraction Helpers -/

private theorem truncate32_extract_byte' (w : Word) (j : Nat) (hj : j < 4) :
    (w.truncate 32).extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp [BitVec.truncate, hb, show 8 * j + b < 32 by omega]

private theorem ushr8_truncate32_extract_byte (w : Word) (j : Nat) (hj : j < 4) :
    ((w >>> 8).truncate 32).extractLsb' (8 * j) 8 = w.extractLsb' (8 * (j + 1)) 8 := by
  rw [truncate32_extract_byte' _ j hj]
  have h := word_ushr_byte w 1 (by omega) j (by omega)
  simpa only [show 8 * 1 = 8 from rfl, show j + 1 < 8 by omega, ↓reduceIte] using h

private theorem byte_zeroExtend64_extract (b : Byte) (j : Nat) (hj : j < 8) :
    (b.zeroExtend 64).extractLsb' (8 * j) 8 = if j = 0 then b else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro bit hbit
  simp only [BitVec.getLsbD_extractLsb', BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    hbit, decide_true, Bool.true_and]
  by_cases hj0 : j = 0
  · subst hj0; simp [hbit, show bit < 64 by omega]
  · rw [if_neg hj0, BitVec.getLsbD_zero, bv_getLsbD_of_ge b (8 * j + bit) (by omega), Bool.and_false]

private theorem word_or_shl_ushr_byte (w v : Word) (r a b : Nat)
    (hr : r < 8) (ha : a ≤ 8) (hb : b ≤ 8)
    (hwHi : ∀ j, r ≤ j → j < 8 → w.extractLsb' (8 * j) 8 = 0#8)
    (hdisj : ∀ j < r, ¬ (j + b < 8 ∧ a ≤ j + b))
    (j : Nat) (hj : j < 8) :
    (w ||| ((v <<< (8 * a)) >>> (8 * b))).extractLsb' (8 * j) 8 =
      if j < r then w.extractLsb' (8 * j) 8
      else if j + b < 8 ∧ a ≤ j + b then v.extractLsb' (8 * (j + b - a)) 8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro bit hbit
  have hsu := congrArg (fun x : Byte => x.getLsbD bit) (word_shl_ushr_byte v a b ha hb j hj)
  simp only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and] at hsu
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hbit, decide_true, Bool.true_and]
  rw [hsu]
  by_cases hlt : j < r
  · rw [if_pos hlt, if_neg (hdisj j hlt), BitVec.getLsbD_zero, Bool.or_false]
    simp [hbit]
  · rw [if_neg hlt]
    have hw0 := congrArg (fun x : Byte => x.getLsbD bit) (hwHi j (by omega) hj)
    simp only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, BitVec.getLsbD_zero] at hw0
    rw [hw0, Bool.false_or]

/-! ### 2. Tail-Extraction Sub-Blocks (`tailExtract4Code` & `tailExtractOtherCode`) -/

def tailExtract4Code (tailDst : Reg) (tailShift : Nat) (tailInit : Bool) (srcReg : Reg) : List Instruction :=
  if tailInit then [.base (.LBU tailDst srcReg (29#12))]
  else if tailShift == 0 then [.base (.LBU .x5 srcReg (29#12))]
  else [.base (.LBU .x5 srcReg (29#12)),
        .base (.SLLI .x5 .x5 (BitVec.ofNat 6 tailShift)),
        .base (.OR tailDst tailDst .x5)]

def tailExtractOtherCode (tailDst : Reg) (tailShift : Nat) (tailInit : Bool) : List Instruction :=
  if tailInit then [.base (.SRLI tailDst .x10 (40#6))]
  else if tailShift == 0 then [.base (.SRLI .x5 .x10 (40#6))]
  else [.base (.SRLI .x5 .x10 (40#6)),
        .base (.SLLI .x5 .x5 (BitVec.ofNat 6 tailShift)),
        .base (.OR tailDst tailDst .x5)]

def TailAccumPre (clean : Prop) (s : MachineState) (tailDst : Reg) (tailShift : Nat)
    (tailInit : Bool) (prevVal : Nat) : Prop :=
  clean →
    if tailInit then True
    else if tailShift == 0 then True
    else prevVal < 2 ^ tailShift ∧ s.getReg tailDst = BitVec.ofNat 64 prevVal

def TailAccumPost (clean : Prop) (s' : MachineState) (tailDst : Reg) (tailShift : Nat)
    (tailInit : Bool) (prevVal t6 : Nat) : Prop :=
  clean →
    if tailInit then s'.getReg tailDst = BitVec.ofNat 64 t6
    else if tailShift == 0 then s'.getReg .x5 = BitVec.ofNat 64 t6
    else s'.getReg tailDst = BitVec.ofNat 64 (prevVal + t6 * 2 ^ tailShift)

private theorem bv64_or_shl_tail6 (prevVal tailShift t6 : Nat)
    (hsh : tailShift + 6 ≤ 64) (hprev : prevVal < 2 ^ tailShift) (ht6 : t6 < 64) :
    BitVec.ofNat 64 prevVal ||| (BitVec.ofNat 64 t6 <<< tailShift) =
      BitVec.ofNat 64 (prevVal + t6 * 2 ^ tailShift) := by
  have hlt_pow : prevVal + t6 * 2 ^ tailShift < 2 ^ (tailShift + 6) := by
    rw [Nat.pow_add, show (2 : Nat) ^ 6 = 64 by decide]
    have h1 : t6 + 1 ≤ 64 := by omega
    have h2 := Nat.mul_le_mul_right (2 ^ tailShift) h1
    linarith
  have hlt64 : prevVal + t6 * 2 ^ tailShift < 2 ^ 64 := by
    have : 2 ^ (tailShift + 6) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hsh
    omega
  apply BitVec.eq_of_toNat_eq
  rw [word_or_shl_add_low64 prevVal tailShift t6 (by omega) hprev (by omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]

private theorem openRuns_tailExtract4 {clean : Prop} {s : MachineState} {pc : Nat}
    {srcReg tailDst : Reg} {srcBase tailShift prevVal : Nat} {tailInit : Bool} {d : Digest}
    (hcode : CodeAt pc (tailExtract4Code tailDst tailShift tailInit srcReg))
    (hpc : s.pc = pcAt pc)
    (hsrc_reg : s.getReg srcReg = BitVec.ofNat 64 srcBase)
    (hsrc_bd : srcBase + 32 ≤ 11341403200)
    (hsrc_b29 : clean → s.getByte (BitVec.ofNat 64 (srcBase + 29)) = d.extractLsb' (8 * 29) 8)
    (hd_clean : clean → mask238 d = d)
    (hsh_bd : tailShift + 6 ≤ 64)
    (htail_ne0 : tailDst ≠ .x0)
    (htail_ne5 : tailInit = false → tailShift ≠ 0 → tailDst ≠ .x5)
    (hpre : TailAccumPre clean s tailDst tailShift tailInit prevVal) :
    ∃ s' : MachineState,
      OpenRuns s (tailExtract4Code tailDst tailShift tailInit srcReg).length
        (tailExtract4Code tailDst tailShift tailInit srcReg).length s' ∧
      s'.pc = pcAt (pc + (tailExtract4Code tailDst tailShift tailInit srcReg).length) ∧
      RegsEqExcept [.x5, tailDst] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) ∧
      TailAccumPost clean s' tailDst tailShift tailInit prevVal (tail6 d).toNat := by
  have haddr : BitVec.ofNat 64 srcBase + signExtend12 (29#12) = BitVec.ofNat 64 (srcBase + 29) := by
    rw [signExtend12_nonneg 29 (by omega), ← BitVec.ofNat_add]
  have hval : accessValid (BitVec.ofNat 64 srcBase + signExtend12 (29#12)) 1 = true := by
    rw [haddr]; exact accessValid_ofNat (srcBase + 29) 1 (by omega) (by omega)
  cases tailInit with
  | true =>
    have hlen : (tailExtract4Code tailDst tailShift true srcReg).length = 1 := rfl
    have hi0 : openInstr pc = .base (.LBU tailDst srcReg (29#12)) := by
      have h := hcode.2 0 (by simp [tailExtract4Code]); simpa [tailExtract4Code] using h
    have hs1 := step_LBU (by have := hcode.1; rw [hlen] at this; omega) hpc hi0 (by rw [hsrc_reg]; exact hval)
    set s1 := (s.setReg tailDst ((s.getByte (s.getReg srcReg + signExtend12 (29#12))).zeroExtend 64)).setPC (pcAt (pc + 1))
    refine ⟨s1, by rw [hlen]; exact hs1, by rw [hlen]; rfl, ?_, fun _ => by simp [s1], ?_⟩
    · intro reg hreg
      have hnet : reg ≠ tailDst := fun h => hreg (by simp [h])
      simp [s1, getReg_setReg_ne' tailDst reg hnet.symm]
    · intro hcl
      simp only [↓reduceIte, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq htail_ne0,
        hsrc_reg, haddr, hsrc_b29 hcl]
      exact byte29_clean_zeroExtend d (hd_clean hcl)
  | false =>
    by_cases hsh0 : tailShift = 0
    · subst hsh0
      have hlen : (tailExtract4Code tailDst 0 false srcReg).length = 1 := rfl
      have hi0 : openInstr pc = .base (.LBU .x5 srcReg (29#12)) := by
        have h := hcode.2 0 (by simp [tailExtract4Code]); simpa [tailExtract4Code] using h
      have hs1 := step_LBU (by have := hcode.1; rw [hlen] at this; omega) hpc hi0 (by rw [hsrc_reg]; exact hval)
      set s1 := (s.setReg .x5 ((s.getByte (s.getReg srcReg + signExtend12 (29#12))).zeroExtend 64)).setPC (pcAt (pc + 1))
      refine ⟨s1, by rw [hlen]; exact hs1, by rw [hlen]; rfl, ?_, fun _ => by simp [s1], ?_⟩
      · intro reg hreg
        have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
        simp [s1, getReg_setReg_ne' .x5 reg hne5.symm]
      · intro hcl
        simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, s1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hsrc_reg, haddr, hsrc_b29 hcl]
        exact byte29_clean_zeroExtend d (hd_clean hcl)
    · have hbeq : (tailShift == 0) = false := beq_false_of_ne hsh0
      have hlen : (tailExtract4Code tailDst tailShift false srcReg).length = 3 := by
        simp [tailExtract4Code, hbeq]
      have hbd : pc + 3 ≤ OPEN_CODE_LEN := by have := hcode.1; rw [hlen] at this; exact this
      have hi0 : openInstr pc = .base (.LBU .x5 srcReg (29#12)) := by
        have h := hcode.2 0 (by rw [hlen]; omega); simpa [tailExtract4Code, hbeq] using h
      have hi1 : openInstr (pc + 1) = .base (.SLLI .x5 .x5 (BitVec.ofNat 6 tailShift)) := by
        have h := hcode.2 1 (by rw [hlen]; omega); simpa [tailExtract4Code, hbeq] using h
      have hi2 : openInstr (pc + 2) = .base (.OR tailDst tailDst .x5) := by
        have h := hcode.2 2 (by rw [hlen]; omega); simpa [tailExtract4Code, hbeq] using h
      have hs1 := step_LBU (by omega) hpc hi0 (by rw [hsrc_reg]; exact hval)
      set s1 := (s.setReg .x5 ((s.getByte (s.getReg srcReg + signExtend12 (29#12))).zeroExtend 64)).setPC (pcAt (pc + 1))
      have hs2 := step_SLLI (s := s1) (by omega) rfl hi1
      set s2 := (s1.setReg .x5 (s1.getReg .x5 <<< (BitVec.ofNat 6 tailShift).toNat)).setPC (pcAt (pc + 1 + 1))
      have hs3 := step_OR (s := s2) (by omega) (by congr 1) hi2
      set s3 := (s2.setReg tailDst (s2.getReg tailDst ||| s2.getReg .x5)).setPC (pcAt (pc + 2 + 1))
      refine ⟨s3, by rw [hlen]; exact (hs1.trans hs2).trans hs3, by rw [hlen]; congr 1, ?_, fun _ => by simp [s3, s2, s1], ?_⟩
      · intro reg hreg
        have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
        have hnet : reg ≠ tailDst := fun h => hreg (by simp [h])
        simp [s3, s2, s1, getReg_setReg_ne' tailDst reg hnet.symm, getReg_setReg_ne' .x5 reg hne5.symm]
      · intro hcl
        have hpre' := hpre hcl
        simp only [Bool.false_eq_true, ↓reduceIte, hbeq] at hpre' ⊢
        have hne5t : tailDst ≠ .x5 := htail_ne5 rfl hsh0
        have hs2_td : s2.getReg tailDst = BitVec.ofNat 64 prevVal := by
          simp [s2, s1, getReg_setReg_ne' .x5 tailDst hne5t.symm, hpre'.2]
        have hs1_x5 : s1.getReg .x5 = BitVec.ofNat 64 (tail6 d).toNat := by
          simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
            hsrc_reg, haddr, hsrc_b29 hcl]
          exact byte29_clean_zeroExtend d (hd_clean hcl)
        have hsh_mod : (BitVec.ofNat 6 tailShift).toNat = tailShift := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hs2_x5 : s2.getReg .x5 = BitVec.ofNat 64 (tail6 d).toNat <<< tailShift := by
          simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs1_x5, hsh_mod]
        simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq htail_ne0, hs2_td, hs2_x5]
        exact bv64_or_shl_tail6 prevVal tailShift (tail6 d).toNat hsh_bd hpre'.1 (tail6 d).isLt

private theorem openRuns_tailExtractOther {clean : Prop} {s : MachineState} {pc : Nat}
    {tailDst : Reg} {tailShift prevVal : Nat} {tailInit : Bool} {d : Digest}
    (hcode : CodeAt pc (tailExtractOtherCode tailDst tailShift tailInit))
    (hpc : s.pc = pcAt pc)
    (hx10 : clean → s.getReg .x10 = d.extractLsb' 192 64)
    (hd_clean : clean → mask238 d = d)
    (hsh_bd : tailShift + 6 ≤ 64)
    (htail_ne0 : tailDst ≠ .x0)
    (htail_ne5 : tailInit = false → tailShift ≠ 0 → tailDst ≠ .x5)
    (hpre : TailAccumPre clean s tailDst tailShift tailInit prevVal) :
    ∃ s' : MachineState,
      OpenRuns s (tailExtractOtherCode tailDst tailShift tailInit).length
        (tailExtractOtherCode tailDst tailShift tailInit).length s' ∧
      s'.pc = pcAt (pc + (tailExtractOtherCode tailDst tailShift tailInit).length) ∧
      RegsEqExcept [.x5, tailDst] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) ∧
      TailAccumPost clean s' tailDst tailShift tailInit prevVal (tail6 d).toNat := by
  have hx10_ushr : clean → s.getReg .x10 >>> 40 = BitVec.ofNat 64 (tail6 d).toNat := by
    intro hcl
    rw [hx10 hcl]
    refine word_tail6_clean (d.extractLsb' 192 64) d (hd_clean hcl) (fun j hj => ?_)
    rw [extractLsb'_extractLsb' d 192 64 (8 * (5 + j)) 8 (by omega)]
    congr 1; omega
  cases tailInit with
  | true =>
    have hlen : (tailExtractOtherCode tailDst tailShift true).length = 1 := rfl
    have hi0 : openInstr pc = .base (.SRLI tailDst .x10 (40#6)) := by
      have h := hcode.2 0 (by simp [tailExtractOtherCode]); simpa [tailExtractOtherCode] using h
    have hs1 := step_SRLI (by have := hcode.1; rw [hlen] at this; omega) hpc hi0
    set s1 := (s.setReg tailDst (s.getReg .x10 >>> (40#6).toNat)).setPC (pcAt (pc + 1))
    refine ⟨s1, by rw [hlen]; exact hs1, by rw [hlen]; rfl, ?_, fun _ => by simp [s1], ?_⟩
    · intro reg hreg
      have hnet : reg ≠ tailDst := fun h => hreg (by simp [h])
      simp [s1, getReg_setReg_ne' tailDst reg hnet.symm]
    · intro hcl
      simp only [↓reduceIte, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq htail_ne0,
        show (40#6 : BitVec 6).toNat = 40 from rfl]
      exact hx10_ushr hcl
  | false =>
    by_cases hsh0 : tailShift = 0
    · subst hsh0
      have hlen : (tailExtractOtherCode tailDst 0 false).length = 1 := rfl
      have hi0 : openInstr pc = .base (.SRLI .x5 .x10 (40#6)) := by
        have h := hcode.2 0 (by simp [tailExtractOtherCode]); simpa [tailExtractOtherCode] using h
      have hs1 := step_SRLI (by have := hcode.1; rw [hlen] at this; omega) hpc hi0
      set s1 := (s.setReg .x5 (s.getReg .x10 >>> (40#6).toNat)).setPC (pcAt (pc + 1))
      refine ⟨s1, by rw [hlen]; exact hs1, by rw [hlen]; rfl, ?_, fun _ => by simp [s1], ?_⟩
      · intro reg hreg
        have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
        simp [s1, getReg_setReg_ne' .x5 reg hne5.symm]
      · intro hcl
        simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, s1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, show (40#6 : BitVec 6).toNat = 40 from rfl]
        exact hx10_ushr hcl
    · have hbeq : (tailShift == 0) = false := beq_false_of_ne hsh0
      have hlen : (tailExtractOtherCode tailDst tailShift false).length = 3 := by
        simp [tailExtractOtherCode, hbeq]
      have hbd : pc + 3 ≤ OPEN_CODE_LEN := by have := hcode.1; rw [hlen] at this; exact this
      have hi0 : openInstr pc = .base (.SRLI .x5 .x10 (40#6)) := by
        have h := hcode.2 0 (by rw [hlen]; omega); simpa [tailExtractOtherCode, hbeq] using h
      have hi1 : openInstr (pc + 1) = .base (.SLLI .x5 .x5 (BitVec.ofNat 6 tailShift)) := by
        have h := hcode.2 1 (by rw [hlen]; omega); simpa [tailExtractOtherCode, hbeq] using h
      have hi2 : openInstr (pc + 2) = .base (.OR tailDst tailDst .x5) := by
        have h := hcode.2 2 (by rw [hlen]; omega); simpa [tailExtractOtherCode, hbeq] using h
      have hs1 := step_SRLI (by omega) hpc hi0
      set s1 := (s.setReg .x5 (s.getReg .x10 >>> (40#6).toNat)).setPC (pcAt (pc + 1))
      have hs2 := step_SLLI (s := s1) (by omega) rfl hi1
      set s2 := (s1.setReg .x5 (s1.getReg .x5 <<< (BitVec.ofNat 6 tailShift).toNat)).setPC (pcAt (pc + 1 + 1))
      have hs3 := step_OR (s := s2) (by omega) (by congr 1) hi2
      set s3 := (s2.setReg tailDst (s2.getReg tailDst ||| s2.getReg .x5)).setPC (pcAt (pc + 2 + 1))
      refine ⟨s3, by rw [hlen]; exact (hs1.trans hs2).trans hs3, by rw [hlen]; congr 1, ?_, fun _ => by simp [s3, s2, s1], ?_⟩
      · intro reg hreg
        have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
        have hnet : reg ≠ tailDst := fun h => hreg (by simp [h])
        simp [s3, s2, s1, getReg_setReg_ne' tailDst reg hnet.symm, getReg_setReg_ne' .x5 reg hne5.symm]
      · intro hcl
        have hpre' := hpre hcl
        simp only [Bool.false_eq_true, ↓reduceIte, hbeq] at hpre' ⊢
        have hne5t : tailDst ≠ .x5 := htail_ne5 rfl hsh0
        have hs2_td : s2.getReg tailDst = BitVec.ofNat 64 prevVal := by
          simp [s2, s1, getReg_setReg_ne' .x5 tailDst hne5t.symm, hpre'.2]
        have hs1_x5 : s1.getReg .x5 = BitVec.ofNat 64 (tail6 d).toNat := by
          simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
            show (40#6 : BitVec 6).toNat = 40 from rfl]
          exact hx10_ushr hcl
        have hsh_mod : (BitVec.ofNat 6 tailShift).toNat = tailShift := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hs2_x5 : s2.getReg .x5 = BitVec.ofNat 64 (tail6 d).toNat <<< tailShift := by
          simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs1_x5, hsh_mod]
        simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq htail_ne0, hs2_td, hs2_x5]
        exact bv64_or_shl_tail6 prevVal tailShift (tail6 d).toNat hsh_bd hpre'.1 (tail6 d).isLt

/-! ### 3. Universal 29-Byte + 6-Bit-Tail Copy (`copy29Code`) -/

def copy29NextR (r : Fin 8) : Fin 8 := ⟨(r.val + 5) % 8, Nat.mod_lt _ (by omega)⟩

def copy29NextDstOff (r : Fin 8) (dstOff : Nat) : Nat :=
  if r.val < 3 then dstOff + 24 else dstOff + 32

def copy29NextFlushedR4 (r : Fin 8) (flushR7 : Bool) : Bool :=
  r.val == 7 && flushR7

def copy29RemCode (rv : Nat) (dstOff : Nat) (flushR7 : Bool) : List Instruction :=
  match rv with
  | 0 => [.base (.AND .x12 .x10 .x11)]
  | 1 => [.base (.SLLI .x6 .x10 (24#6)), .base (.SRLI .x6 .x6 (16#6)), .base (.OR .x12 .x12 .x6)]
  | 2 => [.base (.SLLI .x6 .x10 (24#6)), .base (.SRLI .x6 .x6 (8#6)), .base (.OR .x12 .x12 .x6)]
  | 3 => [.base (.SLLI .x6 .x10 (24#6)), .base (.OR .x12 .x12 .x6),
          .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24)))]
  | 5 => [.base (.SLLI .x6 .x10 (40#6)), .base (.OR .x12 .x12 .x6),
          .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))),
          .base (.SLLI .x12 .x10 (24#6)), .base (.SRLI .x12 .x12 (48#6))]
  | 6 => [.base (.SLLI .x6 .x10 (48#6)), .base (.OR .x12 .x12 .x6),
          .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))),
          .base (.SLLI .x12 .x10 (24#6)), .base (.SRLI .x12 .x12 (40#6))]
  | _ => [.base (.SLLI .x6 .x10 (56#6)), .base (.OR .x12 .x12 .x6),
          .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24)))] ++
         (if flushR7 then
           [.base (.SRLI .x6 .x10 (8#6)), .base (.SW .x25 .x6 (BitVec.ofNat 12 (dstOff + 32)))]
          else
           [.base (.SLLI .x12 .x10 (24#6)), .base (.SRLI .x12 .x12 (32#6))])

def copy29Code (r : Fin 8) (srcReg : Reg) (dstOff : Nat) (tailDst : Reg) (tailShift : Nat)
    (tailInit flushedR4 flushR7 : Bool) : List Instruction :=
  if r.val == 4 then
    dwordsCode ⟨4, by omega⟩ 3 srcReg 0 dstOff flushedR4 true ++
    [.base (.LWU .x5 srcReg (24#12)),
     .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 28))),
     .base (.LBU .x12 srcReg (28#12))] ++
    tailExtract4Code tailDst tailShift tailInit srcReg
  else
    dwordsCode r 3 srcReg 0 dstOff false false ++
    [.base (.LD .x10 srcReg (24#12))] ++
    copy29RemCode r.val dstOff flushR7 ++
    tailExtractOtherCode tailDst tailShift tailInit

private theorem writerState_of_mem_eq {clean : Prop} {s s' : MachineState}
    {r : Fin 8} {fl : Bool} {base dstOff : Nat} {written : List Byte}
    (hw : WriterState clean s r fl base dstOff written)
    (hmem : ∀ a, s'.getMem a = s.getMem a)
    (hx25 : s'.getReg .x25 = s.getReg .x25)
    (hx12 : s'.getReg .x12 = s.getReg .x12) :
    WriterState clean s' r fl base dstOff written := by
  have hbyte : ∀ a, s'.getByte a = s.getByte a := fun a => by
    simp only [MachineState.getByte, hmem]
  refine ⟨hw.hbase8, hw.hdst8, hw.hlen, hw.hbound, hx25.trans hw.rx25, hw.hflushed_ok,
    fun hcl j hj => by rw [hbyte]; exact hw.hbytes hcl j hj,
    fun hcl => ?_⟩
  have hrem := hw.hrem hcl
  cases fl with
  | true =>
    simp only [↓reduceIte] at hrem ⊢
    intro j hj; rw [hbyte]; exact hrem j hj
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
    by_cases hr0 : r.val = 0
    · simp only [hr0, ↓reduceIte]
    · simp only [hr0, ↓reduceIte] at hrem ⊢
      simpa only [hx12] using hrem

/-- Factor `copy29RemCode` execution with plain `pc2 : Nat` to keep `whnf` instantaneous for all 7 non-4 residues. -/
private theorem openRuns_copy29_rem {clean : Prop} {s2 : MachineState} {pc2 : Nat}
    {rv : Nat} (hrv : rv < 8) (hr4 : rv ≠ 4)
    {base dstOff : Nat} {flushR7 : Bool} {written : List Byte} {d : Digest}
    (hcodeR : CodeAt pc2 (copy29RemCode rv dstOff flushR7))
    (hpc2 : s2.pc = pcAt pc2)
    (hs2_x10 : clean → s2.getReg .x10 = d.extractLsb' 192 64)
    (hs2_x11 : s2.getReg .x11 = mask40Word)
    (hdst_off : dstOff + 32 < 2048) (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hdst8 : dstOff % 8 = 0) (hlen_rv : written.length = base + dstOff + rv)
    (hw2 : WriterState clean s2 ⟨rv, hrv⟩ false base (dstOff + 24) (written ++ bitsToBytes d 24)) :
    ∃ s3 : MachineState,
      OpenRuns s2 (copy29RemCode rv dstOff flushR7).length (copy29RemCode rv dstOff flushR7).length s3 ∧
      s3.pc = pcAt (pc2 + (copy29RemCode rv dstOff flushR7).length) ∧
      RegsEqExcept [.x6, .x12] s2 s3 ∧
      ProofWritePreserves s2 s3 ∧
      WriterState clean s3 (copy29NextR ⟨rv, hrv⟩) (copy29NextFlushedR4 ⟨rv, hrv⟩ flushR7)
        base (copy29NextDstOff ⟨rv, hrv⟩ dstOff) (written ++ bitsToBytes d 29) := by
  set d3 : Word := d.extractLsb' 192 64
  have h29_eq : written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8) =
      written ++ bitsToBytes d 29 := by
    rw [List.append_assoc, bitsToBytes_24_append d 5 (by omega)]
  have hbase8 := hw2.hbase8
  have hs2_x25 : s2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := hw2.rx25
  have hdst24_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 24)) =
      BitVec.ofNat 64 (11341403200 + base + (dstOff + 24)) := by
    rw [signExtend12_nonneg (dstOff + 24) (by omega), ← BitVec.ofNat_add]
  have hdst24_val8 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) 8 = true := by
    rw [hdst24_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
  have hdst32_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 32)) =
      BitVec.ofNat 64 (11341403200 + base + (dstOff + 32)) := by
    rw [signExtend12_nonneg (dstOff + 32) (by omega), ← BitVec.ofNat_add]
  have hdst32_val4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 32))) 4 = true := by
    rw [hdst32_addr]; exact accessValid_ofNat _ 4 (by omega) (by omega)
  have hget29_left : ∀ j (hj : j < (written ++ bitsToBytes d 24).length),
      (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length] at hj ⊢; omega) =
        (written ++ bitsToBytes d 24)[j]'hj := by
    intro j hj
    have h1 : (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length] at hj ⊢; omega) =
        (written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8))[j]'(by rw [h29_eq]; simp [bitsToBytes_length] at hj ⊢; omega) := by
      revert h29_eq; generalize written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8) = lhs; rintro rfl; rfl
    rw [h1, List.getElem_append_left hj]
  have hbyte_tail : ∀ j (hj1 : base + dstOff + 24 + rv ≤ j) (hj2 : j < base + dstOff + 29 + rv),
      (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length]; omega) =
        d3.extractLsb' (8 * (j - (base + dstOff + 24 + rv))) 8 := by
    intro j hj1 hj2
    have hlen24 : (written ++ bitsToBytes d 24).length = base + dstOff + 24 + rv := by
      simp [bitsToBytes_length]; omega
    have h1 : (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length]; omega) =
        (written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8))[j]'(by rw [h29_eq]; simp [bitsToBytes_length]; omega) := by
      revert h29_eq; generalize written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8) = lhs; rintro rfl; rfl
    rw [h1, List.getElem_append_right (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1; omega
  have hlen24_all : (written ++ bitsToBytes d 24).length = base + dstOff + 24 + rv := by
    simp [bitsToBytes_length, hlen_rv]; omega
  have hcs : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 5 ∨ rv = 6 ∨ rv = 7 := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- rv = 0: AND x12 x10 x11
    have hlen : (copy29RemCode 0 dstOff flushR7).length = 1 := rfl
    have hi0 : openInstr pc2 = .base (.AND .x12 .x10 .x11) := by
      have h := hcodeR.2 0 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hs := step_AND (s := s2) (by have := hcodeR.1; rw [hlen] at this; omega) hpc2 hi0
    set s3 := (s2.setReg .x12 (s2.getReg .x10 &&& s2.getReg .x11)).setPC (pcAt (pc2 + 1))
    refine ⟨s3, by rw [hlen]; exact hs, by rw [hlen]; rfl, ?_, fun _ _ => by simp [s3], ?_⟩
    · intro reg hreg; have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      simp [s3, getReg_setReg_ne' .x12 reg hne12.symm]
    · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega, by simp [s3, getReg_setReg_ne', hs2_x25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
      · simp only [copy29NextDstOff, show (0 : Nat) < 3 by omega, ↓reduceIte] at hj
        simp only [s3, getByte_setPC, getByte_setReg]
        rw [hget29_left j (by have := hw2.hlen; omega)]
        exact hw2.hbytes hcl j hj
      · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show (0 : Nat) < 3 by omega,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ (((0 + 5) % 8 : Nat) = 0) by decide]
        have hx12 : s3.getReg .x12 = d3 &&& mask40Word := by simp [s3, hs2_x10 hcl, hs2_x11]
        refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · rw [hx12, and_mask40_byte d3 j (by omega), if_pos (by omega), hbyte_tail (base + (dstOff + 24) + j) (by omega) (by omega)]
          congr 1; omega
        · rw [hx12, and_mask40_byte d3 j hj2, if_neg (by omega)]
  · -- rv = 1: SLLI x6 x10 24; SRLI x6 x6 16; OR x12 x12 x6
    have hlen : (copy29RemCode 1 dstOff flushR7).length = 3 := rfl
    have hbd : pc2 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [hlen] at this; exact this
    have hi0 : openInstr pc2 = .base (.SLLI .x6 .x10 (24#6)) := by have h := hcodeR.2 0 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi1 : openInstr (pc2 + 1) = .base (.SRLI .x6 .x6 (16#6)) := by have h := hcodeR.2 1 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi2 : openInstr (pc2 + 2) = .base (.OR .x12 .x12 .x6) := by have h := hcodeR.2 2 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have ha1 := step_SLLI (s := s2) (by omega) hpc2 hi0
    set t1 := (s2.setReg .x6 (s2.getReg .x10 <<< (24#6).toNat)).setPC (pcAt (pc2 + 1))
    have ha2 := step_SRLI (s := t1) (by omega) rfl hi1
    set t2 := (t1.setReg .x6 (t1.getReg .x6 >>> (16#6).toNat)).setPC (pcAt (pc2 + 1 + 1))
    have ha3 := step_OR (s := t2) (by omega) (by congr 1) hi2
    set s3 := (t2.setReg .x12 (t2.getReg .x12 ||| t2.getReg .x6)).setPC (pcAt (pc2 + 2 + 1))
    refine ⟨s3, by rw [hlen]; exact (ha1.trans ha2).trans ha3, by rw [hlen]; congr 1, ?_, fun _ _ => by simp [s3, t2, t1], ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      simp [s3, t2, t1, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
    · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega, by simp [s3, t2, t1, getReg_setReg_ne', hs2_x25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
      · simp only [copy29NextDstOff, show (1 : Nat) < 3 by omega, ↓reduceIte] at hj
        simp only [s3, t2, t1, getByte_setPC, getByte_setReg]
        rw [hget29_left j (by have := hw2.hlen; omega)]
        exact hw2.hbytes hcl j hj
      · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show (1 : Nat) < 3 by omega,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ (((1 + 5) % 8 : Nat) = 0) by decide]
        have hrem2 := hw2.hrem hcl
        simp only [Bool.false_eq_true, ↓reduceIte, show ¬ ((1 : Nat) = 0) by omega] at hrem2
        have hx12 : s3.getReg .x12 = s2.getReg .x12 ||| ((d3 <<< (8 * 3)) >>> (8 * 2)) := by
          simp [s3, t2, t1, getReg_setReg_ne', hs2_x10 hcl]
        refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · rw [hx12, word_or_shl_ushr_byte _ d3 1 3 2 (by omega) (by omega) (by omega) hrem2.2 (fun _ _ => by omega) j (by omega)]
          split_ifs with hj1 hcond
          · rw [hrem2.1 j hj1, hget29_left (base + (dstOff + 24) + j) (by omega)]
          · rw [hbyte_tail (base + (dstOff + 24) + j) (by omega) (by omega)]; congr 1; omega
          · omega
        · rw [hx12, word_or_shl_ushr_byte _ d3 1 3 2 (by omega) (by omega) (by omega) hrem2.2 (fun _ _ => by omega) j hj2,
            if_neg (by omega), if_neg (by omega)]
  · -- rv = 2: SLLI x6 x10 24; SRLI x6 x6 8; OR x12 x12 x6
    have hlen : (copy29RemCode 2 dstOff flushR7).length = 3 := rfl
    have hbd : pc2 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [hlen] at this; exact this
    have hi0 : openInstr pc2 = .base (.SLLI .x6 .x10 (24#6)) := by have h := hcodeR.2 0 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi1 : openInstr (pc2 + 1) = .base (.SRLI .x6 .x6 (8#6)) := by have h := hcodeR.2 1 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi2 : openInstr (pc2 + 2) = .base (.OR .x12 .x12 .x6) := by have h := hcodeR.2 2 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have ha1 := step_SLLI (s := s2) (by omega) hpc2 hi0
    set t1 := (s2.setReg .x6 (s2.getReg .x10 <<< (24#6).toNat)).setPC (pcAt (pc2 + 1))
    have ha2 := step_SRLI (s := t1) (by omega) rfl hi1
    set t2 := (t1.setReg .x6 (t1.getReg .x6 >>> (8#6).toNat)).setPC (pcAt (pc2 + 1 + 1))
    have ha3 := step_OR (s := t2) (by omega) (by congr 1) hi2
    set s3 := (t2.setReg .x12 (t2.getReg .x12 ||| t2.getReg .x6)).setPC (pcAt (pc2 + 2 + 1))
    refine ⟨s3, by rw [hlen]; exact (ha1.trans ha2).trans ha3, by rw [hlen]; congr 1, ?_, fun _ _ => by simp [s3, t2, t1], ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      simp [s3, t2, t1, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
    · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega, by simp [s3, t2, t1, getReg_setReg_ne', hs2_x25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
      · simp only [copy29NextDstOff, show (2 : Nat) < 3 by omega, ↓reduceIte] at hj
        simp only [s3, t2, t1, getByte_setPC, getByte_setReg]
        rw [hget29_left j (by have := hw2.hlen; omega)]
        exact hw2.hbytes hcl j hj
      · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show (2 : Nat) < 3 by omega,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ (((2 + 5) % 8 : Nat) = 0) by decide]
        have hrem2 := hw2.hrem hcl
        simp only [Bool.false_eq_true, ↓reduceIte, show ¬ ((2 : Nat) = 0) by omega] at hrem2
        have hx12 : s3.getReg .x12 = s2.getReg .x12 ||| ((d3 <<< (8 * 3)) >>> (8 * 1)) := by
          simp [s3, t2, t1, getReg_setReg_ne', hs2_x10 hcl]
        refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · rw [hx12, word_or_shl_ushr_byte _ d3 2 3 1 (by omega) (by omega) (by omega) hrem2.2 (fun _ _ => by omega) j (by omega)]
          split_ifs with hj1 hcond
          · rw [hrem2.1 j hj1, hget29_left (base + (dstOff + 24) + j) (by omega)]
          · rw [hbyte_tail (base + (dstOff + 24) + j) (by omega) (by omega)]; congr 1; omega
          · omega
        · rw [hx12, word_or_shl_ushr_byte _ d3 2 3 1 (by omega) (by omega) (by omega) hrem2.2 (fun _ _ => by omega) j hj2,
            if_neg (by omega), if_neg (by omega)]
  · -- rv = 3: SLLI x6 x10 24; OR x12 x12 x6; SD x25 x12 (dstOff+24)
    have hlen : (copy29RemCode 3 dstOff flushR7).length = 3 := rfl
    have hbd : pc2 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [hlen] at this; exact this
    have hi0 : openInstr pc2 = .base (.SLLI .x6 .x10 (24#6)) := by have h := hcodeR.2 0 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi1 : openInstr (pc2 + 1) = .base (.OR .x12 .x12 .x6) := by have h := hcodeR.2 1 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi2 : openInstr (pc2 + 2) = .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))) := by have h := hcodeR.2 2 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have ha1 := step_SLLI (s := s2) (by omega) hpc2 hi0
    set t1 := (s2.setReg .x6 (s2.getReg .x10 <<< (24#6).toNat)).setPC (pcAt (pc2 + 1))
    have ha2 := step_OR (s := t1) (by omega) rfl hi1
    set t2 := (t1.setReg .x12 (t1.getReg .x12 ||| t1.getReg .x6)).setPC (pcAt (pc2 + 1 + 1))
    have ht2_x25 : t2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by simp [t2, t1, getReg_setReg_ne', hs2_x25]
    have ha3 := step_SD (s := t2) (by omega) (by congr 1) hi2 (by rw [ht2_x25]; exact hdst24_val8)
    set s3 := (t2.setMem (t2.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) (t2.getReg .x12)).setPC (pcAt (pc2 + 2 + 1))
    refine ⟨s3, by rw [hlen]; exact (ha1.trans ha2).trans ha3, by rw [hlen]; congr 1, ?_, ?_, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      simp [s3, t2, t1, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
    · intro a ha
      simp only [s3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg, ht2_x25, hdst24_addr]
      exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
    · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega, by simp [s3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun _ => by simp [copy29NextR, copy29NextFlushedR4]⟩
      simp only [copy29NextDstOff, show ¬ ((3 : Nat) < 3) by omega, ↓reduceIte] at hj
      have hrem2 := hw2.hrem hcl
      simp only [Bool.false_eq_true, ↓reduceIte, show ¬ ((3 : Nat) = 0) by omega] at hrem2
      have ht2_x12 : t2.getReg .x12 = s2.getReg .x12 ||| (d3 <<< (8 * 3)) := by
        simp [t2, t1, getReg_setReg_ne', hs2_x10 hcl]
      simp only [s3, getByte_setPC, ht2_x25, hdst24_addr, ht2_x12]
      change (s2.setMem (BitVec.ofNat 64 (11341403200 + base + (dstOff + 24))) (s2.getReg .x12 ||| (d3 <<< (8 * 3)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
      by_cases hlt : j < base + (dstOff + 24)
      · rw [setMem_getByte_ofNat s2 _ _ _ (by omega) (by omega) (by omega) (by omega),
          hget29_left j (by have := hw2.hlen; omega)]
        exact hw2.hbytes hcl j hlt
      · have hk : j - (base + (dstOff + 24)) < 8 := by omega
        have heq : 11341403200 + j = (11341403200 + base + (dstOff + 24)) + (j - (base + (dstOff + 24))) := by omega
        rw [heq, setMem_getByte_inside s2 _ _ _ (by omega) hk,
          word_or_shl_byte (s2.getReg .x12) d3 3 (by omega) hrem2.2 _ hk]
        split_ifs with hkr
        · rw [hrem2.1 _ hkr, hget29_left j (by omega)]; congr 1; omega
        · rw [hbyte_tail j (by omega) (by omega),
            show 8 * (j - (base + (dstOff + 24)) - 3) = 8 * (j - (base + dstOff + 24 + 3)) by omega]
  · -- rv = 5: SLLI x6 x10 40; OR x12 x12 x6; SD x25 x12 (dstOff+24); SLLI x12 x10 24; SRLI x12 x12 48
    have hlen : (copy29RemCode 5 dstOff flushR7).length = 5 := rfl
    have hbd : pc2 + 5 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [hlen] at this; exact this
    have hi0 : openInstr pc2 = .base (.SLLI .x6 .x10 (40#6)) := by have h := hcodeR.2 0 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi1 : openInstr (pc2 + 1) = .base (.OR .x12 .x12 .x6) := by have h := hcodeR.2 1 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi2 : openInstr (pc2 + 2) = .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))) := by have h := hcodeR.2 2 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi3 : openInstr (pc2 + 3) = .base (.SLLI .x12 .x10 (24#6)) := by have h := hcodeR.2 3 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi4 : openInstr (pc2 + 4) = .base (.SRLI .x12 .x12 (48#6)) := by have h := hcodeR.2 4 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have ha1 := step_SLLI (s := s2) (by omega) hpc2 hi0
    set t1 := (s2.setReg .x6 (s2.getReg .x10 <<< (40#6).toNat)).setPC (pcAt (pc2 + 1))
    have ha2 := step_OR (s := t1) (by omega) rfl hi1
    set t2 := (t1.setReg .x12 (t1.getReg .x12 ||| t1.getReg .x6)).setPC (pcAt (pc2 + 1 + 1))
    have ht2_x25 : t2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by simp [t2, t1, getReg_setReg_ne', hs2_x25]
    have ha3 := step_SD (s := t2) (by omega) (by congr 1) hi2 (by rw [ht2_x25]; exact hdst24_val8)
    set t3 := (t2.setMem (t2.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) (t2.getReg .x12)).setPC (pcAt (pc2 + 2 + 1))
    have ha4 := step_SLLI (s := t3) (by omega) (by congr 1) hi3
    set t4 := (t3.setReg .x12 (t3.getReg .x10 <<< (24#6).toNat)).setPC (pcAt (pc2 + 3 + 1))
    have ha5 := step_SRLI (s := t4) (by omega) (by congr 1) hi4
    set s3 := (t4.setReg .x12 (t4.getReg .x12 >>> (48#6).toNat)).setPC (pcAt (pc2 + 4 + 1))
    refine ⟨s3, by rw [hlen]; exact (((ha1.trans ha2).trans ha3).trans ha4).trans ha5, by rw [hlen]; congr 1, ?_, ?_, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
    · intro a ha
      simp only [s3, t4, t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg, ht2_x25, hdst24_addr]
      exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
    · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega, by simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
      · simp only [copy29NextDstOff, show ¬ ((5 : Nat) < 3) by omega, ↓reduceIte] at hj
        have hrem2 := hw2.hrem hcl
        simp only [Bool.false_eq_true, ↓reduceIte, show ¬ ((5 : Nat) = 0) by omega] at hrem2
        have ht2_x12 : t2.getReg .x12 = s2.getReg .x12 ||| (d3 <<< (8 * 5)) := by
          simp [t2, t1, getReg_setReg_ne', hs2_x10 hcl]
        simp only [s3, t4, t3, getByte_setPC, getByte_setReg, ht2_x25, hdst24_addr, ht2_x12]
        change (s2.setMem (BitVec.ofNat 64 (11341403200 + base + (dstOff + 24))) (s2.getReg .x12 ||| (d3 <<< (8 * 5)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
        by_cases hlt : j < base + (dstOff + 24)
        · rw [setMem_getByte_ofNat s2 _ _ _ (by omega) (by omega) (by omega) (by omega),
            hget29_left j (by have := hw2.hlen; omega)]
          exact hw2.hbytes hcl j hlt
        · have hk : j - (base + (dstOff + 24)) < 8 := by omega
          have heq : 11341403200 + j = (11341403200 + base + (dstOff + 24)) + (j - (base + (dstOff + 24))) := by omega
          rw [heq, setMem_getByte_inside s2 _ _ _ (by omega) hk,
            word_or_shl_byte (s2.getReg .x12) d3 5 (by omega) hrem2.2 _ hk]
          split_ifs with hkr
          · rw [hrem2.1 _ hkr, hget29_left j (by omega)]; congr 1; omega
          · rw [hbyte_tail j (by omega) (by omega),
              show 8 * (j - (base + (dstOff + 24)) - 5) = 8 * (j - (base + dstOff + 24 + 5)) by omega]
      · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show ¬ ((5 : Nat) < 3) by omega,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ (((5 + 5) % 8 : Nat) = 0) by decide]
        have hx12 : s3.getReg .x12 = (d3 <<< (8 * 3)) >>> (8 * 6) := by
          simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x10 hcl]
        refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · rw [hx12, word_shl_ushr_byte d3 3 6 (by omega) (by omega) j (by omega), if_pos (by omega),
            hbyte_tail (base + (dstOff + 32) + j) (by omega) (by omega)]
          congr 1; omega
        · rw [hx12, word_shl_ushr_byte d3 3 6 (by omega) (by omega) j hj2, if_neg (by omega)]
  · -- rv = 6: SLLI x6 x10 48; OR x12 x12 x6; SD x25 x12 (dstOff+24); SLLI x12 x10 24; SRLI x12 x12 40
    have hlen : (copy29RemCode 6 dstOff flushR7).length = 5 := rfl
    have hbd : pc2 + 5 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [hlen] at this; exact this
    have hi0 : openInstr pc2 = .base (.SLLI .x6 .x10 (48#6)) := by have h := hcodeR.2 0 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi1 : openInstr (pc2 + 1) = .base (.OR .x12 .x12 .x6) := by have h := hcodeR.2 1 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi2 : openInstr (pc2 + 2) = .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))) := by have h := hcodeR.2 2 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi3 : openInstr (pc2 + 3) = .base (.SLLI .x12 .x10 (24#6)) := by have h := hcodeR.2 3 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have hi4 : openInstr (pc2 + 4) = .base (.SRLI .x12 .x12 (40#6)) := by have h := hcodeR.2 4 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
    have ha1 := step_SLLI (s := s2) (by omega) hpc2 hi0
    set t1 := (s2.setReg .x6 (s2.getReg .x10 <<< (48#6).toNat)).setPC (pcAt (pc2 + 1))
    have ha2 := step_OR (s := t1) (by omega) rfl hi1
    set t2 := (t1.setReg .x12 (t1.getReg .x12 ||| t1.getReg .x6)).setPC (pcAt (pc2 + 1 + 1))
    have ht2_x25 : t2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by simp [t2, t1, getReg_setReg_ne', hs2_x25]
    have ha3 := step_SD (s := t2) (by omega) (by congr 1) hi2 (by rw [ht2_x25]; exact hdst24_val8)
    set t3 := (t2.setMem (t2.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) (t2.getReg .x12)).setPC (pcAt (pc2 + 2 + 1))
    have ha4 := step_SLLI (s := t3) (by omega) (by congr 1) hi3
    set t4 := (t3.setReg .x12 (t3.getReg .x10 <<< (24#6).toNat)).setPC (pcAt (pc2 + 3 + 1))
    have ha5 := step_SRLI (s := t4) (by omega) (by congr 1) hi4
    set s3 := (t4.setReg .x12 (t4.getReg .x12 >>> (40#6).toNat)).setPC (pcAt (pc2 + 4 + 1))
    refine ⟨s3, by rw [hlen]; exact (((ha1.trans ha2).trans ha3).trans ha4).trans ha5, by rw [hlen]; congr 1, ?_, ?_, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
    · intro a ha
      simp only [s3, t4, t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg, ht2_x25, hdst24_addr]
      exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
    · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega, by simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
      · simp only [copy29NextDstOff, show ¬ ((6 : Nat) < 3) by omega, ↓reduceIte] at hj
        have hrem2 := hw2.hrem hcl
        simp only [Bool.false_eq_true, ↓reduceIte, show ¬ ((6 : Nat) = 0) by omega] at hrem2
        have ht2_x12 : t2.getReg .x12 = s2.getReg .x12 ||| (d3 <<< (8 * 6)) := by
          simp [t2, t1, getReg_setReg_ne', hs2_x10 hcl]
        simp only [s3, t4, t3, getByte_setPC, getByte_setReg, ht2_x25, hdst24_addr, ht2_x12]
        change (s2.setMem (BitVec.ofNat 64 (11341403200 + base + (dstOff + 24))) (s2.getReg .x12 ||| (d3 <<< (8 * 6)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
        by_cases hlt : j < base + (dstOff + 24)
        · rw [setMem_getByte_ofNat s2 _ _ _ (by omega) (by omega) (by omega) (by omega),
            hget29_left j (by have := hw2.hlen; omega)]
          exact hw2.hbytes hcl j hlt
        · have hk : j - (base + (dstOff + 24)) < 8 := by omega
          have heq : 11341403200 + j = (11341403200 + base + (dstOff + 24)) + (j - (base + (dstOff + 24))) := by omega
          rw [heq, setMem_getByte_inside s2 _ _ _ (by omega) hk,
            word_or_shl_byte (s2.getReg .x12) d3 6 (by omega) hrem2.2 _ hk]
          split_ifs with hkr
          · rw [hrem2.1 _ hkr, hget29_left j (by omega)]; congr 1; omega
          · rw [hbyte_tail j (by omega) (by omega),
              show 8 * (j - (base + (dstOff + 24)) - 6) = 8 * (j - (base + dstOff + 24 + 6)) by omega]
      · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show ¬ ((6 : Nat) < 3) by omega,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ (((6 + 5) % 8 : Nat) = 0) by decide]
        have hx12 : s3.getReg .x12 = (d3 <<< (8 * 3)) >>> (8 * 5) := by
          simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x10 hcl]
        refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · rw [hx12, word_shl_ushr_byte d3 3 5 (by omega) (by omega) j (by omega), if_pos (by omega),
            hbyte_tail (base + (dstOff + 32) + j) (by omega) (by omega)]
          congr 1; omega
        · rw [hx12, word_shl_ushr_byte d3 3 5 (by omega) (by omega) j hj2, if_neg (by omega)]
  · -- rv = 7
    have hlen : (copy29RemCode 7 dstOff flushR7).length = 5 := by cases flushR7 <;> rfl
    have hbd : pc2 + 5 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [hlen] at this; exact this
    have hi0 : openInstr pc2 = .base (.SLLI .x6 .x10 (56#6)) := by
      have h := hcodeR.2 0 (by rw [hlen]; omega); cases flushR7 <;> simpa [copy29RemCode] using h
    have hi1 : openInstr (pc2 + 1) = .base (.OR .x12 .x12 .x6) := by
      have h := hcodeR.2 1 (by rw [hlen]; omega); cases flushR7 <;> simpa [copy29RemCode] using h
    have hi2 : openInstr (pc2 + 2) = .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))) := by
      have h := hcodeR.2 2 (by rw [hlen]; omega); cases flushR7 <;> simpa [copy29RemCode] using h
    have ha1 := step_SLLI (s := s2) (by omega) hpc2 hi0
    set t1 := (s2.setReg .x6 (s2.getReg .x10 <<< (56#6).toNat)).setPC (pcAt (pc2 + 1))
    have ha2 := step_OR (s := t1) (by omega) rfl hi1
    set t2 := (t1.setReg .x12 (t1.getReg .x12 ||| t1.getReg .x6)).setPC (pcAt (pc2 + 1 + 1))
    have ht2_x25 : t2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by simp [t2, t1, getReg_setReg_ne', hs2_x25]
    have ha3 := step_SD (s := t2) (by omega) (by congr 1) hi2 (by rw [ht2_x25]; exact hdst24_val8)
    set t3 := (t2.setMem (t2.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) (t2.getReg .x12)).setPC (pcAt (pc2 + 2 + 1))
    have ht3_bytes : clean → ∀ j (hj : j < base + (dstOff + 32)),
        t3.getByte (BitVec.ofNat 64 (11341403200 + j)) = (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length, hlen_rv]; omega) := by
      intro hcl j hj
      have hrem2 := hw2.hrem hcl
      simp only [Bool.false_eq_true, ↓reduceIte, show ¬ ((7 : Nat) = 0) by omega] at hrem2
      have ht2_x12 : t2.getReg .x12 = s2.getReg .x12 ||| (d3 <<< (8 * 7)) := by
        simp [t2, t1, getReg_setReg_ne', hs2_x10 hcl]
      simp only [t3, getByte_setPC, ht2_x25, hdst24_addr, ht2_x12]
      change (s2.setMem (BitVec.ofNat 64 (11341403200 + base + (dstOff + 24))) (s2.getReg .x12 ||| (d3 <<< (8 * 7)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
      by_cases hlt : j < base + (dstOff + 24)
      · rw [setMem_getByte_ofNat s2 _ _ _ (by omega) (by omega) (by omega) (by omega),
          hget29_left j (by have := hw2.hlen; omega)]
        exact hw2.hbytes hcl j hlt
      · have hk : j - (base + (dstOff + 24)) < 8 := by omega
        have heq : 11341403200 + j = (11341403200 + base + (dstOff + 24)) + (j - (base + (dstOff + 24))) := by omega
        rw [heq, setMem_getByte_inside s2 _ _ _ (by omega) hk,
          word_or_shl_byte (s2.getReg .x12) d3 7 (by omega) hrem2.2 _ hk]
        split_ifs with hkr
        · rw [hrem2.1 _ hkr, hget29_left j (by omega)]; congr 1; omega
        · rw [hbyte_tail j (by omega) (by omega),
            show 8 * (j - (base + (dstOff + 24)) - 7) = 8 * (j - (base + dstOff + 24 + 7)) by omega]
    have hp3 : ProofWritePreserves s2 t3 := by
      intro a ha
      simp only [t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg, ht2_x25, hdst24_addr]
      exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
    cases flushR7 with
    | true =>
      have hi3 : openInstr (pc2 + 3) = .base (.SRLI .x6 .x10 (8#6)) := by
        have h := hcodeR.2 3 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
      have hi4 : openInstr (pc2 + 4) = .base (.SW .x25 .x6 (BitVec.ofNat 12 (dstOff + 32))) := by
        have h := hcodeR.2 4 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
      have ha4 := step_SRLI (s := t3) (by omega) (by congr 1) hi3
      set t4 := (t3.setReg .x6 (t3.getReg .x10 >>> (8#6).toNat)).setPC (pcAt (pc2 + 3 + 1))
      have ht4_x25 : t4.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
        simp [t4, t3, getReg_setMem, getReg_setReg_ne', ht2_x25]
      have ha5 := step_SW (s := t4) (by omega) (by congr 1) hi4 (by rw [ht4_x25]; exact hdst32_val4)
      set s3 := (t4.setWord32 (t4.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 32))) ((t4.getReg .x6).truncate 32)).setPC (pcAt (pc2 + 4 + 1))
      refine ⟨s3, by rw [hlen]; exact (((ha1.trans ha2).trans ha3).trans ha4).trans ha5, by rw [hlen]; congr 1, ?_, ?_, ?_⟩
      · intro reg hreg
        have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
        have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
        simp [s3, t4, t3, t2, t1, getReg_setWord32, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
      · refine hp3.trans ?_
        intro a ha
        simp only [s3, t4, MachineState.getMem_setPC, MachineState.getMem_setReg, ht4_x25, hdst32_addr]
        exact ProofWritePreserves.setWord32_proof (by omega) (by omega) (by omega) a ha
      · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
          by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
          by simp [copy29NextDstOff]; omega, by simp [s3, t4, t3, getReg_setWord32, getReg_setMem, getReg_setReg_ne', ht2_x25],
          fun _ => by simp [copy29NextR], fun hcl j hj => ?_, fun hcl => ?_⟩
        · simp only [copy29NextDstOff, show ¬ ((7 : Nat) < 3) by omega, ↓reduceIte] at hj
          simp only [s3, t4, getByte_setPC, ht4_x25, hdst32_addr]
          change (t3.setWord32 (BitVec.ofNat 64 (11341403200 + base + (dstOff + 32))) _).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
          rw [setWord32_getByte_ofNat t3 _ _ _ (by omega) (by omega) (by omega), dif_neg (by omega)]
          exact ht3_bytes hcl j hj
        · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show ¬ ((7 : Nat) < 3) by omega,
            beq_self_eq_true, Bool.and_self, ↓reduceIte]
          intro j hj
          have ht4_x6 : (t4.getReg .x6).truncate 32 = (d3 >>> 8).truncate 32 := by
            simp [t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x10 hcl]
          simp only [s3, getByte_setPC, ht4_x25, hdst32_addr, ht4_x6]
          change (t3.setWord32 (BitVec.ofNat 64 (11341403200 + base + (dstOff + 32))) ((d3 >>> 8).truncate 32)).getByte
              (BitVec.ofNat 64 (11341403200 + base + (dstOff + 32) + j)) = _
          rw [setWord32_getByte_ofNat t3 _ _ _ (by omega) (by omega) (by omega), dif_pos (by omega),
            show 11341403200 + base + (dstOff + 32) + j - (11341403200 + base + (dstOff + 32)) = j by omega,
            ushr8_truncate32_extract_byte d3 j hj, hbyte_tail (base + (dstOff + 32) + j) (by omega) (by omega)]
          congr 1; omega
    | false =>
      have hi3 : openInstr (pc2 + 3) = .base (.SLLI .x12 .x10 (24#6)) := by
        have h := hcodeR.2 3 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
      have hi4 : openInstr (pc2 + 4) = .base (.SRLI .x12 .x12 (32#6)) := by
        have h := hcodeR.2 4 (by simp [copy29RemCode]); simpa [copy29RemCode] using h
      have ha4 := step_SLLI (s := t3) (by omega) (by congr 1) hi3
      set t4 := (t3.setReg .x12 (t3.getReg .x10 <<< (24#6).toNat)).setPC (pcAt (pc2 + 3 + 1))
      have ha5 := step_SRLI (s := t4) (by omega) (by congr 1) hi4
      set s3 := (t4.setReg .x12 (t4.getReg .x12 >>> (32#6).toNat)).setPC (pcAt (pc2 + 4 + 1))
      refine ⟨s3, by rw [hlen]; exact (((ha1.trans ha2).trans ha3).trans ha4).trans ha5, by rw [hlen]; congr 1, ?_, ?_, ?_⟩
      · intro reg hreg
        have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
        have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
        simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x6 reg hne6.symm]
      · refine hp3.trans (fun _ _ => by simp [s3, t4])
      · refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
          by simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
          by simp [copy29NextDstOff]; omega, by simp [s3, t4, t3, getReg_setMem, getReg_setReg_ne', ht2_x25],
          by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
        · simp only [copy29NextDstOff, show ¬ ((7 : Nat) < 3) by omega, ↓reduceIte] at hj
          simp only [s3, t4, getByte_setPC, getByte_setReg]
          exact ht3_bytes hcl j hj
        · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show ¬ ((7 : Nat) < 3) by omega,
            Bool.and_false, Bool.false_eq_true, ↓reduceIte, show ¬ (((7 + 5) % 8 : Nat) = 0) by decide]
          have hx12 : s3.getReg .x12 = (d3 <<< (8 * 3)) >>> (8 * 4) := by
            simp [s3, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hs2_x10 hcl]
          refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
          · rw [hx12, word_shl_ushr_byte d3 3 4 (by omega) (by omega) j (by omega), if_pos (by omega),
              hbyte_tail (base + (dstOff + 32) + j) (by omega) (by omega)]
            congr 1; omega
          · rw [hx12, word_shl_ushr_byte d3 3 4 (by omega) (by omega) j hj2, if_neg (by omega)]

/-- Step a full 29-byte + 6-bit-tail `mask238`-clean node through `copy29Code` at ANY residue `r : Fin 8`. -/
theorem openRuns_copy29 {clean : Prop} {s : MachineState} {pc : Nat}
    {r : Fin 8} {srcReg tailDst : Reg} {srcBase base dstOff tailShift prevVal : Nat}
    {tailInit flushedR4 flushR7 : Bool} {written : List Byte} {d : Digest}
    (hcode : CodeAt pc (copy29Code r srcReg dstOff tailDst tailShift tailInit flushedR4 flushR7))
    (hpc : s.pc = pcAt pc)
    (hsrc_ne : srcReg ≠ .x5 ∧ srcReg ≠ .x6 ∧ srcReg ≠ .x11 ∧ srcReg ≠ .x12 ∧ srcReg ≠ .x25 ∧ srcReg ≠ tailDst)
    (htail_ne : tailDst ≠ .x0 ∧ tailDst ≠ .x6 ∧ tailDst ≠ .x10 ∧ tailDst ≠ .x11 ∧ tailDst ≠ .x12 ∧ tailDst ≠ .x25)
    (htail_ne5 : tailInit = false → tailShift ≠ 0 → tailDst ≠ .x5)
    (hsh_bd : tailShift + 6 ≤ 64)
    (hx11 : s.getReg .x11 = mask40Word)
    (hsrc_reg : s.getReg srcReg = BitVec.ofNat 64 srcBase)
    (hsrc_al : srcBase % 8 = 0)
    (hsrc_bd : srcBase + 32 ≤ 11341403200)
    (hsrc_mem : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (srcBase + 8 * k)) = d.extractLsb' (64 * k) 64)
    (hd_clean : clean → mask238 d = d)
    (hdst_off : dstOff + 32 < 2048)
    (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hw : WriterState clean s r flushedR4 base dstOff written)
    (hpre : TailAccumPre clean s tailDst tailShift tailInit prevVal) :
    ∃ s' : MachineState,
      OpenRuns s (copy29Code r srcReg dstOff tailDst tailShift tailInit flushedR4 flushR7).length
        (copy29Code r srcReg dstOff tailDst tailShift tailInit flushedR4 flushR7).length s' ∧
      s'.pc = pcAt (pc + (copy29Code r srcReg dstOff tailDst tailShift tailInit flushedR4 flushR7).length) ∧
      RegsEqExcept [.x5, .x6, .x10, .x12, tailDst] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' (copy29NextR r) (copy29NextFlushedR4 r flushR7) base (copy29NextDstOff r dstOff)
        (written ++ bitsToBytes d 29) ∧
      TailAccumPost clean s' tailDst tailShift tailInit prevVal (tail6 d).toNat := by
  set d3 : Word := d.extractLsb' 192 64
  have h29_eq : written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8) =
      written ++ bitsToBytes d 29 := by
    rw [List.append_assoc, bitsToBytes_24_append d 5 (by omega)]
  have hbase8 := hw.hbase8
  have hdst8 := hw.hdst8
  have hsrc24_addr : BitVec.ofNat 64 srcBase + signExtend12 (24#12) = BitVec.ofNat 64 (srcBase + 24) := by
    rw [signExtend12_nonneg 24 (by omega), ← BitVec.ofNat_add]
  have hsrc28_addr : BitVec.ofNat 64 srcBase + signExtend12 (28#12) = BitVec.ofNat 64 (srcBase + 28) := by
    rw [signExtend12_nonneg 28 (by omega), ← BitVec.ofNat_add]
  have hsrc24_val8 : accessValid (BitVec.ofNat 64 srcBase + signExtend12 (24#12)) 8 = true := by
    rw [hsrc24_addr]; exact accessValid_ofNat (srcBase + 24) 8 (by omega) (by omega)
  have hsrc24_val4 : accessValid (BitVec.ofNat 64 srcBase + signExtend12 (24#12)) 4 = true := by
    rw [hsrc24_addr]; exact accessValid_ofNat (srcBase + 24) 4 (by omega) (by omega)
  have hsrc28_val1 : accessValid (BitVec.ofNat 64 srcBase + signExtend12 (28#12)) 1 = true := by
    rw [hsrc28_addr]; exact accessValid_ofNat (srcBase + 28) 1 (by omega) (by omega)
  have hdst24_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 24)) =
      BitVec.ofNat 64 (11341403200 + base + (dstOff + 24)) := by
    rw [signExtend12_nonneg (dstOff + 24) (by omega), ← BitVec.ofNat_add]
  have hdst24_val8 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) 8 = true := by
    rw [hdst24_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
  have hdst28_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 28)) =
      BitVec.ofNat 64 (11341403200 + base + dstOff + 28) := by
    rw [signExtend12_nonneg (dstOff + 28) (by omega), ← BitVec.ofNat_add, ← Nat.add_assoc]
  have hdst28_val4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 28))) 4 = true := by
    rw [hdst28_addr]; exact accessValid_ofNat _ 4 (by omega) (by omega)
  have hdst32_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 32)) =
      BitVec.ofNat 64 (11341403200 + base + (dstOff + 32)) := by
    rw [signExtend12_nonneg (dstOff + 32) (by omega), ← BitVec.ofNat_add]
  have hdst32_val4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 32))) 4 = true := by
    rw [hdst32_addr]; exact accessValid_ofNat _ 4 (by omega) (by omega)
  rcases r with ⟨rv, hrv⟩
  have hlen_rv : written.length = base + dstOff + rv := hw.hlen
  have hget29_left : ∀ j (hj : j < (written ++ bitsToBytes d 24).length),
      (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length] at hj ⊢; omega) =
        (written ++ bitsToBytes d 24)[j]'hj := by
    intro j hj
    have h1 : (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length] at hj ⊢; omega) =
        (written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8))[j]'(by rw [h29_eq]; simp [bitsToBytes_length] at hj ⊢; omega) := by
      revert h29_eq; generalize written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8) = lhs; rintro rfl; rfl
    rw [h1, List.getElem_append_left hj]
  have hbyte_tail : ∀ j (hj1 : base + dstOff + 24 + rv ≤ j) (hj2 : j < base + dstOff + 29 + rv),
      (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length]; omega) =
        d3.extractLsb' (8 * (j - (base + dstOff + 24 + rv))) 8 := by
    intro j hj1 hj2
    have hlen24 : (written ++ bitsToBytes d 24).length = base + dstOff + 24 + rv := by
      simp [bitsToBytes_length]; omega
    have h1 : (written ++ bitsToBytes d 29)[j]'(by simp [bitsToBytes_length]; omega) =
        (written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8))[j]'(by rw [h29_eq]; simp [bitsToBytes_length]; omega) := by
      revert h29_eq; generalize written ++ bitsToBytes d 24 ++ (List.range 5).map (fun j => d3.extractLsb' (8 * j) 8) = lhs; rintro rfl; rfl
    rw [h1, List.getElem_append_right (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1; omega
  by_cases hr4 : rv = 4
  · subst hr4
    have hcode_unfold : copy29Code ⟨4, hrv⟩ srcReg dstOff tailDst tailShift tailInit flushedR4 flushR7 =
        (dwordsCode ⟨4, by omega⟩ 3 srcReg 0 dstOff flushedR4 true ++
         [.base (.LWU .x5 srcReg (24#12)),
          .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 28))),
          .base (.LBU .x12 srcReg (28#12))]) ++
        tailExtract4Code tailDst tailShift tailInit srcReg := by
      simp [copy29Code]
    rw [hcode_unfold] at hcode ⊢
    have hcodeA := hcode.left
    have hcodeD := hcodeA.left
    have hcodeM := hcodeA.right
    have hcodeT := hcode.right
    obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_dwords 3 (s := s) (r := ⟨4, by omega⟩)
      (vals := fun k => d.extractLsb' (64 * k) 64)
      (by omega) hcodeD hpc ⟨hsrc_ne.1, hsrc_ne.2.1, hsrc_ne.2.2.2.1, hsrc_ne.2.2.2.2.1⟩
      hsrc_reg (by omega) (by omega) (by omega)
      (fun hcl k hk => by simpa only [Nat.add_zero] using hsrc_mem hcl k (by omega))
      (by omega) (by omega) hw
    rw [(bitsToBytes_take_dwords d 3).symm] at hw1
    set pc1 := pc + (dwordsCode ⟨4, by omega⟩ 3 srcReg 0 dstOff flushedR4 true).length
    have hs1_src : s1.getReg srcReg = BitVec.ofNat 64 srcBase :=
      (hregs1 srcReg (by simp [hsrc_ne.1, hsrc_ne.2.1, hsrc_ne.2.2.2.1])).trans hsrc_reg
    have hs1_d3 : clean → s1.getMem (BitVec.ofNat 64 (srcBase + 24)) = d3 := by
      intro hcl
      have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + 24)).toNat ∧
          (BitVec.ofNat 64 (srcBase + 24)).toNat < 19897793624) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [hp1 _ hnot]
      simpa only [show 8 * 3 = 24 from rfl, show 64 * 3 = 192 from rfl] using hsrc_mem hcl 3 (by omega)
    have hbdM : pc1 + 3 ≤ OPEN_CODE_LEN := by have := hcodeM.1; simpa using this
    have hi0 : openInstr pc1 = .base (.LWU .x5 srcReg (24#12)) := by have h := hcodeM.2 0 (by simp); simpa using h
    have hi1 : openInstr (pc1 + 1) = .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 28))) := by have h := hcodeM.2 1 (by simp); simpa using h
    have hi2 : openInstr (pc1 + 2) = .base (.LBU .x12 srcReg (28#12)) := by have h := hcodeM.2 2 (by simp); simpa using h
    have ha1 := step_LWU (s := s1) (by omega) hpc1 hi0 (by rw [hs1_src]; exact hsrc24_val4)
    set s2 := (s1.setReg .x5 ((s1.getWord32 (s1.getReg srcReg + signExtend12 (24#12))).zeroExtend 64)).setPC (pcAt (pc1 + 1))
    have hs2_x25 : s2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
      simp [s2, getReg_setReg_ne', hw1.rx25]
    have ha2 := step_SW (s := s2) (by omega) rfl hi1 (by rw [hs2_x25]; exact hdst28_val4)
    set s3 := (s2.setWord32 (s2.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 28))) ((s2.getReg .x5).truncate 32)).setPC (pcAt (pc1 + 1 + 1))
    have hs3_src : s3.getReg srcReg = BitVec.ofNat 64 srcBase := by
      simp [s3, s2, getReg_setWord32, getReg_setReg_ne' .x5 srcReg hsrc_ne.1.symm, hs1_src]
    have ha3 := step_LBU (s := s3) (by omega) (by congr 1) hi2 (by rw [hs3_src]; exact hsrc28_val1)
    set s4 := (s3.setReg .x12 ((s3.getByte (s3.getReg srcReg + signExtend12 (28#12))).zeroExtend 64)).setPC (pcAt (pc1 + 2 + 1))
    have hp4 : ProofWritePreserves s s4 := by
      refine hp1.trans ?_
      intro a ha
      simp only [s4, s3, s2, MachineState.getMem_setPC, MachineState.getMem_setReg, hs2_x25, hdst28_addr]
      exact ProofWritePreserves.setWord32_proof (by omega) (by omega) (by omega) a ha
    have hs4_src : s4.getReg srcReg = BitVec.ofNat 64 srcBase := by
      simp [s4, getReg_setReg_ne' .x12 srcReg hsrc_ne.2.2.2.1.symm, hs3_src]
    have hs4_d3 : clean → s4.getMem (BitVec.ofNat 64 (srcBase + 24)) = d3 := by
      intro hcl
      have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + 24)).toNat ∧
          (BitVec.ofNat 64 (srcBase + 24)).toNat < 19897793624) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [hp4 _ hnot]
      simpa only [show 8 * 3 = 24 from rfl, show 64 * 3 = 192 from rfl] using hsrc_mem hcl 3 (by omega)
    have hs4_b29 : clean → s4.getByte (BitVec.ofNat 64 (srcBase + 29)) = d.extractLsb' (8 * 29) 8 := by
      intro hcl
      have hb := getMem_extractByte (s := s4) (addr := srcBase + 24) (j := 5) (by omega) (by omega)
      rw [show srcBase + 24 + 5 = srcBase + 29 by omega, hs4_d3 hcl] at hb
      rw [← hb, show 8 * 5 = 40 from rfl, extractLsb'_extractLsb' d 192 64 40 8 (by omega)]
    have hpre4 : TailAccumPre clean s4 tailDst tailShift tailInit prevVal := by
      intro hcl
      have hp := hpre hcl
      cases tailInit with
      | true => simp
      | false =>
        by_cases hs0 : tailShift = 0
        · simp [hs0]
        · have hb : (tailShift == 0) = false := beq_false_of_ne hs0
          simp only [Bool.false_eq_true, hb, ↓reduceIte] at hp ⊢
          have hne5t : tailDst ≠ .x5 := htail_ne5 rfl hs0
          have htd : s4.getReg tailDst = s.getReg tailDst :=
            (by simp [s4, s3, s2, getReg_setWord32, getReg_setReg_ne' .x12 tailDst htail_ne.2.2.2.2.1.symm,
              getReg_setReg_ne' .x5 tailDst hne5t.symm] : s4.getReg tailDst = s1.getReg tailDst).trans
              (hregs1 tailDst (by simp [hne5t, htail_ne.2.1, htail_ne.2.2.2.2.1]))
          exact ⟨hp.1, htd.trans hp.2⟩
    have hpc4 : s4.pc = pcAt (pc + (dwordsCode ⟨4, by omega⟩ 3 srcReg 0 dstOff flushedR4 true ++
        ([.base (.LWU .x5 srcReg (24#12)), .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 28))),
         .base (.LBU .x12 srcReg (28#12))] : List Instruction)).length) := by
      change pcAt (pc1 + 2 + 1) = _
      simp only [List.length_append, List.length_cons, List.length_nil, pc1, Nat.add_assoc]
    obtain ⟨s5, hr5, hpc5, hregs5, hmem5, hpost5⟩ := openRuns_tailExtract4 hcodeT hpc4 hs4_src hsrc_bd
      hs4_b29 hd_clean hsh_bd htail_ne.1 htail_ne5 hpre4
    have hw4 : WriterState clean s4 (copy29NextR ⟨4, hrv⟩) (copy29NextFlushedR4 ⟨4, hrv⟩ flushR7)
        base (copy29NextDstOff ⟨4, hrv⟩ dstOff) (written ++ bitsToBytes d 29) := by
      refine ⟨hbase8, by simp [copy29NextDstOff]; omega,
        by have := hw.hlen; simp [copy29NextR, copy29NextDstOff, bitsToBytes_length]; omega,
        by simp [copy29NextDstOff]; omega,
        by simp [s4, s3, s2, getReg_setWord32, getReg_setReg_ne', hw1.rx25],
        by simp [copy29NextFlushedR4], fun hcl j hj => ?_, fun hcl => ?_⟩
      · simp only [copy29NextDstOff, show ¬ ((4 : Nat) < 3) by omega, ↓reduceIte] at hj
        have hs2_w32 : (s2.getReg .x5).truncate 32 = d3.truncate 32 := by
          simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
            hs1_src, hsrc24_addr, truncate32_zeroExtend64]
          rw [getWord32_ofNat_align8 s1 (srcBase + 24) (by omega) (by omega), hs1_d3 hcl]
        simp only [s4, s3, getByte_setPC, getByte_setReg, hs2_x25, hdst28_addr, hs2_w32]
        change (s1.setWord32 (BitVec.ofNat 64 (11341403200 + base + dstOff + 28)) (d3.truncate 32)).getByte
            (BitVec.ofNat 64 (11341403200 + j)) = _
        rw [setWord32_getByte_ofNat s1 (11341403200 + base + dstOff + 28) (11341403200 + j)
            (d3.truncate 32) (by omega) (by omega) (by omega)]
        have hlen24_4 : (written ++ bitsToBytes d 24).length = base + dstOff + 28 := by
          have := hw.hlen; simp [bitsToBytes_length]; omega
        by_cases hlt24 : j < base + dstOff + 24
        · rw [dif_neg (by omega), hget29_left j (by omega)]
          exact hw1.hbytes hcl j (by omega)
        · by_cases hlt28 : j < base + dstOff + 28
          · rw [dif_neg (by omega), hget29_left j (by omega)]
            have hrem1 := hw1.hrem hcl
            simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte] at hrem1
            have hq := hrem1 (j - (base + dstOff + 24)) (by omega)
            rw [show 11341403200 + base + (dstOff + 24) + (j - (base + dstOff + 24)) = 11341403200 + j by omega] at hq
            simpa only [show base + (dstOff + 24) + (j - (base + dstOff + 24)) = j by omega] using hq
          · rw [dif_pos (by omega),
              show 11341403200 + j - (11341403200 + base + dstOff + 28) = j - (base + dstOff + 28) by omega,
              truncate32_extract_byte' d3 _ (by omega), hbyte_tail j (by omega) (by omega)]
      · simp only [copy29NextR, copy29NextDstOff, copy29NextFlushedR4, show ¬ ((4 : Nat) < 3) by omega,
          ↓reduceIte, show ¬ (((4 + 5) % 8 : Nat) = 0) by decide]
        have hs3_b28 : s3.getByte (BitVec.ofNat 64 (srcBase + 28)) = d3.extractLsb' (8 * 4) 8 := by
          have hb := getMem_extractByte (s := s3) (addr := srcBase + 24) (j := 4) (by omega) (by omega)
          have hm3 : s3.getMem (BitVec.ofNat 64 (srcBase + 24)) = d3 := by
            have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + 24)).toNat ∧
                (BitVec.ofNat 64 (srcBase + 24)).toNat < 19897793624) := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
            have h := hp4 (BitVec.ofNat 64 (srcBase + 24)) hnot
            simp only [s4, MachineState.getMem_setPC, MachineState.getMem_setReg] at h
            rw [h]; simpa only [show 8 * 3 = 24 from rfl, show 64 * 3 = 192 from rfl] using hsrc_mem hcl 3 (by omega)
          rw [show srcBase + 24 + 4 = srcBase + 28 by omega, hm3] at hb; exact hb.symm
        have hx12 : s4.getReg .x12 = (d3.extractLsb' (8 * 4) 8).zeroExtend 64 := by
          simp [s4, hs3_src, hsrc28_addr, hs3_b28]
        refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · have hj0 : j = 0 := by omega
          subst hj0
          rw [hx12, byte_zeroExtend64_extract _ 0 (by omega), if_pos rfl, hbyte_tail (base + (dstOff + 32) + 0) (by omega) (by omega)]
          congr 1; omega
        · rw [hx12, byte_zeroExtend64_extract _ j hj2, if_neg (by omega)]
    refine ⟨s5, ?_, ?_, ?_, hp4.trans (fun a _ => hmem5 a), ?_, hpost5⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      exact (((hr1.trans ha1).trans ha2).trans ha3).trans hr5
    · rw [hpc5]; simp only [List.length_append, List.length_cons, List.length_nil]; congr 1; omega
    · intro reg hreg
      have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      have hnet : reg ≠ tailDst := fun h => hreg (by simp [h])
      have h54 : s5.getReg reg = s4.getReg reg := hregs5 reg (by simp [hne5, hnet])
      have h41 : s4.getReg reg = s1.getReg reg := by
        simp [s4, s3, s2, getReg_setWord32, getReg_setReg_ne' .x12 reg hne12.symm, getReg_setReg_ne' .x5 reg hne5.symm]
      exact h54.trans (h41.trans (hregs1 reg (by simp [hne5, hne6, hne12])))
    · exact writerState_of_mem_eq hw4 hmem5
        (hregs5 .x25 (by simp [htail_ne.2.2.2.2.2.symm]))
        (hregs5 .x12 (by simp [htail_ne.2.2.2.2.1.symm]))
  · -- rv ≠ 4: dwords 3 + LD x10 srcReg 24 + copy29RemCode + tailExtractOtherCode
    have hbeq4 : (rv == 4) = false := beq_false_of_ne hr4
    have hcode_unfold : copy29Code ⟨rv, hrv⟩ srcReg dstOff tailDst tailShift tailInit flushedR4 flushR7 =
        ((dwordsCode ⟨rv, hrv⟩ 3 srcReg 0 dstOff false false ++ [.base (.LD .x10 srcReg (24#12))]) ++
         copy29RemCode rv dstOff flushR7) ++
        tailExtractOtherCode tailDst tailShift tailInit := by
      simp [copy29Code, hbeq4]
    rw [hcode_unfold] at hcode ⊢
    have hfl_false : flushedR4 = false := by
      cases hf : flushedR4
      · rfl
      · exact absurd (hw.hflushed_ok hf) hr4
    subst hfl_false
    have hcodeT := hcode.right
    have hcodeR := hcode.left.right
    have hcodeL := hcode.left.left.right
    have hcodeD := hcode.left.left.left
    obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_dwords 3 (s := s) (r := ⟨rv, hrv⟩)
      (vals := fun k => d.extractLsb' (64 * k) 64)
      (by omega) hcodeD hpc ⟨hsrc_ne.1, hsrc_ne.2.1, hsrc_ne.2.2.2.1, hsrc_ne.2.2.2.2.1⟩
      hsrc_reg (by omega) (by omega) (by omega)
      (fun hcl k hk => by simpa only [Nat.add_zero] using hsrc_mem hcl k (by omega))
      (by omega) (by omega) hw
    rw [(bitsToBytes_take_dwords d 3).symm] at hw1
    simp only [hbeq4, Bool.false_and] at hw1
    set pc1 := pc + (dwordsCode ⟨rv, hrv⟩ 3 srcReg 0 dstOff false false).length
    have hs1_src : s1.getReg srcReg = BitVec.ofNat 64 srcBase :=
      (hregs1 srcReg (by simp [hsrc_ne.1, hsrc_ne.2.1, hsrc_ne.2.2.2.1])).trans hsrc_reg
    have hs1_d3 : clean → s1.getMem (BitVec.ofNat 64 (srcBase + 24)) = d3 := by
      intro hcl
      have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + 24)).toNat ∧
          (BitVec.ofNat 64 (srcBase + 24)).toNat < 19897793624) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [hp1 _ hnot]
      simpa only [show 8 * 3 = 24 from rfl, show 64 * 3 = 192 from rfl] using hsrc_mem hcl 3 (by omega)
    have hiLD : openInstr pc1 = .base (.LD .x10 srcReg (24#12)) := by
      have h := hcodeL.2 0 (by simp); simpa using h
    have haLD := step_LD (s := s1) (by have := hcodeL.1; simp at this; omega) hpc1 hiLD
      (by rw [hs1_src]; exact hsrc24_val8)
    set s2 := (s1.setReg .x10 (s1.getMem (s1.getReg srcReg + signExtend12 (24#12)))).setPC (pcAt (pc1 + 1))
    have hs2_x10 : clean → s2.getReg .x10 = d3 := fun hcl => by
      simp [s2, hs1_src, hsrc24_addr, hs1_d3 hcl]
    have hs2_x11 : s2.getReg .x11 = mask40Word := by
      simp [s2, getReg_setReg_ne', (hregs1 .x11 (by simp)).trans hx11]
    have hs2_x25 : s2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
      simp [s2, getReg_setReg_ne', hw1.rx25]
    have hs2_x12 : s2.getReg .x12 = s1.getReg .x12 := by simp [s2, getReg_setReg_ne']
    have hs2_mem : ∀ a, s2.getMem a = s1.getMem a := fun a => by simp [s2]
    have hpc2 : s2.pc = pcAt (pc + (dwordsCode ⟨rv, hrv⟩ 3 srcReg 0 dstOff false false ++
        ([.base (.LD .x10 srcReg (24#12))] : List Instruction)).length) := by
      change pcAt (pc1 + 1) = _
      simp only [List.length_append, List.length_singleton, pc1, Nat.add_assoc]
    set pc2 := pc + (dwordsCode ⟨rv, hrv⟩ 3 srcReg 0 dstOff false false ++ ([.base (.LD .x10 srcReg (24#12))] : List Instruction)).length
    have hw2 : WriterState clean s2 ⟨rv, hrv⟩ false base (dstOff + 24) (written ++ bitsToBytes d 24) :=
      writerState_of_mem_eq hw1 hs2_mem (by simp [s2, getReg_setReg_ne']) hs2_x12
    obtain ⟨s3, hr3, hpc3, hregs3, hp3, hw3⟩ := openRuns_copy29_rem hrv hr4 hcodeR hpc2
      hs2_x10 hs2_x11 hdst_off hdst_bd hdst8 hlen_rv hw2
    have hs3_x10 : clean → s3.getReg .x10 = d3 := fun hcl =>
      (hregs3 .x10 (by simp)).trans (hs2_x10 hcl)
    have hpre3 : TailAccumPre clean s3 tailDst tailShift tailInit prevVal := by
      intro hcl
      have hp := hpre hcl
      cases tailInit with
      | true => simp
      | false =>
        by_cases hs0 : tailShift = 0
        · simp [hs0]
        · have hb : (tailShift == 0) = false := beq_false_of_ne hs0
          simp only [Bool.false_eq_true, hb, ↓reduceIte] at hp ⊢
          have hne5t : tailDst ≠ .x5 := htail_ne5 rfl hs0
          have htd : s3.getReg tailDst = s.getReg tailDst :=
            (hregs3 tailDst (by simp [htail_ne.2.1, htail_ne.2.2.2.2.1])).trans
            ((by simp [s2, getReg_setReg_ne' .x10 tailDst htail_ne.2.2.1.symm] : s2.getReg tailDst = s1.getReg tailDst).trans
             (hregs1 tailDst (by simp [hne5t, htail_ne.2.1, htail_ne.2.2.2.2.1])))
          exact ⟨hp.1, htd.trans hp.2⟩
    have hpc3' : s3.pc = pcAt (pc + ((dwordsCode ⟨rv, hrv⟩ 3 srcReg 0 dstOff false false ++
        ([.base (.LD .x10 srcReg (24#12))] : List Instruction)) ++ copy29RemCode rv dstOff flushR7).length) := by
      rw [hpc3]; simp only [List.length_append, pc2]; congr 1; omega
    obtain ⟨s4, hr4', hpc4, hregs4, hmem4, hpost4⟩ := openRuns_tailExtractOther hcodeT hpc3' hs3_x10
      hd_clean hsh_bd htail_ne.1 htail_ne5 hpre3
    have hp2 : ProofWritePreserves s1 s2 := fun a _ => hs2_mem a
    have hp4' : ProofWritePreserves s3 s4 := fun a _ => hmem4 a
    refine ⟨s4, ?_, ?_, ?_, hp1.trans (hp2.trans (hp3.trans hp4')), ?_, hpost4⟩
    · simp only [List.length_append, List.length_singleton]
      exact ((hr1.trans haLD).trans hr3).trans hr4'
    · rw [hpc4]; simp only [List.length_append, List.length_singleton]; congr 1; omega
    · intro reg hreg
      have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne10 : reg ≠ .x10 := fun h => hreg (by simp [h])
      have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
      have hnet : reg ≠ tailDst := fun h => hreg (by simp [h])
      exact (hregs4 reg (by simp [hne5, hnet])).trans
        ((hregs3 reg (by simp [hne6, hne12])).trans
         ((by simp [s2, getReg_setReg_ne' .x10 reg hne10.symm] : s2.getReg reg = s1.getReg reg).trans
          (hregs1 reg (by simp [hne5, hne6, hne12]))))
    · exact writerState_of_mem_eq hw3 hmem4
        (hregs4 .x25 (by simp [htail_ne.2.2.2.2.2.symm]))
        (hregs4 .x12 (by simp [htail_ne.2.2.2.2.1.symm]))

/-! ### 4. Universal 6-Bit Cap-Frontier Tail Push (`tailPush6Code`) -/

def tailPush6Code : List Instruction :=
  [.base (.SLL .x6 .x5 .x17),
   .base (.OR .x16 .x16 .x6),
   .base (.ADDI .x17 .x17 (6#12)),
   .base (.BLT .x17 .x0 (28#13)),
   .base (.SD .x15 .x16 (0#12)),
   .base (.ADDI .x15 .x15 (8#12)),
   .base (.ADDI .x7 .x0 (6#12)),
   .base (.SUB .x7 .x7 .x17),
   .base (.SRL .x16 .x5 .x7),
   .base (.ADDI .x17 .x17 (4032#12))]

/-- Step a single 6-bit tail push from `x5` into `(x15, x16, x17)`: `4` cycles non-flush, `10` flush. -/
theorem openRuns_tailPush6_neg {clean : Prop} {s : MachineState} {pc : Nat}
    {tails : List (BitVec 6)} {t6 : BitVec 6} {flushes : Nat}
    (hcode : CodeAt pc tailPush6Code)
    (hpc : s.pc = pcAt pc)
    (hx5 : clean → s.getReg .x5 = BitVec.ofNat 64 t6.toNat)
    (ht : TailState clean s tails flushes)
    (hbd_next : 8 * (flushes + 1) + 16 ≤ 48719475936) :
    let tCnt := (6 * tails.length) % 64
    let fl : Nat := if tCnt + 6 < 64 then 0 else 1
    let cyc : Nat := 4 + 6 * fl
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt (pc + 10) ∧
      RegsEqExcept [.x6, .x7, .x15, .x16, .x17] s s' ∧
      TailWritePreserves s s' ∧
      TailState clean s' (tails ++ [t6]) (flushes + fl) := by
  set tCnt := (6 * tails.length) % 64
  have htCnt_lt : tCnt < 64 := Nat.mod_lt _ (by omega)
  have hcodeLen : tailPush6Code.length = 10 := rfl
  have hbd : pc + 10 ≤ OPEN_CODE_LEN := by have := hcode.1; rw [hcodeLen] at this; exact this
  have hi0 : openInstr pc = .base (.SLL .x6 .x5 .x17) := by have h := hcode.2 0 (by omega); simpa [tailPush6Code] using h
  have hi1 : openInstr (pc + 1) = .base (.OR .x16 .x16 .x6) := by have h := hcode.2 1 (by omega); simpa [tailPush6Code] using h
  have hi2 : openInstr (pc + 2) = .base (.ADDI .x17 .x17 (6#12)) := by have h := hcode.2 2 (by omega); simpa [tailPush6Code] using h
  have hi3 : openInstr (pc + 3) = .base (.BLT .x17 .x0 (28#13)) := by have h := hcode.2 3 (by omega); simpa [tailPush6Code] using h
  have hi4 : openInstr (pc + 4) = .base (.SD .x15 .x16 (0#12)) := by have h := hcode.2 4 (by omega); simpa [tailPush6Code] using h
  have hi5 : openInstr (pc + 5) = .base (.ADDI .x15 .x15 (8#12)) := by have h := hcode.2 5 (by omega); simpa [tailPush6Code] using h
  have hi6 : openInstr (pc + 6) = .base (.ADDI .x7 .x0 (6#12)) := by have h := hcode.2 6 (by omega); simpa [tailPush6Code] using h
  have hi7 : openInstr (pc + 7) = .base (.SUB .x7 .x7 .x17) := by have h := hcode.2 7 (by omega); simpa [tailPush6Code] using h
  have hi8 : openInstr (pc + 8) = .base (.SRL .x16 .x5 .x7) := by have h := hcode.2 8 (by omega); simpa [tailPush6Code] using h
  have hi9 : openInstr (pc + 9) = .base (.ADDI .x17 .x17 (4032#12)) := by have h := hcode.2 9 (by omega); simpa [tailPush6Code] using h
  have hs1 := step_SLL (by omega) hpc hi0
  set s1 := (s.setReg .x6 (s.getReg .x5 <<< ((s.getReg .x17).toNat % 64))).setPC (pcAt (pc + 1))
  have hs2 := step_OR (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x16 (s1.getReg .x16 ||| s1.getReg .x6)).setPC (pcAt (pc + 1 + 1))
  have hs3 := step_ADDI (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x17 (s2.getReg .x17 + signExtend12 (6#12))).setPC (pcAt (pc + 2 + 1))
  have hrx17 : s.getReg .x17 = negCnt tCnt := ht.rx17
  have hs2_x17 : s2.getReg .x17 = negCnt tCnt := by simp [s2, s1, getReg_setReg_ne', hrx17]
  have ht6_lt : t6.toNat < 64 := t6.isLt
  have hbits_append : 6 * (tails ++ [t6]).length = 64 * flushes + (tCnt + 6) := by
    simp only [List.length_append, List.length_singleton]; have := ht.hbits; omega
  have hbits6_sing : bitsOf6 [t6] = t6.toNat := by simp [bitsOf6]
  by_cases hnf : tCnt + 6 < 64
  · -- Non-flush: BLT taken -> pc + 10 (4 cycles)
    have hs3_x17 : s3.getReg .x17 = negCnt (tCnt + 6) := by
      simp [s3, hs2_x17, show (6#12 : BitVec 12) = BitVec.ofNat 12 6 from rfl, negCnt_add_lt tCnt 6 hnf]
    have hlt_slt : BitVec.slt (s3.getReg .x17) (s3.getReg .x0) = true := by
      rw [hs3_x17, show s3.getReg .x0 = 0#64 from rfl]; exact negCnt_slt_zero _ hnf
    have htgt : pcAt (pc + 3) + signExtend13 (28#13) = pcAt (pc + 10) := by
      simpa only [show 4 * (pc + 10 - (pc + 3)) = 28 by omega] using pcAt_add_pos13 (pc + 3) (pc + 10) (by omega) (by omega)
    have hs4 := step_BLT_taken (s := s3) (by omega) (by congr 1) hi3 hlt_slt htgt
    set s4 := s3.setPC (pcAt (pc + 10))
    simp only [hnf, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    refine ⟨s4, ((hs1.trans hs2).trans hs3).trans hs4, rfl, ?_, TailWritePreserves.refl s, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne16 : reg ≠ .x16 := fun h => hreg (by simp [h])
      have hne17 : reg ≠ .x17 := fun h => hreg (by simp [h])
      simp [s4, s3, s2, s1, getReg_setReg_ne' .x17 reg hne17.symm,
        getReg_setReg_ne' .x16 reg hne16.symm, getReg_setReg_ne' .x6 reg hne6.symm]
    · have hmod : (6 * (tails ++ [t6]).length) % 64 = tCnt + 6 := by
        rw [hbits_append, Nat.mul_add_mod, Nat.mod_eq_of_lt hnf]
      refine ⟨by rw [hmod, hbits_append], ht.hbound,
        by simp [s4, s3, s2, s1, getReg_setReg_ne', ht.rx15],
        by rw [hmod]; exact hs3_x17, fun hcl => ?_⟩
      obtain ⟨tBuf, htBuf_lt, hx16, hsum⟩ := ht.hdata hcl
      have hnew_lt : tBuf + t6.toNat * 2 ^ tCnt < 2 ^ (tCnt + 6) := by
        rw [Nat.pow_add, show (2 : Nat) ^ 6 = 64 by decide]
        have h1 : t6.toNat + 1 ≤ 64 := by omega
        have h2 := Nat.mul_le_mul_right (2 ^ tCnt) h1
        linarith
      have hnew_lt64 : tBuf + t6.toNat * 2 ^ tCnt < 2 ^ 64 := by
        have : 2 ^ (tCnt + 6) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      refine ⟨tBuf + t6.toNat * 2 ^ tCnt, by rw [hmod]; exact hnew_lt, ?_, ?_⟩
      · have hs4_x16 : s4.getReg .x16 = BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 t6.toNat <<< tCnt) := by
          simp [s4, s3, s2, s1, getReg_setReg_ne', hx16, hx5 hcl, hrx17, negCnt_mod64 tCnt htCnt_lt]
        rw [hs4_x16]
        apply BitVec.eq_of_toNat_eq
        rw [word_or_shl_add_low64 tBuf tCnt t6.toNat htCnt_lt htBuf_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
      · have hmem : ∀ j, s4.getByte j = s.getByte j := fun j => by simp [s4, s3, s2, s1, getByte_setPC, getByte_setReg]
        simp only [hmem, bitsOf6_append, hbits6_sing]
        have hpow : 2 ^ (64 * flushes) * 2 ^ tCnt = 2 ^ (6 * tails.length) := by
          rw [← Nat.pow_add, ht.hbits]
        calc
          bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
              2 ^ (64 * flushes) * (tBuf + t6.toNat * 2 ^ tCnt)
            = (bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
                2 ^ (64 * flushes) * tBuf) + (2 ^ (64 * flushes) * 2 ^ tCnt) * t6.toNat := by ring
          _ = bitsOf6 tails + 2 ^ (6 * tails.length) * t6.toNat := by rw [hsum, hpow]
  · -- Flush: BLT not taken -> SD + ADDI x15 + ADDI x7 6 + SUB x7 + SRL x16 + ADDI x17 (-64) (10 cycles)
    have hge64 : 64 ≤ tCnt + 6 := by omega
    have hnew_cnt_lt : tCnt + 6 - 64 < 64 := by omega
    have htCnt_pos : 0 < tCnt := by omega
    have hs3_x17 : s3.getReg .x17 = BitVec.ofNat 64 (tCnt + 6 - 64) := by
      simp [s3, hs2_x17, show (6#12 : BitVec 12) = BitVec.ofNat 12 6 from rfl,
        negCnt_add_ge tCnt 6 htCnt_lt (by omega) hge64]
    have hslt_f : BitVec.slt (s3.getReg .x17) (s3.getReg .x0) = false := by
      rw [hs3_x17, show s3.getReg .x0 = 0#64 from rfl]; exact nonneg_not_slt_zero _ hnew_cnt_lt
    have hs4 := step_BLT_not_taken (s := s3) (by omega) (by congr 1) hi3 hslt_f
    set s4 := s3.setPC (pcAt (pc + 3 + 1))
    have hs4_x15 : s4.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes) := by
      simp [s4, s3, s2, s1, getReg_setReg_ne', ht.rx15]
    have hsd_addr : s4.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + 8 * flushes) := by
      rw [hs4_x15, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsd_valid : accessValid (s4.getReg .x15 + signExtend12 (0#12)) 8 = true := by
      rw [hsd_addr]; have htbb : tailBufBase = 20000000000 := rfl
      exact accessValid_ofNat (tailBufBase + 8 * flushes) 8 (by have := ht.hbound; omega) (by omega)
    have hs5 := step_SD (s := s4) (by omega) (by congr 1) hi4 hsd_valid
    set s5 := (s4.setMem (s4.getReg .x15 + signExtend12 (0#12)) (s4.getReg .x16)).setPC (pcAt (pc + 4 + 1))
    have hs6 := step_ADDI (s := s5) (by omega) (by congr 1) hi5
    set s6 := (s5.setReg .x15 (s5.getReg .x15 + signExtend12 (8#12))).setPC (pcAt (pc + 5 + 1))
    have hs7 := step_ADDI (s := s6) (by omega) (by congr 1) hi6
    set s7 := (s6.setReg .x7 (s6.getReg .x0 + signExtend12 (6#12))).setPC (pcAt (pc + 6 + 1))
    have hs8 := step_SUB (s := s7) (by omega) (by congr 1) hi7
    set s8 := (s7.setReg .x7 (s7.getReg .x7 - s7.getReg .x17)).setPC (pcAt (pc + 7 + 1))
    have hs9 := step_SRL (s := s8) (by omega) (by congr 1) hi8
    set s9 := (s8.setReg .x16 (s8.getReg .x5 >>> ((s8.getReg .x7).toNat % 64))).setPC (pcAt (pc + 8 + 1))
    have hs10 := step_ADDI (s := s9) (by omega) (by congr 1) hi9
    set s10 := (s9.setReg .x17 (s9.getReg .x17 + signExtend12 (4032#12))).setPC (pcAt (pc + 9 + 1))
    simp only [hnf, ↓reduceIte, Nat.mul_one]
    have hmod : (6 * (tails ++ [t6]).length) % 64 = tCnt + 6 - 64 := by
      have h1 : 6 * (tails ++ [t6]).length = 64 * (flushes + 1) + (tCnt + 6 - 64) := by omega
      rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hnew_cnt_lt]
    refine ⟨s10, ((((((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).trans hs7).trans hs8).trans hs9).trans hs10,
      by congr 1, ?_, ?_, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne7 : reg ≠ .x7 := fun h => hreg (by simp [h])
      have hne15 : reg ≠ .x15 := fun h => hreg (by simp [h])
      have hne16 : reg ≠ .x16 := fun h => hreg (by simp [h])
      have hne17 : reg ≠ .x17 := fun h => hreg (by simp [h])
      simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setMem,
        getReg_setReg_ne' .x17 reg hne17.symm, getReg_setReg_ne' .x16 reg hne16.symm,
        getReg_setReg_ne' .x7 reg hne7.symm, getReg_setReg_ne' .x15 reg hne15.symm,
        getReg_setReg_ne' .x6 reg hne6.symm]
    · intro a ha
      simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsd_addr]
      have htbb : tailBufBase = 20000000000 := rfl
      exact TailWritePreserves.setMem_tail (by omega) (by have := ht.hbound; omega) (by omega) a ha
    · have hs10_x15 : s10.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * (flushes + 1)) := by
        simp [s10, s9, s8, s7, s6, s5, getReg_setMem, getReg_setReg_ne', hs4_x15, signExtend12_nonneg 8 (by omega),
          ← BitVec.ofNat_add, show tailBufBase + 8 * flushes + 8 = tailBufBase + 8 * (flushes + 1) by omega]
      have hs10_x17 : s10.getReg .x17 = negCnt (tCnt + 6 - 64) := by
        have h9 : s9.getReg .x17 = BitVec.ofNat 64 (tCnt + 6 - 64) := by
          simp [s9, s8, s7, s6, s5, s4, getReg_setMem, getReg_setReg_ne', hs3_x17]
        rw [show s10.getReg .x17 = s9.getReg .x17 + signExtend12 (BitVec.ofNat 12 (4096 - 64)) by simp [s10], h9]
        exact negCnt_sub64 (tCnt + 6 - 64) hnew_cnt_lt
      refine ⟨by omega, hbd_next, hs10_x15, by rw [hmod]; exact hs10_x17, fun hcl => ?_⟩
      obtain ⟨tBuf, htBuf_lt, hx16, hsum⟩ := ht.hdata hcl
      set newBuf := (tBuf + t6.toNat * 2 ^ tCnt) / 2 ^ 64
      have hnew_lt : newBuf < 2 ^ (tCnt + 6 - 64) := by
        have htot : tBuf + t6.toNat * 2 ^ tCnt < 2 ^ (tCnt + 6) := by
          rw [Nat.pow_add, show (2 : Nat) ^ 6 = 64 by decide]
          have h1 : t6.toNat + 1 ≤ 64 := by omega
          have h2 := Nat.mul_le_mul_right (2 ^ tCnt) h1
          linarith
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), ← Nat.pow_add,
          show tCnt + 6 - 64 + 64 = tCnt + 6 by omega]
        exact htot
      refine ⟨newBuf, by rw [hmod]; exact hnew_lt, ?_, ?_⟩
      · have hs8_x5 : s8.getReg .x5 = BitVec.ofNat 64 t6.toNat := by
          simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setMem, getReg_setReg_ne', hx5 hcl]
        have hs8_x7 : (s8.getReg .x7).toNat % 64 = 64 - tCnt := by
          have h7_7 : s7.getReg .x7 = BitVec.ofNat 64 6 := by
            simp [s7, show s6.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 6 (by omega)]
          have h7_17 : s7.getReg .x17 = BitVec.ofNat 64 (tCnt + 6 - 64) := by
            simp [s7, s6, s5, s4, getReg_setMem, getReg_setReg_ne', hs3_x17]
          have h8_7 : s8.getReg .x7 = BitVec.ofNat 64 (64 - tCnt) := by
            simp only [s8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, h7_7, h7_17]
            rw [bv64_ofNat_sub 6 (tCnt + 6 - 64) (by omega)]; congr 1; omega
          rw [h8_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 64 - tCnt < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 64 - tCnt < 64)]
        have hs10_x16 : s10.getReg .x16 = BitVec.ofNat 64 t6.toNat >>> (64 - tCnt) := by
          simp [s10, s9, getReg_setReg_ne', hs8_x5, hs8_x7]
        rw [hs10_x16]
        apply BitVec.eq_of_toNat_eq
        rw [tail_hi_ushr tBuf tCnt t6.toNat htCnt_lt htBuf_lt (by omega) htCnt_pos,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
            have : 2 ^ (tCnt + 6 - 64) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
            omega)]
      · have hs4_x16 : s4.getReg .x16 = BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 t6.toNat <<< tCnt) := by
          simp [s4, s3, s2, s1, getReg_setReg_ne', hx16, hx5 hcl, hrx17, negCnt_mod64 tCnt htCnt_lt]
        have hlow64 : (s4.getReg .x16).toNat = (tBuf + t6.toNat * 2 ^ tCnt) % 2 ^ 64 := by
          rw [hs4_x16]; exact word_or_shl_add_low64 tBuf tCnt t6.toNat htCnt_lt htBuf_lt (by omega)
        have hmap_eq : ((List.range (8 * (flushes + 1))).map fun j => s10.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
            ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) ++
            bytesOfWord (s4.getReg .x16) := by
          apply List.ext_getElem
          · simp [bytesOfWord_length]; omega
          · intro j hj1 hj2
            simp only [List.length_map, List.length_range] at hj1
            simp only [List.getElem_map, List.getElem_range]
            simp only [s10, s9, s8, s7, s6, s5, getByte_setPC, getByte_setReg, hsd_addr]
            change (s.setMem (BitVec.ofNat 64 (tailBufBase + 8 * flushes)) (s4.getReg .x16)).getByte (BitVec.ofNat 64 (tailBufBase + j)) = _
            have htbb : tailBufBase = 20000000000 := rfl
            by_cases hlt : j < 8 * flushes
            · rw [setMem_getByte_ofNat s (tailBufBase + 8 * flushes) (tailBufBase + j) _ (by omega) (by have := ht.hbound; omega) (by have := ht.hbound; omega) (by omega)]
              rw [List.getElem_append_left (by simp; exact hlt)]; simp
            · have hk : j - 8 * flushes < 8 := by omega
              have heq : tailBufBase + j = (tailBufBase + 8 * flushes) + (j - 8 * flushes) := by omega
              rw [heq, setMem_getByte_inside s (tailBufBase + 8 * flushes) _ _ (by omega) hk]
              rw [List.getElem_append_right (by simp; omega)]
              simp only [List.length_map, List.length_range, bytesOfWord_getElem _ _ hk]
        rw [hmap_eq, bytesToNat_append, List.length_map, List.length_range, bytesOfWord, bytesToNat_word_bytes, hlow64, bitsOf6_append, hbits6_sing]
        have hpow64 : 2 ^ (64 * (flushes + 1)) = 2 ^ (64 * flushes) * 2 ^ 64 := by
          rw [show 64 * (flushes + 1) = 64 * flushes + 64 by omega, Nat.pow_add]
        have hpow_t : 2 ^ (64 * flushes) * 2 ^ tCnt = 2 ^ (6 * tails.length) := by
          rw [← Nat.pow_add, ht.hbits]
        have hdm : (tBuf + t6.toNat * 2 ^ tCnt) % 2 ^ 64 + 2 ^ 64 * newBuf = tBuf + t6.toNat * 2 ^ tCnt := by
          unfold newBuf; omega
        calc
          bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
              2 ^ (8 * (8 * flushes)) * ((tBuf + t6.toNat * 2 ^ tCnt) % 2 ^ 64) +
              2 ^ (64 * (flushes + 1)) * newBuf
            = bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
                2 ^ (64 * flushes) * ((tBuf + t6.toNat * 2 ^ tCnt) % 2 ^ 64 + 2 ^ 64 * newBuf) := by
              rw [show 8 * (8 * flushes) = 64 * flushes by omega, hpow64]; ring
          _ = bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
                2 ^ (64 * flushes) * tBuf + (2 ^ (64 * flushes) * 2 ^ tCnt) * t6.toNat := by
              rw [hdm]; ring
          _ = bitsOf6 tails + 2 ^ (6 * tails.length) * t6.toNat := by rw [hsum, hpow_t]

end CommitGolfCandidate.MoonOpen
