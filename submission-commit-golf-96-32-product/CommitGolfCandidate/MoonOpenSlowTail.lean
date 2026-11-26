import CommitGolfCandidate.MoonOpenSlowExec

/-! Symbolic execution of `slow_tail` (`PC 4802..4917`, `5,592,384 ≤ g ≤ 5,592,405`)
and the unified `openRuns_slow_body` handler (`PC 4488`, combining lazy jump-table init,
`slow_mid`, and `slow_tail`). -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

private theorem slowTbl_get {s : MachineState} (ht : SlowTablesState s true) (r : Fin 8) :
    s.getMem (BitVec.ofNat 64 (1344 + 8 * r.val)) = pcAt (pcCopy29 r) ∧
    s.getMem (BitVec.ofNat 64 (1408 + 8 * r.val)) = pcAt (pcCopy30 r) ∧
    s.getMem (BitVec.ofNat 64 (1472 + 8 * r.val)) = pcAt (pcCopy32 r) ∧
    s.getMem (BitVec.ofNat 64 (1536 + 8 * r.val)) = pcAt (pcRec r) ∧
    s.getMem (BitVec.ofNat 64 (1600 + 8 * r.val)) = pcAt (pcCopy32x3 r) ∧
    s.getMem (BitVec.ofNat 64 (1664 + 8 * r.val)) = pcAt (pcCopy30x4 r) ∧
    s.getMem (BitVec.ofNat 64 (1728 + 8 * r.val)) = pcAt (pcCopy29x2 r) := by
  unfold SlowTablesState at ht; simp only [↓reduceIte] at ht; exact ht r

/-! ### 1. Factored Dynamic Stages of `slow_tail` (`L0`, `L2`, `L4`) -/

/-- `slow_tail` L0 stage (`4809..4823 → 4824`): skips L0 iff `g = 5592405`. -/
private theorem openRuns_slow_tail_l0 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {r0 : Fin 8} {base : Nat} {written : List Byte} {i : Index} {s : MachineState}
    (hg1 : 5592384 ≤ i.val / 3) (hg2 : i.val / 3 ≤ 5592405)
    (hbd_w : base + 72 ≤ 8556390424)
    (hpc : s.pc = pcAt 4809)
    (hx4 : s.getReg .x4 = 1#64)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * (i.val / 3)))
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 (i.val % 3))
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 5592064)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r0.val))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val / 3))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (htbl : SlowTablesState s true)
    (hw : WriterState (CleanTrapdoor trapdoor) s r0 false base 0 written) :
    let g := i.val / 3
    let hasL0 := decide (g ≠ 5592405)
    let l0Bytes := if g = 5592405 then [] else bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32
    let base1 := base + if g = 5592405 then 0 else 64
    ∃ cyc s',
      OpenRuns s cyc cyc s' ∧
      cyc ≤ 2 + (if hasL0 then 6 + 2 + (copy32SubCode r0).length + 1 + 2 + (copy32SubCode r0).length else 0) ∧
      s'.pc = pcAt 4824 ∧
      RegsEqExcept [.x1, .x5, .x6, .x10, .x12, .x19, .x25, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' r0 false base1 0 (written ++ l0Bytes) := by
  set g := i.val / 3
  have hi_lt : i.val < 16777216 := i.isLt
  have h4809 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 4809 = .base (.ADDI .x19 .x13 (341#12)))
  set s1 := (s.setReg .x19 (s.getReg .x13 + signExtend12 (341#12))).setPC (pcAt 4810)
  have hs1_19 : s1.getReg .x19 = BitVec.ofNat 64 5592405 := by
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hx13, signExtend12_nonneg 341 (by omega), ← BitVec.ofNat_add]
  have hs1_22 : s1.getReg .x22 = BitVec.ofNat 64 g := by simp [s1, getReg_setReg_ne', hx22]
  by_cases hg_eq : g = 5592405
  · have hbr : pcAt 4810 + signExtend13 (56#13) = pcAt 4824 := by
      simpa only [show 4 * (4824 - 4810) = 56 by decide] using pcAt_add_pos13 4810 4824 (by decide) (by decide)
    have h4810 := step_BEQ_taken (s := s1) (by decide) rfl (rfl : openInstr 4810 = .base (.BEQ .x22 .x19 (56#13)))
      (by rw [hs1_22, hs1_19, hg_eq]) hbr
    set s2 := s1.setPC (pcAt 4824)
    simp only [hg_eq, ↓reduceIte, Nat.add_zero, List.append_nil]
    refine ⟨2, s2, h4809.trans h4810, by omega, rfl, ?_, fun _ _ => by simp [s2, s1], ?_⟩
    · intro reg hreg; have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
      simp [s2, s1, getReg_setReg_ne' .x19 reg h19'.symm]
    · exact writerState_of_mem_eq hw (fun _ => by simp [s2, s1]) (by simp [s2, s1, getReg_setReg_ne']) (by simp [s2, s1, getReg_setReg_ne'])
  · have hne : s1.getReg .x22 ≠ s1.getReg .x19 := by
      rw [hs1_22, hs1_19]; intro h; have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : g < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 5592405 < 2 ^ 64)] at hn; exact hg_eq hn
    have h4810 := step_BEQ_not_taken (s := s1) (by decide) rfl (rfl : openInstr 4810 = .base (.BEQ .x22 .x19 (56#13))) hne
    set s2 := s1.setPC (pcAt 4811)
    have hl0a_lt : l0Sib1Idx i < levelSize 0 := by unfold l0Sib1Idx; rw [levelSize_0]; split_ifs <;> omega
    have hl0b_lt : l0Sib2Idx i < levelSize 0 := by unfold l0Sib2Idx; rw [levelSize_0]; split_ifs <;> omega
    obtain ⟨cL0, s3, hr3, hcL0, hpc3, hs3_10, hs3_28, hreg3, hmem3⟩ :=
      openRuns_l0_sibs (i := i) (codeAt_of_list_eq 4811 l0SibsCode (by decide) rfl) (rfl : s2.pc = pcAt 4811)
        (by simp [s2, s1, getReg_setReg_ne', hx4]) (by simp [s2, s1, getReg_setReg_ne', hx6, g])
        (by simp [s2, s1, getReg_setReg_ne', hx8]) (by simp [s2, s1, getReg_setReg_ne', hx9])
    have hmem30 : ∀ a, s3.getMem a = s.getMem a := fun a => (hmem3 a).trans (by simp [s2, s1])
    obtain ⟨s3c, hr3c, hpc3c, hs3c_1, hreg3c, hmem3c⟩ :=
      call_ld_jalr (r := r0) (tblOff := 1472) (tgt := pcCopy32 r0)
        (rfl : openInstr 4819 = .base (.LD .x6 .x14 (1472#12)))
        (rfl : openInstr 4820 = .base (.JALR .x1 .x6 (0#12)))
        (by decide) (by omega) (by omega) hpc3
        ((hreg3 .x14 (by simp)).trans (by simp [s2, s1, getReg_setReg_ne', hx14]))
        (by rw [hmem30]; exact (slowTbl_get htbl r0).2.2.1)
    have hmem3c0 : ∀ a, s3c.getMem a = s.getMem a := fun a => (hmem3c a).trans (hmem30 a)
    have hro3c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s3c :=
      fun a ha => (hmem3c0 a).trans (hro a ha)
    have hw3c := writerState_of_mem_eq hw hmem3c0
      ((hreg3c .x25 (by simp)).trans ((hreg3 .x25 (by simp)).trans (by simp [s2, s1, getReg_setReg_ne'])))
      ((hreg3c .x12 (by simp)).trans ((hreg3 .x12 (by simp)).trans (by simp [s2, s1, getReg_setReg_ne'])))
    obtain ⟨s4, hr4, hpc4, hreg4, hp4, hw4⟩ := openRuns_sub_copy32 (r := r0) (retPc := 4821)
      (d := tdNode trapdoor 0 (l0Sib1Idx i)) hpc3c hs3c_1
      ((hreg3c .x10 (by simp)).trans hs3_10)
      (by have h1 := levelBase_align8' 0 (by omega); have h2 := nodeOffset_align8' 0 (l0Sib1Idx i); omega)
      (by have := nodeOffset_lt_treeBytes' 0 _ (by omega) hl0a_lt; omega)
      (fun _ k hk => readOnly_getMem_tdNode hro3c 0 _ k (by omega) hl0a_lt hk)
      (by omega) hw3c
    have h4821 := step_ADDI (s := s4) (by decide) hpc4 (rfl : openInstr 4821 = .base (.ADDI .x10 .x28 (0#12)))
    set s5 := (s4.setReg .x10 (s4.getReg .x28 + signExtend12 (0#12))).setPC (pcAt 4822)
    have hs5_10 : s5.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 0 + nodeOffset 0 (l0Sib2Idx i)) := by
      have h4_28 := (hreg4 .x28 (by simp)).trans ((hreg3c .x28 (by simp)).trans hs3_28)
      simp [s5, h4_28, signExtend12_nonneg 0 (by omega)]
    have hro5 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s5 :=
      fun a ha => (by simp [s5] : s5.getMem a = s4.getMem a).trans (ReadOnlyPreserved.of_proofWrite hro3c hp4 a ha)
    have htbl5 : SlowTablesState s5 true := slowTablesState_of_eq htbl (fun a h1 h2 =>
      (by simp [s5] : s5.getMem a = s4.getMem a).trans ((hp4 a (by omega)).trans (hmem3c0 a)))
    obtain ⟨s5c, hr5c, hpc5c, hs5c_1, hreg5c, hmem5c⟩ :=
      call_ld_jalr (r := r0) (tblOff := 1472) (tgt := pcCopy32 r0)
        (rfl : openInstr 4822 = .base (.LD .x6 .x14 (1472#12)))
        (rfl : openInstr 4823 = .base (.JALR .x1 .x6 (0#12)))
        (by decide) (by omega) (by omega) (rfl : s5.pc = pcAt 4822)
        ((by simp [s5, getReg_setReg_ne'] : s5.getReg .x14 = s4.getReg .x14).trans
          ((hreg4 .x14 (by simp)).trans ((hreg3c .x14 (by simp)).trans ((hreg3 .x14 (by simp)).trans (by simp [s2, s1, getReg_setReg_ne', hx14])))))
        (slowTbl_get htbl5 r0).2.2.1
    have hro5c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s5c :=
      fun a ha => (hmem5c a).trans (hro5 a ha)
    have hw5c := writerState_of_mem_eq hw4 (fun a => (hmem5c a).trans (by simp [s5]))
      ((hreg5c .x25 (by simp)).trans (by simp [s5, getReg_setReg_ne']))
      ((hreg5c .x12 (by simp)).trans (by simp [s5, getReg_setReg_ne']))
    obtain ⟨s6, hr6, hpc6, hreg6, hp6, hw6⟩ := openRuns_sub_copy32 (r := r0) (retPc := 4824)
      (d := tdNode trapdoor 0 (l0Sib2Idx i)) hpc5c hs5c_1
      ((hreg5c .x10 (by simp)).trans hs5_10)
      (by have h1 := levelBase_align8' 0 (by omega); have h2 := nodeOffset_align8' 0 (l0Sib2Idx i); omega)
      (by have := nodeOffset_lt_treeBytes' 0 _ (by omega) hl0b_lt; omega)
      (fun _ k hk => readOnly_getMem_tdNode hro5c 0 _ k (by omega) hl0b_lt hk)
      (by omega) hw5c
    simp only [hg_eq, ↓reduceIte, decide_eq_true (show g ≠ 5592405 from hg_eq)]
    refine ⟨1 + 1 + cL0 + 2 + (copy32SubCode r0).length + 1 + 2 + (copy32SubCode r0).length, s6,
      ((((((h4809.trans h4810).trans hr3).trans hr3c).trans hr4).trans h4821).trans hr5c).trans hr6,
      by omega, hpc6, ?_, ?_, ?_⟩
    · intro reg hreg
      have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
      have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
      have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
      have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
      have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
      have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
      have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
      have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
      exact (hreg6 reg (by simp [h5', h6', h12', h25'])).trans ((hreg5c reg (by simp [h1', h6'])).trans
        ((by simp [s5, getReg_setReg_ne' .x10 reg h10'.symm] : s5.getReg reg = s4.getReg reg).trans
         ((hreg4 reg (by simp [h5', h6', h12', h25'])).trans ((hreg3c reg (by simp [h1', h6'])).trans
          ((hreg3 reg (by simp [h10', h28'])).trans (by simp [s2, s1, getReg_setReg_ne' .x19 reg h19'.symm]))))))
    · exact ProofWritePreserves.trans (fun a _ => hmem3c0 a) <| hp4.trans <| ProofWritePreserves.trans (fun a _ => (hmem5c a).trans (by simp [s5])) hp6
    · simpa only [Nat.add_assoc, List.append_assoc] using hw6

/-- `slow_tail` dynamic L2 stage (`4832..4841 → 4842`). -/
private theorem openRuns_slow_tail_l2 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {r0 : Fin 8} {base idx : Nat} {written : List Byte} {s : MachineState}
    (hidx : idx < 16777216) (hbd_w : base + 40 ≤ 8556390424)
    (hpc : s.pc = pcAt 4832)
    (hx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r0.val))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hbt : BaseTableReady s)
    (htbl : SlowTablesState s true)
    (hw : WriterState (CleanTrapdoor trapdoor) s r0 false base 0 written) :
    let hasL2 := decide ((idx ^^^ 1) < levelSize 2)
    let r2 := if hasL2 then copy30NextR r0 else r0
    let cyc := if hasL2 then 4 + 4 + 2 + (copy30SubCode r0).length else 4
    let addBytes := if (idx ^^^ 1) < levelSize 2 then bitsToBytes (tdNode trapdoor 2 (idx ^^^ 1)) 30 else []
    ∃ base2 s',
      base2 ≤ base + 32 ∧
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt 4842 ∧
      s'.getReg .x14 = BitVec.ofNat 64 (8 * r2.val) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      RegsEqExcept [.x1, .x5, .x6, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' r2 false base2 0 (written ++ addBytes) := by
  have h4832 := step_XORI (s := s) (by decide) hpc (rfl : openInstr 4832 = .base (.XORI .x28 .x22 (1#12)))
  set s1 := (s.setReg .x28 (s.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt 4833)
  have h4833 := step_SRLI (s := s1) (by decide) rfl (rfl : openInstr 4833 = .base (.SRLI .x22 .x22 (1#6)))
  set s2 := (s1.setReg .x22 (s1.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4834)
  have hs2_2 : s2.getReg .x2 = BitVec.ofNat 64 68719475936 := by simp [s2, s1, getReg_setReg_ne', hx2]
  have hsz_addr : s2.getReg .x2 + signExtend12 (72#12) = BitVec.ofNat 64 (68719475936 + 32 * 2 + 8) := by
    rw [hs2_2, signExtend12_nonneg 72 (by omega), ← BitVec.ofNat_add]
  have hsz_val : accessValid (s2.getReg .x2 + signExtend12 (72#12)) 8 = true := by
    rw [hsz_addr]; exact accessValid_ofNat _ 8 (by decide) (by decide)
  have h4834 := step_LD (s := s2) (by decide) rfl (rfl : openInstr 4834 = .base (.LD .x19 .x2 (72#12))) hsz_val
  set s3 := (s2.setReg .x19 (s2.getMem (s2.getReg .x2 + signExtend12 (72#12)))).setPC (pcAt 4835)
  have hs3_28 : s3.getReg .x28 = BitVec.ofNat 64 (idx ^^^ 1) := by
    simp [s3, s2, s1, getReg_setReg_ne', hx22, bv64_xor1 idx (by omega)]
  have hs3_22 : s3.getReg .x22 = BitVec.ofNat 64 (idx / 2) := by
    simp [s3, s2, s1, getReg_setReg_ne', hx22, bv64_ushr idx 1 (by omega), Nat.shiftRight_eq_div_pow]
  have hs3_19 : s3.getReg .x19 = BitVec.ofNat 64 (levelSize 2) := by
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hsz_addr]
    have hm : s2.getMem (BitVec.ofNat 64 (68719475936 + 32 * 2 + 8)) = s.getMem (BitVec.ofNat 64 (68719475936 + 32 * 2 + 8)) := by simp [s2, s1]
    rw [hm]; exact readOnly_getMem_data_size' hro 2 (by omega)
  have hxor_lt : (idx ^^^ 1) < 2 ^ 64 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hsz_lt : levelSize 2 < 2 ^ 64 := by rw [levelSize_2]; omega
  by_cases hlt : (idx ^^^ 1) < levelSize 2
  · have hlt_bv : (s3.getReg .x28).toNat < (s3.getReg .x19).toNat := by
      rw [hs3_28, hs3_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hxor_lt, Nat.mod_eq_of_lt hsz_lt]; exact hlt
    have h4835 := step_BGEU_not_taken (s := s3) (by decide) rfl (rfl : openInstr 4835 = .base (.BGEU .x28 .x19 (28#13))) hlt_bv
    set s4 := s3.setPC (pcAt 4836)
    have h4836 := step_ADD (s := s4) (by decide) rfl (rfl : openInstr 4836 = .base (.ADD .x28 .x28 .x22))
    set s5 := (s4.setReg .x28 (s4.getReg .x28 + s4.getReg .x22)).setPC (pcAt 4837)
    have h4837 := step_SLLI (s := s5) (by decide) rfl (rfl : openInstr 4837 = .base (.SLLI .x28 .x28 (5#6)))
    set s6 := (s5.setReg .x28 (s5.getReg .x28 <<< (5#6).toNat)).setPC (pcAt 4838)
    have hb2_val : accessValid (s6.getReg .x0 + signExtend12 (16#12)) 8 = true := by
      rw [show s6.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega), BitVec.zero_add]
      exact accessValid_ofNat 16 8 (by decide) (by decide)
    have h4838 := step_LD (s := s6) (by decide) rfl (rfl : openInstr 4838 = .base (.LD .x10 .x0 (16#12))) hb2_val
    set s7 := (s6.setReg .x10 (s6.getMem (s6.getReg .x0 + signExtend12 (16#12)))).setPC (pcAt 4839)
    have h4839 := step_ADD (s := s7) (by decide) rfl (rfl : openInstr 4839 = .base (.ADD .x10 .x10 .x28))
    set s8 := (s7.setReg .x10 (s7.getReg .x10 + s7.getReg .x28)).setPC (pcAt 4840)
    have hs8_10 : s8.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 2 + nodeOffset 2 (idx ^^^ 1)) := by
      have h6_28 : s6.getReg .x28 = BitVec.ofNat 64 (nodeOffset 2 (idx ^^^ 1)) := by
        have h5_28 : s5.getReg .x28 = BitVec.ofNat 64 ((idx ^^^ 1) + idx / 2) := by
          simp only [s5, s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq,
            not_false_eq_true, hs3_28, hs3_22, ← BitVec.ofNat_add]
        have hsum : (idx ^^^ 1) + idx / 2 = (idx ^^^ 1) + (idx ^^^ 1) / 2 := by
          have : (idx ^^^ 1) / 2 = idx / 2 := by
            have := @Nat.shiftRight_xor_distrib 1 idx 1
            simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one, show (1 : Nat) / 2 = 0 by decide, Nat.xor_zero] at this
            exact this
          omega
        simp [s6, h5_28, bv64_shl, nodeOffset, gapOffset, hsum]; apply congrArg (BitVec.ofNat 64); omega
      have h7_10 : s7.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 2) := by
        have e : s7.getReg .x10 = s6.getMem (s6.getReg .x0 + signExtend12 (16#12)) := by simp [s7]
        rw [e, show s6.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega), BitVec.zero_add]
        have hm : s6.getMem (BitVec.ofNat 64 16) = s.getMem (BitVec.ofNat 64 16) := by simp [s6, s5, s4, s3, s2, s1]
        rw [hm]; exact hbt.lvlBase 2 (by omega) (by omega)
      simp [s8, h7_10, show s7.getReg .x28 = s6.getReg .x28 by simp [s7, getReg_setReg_ne'], h6_28, ← BitVec.ofNat_add]
    have hmem80 : ∀ a, s8.getMem a = s.getMem a := fun a => by simp [s8, s7, s6, s5, s4, s3, s2, s1]
    obtain ⟨s8c, hr8c, hpc8c, hs8c_1, hreg8c, hmem8c⟩ :=
      call_ld_jalr (r := r0) (tblOff := 1408) (tgt := pcCopy30 r0)
        (rfl : openInstr 4840 = .base (.LD .x6 .x14 (1408#12)))
        (rfl : openInstr 4841 = .base (.JALR .x1 .x6 (0#12)))
        (by decide) (by omega) (by omega) (rfl : s8.pc = pcAt 4840)
        (by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx14])
        (by rw [hmem80]; exact (slowTbl_get htbl r0).2.1)
    have hmem8c0 : ∀ a, s8c.getMem a = s.getMem a := fun a => (hmem8c a).trans (hmem80 a)
    have hro8c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s8c :=
      fun a ha => (hmem8c0 a).trans (hro a ha)
    have hw8c := writerState_of_mem_eq hw hmem8c0
      ((hreg8c .x25 (by simp)).trans (by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
      ((hreg8c .x12 (by simp)).trans (by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
    have hnext_le : copy30NextDstOff r0 0 ≤ 32 := by unfold copy30NextDstOff; split_ifs <;> omega
    obtain ⟨s9, hr9, hpc9, hs9_14, hreg9, hp9, hw9⟩ := openRuns_sub_copy30 (r := r0) (retPc := 4842)
      (d := tdNode trapdoor 2 (idx ^^^ 1)) hpc8c hs8c_1
      ((hreg8c .x10 (by simp)).trans hs8_10)
      (by have h1 := levelBase_align8' 2 (by omega); have h2 := nodeOffset_align8' 2 (idx ^^^ 1); omega)
      (by have := nodeOffset_lt_treeBytes' 2 _ (by omega) hlt; omega)
      (fun _ k hk => readOnly_getMem_tdNode hro8c 2 _ k (by omega) hlt hk)
      (fun hcl => hcl.1 2 (by omega) (by omega) _ hlt)
      (by omega) hw8c
    simp only [hlt, ↓reduceIte, decide_true]
    refine ⟨base + copy30NextDstOff r0 0, s9, by omega,
      ((((((((h4832.trans h4833).trans h4834).trans h4835).trans h4836).trans h4837).trans h4838).trans h4839).trans hr8c).trans hr9,
      hpc9, hs9_14,
      (hreg9 .x22 (by simp)).trans ((hreg8c .x22 (by simp)).trans (by simp [s8, s7, s6, s5, s4, getReg_setReg_ne', hs3_22])),
      ?_, ProofWritePreserves.trans (fun a _ => hmem8c0 a) hp9, hw9⟩
    intro reg hreg
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg9 reg (by simp [h5', h6', h12', h14', h25'])).trans ((hreg8c reg (by simp [h1', h6'])).trans
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne' .x10 reg h10'.symm,
        getReg_setReg_ne' .x28 reg h28'.symm, getReg_setReg_ne' .x19 reg h19'.symm, getReg_setReg_ne' .x22 reg h22'.symm]))
  · have hge_bv : (s3.getReg .x19).toNat ≤ (s3.getReg .x28).toNat := by
      rw [hs3_28, hs3_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hxor_lt, Nat.mod_eq_of_lt hsz_lt]; omega
    have hbr : pcAt 4835 + signExtend13 (28#13) = pcAt 4842 := by
      simpa only [show 4 * (4842 - 4835) = 28 by decide] using pcAt_add_pos13 4835 4842 (by decide) (by decide)
    have h4835 := step_BGEU_taken (s := s3) (by decide) rfl (rfl : openInstr 4835 = .base (.BGEU .x28 .x19 (28#13))) hge_bv hbr
    set s4 := s3.setPC (pcAt 4842)
    simp only [hlt, ↓reduceIte, decide_false, List.append_nil]
    refine ⟨base, s4, by omega, ((h4832.trans h4833).trans h4834).trans h4835, rfl,
      by simp [s4, s3, s2, s1, getReg_setReg_ne', hx14], by simpa [s4] using hs3_22,
      ?_, fun _ _ => by simp [s4, s3, s2, s1],
      writerState_of_mem_eq hw (fun _ => by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2, s1, getReg_setReg_ne']) (by simp [s4, s3, s2, s1, getReg_setReg_ne'])⟩
    intro reg hreg
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    simp [s4, s3, s2, s1, getReg_setReg_ne' .x19 reg h19'.symm, getReg_setReg_ne' .x22 reg h22'.symm, getReg_setReg_ne' .x28 reg h28'.symm]

/-- `slow_tail` dynamic L4 stage (`4850..4858 → 4859`). -/
private theorem openRuns_slow_tail_l4 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {r3 : Fin 8} {base idx : Nat} {written : List Byte} {s : MachineState}
    (hidx : idx < 16777216) (hbd_w : base + 40 ≤ 8556390424)
    (hpc : s.pc = pcAt 4850)
    (hx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r3.val))
    (hx21 : s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (htbl : SlowTablesState s true)
    (hw : WriterState (CleanTrapdoor trapdoor) s r3 false base 0 written) :
    let hasL4 := decide ((idx ^^^ 1) < levelSize 4)
    let r4 := if hasL4 then copy30NextR r3 else r3
    let cyc := if hasL4 then 4 + 3 + 2 + (copy30SubCode r3).length else 4
    let addBytes := if (idx ^^^ 1) < levelSize 4 then bitsToBytes (tdNode trapdoor 4 (idx ^^^ 1)) 30 else []
    ∃ base4 s',
      base4 ≤ base + 32 ∧
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt 4859 ∧
      s'.getReg .x14 = BitVec.ofNat 64 (8 * r4.val) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      RegsEqExcept [.x1, .x5, .x6, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' r4 false base4 0 (written ++ addBytes) := by
  have h4850 := step_XORI (s := s) (by decide) hpc (rfl : openInstr 4850 = .base (.XORI .x28 .x22 (1#12)))
  set s1 := (s.setReg .x28 (s.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt 4851)
  have h4851 := step_SRLI (s := s1) (by decide) rfl (rfl : openInstr 4851 = .base (.SRLI .x22 .x22 (1#6)))
  set s2 := (s1.setReg .x22 (s1.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4852)
  have hs2_2 : s2.getReg .x2 = BitVec.ofNat 64 68719475936 := by simp [s2, s1, getReg_setReg_ne', hx2]
  have hsz_addr : s2.getReg .x2 + signExtend12 (136#12) = BitVec.ofNat 64 (68719475936 + 32 * 4 + 8) := by
    rw [hs2_2, signExtend12_nonneg 136 (by omega), ← BitVec.ofNat_add]
  have hsz_val : accessValid (s2.getReg .x2 + signExtend12 (136#12)) 8 = true := by
    rw [hsz_addr]; exact accessValid_ofNat _ 8 (by decide) (by decide)
  have h4852 := step_LD (s := s2) (by decide) rfl (rfl : openInstr 4852 = .base (.LD .x19 .x2 (136#12))) hsz_val
  set s3 := (s2.setReg .x19 (s2.getMem (s2.getReg .x2 + signExtend12 (136#12)))).setPC (pcAt 4853)
  have hs3_28 : s3.getReg .x28 = BitVec.ofNat 64 (idx ^^^ 1) := by
    simp [s3, s2, s1, getReg_setReg_ne', hx22, bv64_xor1 idx (by omega)]
  have hs3_22 : s3.getReg .x22 = BitVec.ofNat 64 (idx / 2) := by
    simp [s3, s2, s1, getReg_setReg_ne', hx22, bv64_ushr idx 1 (by omega), Nat.shiftRight_eq_div_pow]
  have hs3_19 : s3.getReg .x19 = BitVec.ofNat 64 (levelSize 4) := by
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hsz_addr]
    have hm : s2.getMem (BitVec.ofNat 64 (68719475936 + 32 * 4 + 8)) = s.getMem (BitVec.ofNat 64 (68719475936 + 32 * 4 + 8)) := by simp [s2, s1]
    rw [hm]; exact readOnly_getMem_data_size' hro 4 (by omega)
  have hxor_lt : (idx ^^^ 1) < 2 ^ 64 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hsz4 : levelSize 4 = 699051 := by decide
  have hsz_lt : levelSize 4 < 2 ^ 64 := by omega
  by_cases hlt : (idx ^^^ 1) < levelSize 4
  · have hlt_bv : (s3.getReg .x28).toNat < (s3.getReg .x19).toNat := by
      rw [hs3_28, hs3_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hxor_lt, Nat.mod_eq_of_lt hsz_lt]; exact hlt
    have h4853 := step_BGEU_not_taken (s := s3) (by decide) rfl (rfl : openInstr 4853 = .base (.BGEU .x28 .x19 (24#13))) hlt_bv
    set s4 := s3.setPC (pcAt 4854)
    have h4854 := step_ADD (s := s4) (by decide) rfl (rfl : openInstr 4854 = .base (.ADD .x28 .x28 .x22))
    set s5 := (s4.setReg .x28 (s4.getReg .x28 + s4.getReg .x22)).setPC (pcAt 4855)
    have h4855 := step_SLLI (s := s5) (by decide) rfl (rfl : openInstr 4855 = .base (.SLLI .x28 .x28 (5#6)))
    set s6 := (s5.setReg .x28 (s5.getReg .x28 <<< (5#6).toNat)).setPC (pcAt 4856)
    have h4856 := step_ADD (s := s6) (by decide) rfl (rfl : openInstr 4856 = .base (.ADD .x10 .x21 .x28))
    set s7 := (s6.setReg .x10 (s6.getReg .x21 + s6.getReg .x28)).setPC (pcAt 4857)
    have hs7_10 : s7.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 4 + nodeOffset 4 (idx ^^^ 1)) := by
      have h6_28 : s6.getReg .x28 = BitVec.ofNat 64 (nodeOffset 4 (idx ^^^ 1)) := by
        have h5_28 : s5.getReg .x28 = BitVec.ofNat 64 ((idx ^^^ 1) + idx / 2) := by
          simp only [s5, s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq,
            not_false_eq_true, hs3_28, hs3_22, ← BitVec.ofNat_add]
        have hsum : (idx ^^^ 1) + idx / 2 = (idx ^^^ 1) + (idx ^^^ 1) / 2 := by
          have : (idx ^^^ 1) / 2 = idx / 2 := by
            have := @Nat.shiftRight_xor_distrib 1 idx 1
            simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one, show (1 : Nat) / 2 = 0 by decide, Nat.xor_zero] at this
            exact this
          omega
        simp [s6, h5_28, bv64_shl, nodeOffset, gapOffset, hsum]; apply congrArg (BitVec.ofNat 64); omega
      have h6_21 : s6.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4) := by
        simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx21]
      simp [s7, h6_21, h6_28, ← BitVec.ofNat_add]
    have hmem70 : ∀ a, s7.getMem a = s.getMem a := fun a => by simp [s7, s6, s5, s4, s3, s2, s1]
    obtain ⟨s7c, hr7c, hpc7c, hs7c_1, hreg7c, hmem7c⟩ :=
      call_ld_jalr (r := r3) (tblOff := 1408) (tgt := pcCopy30 r3)
        (rfl : openInstr 4857 = .base (.LD .x6 .x14 (1408#12)))
        (rfl : openInstr 4858 = .base (.JALR .x1 .x6 (0#12)))
        (by decide) (by omega) (by omega) (rfl : s7.pc = pcAt 4857)
        (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx14])
        (by rw [hmem70]; exact (slowTbl_get htbl r3).2.1)
    have hmem7c0 : ∀ a, s7c.getMem a = s.getMem a := fun a => (hmem7c a).trans (hmem70 a)
    have hro7c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7c :=
      fun a ha => (hmem7c0 a).trans (hro a ha)
    have hw7c := writerState_of_mem_eq hw hmem7c0
      ((hreg7c .x25 (by simp)).trans (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
      ((hreg7c .x12 (by simp)).trans (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
    have hnext_le : copy30NextDstOff r3 0 ≤ 32 := by unfold copy30NextDstOff; split_ifs <;> omega
    obtain ⟨s8, hr8, hpc8, hs8_14, hreg8, hp8, hw8⟩ := openRuns_sub_copy30 (r := r3) (retPc := 4859)
      (d := tdNode trapdoor 4 (idx ^^^ 1)) hpc7c hs7c_1
      ((hreg7c .x10 (by simp)).trans hs7_10)
      (by have h1 := levelBase_align8' 4 (by omega); have h2 := nodeOffset_align8' 4 (idx ^^^ 1); omega)
      (by have := nodeOffset_lt_treeBytes' 4 _ (by omega) hlt; omega)
      (fun _ k hk => readOnly_getMem_tdNode hro7c 4 _ k (by omega) hlt hk)
      (fun hcl => hcl.1 4 (by omega) (by omega) _ hlt)
      (by omega) hw7c
    simp only [hlt, ↓reduceIte, decide_true]
    refine ⟨base + copy30NextDstOff r3 0, s8, by omega,
      (((((((h4850.trans h4851).trans h4852).trans h4853).trans h4854).trans h4855).trans h4856).trans hr7c).trans hr8,
      hpc8, hs8_14,
      (hreg8 .x22 (by simp)).trans ((hreg7c .x22 (by simp)).trans (by simp [s7, s6, s5, s4, getReg_setReg_ne', hs3_22])),
      ?_, ProofWritePreserves.trans (fun a _ => hmem7c0 a) hp8, hw8⟩
    intro reg hreg
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg8 reg (by simp [h5', h6', h12', h14', h25'])).trans ((hreg7c reg (by simp [h1', h6'])).trans
      (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne' .x10 reg h10'.symm,
        getReg_setReg_ne' .x28 reg h28'.symm, getReg_setReg_ne' .x19 reg h19'.symm, getReg_setReg_ne' .x22 reg h22'.symm]))
  · have hge_bv : (s3.getReg .x19).toNat ≤ (s3.getReg .x28).toNat := by
      rw [hs3_28, hs3_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hxor_lt, Nat.mod_eq_of_lt hsz_lt]; omega
    have hbr : pcAt 4853 + signExtend13 (24#13) = pcAt 4859 := by
      simpa only [show 4 * (4859 - 4853) = 24 by decide] using pcAt_add_pos13 4853 4859 (by decide) (by decide)
    have h4853 := step_BGEU_taken (s := s3) (by decide) rfl (rfl : openInstr 4853 = .base (.BGEU .x28 .x19 (24#13))) hge_bv hbr
    set s4 := s3.setPC (pcAt 4859)
    simp only [hlt, ↓reduceIte, decide_false, List.append_nil]
    refine ⟨base, s4, by omega, ((h4850.trans h4851).trans h4852).trans h4853, rfl,
      by simp [s4, s3, s2, s1, getReg_setReg_ne', hx14], by simpa [s4] using hs3_22,
      ?_, fun _ _ => by simp [s4, s3, s2, s1],
      writerState_of_mem_eq hw (fun _ => by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2, s1, getReg_setReg_ne']) (by simp [s4, s3, s2, s1, getReg_setReg_ne'])⟩
    intro reg hreg
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    simp [s4, s3, s2, s1, getReg_setReg_ne' .x19 reg h19'.symm, getReg_setReg_ne' .x22 reg h22'.symm, getReg_setReg_ne' .x28 reg h28'.symm]

/-! ### 2. Full `slow_tail` Execution (`PC 4802 → rec_r{rEnd}` or `cap_pass`) -/

/-- Execute `slow_tail` (`4802..4917`) for `5,592,384 ≤ g ≤ 5,592,405`. -/
theorem openRuns_slow_tail {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg1 : 5592384 ≤ ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)
    (hpc : s.pc = pcAt 4802)
    (hinv : SlowEntryInv trapdoor positions ordinal r0 base written tails flushes true
              ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) (s.setPC (pcAt PC_slow_body))) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    ∃ cycNf rEnd baseEnd s',
      OpenRuns s (cycNf + 4 * fl) (cycNf + 4 * fl) s' ∧
      8 * (slowEntryCyc r0 + 4 + cycNf) + phi8 rEnd ≤ 3453 + phi8 r0 ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) true s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hi_lt : i.val < 16777216 := i.isLt
  have hg2 : g ≤ 5592405 := by omega
  have hst := level_sib_of_slow_tail g hg1 hg2
  have hl1_lt : (g ^^^ 1) < levelSize 1 := by rw [levelSize_1]; exact xor_one_lt_even (m := 2796203) (by omega)
  have hrec_eq := record_slow_tail_eq (tdNode trapdoor) (tdSalt trapdoor) i hg1 hg2
  have hrx3 : s.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11) := hinv.rx3
  have hrx4 : s.getReg .x4 = 1#64 := hinv.rx4
  have hrx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * g) := hinv.rx6
  have hrx7 : s.getReg .x7 = BitVec.ofNat 64 (4294971424 + levelBase 10) := hinv.rx7
  have hrx8 : s.getReg .x8 = BitVec.ofNat 64 (i.val % 3) := hinv.rx8
  have hrx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424 := hinv.rx9
  have hrx11 : s.getReg .x11 = mask40Word := hinv.rx11
  have hrx13 : s.getReg .x13 = BitVec.ofNat 64 5592064 := hinv.rx13
  have hrx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r0.val) := hinv.rx14
  have hrx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952) := hinv.rx18
  have hrx20 : s.getReg .x20 = BitVec.ofNat 64 3 := hinv.rx20
  have hrx21 : s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4) := hinv.rx21
  have hrx22 : s.getReg .x22 = BitVec.ofNat 64 g := hinv.rx22
  have hrx23 : s.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9) := hinv.rx23
  have hrx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ordinal) := hinv.rx24
  have hrx26 : s.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5) := hinv.rx26
  have hrx27 : s.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card) := hinv.rx27
  have hrx29 : s.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6) := hinv.rx29
  have hrx30 : s.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7) := hinv.rx30
  have hrx31 : s.getReg .x31 = BitVec.ofNat 64 (4294971424 + levelBase 8) := hinv.rx31
  have hro0 := hinv.hro
  have hbt0 : BaseTableReady s := baseTableReady_of_lowEq hinv.hbt (fun _ _ => rfl)
  have hcm0 : CapMarks15State s positions ordinal := capMarks15State_of_lowEq hinv.hcm (fun _ _ _ => rfl)
  have htbl0 : SlowTablesState s true := slowTablesState_of_eq hinv.htbl (fun _ _ _ => rfl)
  have hw0 : WriterState (CleanTrapdoor trapdoor) s r0 false (base + 24) 0
      (written ++ bitsToBytes (tdSalt trapdoor i) 24) := writerState_of_mem_eq hinv.hw (fun _ => rfl) rfl rfl
  have ht0 : TailState (CleanTrapdoor trapdoor) s tails flushes := TailState.of_proofWrite hinv.ht (fun _ _ => rfl) rfl rfl rfl
  -- 1. Load OPENING_DATABASE into x2 (7 cyc, 4802 -> 4809)
  obtain ⟨s0, hr0, hpc0, hs0_2, hreg0, hmem0⟩ := openRuns_load_opening_db hpc
  have hro_s0 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s0 :=
    fun a ha => (hmem0 a).trans (hro0 a ha)
  have htbl_s0 : SlowTablesState s0 true := slowTablesState_of_eq htbl0 (fun a _ _ => hmem0 a)
  have hw_s0 := writerState_of_mem_eq hw0 hmem0 (hreg0 .x25 (by simp)) (hreg0 .x12 (by simp))
  -- 2. L0 (4809..4823 -> 4824)
  obtain ⟨cL0, s1, hr1, hcL0, hpc1, hreg1, hp1, hw1⟩ := openRuns_slow_tail_l0 hg1 hg2 (by omega) hpc0
    ((hreg0 .x4 (by simp)).trans hrx4) ((hreg0 .x6 (by simp)).trans hrx6)
    ((hreg0 .x8 (by simp)).trans hrx8) ((hreg0 .x9 (by simp)).trans hrx9)
    ((hreg0 .x13 (by simp)).trans hrx13) ((hreg0 .x14 (by simp)).trans hrx14)
    ((hreg0 .x22 (by simp)).trans hrx22) hro_s0 htbl_s0 hw_s0
  set base1 := base + 24 + if g = 5592405 then 0 else 64
  have hbase1_le : base1 ≤ base + 88 := by unfold base1; split_ifs <;> omega
  have hro1 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s1 :=
    ReadOnlyPreserved.of_proofWrite hro_s0 hp1
  have hbt1 : BaseTableReady s1 := baseTableReady_of_lowEq hbt0 (fun a ha => (hp1 a (by omega)).trans (hmem0 a))
  have htbl1 : SlowTablesState s1 true := slowTablesState_of_eq htbl0 (fun a _ _ => (hp1 a (by omega)).trans (hmem0 a))
  have hreg10 : RegsEqExcept [.x1, .x2, .x5, .x6, .x10, .x12, .x19, .x25, .x28] s s1 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h2' : reg ≠ .x2 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg1 reg (by simp [h1', h5', h6', h10', h12', h19', h25', h28'])).trans (hreg0 reg (by simp [h2']))
  -- 3. L1 (4824..4831 -> 4832)
  obtain ⟨s2a, hr2a, hpc2a, hs2a_22, hs2a_10, hreg2a, hmem2a⟩ :=
    openRuns_lvl_addr_mem (codeAt_of_list_eq 4824 (lvlAddrMemCode .x10 1) (by decide) rfl)
      hpc1 (by omega) (by omega) (by omega) (by decide) ((hreg10 .x22 (by simp)).trans hrx22) hbt1
  obtain ⟨s2c, hr2c, hpc2c, hs2c_1, hreg2c, hmem2c⟩ :=
    call_ld_jalr (r := r0) (tblOff := 1472) (tgt := pcCopy32 r0)
      (rfl : openInstr 4830 = .base (.LD .x6 .x14 (1472#12)))
      (rfl : openInstr 4831 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc2a
      ((hreg2a .x14 (by simp)).trans ((hreg10 .x14 (by simp)).trans hrx14))
      (by rw [hmem2a]; exact (slowTbl_get htbl1 r0).2.2.1)
  have hmem2c1 : ∀ a, s2c.getMem a = s1.getMem a := fun a => (hmem2c a).trans (hmem2a a)
  have hro2c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s2c :=
    fun a ha => (hmem2c1 a).trans (hro1 a ha)
  have hw2c := writerState_of_mem_eq hw1 hmem2c1
    ((hreg2c .x25 (by simp)).trans (hreg2a .x25 (by simp)))
    ((hreg2c .x12 (by simp)).trans (hreg2a .x12 (by simp)))
  obtain ⟨s2, hr2, hpc2, hreg2, hp2, hw2⟩ := openRuns_sub_copy32 (r := r0) (retPc := 4832)
    (d := tdNode trapdoor 1 (g ^^^ 1)) hpc2c hs2c_1
    ((hreg2c .x10 (by simp)).trans hs2a_10)
    (by have h1 := levelBase_align8' 1 (by omega); have h2 := nodeOffset_align8' 1 (g ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 1 _ (by omega) hl1_lt; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro2c 1 _ k (by omega) hl1_lt hk)
    (by omega) hw2c
  have hp2_s0 : ProofWritePreserves s0 s2 := hp1.trans <| ProofWritePreserves.trans (fun a _ => hmem2c1 a) hp2
  have hro2 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s2 :=
    ReadOnlyPreserved.of_proofWrite hro2c hp2
  have hbt2 : BaseTableReady s2 := baseTableReady_of_lowEq hbt1 (fun a ha => (hp2 a (by omega)).trans (hmem2c1 a))
  have htbl2 : SlowTablesState s2 true := slowTablesState_of_eq htbl1 (fun a _ _ => (hp2 a (by omega)).trans (hmem2c1 a))
  have hs2_22 : s2.getReg .x22 = BitVec.ofNat 64 (g >>> 1) := by
    have h := (hreg2 .x22 (by simp)).trans ((hreg2c .x22 (by simp)).trans hs2a_22)
    simpa only [show g / 2 = g >>> 1 by simp [Nat.shiftRight_eq_div_pow]] using h
  have hs2_2 : s2.getReg .x2 = BitVec.ofNat 64 68719475936 :=
    (hreg2 .x2 (by simp)).trans ((hreg2c .x2 (by simp)).trans ((hreg2a .x2 (by simp)).trans ((hreg1 .x2 (by simp)).trans hs0_2)))
  have hreg20 : RegsEqExcept [.x1, .x2, .x5, .x6, .x10, .x12, .x19, .x22, .x25, .x28] s s2 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h2' : reg ≠ .x2 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg2 reg (by simp [h5', h6', h12', h25'])).trans ((hreg2c reg (by simp [h1', h6'])).trans
      ((hreg2a reg (by simp [h10', h22', h28'])).trans (hreg10 reg (by simp [h1', h2', h5', h6', h10', h12', h19', h25', h28']))))
  -- 4. L2 (dynamic, 4832..4841 -> 4842)
  set hasL2 : Bool := decide (((g >>> 1) ^^^ 1) < levelSize 2)
  set r2 : Fin 8 := if hasL2 then copy30NextR r0 else r0
  obtain ⟨base2, s3, hbase2_le, hr3, hpc3, hs3_14, hs3_22, hreg3, hp3, hw3⟩ :=
    openRuns_slow_tail_l2 (by simp [Nat.shiftRight_eq_div_pow]; omega) (by omega)
      hpc2 hs2_2 ((hreg20 .x14 (by simp)).trans hrx14) hs2_22 hro2 hbt2 htbl2 hw2
  rw [div2_ushr_eq g 1 2] at hs3_22
  have hro3 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s3 :=
    ReadOnlyPreserved.of_proofWrite hro2 hp3
  have hbt3 : BaseTableReady s3 := baseTableReady_of_lowEq hbt2 (fun a ha => hp3 a (by omega))
  have htbl3 : SlowTablesState s3 true := slowTablesState_of_eq htbl2 (fun a _ _ => hp3 a (by omega))
  -- 5. L3 (4842..4849 -> 4850)
  obtain ⟨s4a, hr4a, hpc4a, hs4a_22, hs4a_10, hreg4a, hmem4a⟩ :=
    openRuns_lvl_addr_mem (codeAt_of_list_eq 4842 (lvlAddrMemCode .x10 3) (by decide) rfl)
      hpc3 (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) hs3_22 hbt3
  rw [div2_ushr_eq g 2 3] at hs4a_22
  obtain ⟨s4c, hr4c, hpc4c, hs4c_1, hreg4c, hmem4c⟩ :=
    call_ld_jalr (r := r2) (tblOff := 1408) (tgt := pcCopy30 r2)
      (rfl : openInstr 4848 = .base (.LD .x6 .x14 (1408#12)))
      (rfl : openInstr 4849 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc4a
      ((hreg4a .x14 (by simp)).trans hs3_14)
      (by rw [hmem4a]; exact (slowTbl_get htbl3 r2).2.1)
  have hmem4c3 : ∀ a, s4c.getMem a = s3.getMem a := fun a => (hmem4c a).trans (hmem4a a)
  have hro4c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s4c :=
    fun a ha => (hmem4c3 a).trans (hro3 a ha)
  have hw4c := writerState_of_mem_eq hw3 hmem4c3
    ((hreg4c .x25 (by simp)).trans (hreg4a .x25 (by simp)))
    ((hreg4c .x12 (by simp)).trans (hreg4a .x12 (by simp)))
  set r3 : Fin 8 := copy30NextR r2
  have hd_r2 : copy30NextDstOff r2 0 ≤ 32 := by unfold copy30NextDstOff; split_ifs <;> omega
  obtain ⟨s4, hr4, hpc4, hs4_14, hreg4, hp4, hw4⟩ := openRuns_sub_copy30 (r := r2) (retPc := 4850)
    (d := tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) hpc4c hs4c_1
    ((hreg4c .x10 (by simp)).trans hs4a_10)
    (by have h1 := levelBase_align8' 3 (by omega); have h2 := nodeOffset_align8' 3 ((g >>> 2) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 3 _ (by omega) hst.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro4c 3 _ k (by omega) hst.1 hk)
    (fun hcl => hcl.1 3 (by omega) (by omega) _ hst.1)
    (by omega) hw4c
  have hro4 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s4 :=
    ReadOnlyPreserved.of_proofWrite hro4c hp4
  have hbt4 : BaseTableReady s4 := baseTableReady_of_lowEq hbt3 (fun a ha => (hp4 a (by omega)).trans (hmem4c3 a))
  have htbl4 : SlowTablesState s4 true := slowTablesState_of_eq htbl3 (fun a _ _ => (hp4 a (by omega)).trans (hmem4c3 a))
  have hreg40 : RegsEqExcept [.x1, .x2, .x5, .x6, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s4 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h2' : reg ≠ .x2 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg4 reg (by simp [h5', h6', h12', h14', h25'])).trans ((hreg4c reg (by simp [h1', h6'])).trans
      ((hreg4a reg (by simp [h10', h22', h28'])).trans
       ((hreg3 reg (by simp [h1', h5', h6', h10', h12', h14', h19', h22', h25', h28'])).trans
        (hreg20 reg (by simp [h1', h2', h5', h6', h10', h12', h19', h22', h25', h28'])))))
  -- 6. L4 (dynamic, 4850..4858 -> 4859)
  set hasL4 : Bool := decide (((g >>> 3) ^^^ 1) < levelSize 4)
  set r4 : Fin 8 := if hasL4 then copy30NextR r3 else r3
  obtain ⟨base4, s5, hbase4_le, hr5, hpc5, hs5_14, hs5_22, hreg5, hp5, hw5⟩ :=
    openRuns_slow_tail_l4 (by simp [Nat.shiftRight_eq_div_pow]; omega) (by omega) hpc4
      ((hreg4 .x2 (by simp)).trans ((hreg4c .x2 (by simp)).trans ((hreg4a .x2 (by simp)).trans ((hreg3 .x2 (by simp)).trans hs2_2))))
      hs4_14 ((hreg40 .x21 (by simp)).trans hrx21)
      ((hreg4 .x22 (by simp)).trans ((hreg4c .x22 (by simp)).trans hs4a_22))
      hro4 htbl4 hw4
  rw [div2_ushr_eq g 3 4] at hs5_22
  have hro5 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s5 :=
    ReadOnlyPreserved.of_proofWrite hro4 hp5
  have hbt5 : BaseTableReady s5 := baseTableReady_of_lowEq hbt4 (fun a ha => hp5 a (by omega))
  have htbl5 : SlowTablesState s5 true := slowTablesState_of_eq htbl4 (fun a _ _ => hp5 a (by omega))
  -- 7. L5 (4859..4865 -> 4866)
  obtain ⟨s6a, hr6a, hpc6a, hs6a_22, hs6a_10, hreg6a, hmem6a⟩ :=
    openRuns_lvl_addr_reg (codeAt_of_list_eq 4859 (lvlAddrRegCode .x10 .x26) (by decide) rfl)
      hpc5 (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs5_22 ((hreg5 .x26 (by simp)).trans ((hreg40 .x26 (by simp)).trans hrx26))
  rw [div2_ushr_eq g 4 5] at hs6a_22
  obtain ⟨s6c, hr6c, hpc6c, hs6c_1, hreg6c, hmem6c⟩ :=
    call_ld_jalr (r := r4) (tblOff := 1408) (tgt := pcCopy30 r4)
      (rfl : openInstr 4864 = .base (.LD .x6 .x14 (1408#12)))
      (rfl : openInstr 4865 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc6a
      ((hreg6a .x14 (by simp)).trans hs5_14)
      (by rw [hmem6a]; exact (slowTbl_get htbl5 r4).2.1)
  have hmem6c5 : ∀ a, s6c.getMem a = s5.getMem a := fun a => (hmem6c a).trans (hmem6a a)
  have hro6c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s6c :=
    fun a ha => (hmem6c5 a).trans (hro5 a ha)
  have hw6c := writerState_of_mem_eq hw5 hmem6c5
    ((hreg6c .x25 (by simp)).trans (hreg6a .x25 (by simp)))
    ((hreg6c .x12 (by simp)).trans (hreg6a .x12 (by simp)))
  set r5 : Fin 8 := copy30NextR r4
  have hd_r4 : copy30NextDstOff r4 0 ≤ 32 := by unfold copy30NextDstOff; split_ifs <;> omega
  obtain ⟨s6, hr6, hpc6, hs6_14, hreg6, hp6, hw6⟩ := openRuns_sub_copy30 (r := r4) (retPc := 4866)
    (d := tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) hpc6c hs6c_1
    ((hreg6c .x10 (by simp)).trans hs6a_10)
    (by have h1 := levelBase_align8' 5 (by omega); have h2 := nodeOffset_align8' 5 ((g >>> 4) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 5 _ (by omega) hst.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro6c 5 _ k (by omega) hst.2.1 hk)
    (fun hcl => hcl.1 5 (by omega) (by omega) _ hst.2.1)
    (by omega) hw6c
  have hro6 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s6 :=
    ReadOnlyPreserved.of_proofWrite hro6c hp6
  have hbt6 : BaseTableReady s6 := baseTableReady_of_lowEq hbt5 (fun a ha => (hp6 a (by omega)).trans (hmem6c5 a))
  have htbl6 : SlowTablesState s6 true := slowTablesState_of_eq htbl5 (fun a _ _ => (hp6 a (by omega)).trans (hmem6c5 a))
  have hreg60 : RegsEqExcept [.x1, .x2, .x5, .x6, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s6 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg6 reg (by simp [h5', h6', h12', h14', h25'])).trans ((hreg6c reg (by simp [h1', h6'])).trans
      ((hreg6a reg (by simp [h10', h22', h28'])).trans
       ((hreg5 reg (by simp [h1', h5', h6', h10', h12', h14', h19', h22', h25', h28'])).trans (hreg40 reg hreg))))
  -- 8. L7 + L9 via copy29_x2 (4866..4880 -> 4881)
  have h4866 := step_SRLI (s := s6) (by decide) hpc6 (rfl : openInstr 4866 = .base (.SRLI .x22 .x22 (1#6)))
  set s7_0 := (s6.setReg .x22 (s6.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4867)
  have hs7_0_22 : s7_0.getReg .x22 = BitVec.ofNat 64 (g >>> 6) := by
    have h6_22 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> 5) :=
      (hreg6 .x22 (by simp)).trans ((hreg6c .x22 (by simp)).trans hs6a_22)
    simp only [s7_0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h6_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 5) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 5) >>> 1 = g >>> 6 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hs7_0_30 : s7_0.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7) :=
    (by simp [s7_0, getReg_setReg_ne'] : s7_0.getReg .x30 = s6.getReg .x30).trans ((hreg60 .x30 (by decide)).trans hrx30)
  obtain ⟨s7a, hr7a, hpc7a, hs7a_22, hs7a_10, hreg7a, hmem7a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4867 (lvlAddrInRegCode .x10 .x30) (by decide) rfl)
      rfl (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide) hs7_0_22 hs7_0_30
  rw [div2_ushr_eq g 6 7] at hs7a_22
  have h4872 := step_SRLI (s := s7a) (by decide) hpc7a (rfl : openInstr 4872 = .base (.SRLI .x22 .x22 (1#6)))
  set s7_1 := (s7a.setReg .x22 (s7a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4873)
  have hs7_1_22 : s7_1.getReg .x22 = BitVec.ofNat 64 (g >>> 8) := by
    simp only [s7_1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hs7a_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 7) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 7) >>> 1 = g >>> 8 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hs7_1_23 : s7_1.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9) :=
    (by simp [s7_1, getReg_setReg_ne'] : s7_1.getReg .x23 = s7a.getReg .x23).trans
      ((hreg7a .x23 (by decide)).trans ((by simp [s7_0, getReg_setReg_ne'] : s7_0.getReg .x23 = s6.getReg .x23).trans ((hreg60 .x23 (by decide)).trans hrx23)))
  obtain ⟨s7b, hr7b, hpc7b, hs7b_22, hs7b_28, hreg7b, hmem7b⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4873 (lvlAddrInRegCode .x28 .x23) (by decide) rfl)
      rfl (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide) hs7_1_22 hs7_1_23
  rw [div2_ushr_eq g 8 9] at hs7b_22
  have hreg7b_6 : RegsEqExcept [.x10, .x22, .x28] s6 s7b := fun reg hreg => by
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    have e1 : s7_1.getReg reg = s7a.getReg reg := by simp [s7_1, getReg_setReg_ne' .x22 reg h22'.symm]
    have e2 : s7_0.getReg reg = s6.getReg reg := by simp [s7_0, getReg_setReg_ne' .x22 reg h22'.symm]
    exact (hreg7b reg (by simp [h22', h28'])).trans (e1.trans ((hreg7a reg (by simp [h22', h10'])).trans e2))
  have hmem7b6 : ∀ a, s7b.getMem a = s6.getMem a := fun a => by simp [hmem7b, s7_1, hmem7a, s7_0]
  obtain ⟨s7c, hr7c, hpc7c, hs7c_1, hreg7c, hmem7c⟩ :=
    call_ld_jalr (r := r5) (tblOff := 1728) (tgt := pcCopy29x2 r5)
      (rfl : openInstr 4878 = .base (.LD .x6 .x14 (1728#12)))
      (rfl : openInstr 4879 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc7b
      ((hreg7b_6 .x14 (by decide)).trans hs6_14)
      (by rw [hmem7b6]; exact (slowTbl_get htbl6 r5).2.2.2.2.2.2)
  have hmem7c6 : ∀ a, s7c.getMem a = s6.getMem a := fun a => (hmem7c a).trans (hmem7b6 a)
  have hro7c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7c :=
    fun a ha => (hmem7c6 a).trans (hro6 a ha)
  have hw7c := writerState_of_mem_eq hw6 hmem7c6
    ((hreg7c .x25 (by decide)).trans (hreg7b_6 .x25 (by decide)))
    ((hreg7c .x12 (by decide)).trans (hreg7b_6 .x12 (by decide)))
  set r79 : Fin 8 := copy29x2NextR r5
  have hd_r5 : copy29x2NextDstOff r5 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  have hs7c_10 : s7c.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 7 + nodeOffset 7 ((g >>> 6) ^^^ 1)) := by
    have e1 : s7_1.getReg .x10 = s7a.getReg .x10 := by simp [s7_1, getReg_setReg_ne']
    exact (hreg7c .x10 (by decide)).trans ((hreg7b .x10 (by decide)).trans (e1.trans hs7a_10))
  obtain ⟨s7, hr7, hpc7, hs7_14, hs7_5, hreg7, hp7, hw7⟩ := openRuns_sub_copy29x2 (r := r5) (retPc := 4880)
    (d0 := tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) (d1 := tdNode trapdoor 9 ((g >>> 8) ^^^ 1))
    hpc7c hs7c_1
    ((hreg7c .x11 (by decide)).trans ((hreg7b_6 .x11 (by decide)).trans ((hreg60 .x11 (by decide)).trans hrx11)))
    hs7c_10 ((hreg7c .x28 (by decide)).trans hs7b_28)
    (by have h1 := levelBase_align8' 7 (by omega); have h2 := nodeOffset_align8' 7 ((g >>> 6) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 9 (by omega); have h2 := nodeOffset_align8' 9 ((g >>> 8) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 7 _ (by omega) hst.2.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 9 _ (by omega) hst.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro7c 7 _ k (by omega) hst.2.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro7c 9 _ k (by omega) hst.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 7 (by omega) (by omega) _ hst.2.2.2.1)
    (fun hcl => hcl.2 9 (by omega) (by omega) _ hst.2.2.2.2.2.1)
    (by omega) hw7c
  have h4880 := step_ADDI (s := s7) (by decide) hpc7 (rfl : openInstr 4880 = .base (.ADDI .x8 .x5 (0#12)))
  set s8 := (s7.setReg .x8 (s7.getReg .x5 + signExtend12 (0#12))).setPC (pcAt 4881)
  have hs8_8 : CleanTrapdoor trapdoor → s8.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))]) :=
    fun hcl => by simp [s8, hs7_5 hcl, signExtend12_nonneg 0 (by omega)]
  have hs8_22 : s8.getReg .x22 = BitVec.ofNat 64 (g >>> 9) := by
    simp [s8, getReg_setReg_ne', (hreg7 .x22 (by simp)).trans ((hreg7c .x22 (by simp)).trans hs7b_22)]
  have hs8_14 : s8.getReg .x14 = BitVec.ofNat 64 (8 * r79.val) := by simp [s8, getReg_setReg_ne', hs7_14, r79]
  have hro8 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s8 :=
    fun a ha => (by simp [s8] : s8.getMem a = s7.getMem a).trans (ReadOnlyPreserved.of_proofWrite hro7c hp7 a ha)
  have hbt8 : BaseTableReady s8 := baseTableReady_of_lowEq hbt6 (fun a ha => (by simp [s8] : s8.getMem a = s7.getMem a).trans ((hp7 a (by omega)).trans (hmem7c6 a)))
  have htbl8 : SlowTablesState s8 true := slowTablesState_of_eq htbl6 (fun a _ _ => (by simp [s8] : s8.getMem a = s7.getMem a).trans ((hp7 a (by omega)).trans (hmem7c6 a)))
  have hreg80 : RegsEqExcept [.x1, .x2, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s8 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h2' : reg ≠ .x2 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    simp only [s8, MachineState.getReg_setPC, getReg_setReg_ne' .x8 reg h8'.symm]
    exact (hreg7 reg (by simp [h5', h6', h10', h12', h14', h19', h25'])).trans ((hreg7c reg (by simp [h1', h6'])).trans
      ((hreg7b reg (by simp [h22', h28'])).trans (by
        simp only [s7_1, MachineState.getReg_setPC, getReg_setReg_ne' .x22 reg h22'.symm]
        exact (hreg7a reg (by simp [h22', h10'])).trans (by
          simp only [s7_0, MachineState.getReg_setPC, getReg_setReg_ne' .x22 reg h22'.symm]
          exact hreg60 reg (by simp [h1', h2', h5', h6', h10', h12', h14', h19', h22', h25', h28'])))))
  -- 9. L11 + L13 via copy29_x2 (4881..4898 -> 4899)
  have h4881 := step_SRLI (s := s8) (by decide) rfl (rfl : openInstr 4881 = .base (.SRLI .x22 .x22 (1#6)))
  set s9_0 := (s8.setReg .x22 (s8.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4882)
  have hs9_0_22 : s9_0.getReg .x22 = BitVec.ofNat 64 (g >>> 10) := by
    simp only [s9_0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hs8_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 9) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 9) >>> 1 = g >>> 10 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hs9_0_3 : s9_0.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11) :=
    (by simp [s9_0, getReg_setReg_ne'] : s9_0.getReg .x3 = s8.getReg .x3).trans ((hreg80 .x3 (by decide)).trans hrx3)
  obtain ⟨s9a, hr9a, hpc9a, hs9a_22, hs9a_10, hreg9a, hmem9a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4882 (lvlAddrInRegCode .x10 .x3) (by decide) rfl)
      rfl (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide) hs9_0_22 hs9_0_3
  rw [div2_ushr_eq g 10 11] at hs9a_22
  have h4887 := step_SRLI (s := s9a) (by decide) hpc9a (rfl : openInstr 4887 = .base (.SRLI .x22 .x22 (1#6)))
  set s9_1 := (s9a.setReg .x22 (s9a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4888)
  have hs9_1_22 : s9_1.getReg .x22 = BitVec.ofNat 64 (g >>> 12) := by
    simp only [s9_1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hs9a_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 11) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 11) >>> 1 = g >>> 12 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  obtain ⟨s9b, hr9b, hpc9b, hs9b_22, hs9b_28, hreg9b, hmem9b⟩ :=
    openRuns_lvl_addr_inmem (codeAt_of_list_eq 4888 (lvlAddrInMemCode .x28 13) (by decide) rfl)
      rfl (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide)
      hs9_1_22 (baseTableReady_of_lowEq hbt8 (fun a _ => by simp [s9_1, hmem9a, s9_0]))
  rw [div2_ushr_eq g 12 13] at hs9b_22
  have h4894 := step_SRLI (s := s9b) (by decide) hpc9b (rfl : openInstr 4894 = .base (.SRLI .x22 .x22 (1#6)))
  set s9_2 := (s9b.setReg .x22 (s9b.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4895)
  have hs9_2_22 : s9_2.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) := by
    simp only [s9_2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hs9b_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 13) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega), capLeafOf_eq_div16384]
    rw [show (g >>> 13) >>> 1 = g >>> 14 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hreg92_8 : RegsEqExcept [.x5, .x10, .x22, .x28] s8 s9_2 := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    have e1 : s9_2.getReg reg = s9b.getReg reg := by simp [s9_2, getReg_setReg_ne' .x22 reg h22'.symm]
    have e2 : s9_1.getReg reg = s9a.getReg reg := by simp [s9_1, getReg_setReg_ne' .x22 reg h22'.symm]
    have e3 : s9_0.getReg reg = s8.getReg reg := by simp [s9_0, getReg_setReg_ne' .x22 reg h22'.symm]
    exact e1.trans ((hreg9b reg (by simp [h5', h22', h28'])).trans (e2.trans ((hreg9a reg (by simp [h22', h10'])).trans e3)))
  have hmem928 : ∀ a, s9_2.getMem a = s8.getMem a := fun a => by simp [s9_2, hmem9b, s9_1, hmem9a, s9_0]
  obtain ⟨s9c, hr9c, hpc9c, hs9c_1, hreg9c, hmem9c⟩ :=
    call_ld_jalr (r := r79) (tblOff := 1728) (tgt := pcCopy29x2 r79)
      (rfl : openInstr 4895 = .base (.LD .x6 .x14 (1728#12)))
      (rfl : openInstr 4896 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) rfl
      ((hreg92_8 .x14 (by decide)).trans hs8_14)
      (by rw [hmem928]; exact (slowTbl_get htbl8 r79).2.2.2.2.2.2)
  have hmem9c7 : ∀ a, s9c.getMem a = s7.getMem a := fun a => (hmem9c a).trans ((hmem928 a).trans (by simp [s8]))
  have hro9c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s9c :=
    fun a ha => (hmem9c a).trans ((hmem928 a).trans (hro8 a ha))
  have hw9c := writerState_of_mem_eq hw7 hmem9c7
    ((hreg9c .x25 (by decide)).trans ((hreg92_8 .x25 (by decide)).trans (by simp [s8, getReg_setReg_ne'])))
    ((hreg9c .x12 (by decide)).trans ((hreg92_8 .x12 (by decide)).trans (by simp [s8, getReg_setReg_ne'])))
  set rEnd : Fin 8 := copy29x2NextR r79
  have hd_r79 : copy29x2NextDstOff r79 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  have hs9c_10 : s9c.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 11 + nodeOffset 11 ((g >>> 10) ^^^ 1)) := by
    have e1 : s9_2.getReg .x10 = s9b.getReg .x10 := by simp [s9_2, getReg_setReg_ne']
    have e2 : s9_1.getReg .x10 = s9a.getReg .x10 := by simp [s9_1, getReg_setReg_ne']
    exact (hreg9c .x10 (by decide)).trans (e1.trans ((hreg9b .x10 (by decide)).trans (e2.trans hs9a_10)))
  have hs9c_28 : s9c.getReg .x28 = BitVec.ofNat 64 (4294971424 + levelBase 13 + nodeOffset 13 ((g >>> 12) ^^^ 1)) := by
    have e1 : s9_2.getReg .x28 = s9b.getReg .x28 := by simp [s9_2, getReg_setReg_ne']
    exact (hreg9c .x28 (by decide)).trans (e1.trans hs9b_28)
  obtain ⟨s9, hr9, hpc9, hs9_14, hs9_5, hreg9, hp9, hw9⟩ := openRuns_sub_copy29x2 (r := r79) (retPc := 4897)
    (d0 := tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) (d1 := tdNode trapdoor 13 ((g >>> 12) ^^^ 1))
    hpc9c hs9c_1
    ((hreg9c .x11 (by decide)).trans ((hreg92_8 .x11 (by decide)).trans ((hreg80 .x11 (by decide)).trans hrx11)))
    hs9c_10 hs9c_28
    (by have h1 := levelBase_align8' 11 (by omega); have h2 := nodeOffset_align8' 11 ((g >>> 10) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 13 (by omega); have h2 := nodeOffset_align8' 13 ((g >>> 12) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 11 _ (by omega) hst.2.2.2.2.2.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 13 _ (by omega) hst.2.2.2.2.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro9c 11 _ k (by omega) hst.2.2.2.2.2.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro9c 13 _ k (by omega) hst.2.2.2.2.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 11 (by omega) (by omega) _ hst.2.2.2.2.2.2.2.1)
    (fun hcl => hcl.2 13 (by omega) (by omega) _ hst.2.2.2.2.2.2.2.2.2.1)
    (by omega) hw9c
  set ts4 : List (BitVec 6) :=
    [tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))] ++
    [tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)), tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))]
  have hts4_eq : ts4 = recordTails (tdNode trapdoor) i := by rw [hrec_eq.2]; simp [ts4, g]
  obtain ⟨s9x, hr9x, hpc9x, hs9x_8, hreg9x, hmem9x⟩ := openRuns_combine_tails
    (ts0 := [tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))])
    (ts1 := [tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)), tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))])
    (by simp) (rfl : openInstr 4897 = .base (.SLLI .x5 .x5 (12#6)))
    (rfl : openInstr 4898 = .base (.OR .x8 .x8 .x5)) (by decide) hpc9
    (fun hcl => (hreg9 .x8 (by decide)).trans ((hreg9c .x8 (by decide)).trans ((hreg92_8 .x8 (by decide)).trans (hs8_8 hcl))))
    hs9_5
  have hreg9x0 : RegsEqExcept [.x1, .x2, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s9x := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg9x reg (by simp [h5', h8'])).trans ((hreg9 reg (by simp [h5', h6', h10', h12', h14', h19', h25'])).trans
      ((hreg9c reg (by simp [h1', h6'])).trans (by
        simp only [s9_2, MachineState.getReg_setPC, getReg_setReg_ne' .x22 reg h22'.symm]
        exact (hreg9b reg (by simp [h5', h22', h28'])).trans (by
          simp only [s9_1, MachineState.getReg_setPC, getReg_setReg_ne' .x22 reg h22'.symm]
          exact (hreg9a reg (by simp [h22', h10'])).trans (by
            simp only [s9_0, MachineState.getReg_setPC, getReg_setReg_ne' .x22 reg h22'.symm]
            exact hreg80 reg hreg)))))
  have hp9x_s : ProofWritePreserves s s9x :=
    ProofWritePreserves.trans (fun a _ => hmem0 a) <| hp2_s0.trans <| hp3.trans <|
      ProofWritePreserves.trans (fun a _ => hmem4c3 a) <| hp4.trans <| hp5.trans <|
      ProofWritePreserves.trans (fun a _ => hmem6c5 a) <| hp6.trans <|
      ProofWritePreserves.trans (fun a _ => hmem7c6 a) <| hp7.trans <|
      ProofWritePreserves.trans (fun a _ => hmem9c7 a) <| hp9.trans (fun a _ => hmem9x a)
  have ht9x : TailState (CleanTrapdoor trapdoor) s9x tails flushes :=
    TailState.of_proofWrite ht0 hp9x_s
      (hreg9x0 .x15 (by simp)) (hreg9x0 .x16 (by simp)) (hreg9x0 .x17 (by simp))
  -- 10. tailMerge 24 (4899..4907 -> 4908) + slow_epilogue (4908..4917)
  obtain ⟨s10, hr10, hpc10, hreg10, htw10, ht10⟩ := openRuns_tailMerge_neg (ts := ts4)
    (by simp [ts4]) (by simp [ts4]) (codeAt_of_list_eq 4899 (tailMergeCode 24) (by decide) rfl)
    hpc9x hs9x_8 ht9x hbd_t
  have hro10 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s10 :=
    readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro0 hp9x_s) htw10
  have hbt10 : BaseTableReady s10 := baseTableReady_of_lowEq hbt0 (fun a ha =>
    ((tailWrite_pres_low htw10).1 a ha).trans ((proofWrite_pres_low hp9x_s).1 a ha))
  have htbl10 : SlowTablesState s10 true := slowTablesState_of_eq htbl0 (fun a h1 h2 =>
    ((tailWrite_pres_low htw10).2.2 a h1 h2).trans ((proofWrite_pres_low hp9x_s).2.2 a h1 h2))
  have hcm10 : CapMarks15State s10 positions ordinal := capMarks15State_of_lowEq hcm0 (fun a h1 h2 =>
    ((tailWrite_pres_low htw10).2.1 a h1 h2).trans ((proofWrite_pres_low hp9x_s).2.1 a h1 h2))
  have hfwd_eq : written ++ bitsToBytes (tdSalt trapdoor i) 24 ++
      (if g = 5592405 then [] else bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32) ++
      bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32 ++
      (if ((g >>> 1) ^^^ 1) < levelSize 2 then bitsToBytes (tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) 30 else []) ++
      bitsToBytes (tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) 30 ++
      (if ((g >>> 3) ^^^ 1) < levelSize 4 then bitsToBytes (tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) 30 else []) ++
      bitsToBytes (tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29 =
      written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i := by
    rw [hrec_eq.1]; simp only [List.append_assoc, g]
  have hw10 : WriterState (CleanTrapdoor trapdoor) s10 rEnd false
      (base4 + copy30NextDstOff r4 0 + copy29x2NextDstOff r5 + copy29x2NextDstOff r79) 0
      (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i) := by
    rw [← hfwd_eq]
    have hw9x := writerState_of_mem_eq hw9 hmem9x (hreg9x .x25 (by simp)) (hreg9x .x12 (by simp))
    exact writerState_of_tailWrite hw9x htw10 (hreg10 .x25 (by simp)) (hreg10 .x12 (by simp))
  have ht10' : TailState (CleanTrapdoor trapdoor) s10 (tails ++ recordTails (tdNode trapdoor) i)
      (flushes + if (6 * tails.length) % 64 + 6 * ts4.length < 64 then 0 else 1) := by
    rw [← hts4_eq]; exact ht10
  have hreg10_b : ∀ reg, reg ∉ ([.x1, .x2, .x5, .x6, .x8, .x10, .x12, .x14, .x15, .x16, .x17, .x19, .x22, .x25, .x28] : List Reg) →
      s10.getReg reg = s.getReg reg := fun reg hreg =>
    (hreg10 reg (reg_not_mem_sub (by decide) hreg)).trans
      (hreg9x0 reg (reg_not_mem_sub (by decide) hreg))
  have hs10_14 : s10.getReg .x14 = BitVec.ofNat 64 (8 * rEnd.val) :=
    (hreg10 .x14 (by simp)).trans ((hreg9x .x14 (by simp)).trans hs9_14)
  have hs10_22 : s10.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) :=
    (hreg10 .x22 (by simp)).trans ((hreg9x .x22 (by simp)).trans ((hreg9 .x22 (by simp)).trans ((hreg9c .x22 (by simp)).trans hs9_2_22)))
  obtain ⟨sEnd, hrEnd, hinvEnd⟩ := openRuns_slow_epilogue (isTail := true) hord hpc10
    (fun h => absurd h (by decide)) ((hreg10_b .x3 (by decide)).trans hrx3)
    ((hreg10_b .x4 (by decide)).trans hrx4) ((hreg10_b .x7 (by decide)).trans hrx7)
    ((hreg10_b .x9 (by decide)).trans hrx9) ((hreg10_b .x11 (by decide)).trans hrx11)
    ((hreg10_b .x13 (by decide)).trans hrx13) hs10_14 ((hreg10_b .x18 (by decide)).trans hrx18)
    ((hreg10_b .x20 (by decide)).trans hrx20) ((hreg10_b .x21 (by decide)).trans hrx21)
    hs10_22 ((hreg10_b .x23 (by decide)).trans hrx23) ((hreg10_b .x24 (by decide)).trans hrx24)
    ((hreg10_b .x26 (by decide)).trans hrx26) ((hreg10_b .x27 (by decide)).trans hrx27)
    ((hreg10_b .x29 (by decide)).trans hrx29) ((hreg10_b .x30 (by decide)).trans hrx30)
    ((hreg10_b .x31 (by decide)).trans hrx31) hro10 hbt10 hcm10 htbl10 hw10 ht10'
  set cL2 := if hasL2 then 4 + 4 + 2 + (copy30SubCode r0).length else 4
  set cL4 := if hasL4 then 4 + 3 + 2 + (copy30SubCode r3).length else 4
  set cycNf := 7 + cL0 + (6 + 2 + (copy32SubCode r0).length) + cL2 +
    (6 + 2 + (copy30SubCode r2).length) + cL4 + (5 + 2 + (copy30SubCode r4).length) +
    (1 + 5 + 1 + 5 + 2 + (copy29x2SubCode r5).length + 1) +
    (1 + 5 + 1 + 6 + 1 + 2 + (copy29x2SubCode r79).length + 2) +
    5 + (if ordinal + 1 = positions.card then 4 else 9)
  have hfl_eq : (if (6 * tails.length) % 64 + 6 * ts4.length < 64 then 0 else 1) =
      (if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
    rw [hts4_eq]
  refine ⟨cycNf, rEnd,
    base4 + copy30NextDstOff r4 0 + copy29x2NextDstOff r5 + copy29x2NextDstOff r79, sEnd, ?_, ?_, ?_⟩
  · simp only [↓reduceIte] at hrEnd
    have htotA := ((((((((((((hr0.trans hr1).trans hr2a).trans hr2c).trans hr2).trans hr3).trans hr4a).trans hr4c).trans hr4).trans hr5).trans hr6a).trans hr6c).trans hr6)
    have htotB := ((((((((((((h4866.trans hr7a).trans h4872).trans hr7b).trans hr7c).trans hr7).trans h4880).trans h4881).trans hr9a).trans h4887).trans hr9b).trans h4894).trans (((hr9c.trans hr9).trans hr9x).trans (hr10.trans hrEnd)))
    have htot := htotA.trans htotB
    have heq_c : 7 + cL0 + 6 + 2 + (copy32SubCode r0).length + cL2 + 6 + 2 + (copy30SubCode r2).length +
        cL4 + 5 + 2 + (copy30SubCode r4).length +
        (1 + 5 + 1 + 5 + 2 + (copy29x2SubCode r5).length + 1 + 1 + 5 + 1 + 6 + 1 +
         (2 + (copy29x2SubCode r79).length + 2 +
          ((5 + 4 * (if 6 * tails.length % 64 + 6 * ts4.length < 64 then 0 else 1)) +
           (if ordinal + 1 = positions.card then 4 else 9)))) =
        cycNf + 4 * (if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
      rw [hfl_eq]; unfold cycNf; omega
    rw [heq_c] at htot; exact htot
  · have ha := slowTail_amort r0 (decide (g ≠ 5592405)) hasL2 hasL4
    have hrEnd_eq : rEnd = slowTailEndR r0 hasL2 hasL4 := rfl
    rw [hrEnd_eq]
    have hcL0' : cL0 ≤ 2 + (if decide (g ≠ 5592405) then 6 + 2 + (copy32SubCode r0).length + 1 + 2 + (copy32SubCode r0).length else 0) := hcL0
    have hle : slowEntryCyc r0 + 4 + cycNf ≤ slowTailCyc r0 (decide (g ≠ 5592405)) hasL2 hasL4 := by
      unfold slowTailCyc cycNf cL2 cL4
      dsimp only [r2, r3, r4, r5, r79]
      cases h0 : decide (g ≠ 5592405) <;> cases h2 : hasL2 <;> cases h4 : hasL4 <;>
        simp only [h0, Bool.false_eq_true, ↓reduceIte] at hcL0' ⊢ <;>
        split_ifs <;> omega
    exact le_trans (by omega) ha
  · rw [← hfl_eq]; exact hinvEnd

/-! ### 3. Unified `slow_body` Handler (`PC 4488`) -/

/-- Execute the complete slow-record handler `slow_body` (`PC 4488 → rec_r{rEnd}` or `cap_pass`)
for ANY `g ≥ 5,592,064`, charging `tblExtra = if tblInit then 0 else 168` on first invocation
and guaranteeing the universal amortized non-flush bound
`8 * (slowEntryCyc r0 + cycNf) + phi8 rEnd ≤ 3453 + phi8 r0`. -/
theorem openRuns_slow_body {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit : Bool} {s : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg : 5592064 ≤ ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)
    (hinv : SlowEntryInv trapdoor positions ordinal r0 base written tails flushes tblInit
              ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) s) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    let tblExtra := if tblInit then 0 else 168
    ∃ cycNf rEnd baseEnd s',
      OpenRuns s (cycNf + tblExtra + 4 * fl) (cycNf + tblExtra + 4 * fl) s' ∧
      8 * (slowEntryCyc r0 + cycNf) + phi8 rEnd ≤ 3453 + phi8 r0 ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) true s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hi_lt : i.val < 16777216 := i.isLt
  -- Step 1: Lazy jump-table guard (4488 -> 4658, 2 or 170 cycles)
  obtain ⟨s1, hr1, hpc1, hreg1, hmem1, htbl1⟩ := openRuns_slow_tbl_guard hinv.hpc hinv.htbl
  -- Step 2: 4658 ADDI x5 x13 320; 4659 BGEU x22 x5 572 (-> 4802 slow_tail or 4660 slow_mid)
  have h4658 := step_ADDI (s := s1) (by decide) hpc1 (rfl : openInstr 4658 = .base (.ADDI .x5 .x13 (320#12)))
  set s2 := (s1.setReg .x5 (s1.getReg .x13 + signExtend12 (320#12))).setPC (pcAt 4659)
  have hs2_5 : s2.getReg .x5 = BitVec.ofNat 64 5592384 := by
    have h13 := (hreg1 .x13 (by simp)).trans hinv.rx13
    simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h13, signExtend12_nonneg 320 (by omega), ← BitVec.ofNat_add]
  have hs2_22 : s2.getReg .x22 = BitVec.ofNat 64 g := by
    simp [s2, getReg_setReg_ne', (hreg1 .x22 (by simp)).trans hinv.rx22, g]
  have hmem20 : ∀ a : Word, ¬ (1344 ≤ a.toNat ∧ a.toNat < 1792) → s2.getMem a = s.getMem a :=
    fun a ha => (by simp [s2] : s2.getMem a = s1.getMem a).trans (hmem1 a ha)
  have hinv_s2 : ∀ pcNext, SlowEntryInv trapdoor positions ordinal r0 base written tails flushes true i
      ((s2.setPC (pcAt pcNext)).setPC (pcAt PC_slow_body)) := by
    intro pcNext
    have hreg2 : ∀ reg, reg ≠ .x5 → s2.getReg reg = s.getReg reg := fun reg hne => by
      simp [s2, getReg_setReg_ne' .x5 reg hne.symm, hreg1 reg (by simp [hne])]
    have hro2 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s2 :=
      fun a ha => (hmem20 a (by omega)).trans (hinv.hro a ha)
    have hbt2 : BaseTableReady s2 := baseTableReady_of_lowEq hinv.hbt (fun a ha => hmem20 a (by omega))
    have hcm2 : CapMarks15State s2 positions ordinal := capMarks15State_of_lowEq hinv.hcm (fun a h1 h2 => hmem20 a (by omega))
    have htbl2 : SlowTablesState s2 true := slowTablesState_of_eq htbl1 (fun a _ _ => by simp [s2])
    have hw2 : WriterState (CleanTrapdoor trapdoor) s2 r0 false (base + 24) 0 (written ++ bitsToBytes (tdSalt trapdoor i) 24) := by
      have hbyte : ∀ q < 8556390424, s2.getByte (BitVec.ofNat 64 (11341403200 + q)) = s.getByte (BitVec.ofNat 64 (11341403200 + q)) := by
        intro q hq; simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
        have hal := alignToDword_ofNat_eq (8 * ((11341403200 + q) / 8)) ((11341403200 + q) % 8) (by omega) (by omega)
        rw [show 8 * ((11341403200 + q) / 8) + (11341403200 + q) % 8 = 11341403200 + q by omega] at hal
        apply hmem20; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      refine ⟨hinv.hw.hbase8, hinv.hw.hdst8, hinv.hw.hlen, hinv.hw.hbound, (hreg2 .x25 (by decide)).trans hinv.hw.rx25,
        hinv.hw.hflushed_ok, fun hcl j hj => by have h1 := hinv.hw.hlen; have h2 := hinv.hw.hbound; rw [hbyte j (by omega)]; exact hinv.hw.hbytes hcl j hj, fun hcl => ?_⟩
      have hrem := hinv.hw.hrem hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
      by_cases hr0' : r0.val = 0
      · simp [hr0']
      · simp only [hr0', ↓reduceIte] at hrem ⊢; rw [hreg2 .x12 (by decide)]; exact hrem
    have ht2 : TailState (CleanTrapdoor trapdoor) s2 tails flushes := by
      refine ⟨hinv.ht.hbits, hinv.ht.hbound, (hreg2 .x15 (by decide)).trans hinv.ht.rx15,
        (hreg2 .x17 (by decide)).trans hinv.ht.rx17, fun hcl => ?_⟩
      obtain ⟨tBuf, hlt, hx16', hsum⟩ := hinv.ht.hdata hcl
      refine ⟨tBuf, hlt, (hreg2 .x16 (by decide)).trans hx16', ?_⟩
      have hmap : ((List.range (8 * flushes)).map fun j => s2.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
          ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
        apply List.map_congr_left; intro j hj; have hjlt := List.mem_range.mp hj
        have htbb : tailBufBase = 20000000000 := rfl; have hbd := hinv.ht.hbound
        simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
        have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by omega)
        rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
        apply hmem20; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [hmap]; exact hsum
    refine ⟨rfl,
      (hreg2 .x1 (by decide)).trans hinv.rx1, (hreg2 .x2 (by decide)).trans hinv.rx2,
      (hreg2 .x3 (by decide)).trans hinv.rx3, (hreg2 .x4 (by decide)).trans hinv.rx4,
      (hreg2 .x6 (by decide)).trans hinv.rx6, (hreg2 .x7 (by decide)).trans hinv.rx7,
      (hreg2 .x8 (by decide)).trans hinv.rx8, (hreg2 .x9 (by decide)).trans hinv.rx9,
      (hreg2 .x11 (by decide)).trans hinv.rx11, (hreg2 .x13 (by decide)).trans hinv.rx13,
      (hreg2 .x14 (by decide)).trans hinv.rx14, (hreg2 .x18 (by decide)).trans hinv.rx18,
      (hreg2 .x19 (by decide)).trans hinv.rx19, (hreg2 .x20 (by decide)).trans hinv.rx20,
      (hreg2 .x21 (by decide)).trans hinv.rx21, (hreg2 .x22 (by decide)).trans hinv.rx22,
      (hreg2 .x23 (by decide)).trans hinv.rx23, (hreg2 .x24 (by decide)).trans hinv.rx24,
      (hreg2 .x26 (by decide)).trans hinv.rx26, (hreg2 .x27 (by decide)).trans hinv.rx27,
      (hreg2 .x29 (by decide)).trans hinv.rx29, (hreg2 .x30 (by decide)).trans hinv.rx30,
      (hreg2 .x31 (by decide)).trans hinv.rx31, hro2,
      baseTableReady_of_lowEq hbt2 (fun _ _ => rfl),
      capMarks15State_of_lowEq hcm2 (fun _ _ _ => rfl),
      slowTablesState_of_eq htbl2 (fun _ _ _ => rfl),
      writerState_of_mem_eq hw2 (fun _ => rfl) rfl rfl,
      TailState.of_proofWrite ht2 (fun _ _ => rfl) rfl rfl rfl⟩
  by_cases hmid : g < 5592384
  · have hlt : (s2.getReg .x22).toNat < (s2.getReg .x5).toNat := by
      rw [hs2_22, hs2_5, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : g < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 5592384 < 2 ^ 64)]; omega
    have h4659 := step_BGEU_not_taken (s := s2) (by decide) rfl (rfl : openInstr 4659 = .base (.BGEU .x22 .x5 (572#13))) hlt
    set s3 := s2.setPC (pcAt 4660)
    obtain ⟨cycNf, rEnd, baseEnd, s', hrM, hamort, hpost⟩ :=
      openRuns_slow_mid hord hbd_w hbd_t hg hmid rfl (hinv_s2 4660)
    refine ⟨4 + cycNf, rEnd, baseEnd, s', ?_, by simpa [Nat.add_assoc] using hamort, hpost⟩
    have htot := ((hr1.trans h4658).trans h4659).trans hrM
    have heq : (2 + if tblInit = true then 0 else 168) + 1 + 1 +
        (cycNf + 4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) =
        (4 + cycNf + if tblInit = true then 0 else 168) +
        4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1 := by
      cases tblInit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [heq] at htot; exact htot
  · have hge : 5592384 ≤ g := by omega
    have hle_b : (s2.getReg .x5).toNat ≤ (s2.getReg .x22).toNat := by
      rw [hs2_22, hs2_5, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : g < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 5592384 < 2 ^ 64)]; omega
    have hbr : pcAt 4659 + signExtend13 (572#13) = pcAt 4802 := by
      simpa only [show 4 * (4802 - 4659) = 572 by decide] using pcAt_add_pos13 4659 4802 (by decide) (by decide)
    have h4659 := step_BGEU_taken (s := s2) (by decide) rfl (rfl : openInstr 4659 = .base (.BGEU .x22 .x5 (572#13))) hle_b hbr
    set s3 := s2.setPC (pcAt 4802)
    obtain ⟨cycNf, rEnd, baseEnd, s', hrT, hamort, hpost⟩ :=
      openRuns_slow_tail hord hbd_w hbd_t hge rfl (hinv_s2 4802)
    refine ⟨4 + cycNf, rEnd, baseEnd, s', ?_, by simpa [Nat.add_assoc] using hamort, hpost⟩
    have htot := ((hr1.trans h4658).trans h4659).trans hrT
    have heq : (2 + if tblInit = true then 0 else 168) + 1 + 1 +
        (cycNf + 4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) =
        (4 + cycNf + if tblInit = true then 0 else 168) +
        4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1 := by
      cases tblInit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [heq] at htot; exact htot

end CommitGolfCandidate.MoonOpen
