import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the L2..L14 binary loop, L15 cap-store, and full per-position loop (`pc[141..248]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem evalLevel_succ_of_ge1 (c : Comp96) (w : WitnessPath) (l : Nat) (hl : 1 ≤ l) :
    w.evalLevel c (l + 1) =
      let cur := w.evalLevel c l
      let idx := (w.index.val / 3) >>> (l - 1)
      if (idx ^^^ 1) < levelSize l then
        let inp := if idx % 2 = 0 then binaryInput cur (w.binSib l)
                   else binaryInput (w.binSib l) cur
        let raw := c inp
        if l + 1 = 24 then raw else mask240 raw
      else cur := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rfl

/-- One iteration (`step < 13`, level `l = 2 + step`) of the L2..L14 binary loop (`pc[143..213]`). -/
theorem step_pos_bin_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 13)
    (hpeven : pOff % 2 = 0)
    (hple : pOff + 24 + l0Bytes (posAt input.positions ord) + 32 +
      binPathOff ((posAt input.positions ord).val / 3) step ≤ input.proof.length)
    (s : MachineState) (hpc : s.pc = pcWord 143)
    (hfix : CheckFixedRegs s input.proof.length)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 +
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32 +
        binPathOff ((posAt input.positions ord).val / 3) step)))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15))
    (hcur : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) pOff (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (2 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pCur := pOff + 24 + l0Bytes i + 32 + binPathOff g step
    let pw := parsePartialWitness s0 pOff i (valAt input ord)
    PhaseOutcome oracle s 60 1 (input.proof.length < pCur + binStepBytes g step)
      (fun s' q tr =>
        q ≤ 1 ∧
        pCur + binStepBytes g step ≤ input.proof.length ∧
        s'.pc = (if step + 1 = 13 then pcWord 174 else pcWord 143) ∧
        CheckFixedRegs s' input.proof.length ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pCur + binStepBytes g step)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g pCur pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hpCur_even : pCur % 2 = 0 := by
    have h1 := l0Bytes_even i; have h2 := binPathOff_even g step
    change (pOff + 24 + l0Bytes i + 32 + binPathOff g step) % 2 = 0; omega
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_lt : g < 5592406 := by change i.val / 3 < _; omega
  have hidx_lt : g >>> step < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hidx1_lt : g >>> (step + 1) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g >>> step) / 2 = g >>> (step + 1) := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  -- pc[143]: SRLI x22, x22, 1; pc[144]: XORI x28, x22, 1
  have hst183 := step_ordinary oracle s 143 (.SRLI .x22 .x22 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SRLI .x22 .x22 1#6)
  have hpc1 : s1.pc = pcWord 144 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx22_1 : s1.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, show (1#6 : BitVec 6).toNat = 1 by decide,
      bv64_shr _ 1 (Nat.lt_trans hidx_lt (by decide)), Nat.pow_one, hshr_step]
  have hst184 := step_ordinary oracle s1 144 (.XORI .x28 .x22 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.XORI .x28 .x22 1#12)
  have hpc2 : s2.pc = pcWord 145 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 ((g >>> (step + 1)) ^^^ 1) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22_1, se12_1]
    exact bv64_xor_one _ hidx1_lt
  have hreg2 : ∀ r, r ≠ .x22 → r ≠ .x28 → s2.getReg r = s.getReg r := fun r h22 h28 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
  -- pc[145]: LD x7, 8(x29) -> levelSize (2 + step)
  have ha185 : s2.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475936 + (32 * (2 + step) + 8)) := by
    rw [hreg2 .x29 (by decide) (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv185 : memoryArgumentsValid s2 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha185]
    exact accessValid_ofNat (68719475936 + (32 * (2 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst185 := step_ordinary oracle s2 145 (.LD .x7 .x29 8#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv185])
  let s3 := execInstrBr s2 (.LD .x7 .x29 8#12)
  have hpc3 : s3.pc = pcWord 146 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hsz_val : s2.getMem (BitVec.ofNat 64 (68719475936 + (32 * (2 + step) + 8))) =
      BitVec.ofNat 64 (levelSize (2 + step)) := by
    have hm2 : s2.getMem (BitVec.ofNat 64 (68719475936 + (32 * (2 + step) + 8))) =
        s.getMem (BitVec.ofNat 64 (68719475936 + (32 * (2 + step) + 8))) := by
      simp [MachineState.getMem, hmem2]
    rw [hm2, hhigh.getMem_eq (by omega) (by omega) (by omega),
      check_initial_data_dword input hvalid (32 * (2 + step) + 8) (by omega)]
    exact openingData_dword_1 ⟨2 + step, by omega⟩
  have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (levelSize (2 + step)) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha185]
    rw [MachineState.getReg_setReg_eq (by decide), hsz_val]
  have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 ((g >>> (step + 1)) ^^^ 1) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_2]
  have hsib_lt64 : (g >>> (step + 1)) ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' (g >>> (step + 1)) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega
  have hsz_lt64 : levelSize (2 + step) < 2 ^ 64 := by
    interval_cases step <;> decide
  -- pc[146]: BGEU x28, x7, pc[172]
  have hst186 := step_ordinary oracle s3 146 (.BGEU .x28 .x7 104#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.BGEU .x28 .x7 104#13)
  have hult186 : BitVec.ult (s3.getReg .x28) (s3.getReg .x7) =
      decide (((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)) := by
    rw [hx28_3, hx7_3, bv64_ult_eq _ _ hsib_lt64 hsz_lt64]
  have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
  have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h22 h28 => by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg2 r h22 h28]
  have hx22_3 : s3.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22)]
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x22), hx22_1]
  -- Common loop footer at pc[172..213]
  have hfooter : ∀ (s212 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 54 → qMid ≤ 1 →
      StepsTo oracle s4 s212 kMid qMid trMid →
      s212.pc = pcWord 172 →
      CheckFixedRegs s212 input.proof.length →
      MemEqOutside s s212 256 320 →
      s212.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) →
      s212.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
      s212.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
      s212.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pCur + binStepBytes g step)) →
      s212.getReg .x27 = BitVec.ofNat 64 rem →
      s212.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)) →
      s212.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) →
      readBuffer s212 256 32 = pw.evalLevel c96 (2 + (step + 1)) →
      readBuffer s212 320 32 = 0 →
      (∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle trMid x) →
      pCur + binStepBytes g step ≤ input.proof.length →
      PhaseOutcome oracle s 60 1 (input.proof.length < pCur + binStepBytes g step)
        (fun s' q tr =>
          q ≤ 1 ∧
          pCur + binStepBytes g step ≤ input.proof.length ∧
          s'.pc = (if step + 1 = 13 then pcWord 174 else pcWord 143) ∧
          CheckFixedRegs s' input.proof.length ∧ MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pCur + binStepBytes g step)) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
    intro s212 kMid qMid trMid hkMid hqMid hmid hpc212 hfix212 hout212 h22 h24 h8 h25 h27 h29 h30 hdig212 hgap212 htr212 hple_next
    have hst212 := step_ordinary oracle s212 172 (.ADDI .x29 .x29 32#12) (by decide) hpc212 rfl (by intro h; cases h) rfl
    let s213 := execInstrBr s212 (.ADDI .x29 .x29 32#12)
    have hpc213 : s213.pc = pcWord 173 := by simp only [s213, execInstrBr, MachineState.setPC, hpc212, pcWord_add_four]
    have hx29_213 : s213.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      simp only [s213, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_213 : s213.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) := by
      simp only [s213, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), h30]
    have hst213 := step_ordinary oracle s213 173 (.BNE .x29 .x30 8072#13) (by decide) hpc213 rfl (by intro h; cases h) rfl
    let sFin := execInstrBr s213 (.BNE .x29 .x30 8072#13)
    have hmemFin : sFin.mem = s212.mem := by
      simp only [sFin, execInstrBr]; split <;> simp [s213, execInstrBr, mem_setPC, mem_setReg]
    have hregFin : ∀ r, r ≠ .x29 → sFin.getReg r = s212.getReg r := fun r h29r => by
      have h214 : sFin.getReg r = s213.getReg r := by
        simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
      rw [h214]
      simp only [s213, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h29r.symm
    have hx29_Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      have : sFin.getReg .x29 = s213.getReg .x29 := by
        simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
      exact this.trans hx29_213
    have hpcFin : sFin.pc = if step + 1 = 13 then pcWord 174 else pcWord 143 := by
      have hne_iff : (s213.getReg .x29 != s213.getReg .x30) = decide (step + 1 ≠ 13) := by
        rw [hx29_213, hx30_213, bv64_bne_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      by_cases hdone : step + 1 = 13
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, ite_true, MachineState.setPC, hpc213, pcWord_add_four]
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_false_eq_true, decide_true,
          ite_true, ite_false, MachineState.setPC, hpc213]; decide
    have htot := (((hst183.trans hst184).trans (hst185.trans hst186)).trans hmid).trans (hst212.trans hst213)
    refine .continued sFin (4 + kMid + 2) qMid trMid (by omega) hqMid (by simpa [Nat.add_assoc] using htot)
      ⟨hqMid, hple_next, hpcFin,
       hfix212.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       hout212.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       (hregFin .x22 (by decide)).trans h22, (hregFin .x24 (by decide)).trans h24,
       (hregFin .x8  (by decide)).trans h8,  (hregFin .x25 (by decide)).trans h25,
       (hregFin .x27 (by decide)).trans h27, hx29_Fin,
       (hregFin .x30 (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig212,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap212,
       htr212⟩
  -- Branch on whether sibling exists at level `2 + step`
  by_cases hpair : ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
  · -- Paired: binStepBytes g step = 30
    have hsb : binStepBytes g step = 30 := by unfold binStepBytes; exact if_pos hpair
    have hpc4 : s4.pc = pcWord 147 := by
      simp only [s4, execInstrBr, hult186, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult186, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult186, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
      simpa [s4, execInstrBr, hult186, hpair, MachineState.getReg_setPC] using hx22_3
    -- pc[147]: ADDI x6, x25, 30; pc[148]: BLTU x31, x6, pc[296]
    have hst187 := step_ordinary oracle s4 147 (.ADDI .x6 .x25 30#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ADDI .x6 .x25 30#12)
    have hpc5 : s5.pc = pcWord 148 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hx6_5 : s5.getReg .x6 = BitVec.ofNat 64 (11341403200 + pCur + 30) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg4 .x25 (by decide) (by decide) (by decide),
        hx25, se12_30_ofNat]
      change BitVec.ofNat 64 (11341403200 + pCur) + BitVec.ofNat 64 30 = _
      exact bv64_add _ 30
    have hx31_5 : s5.getReg .x31 = BitVec.ofNat 64 (11341403200 + input.proof.length) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
        hreg4 .x31 (by decide) (by decide) (by decide), hfix.x31]
    have hst188 := step_ordinary oracle s5 148 (.BLTU .x31 .x6 592#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BLTU .x31 .x6 592#13)
    have hpCur_le : pCur ≤ input.proof.length := hple
    have hult188 : BitVec.ult (s5.getReg .x31) (s5.getReg .x6) = decide (input.proof.length < pCur + 30) := by
      rw [hx31_5, hx6_5, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases hshort : input.proof.length < pCur + 30
    · have hpc6 : s6.pc = pcWord 296 := by
        simp only [s6, execInstrBr, hult188, hshort, decide_true, ite_true, MachineState.setPC, hpc5]; decide
      have hrej := (((hst183.trans hst184).trans (hst185.trans hst186)).trans (hst187.trans hst188)).halt
        (halt_reject oracle s6 hpc6)
      exact .rejected 9 0 [] (by rw [hsb]; exact hshort) (by decide) (by decide) (by simpa using hrej)
    · have hge30 : pCur + 30 ≤ input.proof.length := by omega
      have hpc6 : s6.pc = pcWord 149 := by
        simp only [s6, execInstrBr, hult188, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s.mem := by
        have h65 : s6.mem = s5.mem := by
          simp only [s6, execInstrBr, hult188, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
        have h54 : s5.mem = s4.mem := by simp only [s5, execInstrBr, mem_setPC, mem_setReg]
        exact h65.trans (h54.trans hmem4)
      have hreg65 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
        simp only [s6, execInstrBr, hult188, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h6 h7 h22 h28 => by
        rw [hreg65]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        rw [hreg65]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x22), hx22_4]
      -- pc[149]: ANDI x7, x22, 1; pc[150]: BEQ x7, x0, pc[164]
      have hst189 := step_ordinary oracle s6 149 (.ANDI .x7 .x22 1#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ANDI .x7 .x22 1#12)
      have hpc7 : s7.pc = pcWord 150 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hx7_7 : s7.getReg .x7 = BitVec.ofNat 64 ((g >>> (step + 1)) % 2) := by
        simp only [s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hx22_6, se12_1]
        exact bv64_and_one _ (by omega)
      have hst190 := step_ordinary oracle s7 150 (.BEQ .x7 .x0 56#13) (by decide) hpc7 rfl (by intro h; cases h) rfl
      let s8 := execInstrBr s7 (.BEQ .x7 .x0 56#13)
      have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
      let sibD := pw.binSib (2 + step)
      have hsibD_eq : sibD = proofDigest30 s0 (11341403200 + pCur) := by
        simp only [sibD, pw, parsePartialWitness, show 2 + step ≠ 1 by omega, ite_false,
          show 2 ≤ 2 + step ∧ 2 + step ≤ 14 by omega, and_self, ite_true,
          show 2 + step - 2 = step by omega, pCur, Nat.add_assoc]
        dsimp only [g]
      let curD := pw.evalLevel c96 (2 + step)
      let inpL : BitVec 768 :=
        if (g >>> (step + 1)) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
      have hidx_pw : (pw.index.val / 3) >>> (2 + step - 1) = g >>> (step + 1) := by
        change g >>> (2 + step - 1) = g >>> (step + 1)
        exact congrArg (fun k => g >>> k) (by omega)
      have heval_next : pw.evalLevel c96 (2 + (step + 1)) = mask240 (c96 inpL) := by
        rw [show 2 + (step + 1) = (2 + step) + 1 by omega,
          evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
        dsimp only
        rw [hidx_pw, if_pos hpair, if_neg (by omega)]
      have hlinp : pw.levelInput c96 (2 + step) = [inpL] := by
        unfold WitnessPath.levelInput
        dsimp only
        rw [hidx_pw, if_pos hpair]
      -- Common compression + mask240 at pc[168..211] -> pc[172]
      have hcall208 : ∀ (s208 : MachineState) (kA : Nat),
          kA ≤ 46 →
          StepsTo oracle s8 s208 kA 0 [] →
          s208.pc = pcWord 168 →
          CheckFixedRegs s208 input.proof.length →
          MemEqOutside s s208 256 320 →
          s208.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) →
          s208.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
          s208.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
          s208.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pCur + 30)) →
          s208.getReg .x27 = BitVec.ofNat 64 rem →
          s208.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)) →
          s208.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) →
          readBuffer s208 256 96 = inpL →
          readBuffer s208 320 32 = 0 →
          PhaseOutcome oracle s 60 1 (input.proof.length < pCur + binStepBytes g step)
            (fun s' q tr =>
              q ≤ 1 ∧ pCur + binStepBytes g step ≤ input.proof.length ∧ s'.pc = (if step + 1 = 13 then pcWord 174 else pcWord 143) ∧
              CheckFixedRegs s' input.proof.length ∧ MemEqOutside s s' 256 320 ∧
              s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
              s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
              s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
              s'.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pCur + binStepBytes g step)) ∧
              s'.getReg .x27 = BitVec.ofNat 64 rem ∧
              s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
              s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
              readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
              readBuffer s' 320 32 = 0 ∧
              ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
        intro s208 kA hkA hmidA hpc208 hfix208 hout208 h22 h24 h8 h25 h27 h29 h30 hinp208 hgap208
        have hst208 := step_ordinary oracle s208 168 (.ADDI .x10 .x21 0#12) (by decide) hpc208 rfl (by intro h; cases h) rfl
        let s209 := execInstrBr s208 (.ADDI .x10 .x21 0#12)
        have hpc209 : s209.pc = pcWord 169 := by simp only [s209, execInstrBr, MachineState.setPC, hpc208, pcWord_add_four]
        have hst209 := step_ordinary oracle s209 169 (.ADDI .x12 .x21 0#12) (by decide) hpc209 rfl (by intro h; cases h) rfl
        let s210 := execInstrBr s209 (.ADDI .x12 .x21 0#12)
        have hpc210 : s210.pc = pcWord 170 := by simp only [s210, execInstrBr, MachineState.setPC, hpc209, pcWord_add_four]
        have hmem210 : s210.mem = s208.mem := by simp [s210, s209, execInstrBr, mem_setPC, mem_setReg]
        have hreg210 : ∀ r, r ≠ .x10 → r ≠ .x12 → s210.getReg r = s208.getReg r := fun r h10 h12 => by
          simp only [s210, s209, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
        have hx10_210 : s210.getReg .x10 = 256#64 := by
          simp only [s210, s209, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide), hfix208.x21, se12_0, BitVec.add_zero]
        have hx12_210 : s210.getReg .x12 = 256#64 := by
          simp only [s210, s209, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
            hfix208.x21, se12_0, BitVec.add_zero]
        have hec := step_ecall_compress h768 oracle s210 170 256 256 (by decide) hpc210 rfl
          ((hreg210 .x5 (by decide) (by decide)).trans hfix208.x5)
          ((hreg210 .x11 (by decide) (by decide)).trans hfix208.x11)
          ((hreg210 .x13 (by decide) (by decide)).trans hfix208.x13)
          hx10_210 hx12_210 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
        rw [(MemEqOutside.of_mem_eq hmem210 0 0).readBuffer_eq (by decide) (by omega), hinp208] at hec
        let s211 := writeBits s210 (BitVec.ofNat 64 256) (c96 inpL)
        have hpc211 : s211.pc = pcWord 171 := by simp only [s211, writeBits, MachineState.setPC, hpc210, pcWord_add_four]
        have hx21_211 : s211.getReg .x21 = 256#64 :=
          (writeBits_register s210 _ _ .x21).trans ((hreg210 .x21 (by decide) (by decide)).trans hfix208.x21)
        have ha211 : s211.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
          rw [hx21_211]; decide
        have hv211 : memoryArgumentsValid s211 (.SH .x21 .x0 30#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha211]
          exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; decide) (by decide)
        have hst211 := step_ordinary oracle s211 171 (.SH .x21 .x0 30#12) (by decide) hpc211 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv211])
        let s212 := execInstrBr s211 (.SH .x21 .x0 30#12)
        have hpc212 : s212.pc = pcWord 172 := by simp only [s212, execInstrBr, MachineState.setPC, hpc211, pcWord_add_four]
        have hreg212 : ∀ r, r ≠ .x10 → r ≠ .x12 → s212.getReg r = s208.getReg r := fun r h10 h12 => by
          have : s212.getReg r = s211.getReg r := by
            simp [s212, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
          exact this.trans ((writeBits_register s210 _ _ r).trans (hreg210 r h10 h12))
        have hout_sh : MemEqOutside s211 s212 286 288 := by
          intro a ha hout
          simp only [s212, execInstrBr, ha211, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s211 286 _ (by decide) (by decide) a ha hout
        have hout_212 : MemEqOutside s s212 256 320 :=
          hout208.trans ((MemEqOutside.of_mem_eq hmem210 256 320).trans
            (((MemEqOutside_writeBits_digest s210 256 _ (by decide)).mono (by omega) (by omega)).trans
              (hout_sh.mono (by omega) (by omega))))
        have hdig212 : readBuffer s212 256 32 = pw.evalLevel c96 (2 + (step + 1)) := by
          rw [heval_next]
          have hsh : readBuffer s212 256 32 =
              readBuffer (s211.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
            apply readBuffer_congr2; intro j hj
            simp [s212, execInstrBr, ha211, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [hsh, sh_zero_mask240 s211 256 (by decide) (by decide), writeBits_readBuffer_digest]
        have hgap212 : readBuffer s212 320 32 = 0 := by
          rw [hout_sh.readBuffer_eq (by decide) (by omega),
            (MemEqOutside_writeBits_digest s210 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem210 0 0).readBuffer_eq (by decide) (by omega), hgap208]
        have htot := (((hst187.trans hst188).trans (hst189.trans hst190)).trans hmidA).trans
          (((hst208.trans hst209).trans hec).trans hst211)
        refine hfooter s212 (4 + kA + 4) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
          (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
          hpc212 (hfix208.of_agree (fun r hr => hreg212 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hout_212
          ((hreg212 .x22 (by decide) (by decide)).trans h22)
          ((hreg212 .x24 (by decide) (by decide)).trans h24)
          ((hreg212 .x8  (by decide) (by decide)).trans h8)
          (by rw [hsb]; exact (hreg212 .x25 (by decide) (by decide)).trans h25)
          ((hreg212 .x27 (by decide) (by decide)).trans h27)
          ((hreg212 .x29 (by decide) (by decide)).trans h29)
          ((hreg212 .x30 (by decide) (by decide)).trans h30)
          hdig212 hgap212 ?_ (by rw [hsb]; exact hge30)
        intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
        exact InTrace.singleton h768 oracle inpL
      by_cases heven : (g >>> (step + 1)) % 2 = 0
      · -- Even: jump to pc[164..207] -> pc[168]
        have hx7z : s7.getReg .x7 = 0#64 := by rw [hx7_7, heven]
        have hpc8 : s8.pc = pcWord 164 := by
          simp only [s8, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
            MachineState.setPC, hpc7]; decide
        have hmem8 : s8.mem = s.mem := by
          simpa [s8, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem7
        have hreg87 : ∀ r, s8.getReg r = s7.getReg r := fun r => by
          simp only [s8, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        have hreg8 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s8.getReg r = s.getReg r := fun r h6 h7 h22 h28 => by
          rw [hreg87]
          simp only [s7, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
          exact hreg6 r h6 h7 h22 h28
        have hx22_8 : s8.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
          rw [hreg87]
          simp only [s7, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22), hx22_6]
        have hst204 := step_ordinary oracle s8 164 (.ADDI .x12 .x21 32#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 32#12)
        have hpc9 : s9.pc = pcWord 165 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hreg10, hcopy10, hout10⟩ :=
          step_call_read30 oracle 165 s9 (11341403200 + pCur) 288 (by decide) rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                  hreg8 .x25 (by decide) (by decide) (by decide) (by decide), hx25])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide),
                  hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        -- pc[166]: SH x21, x0, 62 (zeros bytes 256+62..256+63 = 288+30..288+31)
        have hx21_10 : s10.getReg .x21 = 256#64 := by
          rw [hreg10 .x21 (by decide) (by decide)]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21),
            hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21]
        have ha206 : s10.getReg .x21 + signExtend12 62#12 = BitVec.ofNat 64 318 := by
          rw [hx21_10]; decide
        have hv206 : memoryArgumentsValid s10 (.SH .x21 .x0 62#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha206]
          exact accessValid_ofNat 318 2 (by unfold MEMORY_BYTES; decide) (by decide)
        have hst206 := step_ordinary oracle s10 166 (.SH .x21 .x0 62#12) (by decide) hpc10 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv206])
        let s11 := execInstrBr s10 (.SH .x21 .x0 62#12)
        have hpc11 : s11.pc = pcWord 167 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
        have hst207 := step_ordinary oracle s11 167 (.ADDI .x25 .x25 30#12) (by decide) hpc11 rfl (by intro h; cases h) rfl
        let s12 := execInstrBr s11 (.ADDI .x25 .x25 30#12)
        have hpc12 : s12.pc = pcWord 168 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
        have hmem9 : s9.mem = s.mem := by simpa [s9, execInstrBr, mem_setPC, mem_setReg] using hmem8
        have hmem12 : s12.mem = s11.mem := by simp [s12, execInstrBr, mem_setPC, mem_setReg]
        have hout_sh : MemEqOutside s10 s11 318 320 := by
          intro a ha hout
          simp only [s11, execInstrBr, ha206, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s10 318 _ (by decide) (by decide) a ha hout
        have hout_all : MemEqOutside s s12 288 320 :=
          (MemEqOutside.of_mem_eq hmem9 288 320).trans
            ((hout10.mono (by omega) (by omega)).trans
              ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem12 288 320)))
        have hreg12 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x22 → r ≠ .x25 → r ≠ .x28 →
            s12.getReg r = s.getReg r := fun r h1 h6 h7 h12 h22 h25 h28 => by
          simp only [s12, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h25.symm]
          have : s11.getReg r = s10.getReg r := by
            simp [s11, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
          rw [this, hreg10 r h1 h6]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
          exact hreg8 r h6 h7 h22 h28
        have hgap12 : readBuffer s12 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp12 : readBuffer s12 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s12 256 hgap12]
          have hL : readBuffer s12 256 32 = curD :=
            (hout_all.readBuffer_eq (by decide) (by omega)).trans hcur
          have hR : readBuffer s12 288 32 = sibD := by
            rw [hsibD_eq, (MemEqOutside.of_mem_eq hmem12 0 0).readBuffer_eq (by decide) (by omega)]
            have hsh_eq : readBuffer s11 288 32 =
                readBuffer (s10.setHalfword (BitVec.ofNat 64 (288 + 30)) 0#16) 288 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s11, execInstrBr, ha206, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh_eq]
            apply sh_zero_readBuffer30 s10 s0 288 (11341403200 + pCur) (by decide) (by decide)
            intro j hj
            have hc := hcopy10 j hj
            simp only [MachineState.getByte, MachineState.getMem, hmem9] at hc ⊢
            exact hc.trans (hhigh (11341403200 + pCur + j) (by omega) (by omega))
          rw [hL, hR]; simp only [inpL, heven, ite_true]
        refine hcall208 s12 35 (by decide)
          (by simpa using (hst204.trans hs10).trans (hst206.trans hst207)) hpc12
          (hfix.of_agree (fun r hr => hreg12 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          (hout_all.mono (by omega) (by omega))
          (by simp only [s12, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x22)]
              have : s11.getReg .x22 = s10.getReg .x22 := by
                simp [s11, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
              rw [this, hreg10 .x22 (by decide) (by decide)]
              simp only [s9, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x22), hx22_8])
          ((hreg12 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg12 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          (by simp only [s12, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide)]
              have : s11.getReg .x25 = s10.getReg .x25 := by
                simp [s11, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
              rw [this, hreg10 .x25 (by decide) (by decide)]
              simp only [s9, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg8 .x25 (by decide) (by decide) (by decide) (by decide), hx25,
                se12_30_ofNat]
              change BitVec.ofNat 64 (11341403200 + pCur) + BitVec.ofNat 64 30 = _
              rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega))
          ((hreg12 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg12 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg12 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp12 hgap12
      · -- Odd: fall through to pc[151..203] -> pc[168]
        have hodd : (g >>> (step + 1)) % 2 = 1 := by omega
        have hx7o : s7.getReg .x7 = 1#64 := by rw [hx7_7, hodd]
        have hpc8 : s8.pc = pcWord 151 := by
          simp only [s8, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc7, pcWord_add_four]
        have hmem8 : s8.mem = s.mem := by
          simpa [s8, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            MachineState.setPC] using hmem7
        have hreg87 : ∀ r, s8.getReg r = s7.getReg r := fun r => by
          simp only [s8, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        have hreg8 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s8.getReg r = s.getReg r := fun r h6 h7 h22 h28 => by
          rw [hreg87]
          simp only [s7, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
          exact hreg6 r h6 h7 h22 h28
        have hx22_8 : s8.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
          rw [hreg87]
          simp only [s7, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22), hx22_6]
        have hcp : ∀ j < 4,
            checkInstr (151 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (151 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s9, hs9, hpc9, hreg9, hcopy9, hout9⟩ :=
          step_copy_dwords oracle 151 4 .x21 .x21 0 32 s8 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp hpc8
            ((hreg8 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
            ((hreg8 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
            (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
        have hst199 := step_ordinary oracle s9 159 (.ADDI .x12 .x21 0#12) (by decide) hpc9 rfl (by intro h; cases h) rfl
        let s10 := execInstrBr s9 (.ADDI .x12 .x21 0#12)
        have hpc10 : s10.pc = pcWord 160 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
        obtain ⟨s11, hs11, hpc11, hreg11, hcopy11, hout11⟩ :=
          step_call_read30 oracle 160 s10 (11341403200 + pCur) 256 (by decide) rfl hpc10
            (by simp only [s10, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg9 .x25 (by decide),
                  hreg8 .x25 (by decide) (by decide) (by decide) (by decide), hx25])
            (by simp only [s10, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg9 .x21 (by decide),
                  hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hx21_11 : s11.getReg .x21 = 256#64 := by
          rw [hreg11 .x21 (by decide) (by decide)]
          simp only [s10, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg9 .x21 (by decide),
            hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21]
        have ha201 : s11.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
          rw [hx21_11]; decide
        have hv201 : memoryArgumentsValid s11 (.SH .x21 .x0 30#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha201]
          exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; decide) (by decide)
        have hst201 := step_ordinary oracle s11 161 (.SH .x21 .x0 30#12) (by decide) hpc11 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv201])
        let s12 := execInstrBr s11 (.SH .x21 .x0 30#12)
        have hpc12 : s12.pc = pcWord 162 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
        have hst202 := step_ordinary oracle s12 162 (.ADDI .x25 .x25 30#12) (by decide) hpc12 rfl (by intro h; cases h) rfl
        let s13 := execInstrBr s12 (.ADDI .x25 .x25 30#12)
        have hpc13 : s13.pc = pcWord 163 := by simp only [s13, execInstrBr, MachineState.setPC, hpc12, pcWord_add_four]
        have hst203 := step_ordinary oracle s13 163 (.JAL .x0 20#21) (by decide) hpc13 rfl (by intro h; cases h) rfl
        let s14 := execInstrBr s13 (.JAL .x0 20#21)
        have hpc14 : s14.pc = pcWord 168 := by simp only [s14, execInstrBr, MachineState.setPC, hpc13]; decide
        have hmem10 : s10.mem = s9.mem := by simp [s10, execInstrBr, mem_setPC, mem_setReg]
        have hmem14 : s14.mem = s12.mem := by simp [s14, s13, execInstrBr, mem_setPC, mem_setReg]
        have hout_sh : MemEqOutside s11 s12 286 288 := by
          intro a ha hout
          simp only [s12, execInstrBr, ha201, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s11 286 _ (by decide) (by decide) a ha hout
        have hout_all : MemEqOutside s s14 256 320 :=
          (MemEqOutside.of_mem_eq hmem8 256 320).trans
            ((hout9.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem10 256 320).trans
                ((hout11.mono (by omega) (by omega)).trans
                  ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem14 256 320)))))
        have hreg14 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x22 → r ≠ .x25 → r ≠ .x28 →
            s14.getReg r = s.getReg r := fun r h1 h6 h7 h12 h22 h25 h28 => by
          have : s14.getReg r = s13.getReg r := by simp [s14, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [this]
          simp only [s13, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h25.symm]
          have h12_11 : s12.getReg r = s11.getReg r := by
            simp [s12, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
          rw [h12_11, hreg11 r h1 h6]
          simp only [s10, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg9 r h6]
          exact hreg8 r h6 h7 h22 h28
        have hgap14 : readBuffer s14 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp14 : readBuffer s14 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s14 256 hgap14]
          have hL : readBuffer s14 256 32 = sibD := by
            rw [hsibD_eq, (MemEqOutside.of_mem_eq hmem14 0 0).readBuffer_eq (by decide) (by omega)]
            have hsh_eq : readBuffer s12 256 32 =
                readBuffer (s11.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s12, execInstrBr, ha201, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh_eq]
            apply sh_zero_readBuffer30 s11 s0 256 (11341403200 + pCur) (by decide) (by decide)
            intro j hj
            have h10s : MemEqOutside s s10 288 320 :=
              (MemEqOutside.of_mem_eq hmem8 288 320).trans (hout9.trans (MemEqOutside.of_mem_eq hmem10 288 320))
            exact (hcopy11 j hj).trans
              ((h10s (11341403200 + pCur + j) (by omega) (by omega)).trans
                (hhigh (11341403200 + pCur + j) (by omega) (by omega)))
          have hcur' : readBuffer s 256 32 = curD := hcur
          have hR : readBuffer s14 288 32 = curD := by
            rw [(MemEqOutside.of_mem_eq hmem14 0 0).readBuffer_eq (by decide) (by omega),
              hout_sh.readBuffer_eq (by decide) (by omega),
              hout11.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem10 0 0).readBuffer_eq (by decide) (by omega), ← hcur']
            apply readBuffer_congr2; intro j hj
            have hc := hcopy9 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem8] at hc ⊢
            exact hc
          rw [hL, hR]; simp only [inpL, heven, ite_false]
        refine hcall208 s14 44 (by decide)
          (by simpa using ((hs9.trans hst199).trans hs11).trans ((hst201.trans hst202).trans hst203)) hpc14
          (hfix.of_agree (fun r hr => hreg14 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hout_all
          (by have : s14.getReg .x22 = s13.getReg .x22 := by simp [s14, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
              rw [this]; simp only [s13, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x22)]
              have h12_11 : s12.getReg .x22 = s11.getReg .x22 := by
                simp [s12, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
              rw [h12_11, hreg11 .x22 (by decide) (by decide)]
              simp only [s10, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x22), hreg9 .x22 (by decide), hx22_8])
          ((hreg14 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg14 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          (by have : s14.getReg .x25 = s13.getReg .x25 := by simp [s14, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
              rw [this]; simp only [s13, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide)]
              have h12_11 : s12.getReg .x25 = s11.getReg .x25 := by
                simp [s12, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
              rw [h12_11, hreg11 .x25 (by decide) (by decide)]
              simp only [s10, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg9 .x25 (by decide),
                hreg8 .x25 (by decide) (by decide) (by decide) (by decide), hx25,
                se12_30_ofNat]
              change BitVec.ofNat 64 (11341403200 + pCur) + BitVec.ofNat 64 30 = _
              rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega))
          ((hreg14 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg14 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg14 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp14 hgap14
  · -- Promoted (unpaired): binStepBytes g step = 0, jump directly to pc[172]
    have hsb : binStepBytes g step = 0 := by unfold binStepBytes; exact if_neg hpair
    have hpc4 : s4.pc = pcWord 172 := by
      simp only [s4, execInstrBr, hult186, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc3]; decide
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult186, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult186, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
      simpa [s4, execInstrBr, hult186, hpair, MachineState.getReg_setPC] using hx22_3
    have hidx_pw : (pw.index.val / 3) >>> (2 + step - 1) = g >>> (step + 1) := by
      change g >>> (2 + step - 1) = g >>> (step + 1)
      exact congrArg (fun k => g >>> k) (by omega)
    have heval_same : pw.evalLevel c96 (2 + (step + 1)) = pw.evalLevel c96 (2 + step) := by
      rw [show 2 + (step + 1) = (2 + step) + 1 by omega,
        evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_neg hpair]
    have hlinp_nil : pw.levelInput c96 (2 + step) = [] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_neg hpair]
    refine hfooter s4 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s4) hpc4
      (hfix.of_agree (fun r hr => hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (MemEqOutside.of_mem_eq hmem4 256 320) hx22_4
      ((hreg4 .x24 (by decide) (by decide) (by decide)).trans hx24)
      ((hreg4 .x8  (by decide) (by decide) (by decide)).trans hx8)
      (by rw [hsb, Nat.add_zero]; exact (hreg4 .x25 (by decide) (by decide) (by decide)).trans hx25)
      ((hreg4 .x27 (by decide) (by decide) (by decide)).trans hx27)
      ((hreg4 .x29 (by decide) (by decide) (by decide)).trans hx29)
      ((hreg4 .x30 (by decide) (by decide) (by decide)).trans hx30)
      (by rw [heval_same]; exact ((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hcur)
      (((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
      (by rw [hlinp_nil]; simp) (by rw [hsb, Nat.add_zero]; exact hple)

/-- Phase 1D: entire L2..L14 binary loop (`pc[141..213]` -> `pc[174]`). -/
theorem step_pos_bin_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff rem : Nat) (hord : ord < input.positions.card)
    (hpeven : pOff % 2 = 0)
    (hple : pOff + 24 + l0Bytes (posAt input.positions ord) + 32 ≤ input.proof.length)
    (s : MachineState) (hpc : s.pc = pcWord 141)
    (hfix : CheckFixedRegs s input.proof.length)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pOff + 24 + l0Bytes (posAt input.positions ord) + 32)))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl2 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) pOff (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 2)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pw := parsePartialWitness s0 pOff i (valAt input ord)
    PhaseOutcome oracle s 782 13 (input.proof.length < pOff + recordLen i)
      (fun s' q tr =>
        q ≤ 13 ∧
        pOff + recordLen i ≤ input.proof.length ∧
        s'.pc = pcWord 174 ∧
        CheckFixedRegs s' input.proof.length ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> 13) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pOff + recordLen i)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 15 ∧
        ∀ prev, 2 ≤ prev → prev ≤ 14 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g pw
  -- pc[141]: ADDI x29, x2, 64; pc[142]: ADDI x30, x2, 480
  have hst181 := step_ordinary oracle s 141 (.ADDI .x29 .x2 64#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x29 .x2 64#12)
  have hpc1 : s1.pc = pcWord 142 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst182 := step_ordinary oracle s1 142 (.ADDI .x30 .x2 480#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x30 .x2 480#12)
  have hpc2 : s2.pc = pcWord 143 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x29 → r ≠ .x30 → s2.getReg r = s.getReg r := fun r h29 h30 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h30.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h29.symm]
  have hx29_2 : s2.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 2) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x29), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hfix.x2, se12_64]
    change BitVec.ofNat 64 68719475936 + BitVec.ofNat 64 64 = _
    rw [bv64_add]
  have hx30_2 : s2.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x2),
      hfix.x2, se12_480]
    rw [bv64_add]
  have hloop : ∀ m ≤ 13,
      PhaseOutcome oracle s2 (60 * m) m
        (input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g m)
        (fun s' q tr =>
          q ≤ m ∧
          s'.pc = (if m = 13 then pcWord 174 else pcWord 143) ∧
          CheckFixedRegs s' input.proof.length ∧
          MemEqOutside s2 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> m) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pOff + 24 + l0Bytes i + 32 + binPathOff g m)) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + m)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
          (pOff + 24 + l0Bytes i + 32 + binPathOff g m ≤ input.proof.length) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + m) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev, 2 ≤ prev → prev < 2 + m → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
    intro m hm
    induction m with
    | zero =>
      exact .continued s2 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s2)
        ⟨by decide, by simpa using hpc2,
         hfix.of_agree (fun r hr => hreg2 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         MemEqOutside.refl s2 256 320,
         (hreg2 .x22 (by decide) (by decide)).trans hx22,
         (hreg2 .x24 (by decide) (by decide)).trans hx24,
         (hreg2 .x8  (by decide) (by decide)).trans hx8,
         (hreg2 .x25 (by decide) (by decide)).trans hx25,
         (hreg2 .x27 (by decide) (by decide)).trans hx27,
         hx29_2, hx30_2, hple,
         ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hl2,
         ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hgap,
         fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have hbin_mon : binPathOff g k ≤ binPathOff g (k + 1) := by simp only [binPathOff]; omega
      rw [show 60 * (k + 1) = 60 * k + 60 by omega]
      refine (ih (by omega)).bind_dep
        (fun hlt => by simp only [binPathOff]; omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hout_k, hx22_k, hx24_k, hx8_k, hx25_k, hx27_k,
            hx29_k, hx30_k, hple_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne13 : k ≠ 13 := by omega
          simp only [hne13, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem2 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
          have hstep_k := step_pos_bin_iter h768 oracle input hvalid ord pOff rem k hord (by omega)
            hpeven hple_k sk hpc_k hfix_k hhigh_k hx22_k hx24_k hx8_k hx25_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega)
            (fun hlt => by
              change input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g k + binStepBytes g k at hlt
              simp only [binPathOff]; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hple', hpc', hfix', hout', hx22', hx24', hx8', hx25', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', hout_k.trans hout', hx22', hx24', hx8', ?_, hx27', hx29', hx30', ?_, hdig', hgap', ?_⟩
          · simpa [binPathOff, Nat.add_assoc] using hx25'
          · simpa [binPathOff, Nat.add_assoc] using hple'
          · intro prev hp1 hp2 x hx
            by_cases hprev : prev < 2 + k
            · exact (htr_k prev hp1 hprev x hx).append_left
            · have : prev = 2 + k := by omega
              subst this; exact (htr' x hx).append_right)
  have h13 := hloop 13 (by decide)
  have hpre : StepsTo oracle s s2 2 0 [] := by simpa using hst181.trans hst182
  cases h13 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (2 + k) q tr (by simpa [recordLen, Nat.add_assoc] using hr) (by omega) hq
      (by simpa using hpre.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hout', hx22', hx24', hx8', hx25', hx27', _, _, hple', hdig', _, htr'⟩ := hp
    refine .continued s' (2 + k) q tr (by omega) hq (by simpa using hpre.trans hs)
      ⟨hq', by simpa [recordLen, Nat.add_assoc] using hple', by simpa using hpc', hfix',
       (MemEqOutside.of_mem_eq hmem2 256 320).trans hout',
       hx22', hx24', hx8', by simpa [recordLen, Nat.add_assoc] using hx25', hx27', hdig',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-! #### Phase 1E and Full Per-Position Loop (`pc[174..248]`, `pc[17] -> pc[209]`) -/

theorem gapOffset_disjoint {a b : Nat} (hne : a ≠ b) :
    gapOffset a + 32 ≤ gapOffset b ∨ gapOffset b + 32 ≤ gapOffset a := by
  unfold gapOffset; omega

theorem gapOffset_disjoint_gap (c q : Nat) :
    gapOffset c + 32 ≤ 96 * q + 64 ∨ 96 * q + 96 ≤ gapOffset c := by
  unfold gapOffset; omega

private def capAddrInstrs : List Instr :=
  [.SRLI .x22 .x22 1#6, .SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6,
   .SLLI .x6 .x6 5#6, .ADD .x28 .x19 .x6, .ADD .x29 .x18 .x22]

private theorem pc_248_branch : pcWord 208 + signExtend13 7428#13 = pcWord 17 := by decide
private theorem pc_232_jal : pcWord 192 + signExtend21 52#21 = pcWord 205 := by decide
private theorem pc_221_branch : pcWord 181 + signExtend13 48#13 = pcWord 193 := by decide
private theorem checkInstr_220 : checkInstr 180 = .base (.LBU .x7 .x29 0#12) := rfl
private theorem checkInstr_221 : checkInstr 181 = .base (.BNE .x7 .x0 48#13) := rfl
private theorem checkInstr_222 : checkInstr 182 = .base (.ADDI .x7 .x0 1#12) := rfl
private theorem checkInstr_223 : checkInstr 183 = .base (.SB .x29 .x7 0#12) := rfl
private theorem checkInstr_232 : checkInstr 192 = .base (.JAL .x0 52#21) := rfl
private theorem checkInstr_245 : checkInstr 205 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_246 : checkInstr 206 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_247 : checkInstr 207 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_248 : checkInstr 208 = .base (.BNE .x27 .x0 7428#13) := rfl

private theorem ordinaryStep_ADDI (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    ordinaryStep st (.base (.ADDI rd rs imm)) = some (execInstrBr st (.ADDI rd rs imm)) := rfl

private theorem ordinaryStep_BNE (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    ordinaryStep st (.base (.BNE r1 r2 off)) = some (execInstrBr st (.BNE r1 r2 off)) := rfl

private theorem execInstrBr_ADDI_pc (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr st (.ADDI rd rs imm)).pc = st.pc + (4 : Word) := rfl

private theorem execInstrBr_ADDI_mem (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr st (.ADDI rd rs imm)).mem = st.mem :=
  (mem_setPC _ _).trans (mem_setReg _ _ _)

private theorem execInstrBr_ADDI_getReg_eq (st : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (hne : rd ≠ .x0) :
    (execInstrBr st (.ADDI rd rs imm)).getReg rd = st.getReg rs + signExtend12 imm := by
  simp only [execInstrBr, MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_eq hne

private theorem execInstrBr_ADDI_getReg_ne (st : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (r : Reg) (hne : rd ≠ r) :
    (execInstrBr st (.ADDI rd rs imm)).getReg r = st.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_ne _ _ _ _ hne

private theorem execInstrBr_BNE_mem (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    (execInstrBr st (.BNE r1 r2 off)).mem = st.mem := by
  simp only [execInstrBr]; split <;> rfl

private theorem execInstrBr_BNE_getReg (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr st (.BNE r1 r2 off)).getReg r = st.getReg r := by
  simp only [execInstrBr]; split <;> simp only [MachineState.getReg_setPC]

private theorem execInstrBr_BNE_pc_false (st : MachineState) (r1 r2 : Reg) (off : BitVec 13)
    (h : (st.getReg r1 != st.getReg r2) = false) :
    (execInstrBr st (.BNE r1 r2 off)).pc = st.pc + (4 : Word) := by
  simp only [execInstrBr, h, Bool.false_eq_true, ite_false, MachineState.setPC]

private theorem execInstrBr_BNE_pc_true (st : MachineState) (r1 r2 : Reg) (off : BitVec 13)
    (h : (st.getReg r1 != st.getReg r2) = true) :
    (execInstrBr st (.BNE r1 r2 off)).pc = st.pc + signExtend13 off := by
  simp only [execInstrBr, h, ite_true, MachineState.setPC]

private theorem bv64_add_mul_step (base step n : Nat) :
    BitVec.ofNat 64 (base + step * n) + BitVec.ofNat 64 step =
      BitVec.ofNat 64 (base + step * (n + 1)) :=
  (bv64_add (base + step * n) step).trans
    (congrArg (BitVec.ofNat 64)
      ((Nat.add_assoc base (step * n) step).trans
        (congrArg (base + ·)
          ((congrArg (step * n + ·) (Nat.mul_one step).symm).trans
            (Nat.mul_add step n 1).symm))))

private theorem se12_8_ofNat : signExtend12 8#12 = BitVec.ofNat 64 8 :=
  signExtend12_ofNat_lt2048 8 (by decide)

private theorem hcode_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    checkInstr (174 + j) = .base (capAddrInstrs[j]'hj) := by
  intro j hj; have hj' : j < 6 := hj; interval_cases j <;> rfl

private theorem hpure_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    Instruction.base (capAddrInstrs[j]'hj) ≠ .base .ECALL ∧
    ∀ st, ordinaryStep st (.base (capAddrInstrs[j]'hj)) = some (execInstrBr st (capAddrInstrs[j]'hj)) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).mem = st.mem := by
  intro j hj; have hj' : j < 6 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩

private theorem hcode_capCopy : ∀ j < 4,
    checkInstr (184 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
    checkInstr (184 + 2 * j + 1) = .base (.SD .x28 .x6 (BitVec.ofNat 12 (0 + 8 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem hcode_capCmp : ∀ j < 4,
    checkInstr (193 + 3 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (193 + 3 * j + 1) = .base (.LD .x7 .x28 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (193 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (296 - (193 + 3 * j + 2))))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

private theorem zero64_eq_ofNat : (0#64 : Word) = BitVec.ofNat 64 0 := rfl

private theorem zero_lt_pow64 : 0 < 2 ^ 64 := Nat.pow_pos (Nat.succ_pos 1)

private theorem step_tail_245 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 205)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 206 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 205 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_245
     (by intro h; cases h) (ordinaryStep_ADDI s .x24 .x24 8#12),
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 205)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (6912218176 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 6912218176 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_246 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 206)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (7046435904 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 207 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 206 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_246
     (by intro h; cases h) (ordinaryStep_ADDI s .x8 .x8 256#12),
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 206)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (7046435904 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 7046435904 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_247 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 207)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 208 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 207 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_247
     (by intro h; cases h) (ordinaryStep_ADDI s .x27 .x27 4095#12),
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 207)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_tail_248 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 208)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 209 else pcWord 17) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x27 .x0 7428#13),
    step_ordinary oracle s 208 (.BNE .x27 .x0 7428#13) (by decide) hpc checkInstr_248
      (by intro h; cases h) (ordinaryStep_BNE s .x27 .x0 7428#13),
    ?_, execInstrBr_BNE_mem s .x27 .x0 7428#13, execInstrBr_BNE_getReg s .x27 .x0 7428#13⟩
  have hne_iff : (s.getReg .x27 != s.getReg .x0) = decide (rem1 ≠ 0) := by
    rw [getReg_x0 s, zero64_eq_ofNat, h27]
    exact bv64_bne_eq rem1 0 hrem_lt zero_lt_pow64
  by_cases hz : rem1 = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x27 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false s .x27 .x0 7428#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 208))
  · rw [if_neg hz]
    have ht : (s.getReg .x27 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true s .x27 .x0 7428#13 ht).trans
      ((congrArg (· + signExtend13 7428#13) hpc).trans pc_248_branch)

private theorem step_pos_cap_store_tail (oracle : Oracle) (proofLen ord pOffNext rem1 : Nat)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s245 : MachineState) (hpc245 : s245.pc = pcWord 205)
    (hfix245 : CheckFixedRegs s245 proofLen)
    (h24 : s245.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (h8  : s245.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (h25 : s245.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOffNext))
    (h27 : s245.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s245 sFin 4 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 209 else pcWord 17) ∧
      CheckFixedRegs sFin proofLen ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
      sFin.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOffNext) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s245.mem := by
  obtain ⟨s246, hs1, hpc246, hmem1, hx24_1, hreg1⟩ := step_tail_245 oracle ord s245 hpc245 h24
  obtain ⟨s247, hs2, hpc247, hmem2, hx8_2, hreg2⟩ :=
    step_tail_246 oracle ord s246 hpc246 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s248, hs3, hpc248, hmem3, hx27_3, hreg3⟩ :=
    step_tail_247 oracle rem1 s247 hpc247 ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27))
  obtain ⟨sFin, hs4, hpcFin, hmem4, hreg4⟩ :=
    step_tail_248 oracle rem1 (Nat.lt_of_succ_lt hrem_lt) s248 hpc248 hx27_3
  have hsteps : StepsTo oracle s245 sFin 4 0 [] :=
    (((hs1.trans hs2).trans hs3).trans hs4).eq_of rfl rfl rfl rfl
  have hmemFin : sFin.mem = s245.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x27 → sFin.getReg r = s245.getReg r :=
    fun r h24r h8r h27r => (hreg4 r).trans ((hreg3 r h27r).trans ((hreg2 r h8r).trans (hreg1 r h24r)))
  exact ⟨sFin, hsteps, hpcFin,
    hfix245.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    (hreg4 .x24).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1)),
    (hreg4 .x8).trans ((hreg3 .x8 (by decide)).trans hx8_2),
    (hregFin .x25 (by decide) (by decide) (by decide)).trans h25,
    (hreg4 .x27).trans hx27_3, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 342)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 182) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 256#64)
    (hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c))
    (hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c))
    (d15 : Digest) (hd15 : readBuffer s 256 32 = d15) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 205 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
      readBuffer s7 (8192 + gapOffset c) 32 = d15 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
        (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst222 := step_ordinary oracle s3 182 (.ADDI .x7 .x0 1#12) (by decide) hpc3 checkInstr_222 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 183 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx29_4 : s4.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha223 : s4.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_4, se12_0, BitVec.add_zero]
  have hv223 : memoryArgumentsValid s4 (.SB .x29 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha223]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst223 := step_ordinary oracle s4 183 (.SB .x29 .x7 0#12) (by decide) hpc4 checkInstr_223 (by intro h; cases h)
    (by simp [ordinaryStep, hv223])
  let s5 := execInstrBr s4 (.SB .x29 .x7 0#12)
  have hpc5 : s5.pc = pcWord 184 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (4096 + c)) 1#8).getByte q := by
    intro q
    simp only [s5, execInstrBr, ha223, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
      MachineState.getByte, MachineState.setByte, MachineState.getMem,
      MachineState.setMem, mem_setPC, hmem4]
  have hout5 : MemEqOutside s s5 (4096 + c) (4096 + c + 1) := by
    intro a ha hout
    rw [hbyte5]
    exact MemEqOutside_setByte s (4096 + c) 1#8 (by omega) a ha hout
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s5.getReg r = s.getReg r :=
    fun r h6 h7 h22 h28 h29 => by
      have : s5.getReg r = s4.getReg r := by
        simp [s5, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [this]
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg3 r h6 h7 h22 h28 h29
  have hx28_5 : s5.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
    have : s5.getReg .x28 = s4.getReg .x28 := by
      simp [s5, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    rw [this]
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_3]
  have hgo_al : gapOffset c % 8 = 0 := by unfold gapOffset; omega
  have hgo_bd : 8192 + gapOffset c + 32 ≤ MEMORY_BYTES := by
    unfold gapOffset MEMORY_BYTES; omega
  obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
    step_copy_dwords oracle 184 4 .x21 .x28 0 0 s5 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCopy hpc5
      ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21)
      hx28_5 (by decide) (by omega) (by unfold MEMORY_BYTES; decide) (by omega) (by omega)
  have hst232 := step_ordinary oracle s6 192 (.JAL .x0 52#21) (by decide) hpc6 checkInstr_232 (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 205 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_232_jal
  have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
  have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r :=
    fun r h6 h7 h22 h28 h29 => by
      have : s7.getReg r = s6.getReg r := by simp [s7, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
      exact this.trans ((hreg6 r h6).trans (hreg5 r h6 h7 h22 h28 h29))
  have hm7 : s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 := by
    have : s7.getByte (BitVec.ofNat 64 (4096 + c)) = s6.getByte (BitVec.ofNat 64 (4096 + c)) := by
      simp [MachineState.getByte, MachineState.getMem, hmem7]
    rw [this, hout6 (4096 + c) (by omega) (by omega), hbyte5, set_byte_read]
    simp only [ite_true]
  have hv7 : readBuffer s7 (8192 + gapOffset c) 32 = d15 := by
    rw [(MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← hd15]
    apply readBuffer_congr2; intro j hj
    have hc := hcopy6 j hj
    simp only [Nat.add_zero] at hc
    rw [hc]
    exact hout5 (256 + j) (by omega) (by omega)
  refine ⟨s7, by simpa using ((hst222.trans hst223).trans hs6).trans hst232, hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1E: store or duplicate-check cap leaf at L15 and advance loop counters (`pc[174..248]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext rem1 : Nat) (hord : ord < input.positions.card)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 174)
    (hfix : CheckFixedRegs s input.proof.length)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> 13))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOffNext))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1))
    (marked : Bool)
    (hmark : s.getByte (BitVec.ofNat 64 (4096 + capLeafOf (posAt input.positions ord))) =
      if marked then 1#8 else 0#8)
    (d15 : Digest) (hd15 : readBuffer s 256 32 = d15) :
    let c := capLeafOf (posAt input.positions ord)
    PhaseOutcome oracle s 30 0
      (marked = true ∧ d15 ≠ readBuffer s (8192 + gapOffset c) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = (if rem1 = 0 then pcWord 209 else pcWord 17) ∧
        CheckFixedRegs s' input.proof.length ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
        s'.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOffNext) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
        readBuffer s' (8192 + gapOffset c) 32 = d15 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
          (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro c
  have hc_lt : c < 342 := capLeafOf_lt (posAt input.positions ord)
  have hi_lt : (posAt input.positions ord).val < 16777216 := (posAt input.positions ord).isLt
  have h13_lt : ((posAt input.positions ord).val / 3) >>> 13 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_shr : (((posAt input.positions ord).val / 3) >>> 13) / 2 = c := by
    unfold c capLeafOf
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul, show (2 ^ 13 : Nat) * 2 = 2 ^ 14 by decide]
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 174 capAddrInstrs s (by decide) hcode_capAddr hpure_capAddr hpc
  let s1 := runInstrs s capAddrInstrs
  have hs1 : StepsTo oracle s s1 6 0 [] := hs1
  have hpc1 : s1.pc = pcWord 180 := hpc1
  have hmem1' : s1.mem = s.mem := hmem1
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
    have hcomp : (8192#64 : Word) + ((BitVec.ofNat 64 c + (BitVec.ofNat 64 c >>> 1)) <<< 5) =
        BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [bv64_shr c 1 (by omega), Nat.pow_one, bv64_add, bv64_shl _ 5 (by omega)]
      change BitVec.ofNat 64 8192 + BitVec.ofNat 64 ((c + c / 2) * 32) = _
      rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by unfold gapOffset; omega)
    have hx22_a : (s.getReg .x22 >>> 1) = BitVec.ofNat 64 c := by
      rw [hx22, bv64_shr _ 1 h13_lt, Nat.pow_one, hc_shr]
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22_a, hfix.x19,
      show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide] using hcomp
  have hx29_1 : s1.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    have hcomp : (4096#64 : Word) + BitVec.ofNat 64 c = BitVec.ofNat 64 (4096 + c) := by
      change BitVec.ofNat 64 4096 + BitVec.ofNat 64 c = _; exact bv64_add 4096 c
    have hx22_a : (s.getReg .x22 >>> (1#6 : BitVec 6).toNat) = BitVec.ofNat 64 c := by
      rw [hx22, show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr _ 1 h13_lt, Nat.pow_one, hc_shr]
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22_a, hfix.x18] using hcomp
  have hreg1 : ∀ r, r ≠ .x6 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s1.getReg r = s.getReg r :=
    fun r h6 h22 h28 h29 => by
      simp only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h29.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
  -- pc[180]: LBU x7, 0(x29)
  have ha220 : s1.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_1, se12_0, BitVec.add_zero]
  have hv220 : memoryArgumentsValid s1 (.LBU .x7 .x29 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha220]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst220 := step_ordinary oracle s1 180 (.LBU .x7 .x29 0#12) (by decide) hpc1 checkInstr_220 (by intro h; cases h)
    (by simp [ordinaryStep, hv220])
  let s2 := execInstrBr s1 (.LBU .x7 .x29 0#12)
  have hpc2 : s2.pc = pcWord 181 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1'
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha220]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s1.getByte (BitVec.ofNat 64 (4096 + c)) = if marked then 1#8 else 0#8 := by
      simpa only [c, MachineState.getByte, MachineState.getMem, hmem1'] using hmark
    rw [hb, bool_byte_zeroExtend]
  have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s2.getReg r = s.getReg r :=
    fun r h6 h7 h22 h28 h29 => by
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg1 r h6 h22 h28 h29
  -- pc[181]: BNE x7, x0, pc[193]
  have hst221 := step_ordinary oracle s2 181 (.BNE .x7 .x0 48#13) (by decide) hpc2 checkInstr_221 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 8 0 [] := by simpa using hs1.trans (hst220.trans hst221)
  cases marked with
  | false =>
    have hpc3 : s3.pc = pcWord 182 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
        ite_false, MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, MachineState.setPC] using hmem2
    have hreg3s : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, MachineState.getReg_setPC]
    have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [hreg3s]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
    have hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
      rw [hreg3s]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_1]
    obtain ⟨s7, hs7, hpc7, hreg7, hm7, hv7, hout7⟩ :=
      step_pos_cap_store_first oracle c hc_lt s s3 hpc3 hmem3
        (fun r h6 h7 h22 h28 h29 => (hreg3s r).trans (hreg2 r h6 h7 h22 h28 h29))
        hfix.x21 hx28_3 hx29_3 d15 hd15
    have hfix7 : CheckFixedRegs s7 input.proof.length :=
      hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    obtain ⟨sFin, hsFin, hpcFin, hfixFin, hx24Fin, hx8Fin, hx25Fin, hx27Fin, hmemFin⟩ :=
      step_pos_cap_store_tail oracle input.proof.length ord pOffNext rem1 hrem_lt s7 hpc7 hfix7
        ((hreg7 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7 .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25)
        ((hreg7 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
    exact .continued sFin 23 0 [] (by decide) (by decide)
      (by simpa using (hs03.trans hs7).trans hsFin)
      ⟨rfl, rfl, hpcFin, hfixFin, hx24Fin, hx8Fin, hx25Fin, hx27Fin,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hm7,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)).trans hv7,
       fun a ha hne hout => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout7 a ha hne hout,
       fun h => by cases h⟩
  | true =>
    have hpc3 : s3.pc = pcWord 193 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_221_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.setPC] using hmem2
    have hreg3 : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.getReg_setPC]
    have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [hreg3]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
    have hcmp := step_compare4 oracle 193 .x21 .x28 s3 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCmp hpc3
      ((hreg3 .x21).trans ((hreg2 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
      hx28_3 (by decide) (by unfold gapOffset; omega)
      (by unfold MEMORY_BYTES; decide) (by unfold gapOffset MEMORY_BYTES; omega)
    have hrb_s3_a : readBuffer s3 256 32 = d15 :=
      ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hd15
    have hrb_s3_b : readBuffer s3 (8192 + gapOffset c) 32 = readBuffer s (8192 + gapOffset c) 32 :=
      (MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)
    cases hcmp with
    | rejected k q tr hr hk hq hh =>
      rw [hrb_s3_a, hrb_s3_b] at hr
      exact .rejected (8 + k) q tr ⟨rfl, hr⟩ (by omega) hq
        (by simpa using hs03.halt hh)
    | continued s4 k q tr hk hq hs4 hp4 =>
      obtain ⟨rfl, rfl, heq_dig, hpc4, hmem4, hreg4⟩ := hp4
      rw [hrb_s3_a, hrb_s3_b] at heq_dig
      have hmem4s : s4.mem = s.mem := hmem4.trans hmem3
      have hreg4s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s4.getReg r = s.getReg r :=
        fun r h6 h7 h22 h28 h29 => (hreg4 r h6 h7).trans ((hreg3 r).trans (hreg2 r h6 h7 h22 h28 h29))
      have hfix4 : CheckFixedRegs s4 input.proof.length :=
        hfix.of_agree (fun r hr => hreg4s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, hx24Fin, hx8Fin, hx25Fin, hx27Fin, hmemFin⟩ :=
        step_pos_cap_store_tail oracle input.proof.length ord pOffNext rem1 hrem_lt s4 hpc4 hfix4
          ((hreg4s .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg4s .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg4s .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25)
          ((hreg4s .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
      have hmemFins : sFin.mem = s.mem := hmemFin.trans hmem4s
      exact .continued sFin (8 + k + 4) 0 [] (by omega) (by decide)
        (by simpa [Nat.add_assoc] using (hs03.trans hs4).trans hsFin)
        ⟨rfl, rfl, hpcFin, hfixFin, hx24Fin, hx8Fin, hx25Fin, hx27Fin,
         by simpa [MachineState.getByte, MachineState.getMem, hmemFins] using hmark,
         by rw [(MemEqOutside.of_mem_eq hmemFins 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← heq_dig],
         fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmemFins],
         fun _ => hmemFins⟩

/-! #### Per-Position Loop Invariant and Induction (`pc[17] -> pc[209]`) -/

def posMarked15 (positions : Positions) (n c : Nat) : Bool :=
  decide (∃ j < n, capLeafOf (posAt positions j) = c)

theorem posMarked15_zero (positions : Positions) (c : Nat) :
    posMarked15 positions 0 c = false := by
  simp [posMarked15]

theorem posMarked15_succ (positions : Positions) (n c : Nat) :
    posMarked15 positions (n + 1) c =
      (posMarked15 positions n c || decide (capLeafOf (posAt positions n) = c)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [posMarked15, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hc⟩
    by_cases hjn : j < n
    · exact Or.inl ⟨j, hjn, hc⟩
    · have hjeq : j = n := by omega
      subst hjeq; exact Or.inr hc
  · rintro (⟨j, hj, hc⟩ | hc)
    · exact ⟨j, by omega, hc⟩
    · exact ⟨n, by omega, hc⟩

theorem posMarked15_card_eq_capMark (positions : Positions) (c : Nat) :
    posMarked15 positions positions.card c = capMark positions 15 c := by
  unfold posMarked15
  rw [capMark_15]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j, hj, hc⟩
    exact ⟨posAt positions j, posAt_mem positions j hj, hc⟩
  · rintro ⟨i, hi, hc⟩
    have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
    have hjc : j < positions.card := by simpa using hj
    refine ⟨j, hjc, ?_⟩
    simp only [posAt, dif_pos hjc, hget, hc]

/-- Consistency condition on the first `n` positions preventing any rejection during the
per-position verification loop. -/
def PosConsistent (c96 : Comp96) (s0 : MachineState) (input : CheckInput) (n : Nat) : Prop :=
  posRecordOff input.positions n ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 (posRecordOff input.positions j1) (posAt input.positions j1) (valAt input j1)).evalLevel c96 15 =
    (parsePartialWitness s0 (posRecordOff input.positions j2) (posAt input.positions j2) (valAt input j2)).evalLevel c96 15

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s input.proof.length
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if n = input.positions.card then pcWord 209 else pcWord 17
  x24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * n)
  x25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + posRecordOff input.positions n)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (input.positions.card - n)
  poff_le : posRecordOff input.positions n ≤ input.proof.length
  mark15 : ∀ c < 342, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if posMarked15 input.positions n c then 1#8 else 0#8
  mark_hi_zero : ∀ a, 4096 + 342 ≤ a → a < 4824 → s.getByte (BitVec.ofNat 64 a) = 0#8
  val15_unmarked_zero : ∀ c < 342, posMarked15 input.positions n c = false →
    ∀ b < 32, s.getByte (BitVec.ofNat 64 (8192 + gapOffset c + b)) = 0#8
  val15_gap_zero : ∀ q < 171, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + 96 * q + 64 + b)) = 0#8
  val_hi_zero : ∀ a, 8192 + capValOff 16 ≤ a → a < 8192 + 33152 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  witnesses : ∀ j < n,
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness (submission.initialState .check input)
      (posRecordOff input.positions j) (posAt input.positions j) (valAt input j)
    pw.evalLevel c96 15 = readBuffer s (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) ∧
    ((posAt input.positions j).val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96)) ∧
    (∀ prev, 1 ≤ prev → prev ≤ 14 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x)

/-- Complete per-position verification loop (`pc[17]` -> `pc[209]`), `≤ 1100 * k` steps, `≤ 19 * k` calls. -/
theorem step_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0)
    (sInit : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sInit (1100 * input.positions.card) (19 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' q tr => q ≤ 19 * input.positions.card ∧ PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (1100 * n) (19 * n)
        (¬ PosConsistent c96 s0 input n)
        (fun s' q tr => q ≤ 19 * n ∧ PosLoopInv h768 oracle input n s' tr) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued sInit 0 0 [] (by decide) (by decide) (StepsTo.refl oracle sInit) ⟨by decide, hinit⟩
    | succ k ih =>
      have hcons_sub : ¬ PosConsistent c96 s0 input k → ¬ PosConsistent c96 s0 input (k + 1) := by
        intro hnot hcons
        apply hnot
        refine ⟨(posRecordOff_mono input.positions (by omega)).trans hcons.1, ?_⟩
        intro j1 j2 hj1 hj2 hc
        exact hcons.2 j1 j2 (by omega) (by omega) hc
      rw [show 1100 * (k + 1) = 1100 * k + 1100 by omega,
        show 19 * (k + 1) = 19 * k + 19 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hlt_k : k < input.positions.card := by omega
        have hpc_k : sk.pc = pcWord 17 := by
          have := hinv_k.pc
          rwa [if_neg (by omega : k ≠ input.positions.card)] at this
        let pOff := posRecordOff input.positions k
        have hpeven : pOff % 2 = 0 := posRecordOff_even input.positions k
        let i := posAt input.positions k
        let pw := parsePartialWitness s0 pOff i (valAt input k)
        let rem1 := input.positions.card - (k + 1)
        have hrem_eq : input.positions.card - k = rem1 + 1 := by omega
        have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
          rw [hinv_k.x27, hrem_eq]
        -- 1A: leaf (105 steps, 4 calls)
        have h1a := step_pos_leaf h768 oracle input hvalid k pOff (rem1 + 1) hlt_k hpeven hinv_k.poff_le
          sk hpc_k hinv_k.fixed hinv_k.high hinv_k.x24 hinv_k.x8 hinv_k.x25 hx27_k
        have hcan_leaf : input.proof.length < pOff + 24 → ¬ PosConsistent c96 s0 input (k + 1) := by
          intro hlt hcons
          have h1 := hcons.1
          rw [posRecordOff_succ] at h1
          unfold recordLen at h1; omega
        -- Chain 1A -> 1B -> 1C -> 1D -> 1E
        refine PhaseOutcome.weaken
          (K1 := 105 + (105 + (60 + (782 + 30)))) (Q1 := 4 + (1 + (1 + (13 + 0))))
          ?_ (by decide) (by decide) id (fun _ _ _ h => h)
        refine h1a.bind_dep hcan_leaf (fun s1 qA trA ⟨hqA, hpleA, hpcA, hfixA, houtA, hx20A, hx24A, hx8A, hx25A, hx27A, hleafA, htrA⟩ => by
          have hhighA : HighMemPreserved s0 s1 := hinv_k.high.trans (houtA.mono (by omega) (by omega))
          have h1b := step_pos_l0 h768 oracle input hvalid k pOff (rem1 + 1) hlt_k hpeven hpleA
            s1 hpcA hfixA hhighA hx20A hx24A hx8A hx25A hx27A hleafA
          have hcan_l0 : input.proof.length < pOff + 24 + l0Bytes i → ¬ PosConsistent c96 s0 input (k + 1) := by
            intro hlt hcons
            have h1 := hcons.1
            rw [posRecordOff_succ] at h1
            change pOff + recordLen i ≤ input.proof.length at h1
            unfold recordLen at h1; omega
          refine h1b.bind_dep hcan_l0 (fun s2 qB trB ⟨hqB, hpleB, hpcB, hfixB, houtB, hx22B, hx24B, hx8B, hx25B, hx27B, hl1B, htrB⟩ => by
            have hhighB : HighMemPreserved s0 s2 := hhighA.trans (houtB.mono (by omega) (by omega))
            have h1c := step_pos_l1 h768 oracle input hvalid k pOff (rem1 + 1) hlt_k hpeven hpleB
              s2 hpcB hfixB hhighB hx22B hx24B hx8B hx25B hx27B hl1B
            have hcan_l1 : input.proof.length < pOff + 24 + l0Bytes i + 32 → ¬ PosConsistent c96 s0 input (k + 1) := by
              intro hlt hcons
              have h1 := hcons.1
              rw [posRecordOff_succ] at h1
              change pOff + recordLen i ≤ input.proof.length at h1
              unfold recordLen at h1; omega
            refine h1c.bind_dep hcan_l1 (fun s3 qC trC ⟨hqC, hpleC, hpcC, hfixC, houtC, hx22C, hx24C, hx8C, hx25C, hx27C, hl2C, hgapC, htrC⟩ => by
              have hhighC : HighMemPreserved s0 s3 := hhighB.trans (houtC.mono (by omega) (by omega))
              have h1d := step_pos_bin_loop h768 oracle input hvalid k pOff (rem1 + 1) hlt_k hpeven hpleC
                s3 hpcC hfixC hhighC hx22C hx24C hx8C hx25C hx27C hl2C hgapC
              have hcan_bin : input.proof.length < pOff + recordLen i → ¬ PosConsistent c96 s0 input (k + 1) := by
                intro hlt hcons
                have h1 := hcons.1
                rw [posRecordOff_succ] at h1
                change pOff + recordLen i ≤ input.proof.length at h1; omega
              refine h1d.bind_dep hcan_bin (fun s4 qD trD ⟨hqD, hpleD, hpcD, hfixD, houtD, hx22D, hx24D, hx8D, hx25D, hx27D, hd15D, htrD⟩ => by
                have hout_sk4 : MemEqOutside sk s4 256 448 :=
                  houtA.trans ((houtB.mono (by omega) (by omega)).trans
                    ((houtC.mono (by omega) (by omega)).trans (houtD.mono (by omega) (by omega))))
                have hc_lt : capLeafOf i < 342 := capLeafOf_lt i
                have hmark4 : s4.getByte (BitVec.ofNat 64 (4096 + capLeafOf i)) =
                    if posMarked15 input.positions k (capLeafOf i) then 1#8 else 0#8 :=
                  (hout_sk4 (4096 + capLeafOf i) (by omega) (by omega)).trans (hinv_k.mark15 (capLeafOf i) hc_lt)
                have h1e := step_pos_cap_store oracle input k (pOff + recordLen i) rem1 hlt_k (by omega)
                  s4 hpcD hfixD hx22D hx24D hx8D hx25D hx27D (posMarked15 input.positions k (capLeafOf i))
                  hmark4 (pw.evalLevel c96 15) hd15D
                have hcan_dup : (posMarked15 input.positions k (capLeafOf i) = true ∧
                    pw.evalLevel c96 15 ≠ readBuffer s4 (8192 + gapOffset (capLeafOf i)) 32) →
                    ¬ PosConsistent c96 s0 input (k + 1) := by
                  rintro ⟨hm, hne_d⟩ hcons
                  have hex : ∃ j < k, capLeafOf (posAt input.positions j) = capLeafOf i :=
                    of_decide_eq_true hm
                  obtain ⟨j, hj, hcj⟩ := hex
                  have hwj := (hinv_k.witnesses j hj).1
                  have hval_eq : readBuffer s4 (8192 + gapOffset (capLeafOf i)) 32 =
                      readBuffer sk (8192 + gapOffset (capLeafOf i)) 32 :=
                    hout_sk4.readBuffer_eq (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                  rw [hval_eq, ← hcj, ← hwj] at hne_d
                  exact hne_d (hcons.2 k j (by omega) (by omega) hcj.symm)
                refine h1e.weaken (by decide) (by decide) hcan_dup ?_
                rintro s5 qE trE ⟨rfl, rfl, hpcE, hfixE, hx24E, hx8E, hx25E, hx27E, hmark5, hval5, hout5, hmeq5⟩
                -- Combine all invariants for PosLoopInv (k + 1)
                have hmem_pres : ∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + capLeafOf i →
                    (a < 256 ∨ 448 ≤ a) →
                    (a < 8192 + gapOffset (capLeafOf i) ∨ 8192 + gapOffset (capLeafOf i) + 32 ≤ a) →
                    s5.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a ha hne_m hout_s hout_v =>
                  (hout5 a ha hne_m hout_v).trans (hout_sk4 a ha hout_s)
                have hhigh5 : HighMemPreserved s0 s5 := by
                  intro a ha hge
                  have hgo_le : 8192 + gapOffset (capLeafOf i) + 32 ≤ 4294971392 := by
                    unfold gapOffset; omega
                  exact (hmem_pres a ha (by omega) (by omega) (by omega)).trans (hinv_k.high a ha hge)
                refine ⟨by omega, ?_⟩
                refine ⟨hfixE, hhigh5, ?_, hx24E, hx8E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · by_cases hdone : k + 1 = input.positions.card
                  · have hz : rem1 = 0 := by omega
                    simp [hdone, hz, hpcE]
                  · have hnz : rem1 ≠ 0 := by omega
                    simp [hdone, hnz, hpcE]
                · simpa only [posRecordOff_succ, pOff] using hx25E
                · exact hx27E
                · simpa only [posRecordOff_succ, pOff] using hpleD
                · intro c hc
                  rw [posMarked15_succ]
                  change s5.getByte (BitVec.ofNat 64 (4096 + c)) =
                    if (posMarked15 input.positions k c || decide (capLeafOf i = c)) = true then 1#8 else 0#8
                  by_cases heq : capLeafOf i = c
                  · subst heq; simp only [decide_true, Bool.or_true, ite_true]; exact hmark5
                  · simp only [heq, decide_false, Bool.or_false]
                    have hpres := hmem_pres (4096 + c) (by omega) (by omega) (by omega) (by unfold gapOffset; omega)
                    exact hpres.trans (hinv_k.mark15 c hc)
                · intro a ha1 ha2
                  exact (hmem_pres a (by omega) (by omega) (by omega) (by unfold gapOffset; omega)).trans
                    (hinv_k.mark_hi_zero a ha1 ha2)
                · intro c hc hunm b hb
                  rw [posMarked15_succ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hunm
                  have hdisj := gapOffset_disjoint (a := c) (b := capLeafOf i) (fun h => hunm.2 h.symm)
                  exact (hmem_pres (8192 + gapOffset c + b) (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                    (by unfold gapOffset; omega) (by omega)).trans
                    (hinv_k.val15_unmarked_zero c hc hunm.1 b hb)
                · intro q hq b hb
                  have hdisj := gapOffset_disjoint_gap (capLeafOf i) q
                  exact (hmem_pres (8192 + 96 * q + 64 + b) (by omega) (by omega) (by omega) (by omega)).trans
                    (hinv_k.val15_gap_zero q hq b hb)
                · intro a ha1 ha2
                  have h16 : capValOff 16 = 16416 := by decide
                  have hgo : gapOffset (capLeafOf i) + 32 ≤ 16416 := by unfold gapOffset; omega
                  exact (hmem_pres a (by omega) (by omega) (by omega) (by omega)).trans
                    (hinv_k.val_hi_zero a ha1 ha2)
                · intro j hj
                  by_cases hjk : j < k
                  · obtain ⟨hw_val, hw_leaf, hw_l0, hw_bin⟩ := hinv_k.witnesses j hjk
                    have hval_pres : readBuffer s5 (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 =
                        readBuffer sk (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 := by
                      by_cases hsame : capLeafOf (posAt input.positions j) = capLeafOf i
                      · have hm_true : posMarked15 input.positions k (capLeafOf i) = true := by
                          unfold posMarked15; rw [decide_eq_true_eq]; exact ⟨j, hjk, hsame⟩
                        have hm5 := hmeq5 hm_true
                        exact ((MemEqOutside.of_mem_eq hm5 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)).trans
                          (hout_sk4.readBuffer_eq (by unfold gapOffset; omega) (by unfold gapOffset; omega))
                      · have hdisj := gapOffset_disjoint hsame
                        have hcj_lt : capLeafOf (posAt input.positions j) < 342 := capLeafOf_lt _
                        apply readBuffer_congr2; intro b hb
                        exact hmem_pres (8192 + gapOffset (capLeafOf (posAt input.positions j)) + b)
                          (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                          (by unfold gapOffset; omega) (by omega)
                    refine ⟨hw_val.trans hval_pres.symm,
                      fun x hx => (hw_leaf x hx).append_left,
                      fun hf => (hw_l0 hf).append_left,
                      fun prev hp1 hp2 x hx => (hw_bin prev hp1 hp2 x hx).append_left⟩
                  · have hjeq : j = k := by omega
                    subst hjeq
                    refine ⟨hval5.symm, ?_, ?_, ?_⟩
                    · intro x hx
                      exact (((htrA x hx).append_left).append_right)
                    · intro hf
                      exact ((((htrB hf).append_left).append_right).append_right)
                    · intro prev hp1 hp2 x hx
                      by_cases hp_one : prev = 1
                      · subst hp_one
                        exact (((((htrC x hx).append_left).append_right).append_right).append_right)
                      · exact ((((((htrD prev (by omega) hp2 x hx).append_left).append_right).append_right).append_right).append_right))))))
  exact hind input.positions.card (le_refl _)


end CommitGolfCandidate
