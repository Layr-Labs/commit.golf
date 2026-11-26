import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the L2..L5 (240b) and L6..L14 (238b) binary loops, L15 cap-store,
and full per-position loop (`pc[141..242]`, `pc[22] -> pc[243]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem evalLevel_succ_of_ge1 (c : Comp96) (w : WitnessPath) (l : Nat) (hl : 1 ≤ l) :
    w.evalLevel c (l + 1) =
      let cur := w.evalLevel c l
      let idx := (w.index.val / 3) >>> (l - 1)
      if (idx ^^^ 1) < levelSize l then
        let inp := if idx % 2 = 0 then binaryInput cur (w.binSib l)
                   else binaryInput (w.binSib l) cur
        maskLevel (l + 1) (c inp)
      else cur := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rfl

private theorem pc_146_branch : pcWord 146 + signExtend13 128#13 = pcWord 178 := by decide
private theorem pc_148_branch : pcWord 148 + signExtend13 728#13 = pcWord 330 := by decide
private theorem pc_150_branch : pcWord 150 + signExtend13 56#13 = pcWord 164 := by decide
private theorem pc_163_jal : pcWord 163 + signExtend21 20#21 = pcWord 168 := by decide
private theorem pc_172_branch : pcWord 172 + signExtend13 12#13 = pcWord 175 := by decide
private theorem pc_174_jal : pcWord 174 + signExtend21 16#21 = pcWord 178 := by decide
private theorem pc_179_branch : pcWord 179 + signExtend13 8048#13 = pcWord 143 := by decide
private theorem pc_184_branch : pcWord 184 + signExtend13 88#13 = pcWord 206 := by decide
private theorem pc_186_branch : pcWord 186 + signExtend13 48#13 = pcWord 198 := by decide
private theorem pc_197_jal : pcWord 197 + signExtend21 12#21 = pcWord 200 := by decide
private theorem pc_207_branch : pcWord 207 + signExtend13 8088#13 = pcWord 181 := by decide

/-- One iteration (`step < 4`, level `l = 2 + step ∈ 2..5`) of the 240b binary loop (`pc[143..179]`). -/
theorem step_pos_bin240_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 4)
    (s : MachineState) (hpc : s.pc = pcWord 143)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32 +
        binPathOff ((posAt input.positions ord).val / 3) step) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (2 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pCur := pOff + 24 + l0Bytes i + 32 + binPathOff g step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 212 1 (input.proof.length < pCur + binStepBytes g step + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 1 ∧
        s'.pc = (if step + 1 = 4 then pcWord 180 else pcWord 143) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + binStepBytes g step) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g pCur pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hle_cur : pCur + tailBytes tOff ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_lt : g < 5592406 := by change i.val / 3 < _; omega
  have hidx_lt : g >>> step < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hidx1_lt : g >>> (step + 1) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g >>> step) / 2 = g >>> (step + 1) := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  -- pc[143]: SRLI x22, x22, 1; pc[144]: XORI x28, x22, 1
  have hst143 := step_ordinary oracle s 143 (.SRLI .x22 .x22 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SRLI .x22 .x22 1#6)
  have hpc1 : s1.pc = pcWord 144 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx22_1 : s1.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, show (1#6 : BitVec 6).toNat = 1 by decide,
      bv64_shr _ 1 (Nat.lt_trans hidx_lt (by decide)), Nat.pow_one, hshr_step]
  have hst144 := step_ordinary oracle s1 144 (.XORI .x28 .x22 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
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
  have ha145 : s2.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475936 + (32 * (2 + step) + 8)) := by
    rw [hreg2 .x29 (by decide) (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv145 : memoryArgumentsValid s2 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha145]
    exact accessValid_ofNat (68719475936 + (32 * (2 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst145 := step_ordinary oracle s2 145 (.LD .x7 .x29 8#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv145])
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
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha145]
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
  -- pc[146]: BGEU x28, x7, pc[178]
  have hst146 := step_ordinary oracle s3 146 (.BGEU .x28 .x7 128#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.BGEU .x28 .x7 128#13)
  have hult146 : BitVec.ult (s3.getReg .x28) (s3.getReg .x7) =
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
  -- Common loop footer at pc[178..179]
  have hfooter : ∀ (s178 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 206 → qMid ≤ 1 →
      StepsTo oracle s4 s178 kMid qMid trMid →
      s178.pc = pcWord 178 →
      CheckFixedRegs s178 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g step) tOff s178 →
      MemEqOutside s s178 256 320 →
      s178.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) →
      s178.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
      s178.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
      s178.getReg .x27 = BitVec.ofNat 64 rem →
      s178.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)) →
      s178.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) →
      readBuffer s178 256 32 = pw.evalLevel c96 (2 + (step + 1)) →
      readBuffer s178 320 32 = 0 →
      (∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle trMid x) →
      PhaseOutcome oracle s 212 1 (input.proof.length < pCur + binStepBytes g step + tailBytes tOff)
        (fun s' q tr =>
          q ≤ 1 ∧
          s'.pc = (if step + 1 = 4 then pcWord 180 else pcWord 143) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g step) tOff s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
    intro s178 kMid qMid trMid hkMid hqMid hmid hpc178 hfix178 hcur178 hout178 h22 h24 h8 h27 h29 h30 hdig178 hgap178 htr178
    have hst178 := step_ordinary oracle s178 178 (.ADDI .x29 .x29 32#12) (by decide) hpc178 rfl (by intro h; cases h) rfl
    let s179 := execInstrBr s178 (.ADDI .x29 .x29 32#12)
    have hpc179 : s179.pc = pcWord 179 := by simp only [s179, execInstrBr, MachineState.setPC, hpc178, pcWord_add_four]
    have hx29_179 : s179.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      simp only [s179, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_179 : s179.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) := by
      simp only [s179, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), h30]
    have hst179 := step_ordinary oracle s179 179 (.BNE .x29 .x30 8048#13) (by decide) hpc179 rfl (by intro h; cases h) rfl
    let sFin := execInstrBr s179 (.BNE .x29 .x30 8048#13)
    have hmemFin : sFin.mem = s178.mem := by
      simp only [sFin, execInstrBr]; split <;> simp [s179, execInstrBr, mem_setPC, mem_setReg]
    have hregFin : ∀ r, r ≠ .x29 → sFin.getReg r = s178.getReg r := fun r h29r => by
      have h180 : sFin.getReg r = s179.getReg r := by
        simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
      rw [h180]
      simp only [s179, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h29r.symm
    have hx29_Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      have : sFin.getReg .x29 = s179.getReg .x29 := by
        simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
      exact this.trans hx29_179
    have hpcFin : sFin.pc = if step + 1 = 4 then pcWord 180 else pcWord 143 := by
      have hne_iff : (s179.getReg .x29 != s179.getReg .x30) = decide (step + 1 ≠ 4) := by
        rw [hx29_179, hx30_179, bv64_bne_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      by_cases hdone : step + 1 = 4
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, ite_true, MachineState.setPC, hpc179, pcWord_add_four]
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_false_eq_true, decide_true,
          ite_true, ite_false, MachineState.setPC, hpc179]; exact pc_179_branch
    have htot := (((hst143.trans hst144).trans (hst145.trans hst146)).trans hmid).trans (hst178.trans hst179)
    refine .continued sFin (4 + kMid + 2) qMid trMid (by omega) hqMid (by simpa [Nat.add_assoc] using htot)
      ⟨hqMid, hpcFin,
       hfix178.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       hcur178.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
       hout178.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       (hregFin .x22 (by decide)).trans h22, (hregFin .x24 (by decide)).trans h24,
       (hregFin .x8  (by decide)).trans h8,  (hregFin .x27 (by decide)).trans h27,
       hx29_Fin, (hregFin .x30 (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig178,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap178,
       htr178⟩
  -- Branch on whether sibling exists at level `2 + step`
  by_cases hpair : ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
  · -- Paired: binStepBytes g step = 30
    have hsb : binStepBytes g step = 30 := by
      unfold binStepBytes; rw [if_pos hpair, if_pos (by omega)]
    have hpc4 : s4.pc = pcWord 147 := by
      simp only [s4, execInstrBr, hult146, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult146, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult146, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
      simpa [s4, execInstrBr, hult146, hpair, MachineState.getReg_setPC] using hx22_3
    -- pc[147]: ADDI x6, x25, 30; pc[148]: BLTU x31, x6, pc[330]
    have hst147 := step_ordinary oracle s4 147 (.ADDI .x6 .x25 30#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ADDI .x6 .x25 30#12)
    have hpc5 : s5.pc = pcWord 148 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hx6_5 : s5.getReg .x6 = BitVec.ofNat 64 (11341403200 + pCur + 30) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg4 .x25 (by decide) (by decide) (by decide),
        hcur.x25, se12_30_ofNat]
      change BitVec.ofNat 64 (11341403200 + pCur) + BitVec.ofNat 64 30 = _
      exact bv64_add _ 30
    have hx31_5 : s5.getReg .x31 = BitVec.ofNat 64 (11341403200 + (input.proof.length - tailBytes tOff)) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
        hreg4 .x31 (by decide) (by decide) (by decide), hcur.x31]
    have hst148 := step_ordinary oracle s5 148 (.BLTU .x31 .x6 728#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BLTU .x31 .x6 728#13)
    have hult148 : BitVec.ult (s5.getReg .x31) (s5.getReg .x6) =
        decide (input.proof.length < pCur + 30 + tailBytes tOff) := by
      rw [hx31_5, hx6_5, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases hshort : input.proof.length < pCur + 30 + tailBytes tOff
    · have hpc6 : s6.pc = pcWord 330 := by
        simp only [s6, execInstrBr, hult148, hshort, decide_true, ite_true, MachineState.setPC, hpc5]
        exact pc_148_branch
      have hrej := (((hst143.trans hst144).trans (hst145.trans hst146)).trans (hst147.trans hst148)).halt
        (halt_reject oracle s6 hpc6)
      exact .rejected 9 0 [] (by rw [hsb]; exact hshort) (by decide) (by decide) (by simpa using hrej)
    · have hge30 : pCur + 30 + tailBytes tOff ≤ input.proof.length := by omega
      have hpc6 : s6.pc = pcWord 149 := by
        simp only [s6, execInstrBr, hult148, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s.mem := by
        have h65 : s6.mem = s5.mem := by
          simp only [s6, execInstrBr, hult148, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
        have h54 : s5.mem = s4.mem := by simp only [s5, execInstrBr, mem_setPC, mem_setReg]
        exact h65.trans (h54.trans hmem4)
      have hreg65 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
        simp only [s6, execInstrBr, hult148, hshort, decide_false, Bool.false_eq_true, ite_false,
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
      have hst149 := step_ordinary oracle s6 149 (.ANDI .x7 .x22 1#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ANDI .x7 .x22 1#12)
      have hpc7 : s7.pc = pcWord 150 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hx7_7 : s7.getReg .x7 = BitVec.ofNat 64 ((g >>> (step + 1)) % 2) := by
        simp only [s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hx22_6, se12_1]
        exact bv64_and_one _ (by omega)
      have hst150 := step_ordinary oracle s7 150 (.BEQ .x7 .x0 56#13) (by decide) hpc7 rfl (by intro h; cases h) rfl
      let s8 := execInstrBr s7 (.BEQ .x7 .x0 56#13)
      have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
      let sibD := pw.binSib (2 + step)
      have hsibD_eq : sibD = proofDigest30 s0 (11341403200 + pCur) := by
        simp only [sibD, pw, parsePartialWitness, show 2 + step ≠ 1 by omega, ite_false,
          show 2 ≤ 2 + step ∧ 2 + step ≤ 5 by omega, and_self, ite_true,
          show 2 + step - 2 = step by omega, pCur, Nat.add_assoc]
        dsimp only [g]
      let curD := pw.evalLevel c96 (2 + step)
      let inpL : BitVec 768 :=
        if (g >>> (step + 1)) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
      have hidx_pw : (pw.index.val / 3) >>> (2 + step - 1) = g >>> (step + 1) := by
        change g >>> (2 + step - 1) = g >>> (step + 1)
        exact congrArg (fun k => g >>> k) (by omega)
      have heval_next : pw.evalLevel c96 (2 + (step + 1)) = maskLevel (2 + (step + 1)) (c96 inpL) := by
        rw [show 2 + (step + 1) = (2 + step) + 1 by omega,
          evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
        dsimp only
        rw [hidx_pw, if_pos hpair]
      have hlinp : pw.levelInput c96 (2 + step) = [inpL] := by
        unfold WitnessPath.levelInput
        dsimp only
        rw [hidx_pw, if_pos hpair]
      -- Common compression + mask (240b for step < 3, 238b for step = 3) at pc[168..177] -> pc[178]
      have hcall168 : ∀ (s168 : MachineState) (kA : Nat),
          kA ≤ 194 →
          StepsTo oracle s8 s168 kA 0 [] →
          s168.pc = pcWord 168 →
          CheckFixedRegs s168 →
          ProofCursor s0 input.proof.length (pCur + 30) tOff s168 →
          MemEqOutside s s168 256 320 →
          s168.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) →
          s168.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
          s168.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
          s168.getReg .x27 = BitVec.ofNat 64 rem →
          s168.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)) →
          s168.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) →
          readBuffer s168 256 96 = inpL →
          readBuffer s168 320 32 = 0 →
          PhaseOutcome oracle s 212 1 (input.proof.length < pCur + binStepBytes g step + tailBytes tOff)
            (fun s' q tr =>
              q ≤ 1 ∧ s'.pc = (if step + 1 = 4 then pcWord 180 else pcWord 143) ∧
              CheckFixedRegs s' ∧
              ProofCursor s0 input.proof.length (pCur + binStepBytes g step) tOff s' ∧
              MemEqOutside s s' 256 320 ∧
              s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
              s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
              s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
              s'.getReg .x27 = BitVec.ofNat 64 rem ∧
              s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
              s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) ∧
              readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
              readBuffer s' 320 32 = 0 ∧
              ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
        intro s168 kA hkA hmidA hpc168 hfix168 hcur168 hout168 h22 h24 h8 h27 h29 h30 hinp168 hgap168
        have hst168 := step_ordinary oracle s168 168 (.ADDI .x10 .x21 0#12) (by decide) hpc168 rfl (by intro h; cases h) rfl
        let s169 := execInstrBr s168 (.ADDI .x10 .x21 0#12)
        have hpc169 : s169.pc = pcWord 169 := by simp only [s169, execInstrBr, MachineState.setPC, hpc168, pcWord_add_four]
        have hst169 := step_ordinary oracle s169 169 (.ADDI .x12 .x21 0#12) (by decide) hpc169 rfl (by intro h; cases h) rfl
        let s170 := execInstrBr s169 (.ADDI .x12 .x21 0#12)
        have hpc170 : s170.pc = pcWord 170 := by simp only [s170, execInstrBr, MachineState.setPC, hpc169, pcWord_add_four]
        have hmem170 : s170.mem = s168.mem := by simp [s170, s169, execInstrBr, mem_setPC, mem_setReg]
        have hreg170 : ∀ r, r ≠ .x10 → r ≠ .x12 → s170.getReg r = s168.getReg r := fun r h10 h12 => by
          simp only [s170, s169, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
        have hx10_170 : s170.getReg .x10 = 256#64 := by
          simp only [s170, s169, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide), hfix168.x21, se12_0, BitVec.add_zero]
        have hx12_170 : s170.getReg .x12 = 256#64 := by
          simp only [s170, s169, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
            hfix168.x21, se12_0, BitVec.add_zero]
        have hec := step_ecall_compress h768 oracle s170 170 256 256 (by decide) hpc170 rfl
          ((hreg170 .x5 (by decide) (by decide)).trans hfix168.x5)
          ((hreg170 .x11 (by decide) (by decide)).trans hfix168.x11)
          ((hreg170 .x13 (by decide) (by decide)).trans hfix168.x13)
          hx10_170 hx12_170 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
        rw [(MemEqOutside.of_mem_eq hmem170 0 0).readBuffer_eq (by decide) (by omega), hinp168] at hec
        let s171 := writeBits s170 (BitVec.ofNat 64 256) (c96 inpL)
        have hpc171 : s171.pc = pcWord 171 := by simp only [s171, writeBits, MachineState.setPC, hpc170, pcWord_add_four]
        have hreg171 : ∀ r, r ≠ .x10 → r ≠ .x12 → s171.getReg r = s168.getReg r := fun r h10 h12 =>
          (writeBits_register s170 _ _ r).trans (hreg170 r h10 h12)
        -- pc[171]: ADDI x6, x2, 160; pc[172]: BEQ x29, x6, pc[175]
        have hst171 := step_ordinary oracle s171 171 (.ADDI .x6 .x2 160#12) (by decide) hpc171 rfl (by intro h; cases h) rfl
        let s172 := execInstrBr s171 (.ADDI .x6 .x2 160#12)
        have hpc172 : s172.pc = pcWord 172 := by simp only [s172, execInstrBr, MachineState.setPC, hpc171, pcWord_add_four]
        have hx6_172 : s172.getReg .x6 = BitVec.ofNat 64 (68719475936 + 160) := by
          simp only [s172, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hreg171 .x2 (by decide) (by decide), hfix168.x2, se12_160]
          change BitVec.ofNat 64 68719475936 + BitVec.ofNat 64 160 = _; exact bv64_add _ _
        have hx29_172 : s172.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)) := by
          simp only [s172, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hreg171 .x29 (by decide) (by decide), h29]
        have hst172 := step_ordinary oracle s172 172 (.BEQ .x29 .x6 12#13) (by decide) hpc172 rfl (by intro h; cases h) rfl
        let s173 := execInstrBr s172 (.BEQ .x29 .x6 12#13)
        have heq3 : (s172.getReg .x29 == s172.getReg .x6) = decide (step = 3) := by
          rw [hx29_172, hx6_172, bv64_beq_eq _ _ (by omega) (by omega)]
          exact decide_eq_decide.mpr (by omega)
        have hmem173 : s173.mem = s171.mem := by
          simp only [s173, execInstrBr]; split <;> simp [s172, execInstrBr, mem_setPC, mem_setReg]
        have hreg173 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s173.getReg r = s168.getReg r := fun r h6 h10 h12 => by
          have : s173.getReg r = s172.getReg r := by simp only [s173, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
          rw [this]; simp only [s172, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
          exact hreg171 r h10 h12
        have hpre173 := (((hst147.trans hst148).trans (hst149.trans hst150)).trans hmidA).trans
          (((hst168.trans hst169).trans hec).trans (hst171.trans hst172))
        by_cases hs3 : step = 3
        · -- step = 3 (l = 5 -> L6): mask238 at pc[175..177] -> pc[178]
          have hpc173 : s173.pc = pcWord 175 := by
            simp only [s173, execInstrBr, heq3, hs3, decide_true, ite_true, MachineState.setPC, hpc172]
            exact pc_172_branch
          obtain ⟨s178, hs178, hpc178, hreg178, hdig178, hout178⟩ :=
            step_mask238 oracle 175 .x21 s173 256 (by decide) (by decide) rfl rfl rfl hpc173
              ((hreg173 .x21 (by decide) (by decide) (by decide)).trans hfix168.x21)
              ((hreg173 .x9 (by decide) (by decide) (by decide)).trans hfix168.x9)
              (by decide) (by unfold MEMORY_BYTES; decide)
          have hdig_eq : readBuffer s178 256 32 = pw.evalLevel c96 (2 + (step + 1)) := by
            rw [heval_next, hdig178, (MemEqOutside.of_mem_eq hmem173 0 0).readBuffer_eq (by decide) (by omega),
              writeBits_readBuffer_digest]
            unfold maskLevel
            rw [if_neg (by omega), if_neg (by omega)]
          have hgap178 : readBuffer s178 320 32 = 0 := by
            rw [hout178.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem173 0 0).readBuffer_eq (by decide) (by omega),
              (MemEqOutside_writeBits_digest s170 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem170 0 0).readBuffer_eq (by decide) (by omega), hgap168]
          have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s178.getReg r = s168.getReg r :=
            fun r h6 h10 h12 => (hreg178 r h6).trans (hreg173 r h6 h10 h12)
          have hout_all : MemEqOutside s s178 256 320 :=
            hout168.trans ((MemEqOutside.of_mem_eq hmem170 256 320).trans
              (((MemEqOutside_writeBits_digest s170 256 _ (by decide)).mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem173 256 320).trans (hout178.mono (by omega) (by omega)))))
          refine hfooter s178 (4 + kA + 5 + 3) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
            ((hpre173.trans hs178).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
            hpc178
            (hfix168.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
            (by rw [hsb]; exact hcur168.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
            hout_all
            ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
            ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
            ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
            ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
            ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
            ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
            hdig_eq hgap178 ?_
          intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
          exact InTrace.singleton h768 oracle inpL
        · -- step < 3 (l ∈ 2..4 -> L3..L5): SH x21, x0, 30 (mask240) + JAL pc[178]
          have hpc173 : s173.pc = pcWord 173 := by
            simp only [s173, execInstrBr, heq3, hs3, decide_false, Bool.false_eq_true, ite_false,
              MachineState.setPC, hpc172, pcWord_add_four]
          have ha173 : s173.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
            rw [hreg173 .x21 (by decide) (by decide) (by decide), hfix168.x21]; decide
          have hv173 : memoryArgumentsValid s173 (.SH .x21 .x0 30#12) = true := by
            simp only [memoryArgumentsValid, memAccess, ha173]
            exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; decide) (by decide)
          have hst173 := step_ordinary oracle s173 173 (.SH .x21 .x0 30#12) (by decide) hpc173 rfl (by intro h; cases h)
            (by simp [ordinaryStep, hv173])
          let s174 := execInstrBr s173 (.SH .x21 .x0 30#12)
          have hpc174 : s174.pc = pcWord 174 := by simp only [s174, execInstrBr, MachineState.setPC, hpc173, pcWord_add_four]
          have hst174 := step_ordinary oracle s174 174 (.JAL .x0 16#21) (by decide) hpc174 rfl (by intro h; cases h) rfl
          let s178 := execInstrBr s174 (.JAL .x0 16#21)
          have hpc178 : s178.pc = pcWord 178 := by
            simp only [s178, execInstrBr, MachineState.setPC, hpc174]; exact pc_174_jal
          have hmem178 : s178.mem = s174.mem := by simp [s178, execInstrBr, mem_setPC, mem_setReg]
          have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s178.getReg r = s168.getReg r := fun r h6 h10 h12 => by
            have h1 : s178.getReg r = s174.getReg r := by simp [s178, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            have h2 : s174.getReg r = s173.getReg r := by
              simp [s174, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
            exact h1.trans (h2.trans (hreg173 r h6 h10 h12))
          have hout_sh : MemEqOutside s173 s174 286 288 := by
            intro a ha hout
            simp only [s174, execInstrBr, ha173, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
            exact MemEqOutside_setHalfword s173 286 _ (by decide) (by decide) a ha hout
          have hout_all : MemEqOutside s s178 256 320 :=
            hout168.trans ((MemEqOutside.of_mem_eq hmem170 256 320).trans
              (((MemEqOutside_writeBits_digest s170 256 _ (by decide)).mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem173 256 320).trans
                  ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem178 256 320)))))
          have hdig_eq : readBuffer s178 256 32 = pw.evalLevel c96 (2 + (step + 1)) := by
            rw [heval_next, (MemEqOutside.of_mem_eq hmem178 0 0).readBuffer_eq (by decide) (by omega)]
            have hsh : readBuffer s174 256 32 =
                readBuffer (s171.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s174, execInstrBr, ha173, MachineState.getByte, MachineState.setHalfword,
                MachineState.getMem, MachineState.setMem, mem_setPC, hmem173, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh, sh_zero_mask240 s171 256 (by decide) (by decide), writeBits_readBuffer_digest]
            unfold maskLevel
            rw [if_neg (by omega), if_pos (by omega)]
          have hgap178 : readBuffer s178 320 32 = 0 := by
            rw [(MemEqOutside.of_mem_eq hmem178 0 0).readBuffer_eq (by decide) (by omega),
              hout_sh.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem173 0 0).readBuffer_eq (by decide) (by omega),
              (MemEqOutside_writeBits_digest s170 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem170 0 0).readBuffer_eq (by decide) (by omega), hgap168]
          refine hfooter s178 (4 + kA + 5 + 2) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
            ((hpre173.trans (hst173.trans hst174)).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
            hpc178
            (hfix168.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
            (by rw [hsb]; exact hcur168.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
            hout_all
            ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
            ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
            ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
            ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
            ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
            ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
            hdig_eq hgap178 ?_
          intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
          exact InTrace.singleton h768 oracle inpL
      by_cases heven : (g >>> (step + 1)) % 2 = 0
      · -- Even: jump to pc[164..167] -> pc[168]
        have hx7z : s7.getReg .x7 = 0#64 := by rw [hx7_7, heven]
        have hpc8 : s8.pc = pcWord 164 := by
          simp only [s8, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
            MachineState.setPC, hpc7]; exact pc_150_branch
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
        have hst164 := step_ordinary oracle s8 164 (.ADDI .x12 .x21 32#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 32#12)
        have hpc9 : s9.pc = pcWord 165 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hx25_10, hreg10, hcopy10, hout10⟩ :=
          step_call_read_n oracle 165 30 s9 (11341403200 + pCur) 288 (by decide) (by decide) (by decide)
            rfl rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                  hreg8 .x25 (by decide) (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide),
                  hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        -- pc[167]: SH x21, x0, 62
        have hx21_10 : s10.getReg .x21 = 256#64 := by
          rw [hreg10 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21),
            hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21]
        have ha167 : s10.getReg .x21 + signExtend12 62#12 = BitVec.ofNat 64 318 := by
          rw [hx21_10]; decide
        have hv167 : memoryArgumentsValid s10 (.SH .x21 .x0 62#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha167]
          exact accessValid_ofNat 318 2 (by unfold MEMORY_BYTES; decide) (by decide)
        have hst167 := step_ordinary oracle s10 167 (.SH .x21 .x0 62#12) (by decide) hpc10 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv167])
        let s11 := execInstrBr s10 (.SH .x21 .x0 62#12)
        have hpc11 : s11.pc = pcWord 168 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
        have hmem9 : s9.mem = s.mem := by simpa [s9, execInstrBr, mem_setPC, mem_setReg] using hmem8
        have hout_sh : MemEqOutside s10 s11 318 320 := by
          intro a ha hout
          simp only [s11, execInstrBr, ha167, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s10 318 _ (by decide) (by decide) a ha hout
        have hout_all : MemEqOutside s s11 288 320 :=
          (MemEqOutside.of_mem_eq hmem9 288 320).trans
            ((hout10.mono (by omega) (by omega)).trans (hout_sh.mono (by omega) (by omega)))
        have hreg11_10 : ∀ r, s11.getReg r = s10.getReg r := fun r => by
          simp [s11, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        have hreg11 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x25 → r ≠ .x28 →
            s11.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h22 h25 h28 => by
          rw [hreg11_10, hreg10 r h1 h6 h10 h12 h25]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
          exact hreg8 r h6 h7 h22 h28
        have hcur11 : ProofCursor s0 input.proof.length (pCur + 30) tOff s11 := by
          refine ⟨hge30, ?_, ?_, ?_, ?_⟩
          · rw [hreg11_10, hx25_10]; congr 1
          · rw [hreg11 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg11 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg11 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
        have hgap11 : readBuffer s11 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp11 : readBuffer s11 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s11 256 hgap11]
          have hL : readBuffer s11 256 32 = curD :=
            (hout_all.readBuffer_eq (by decide) (by omega)).trans hcurDig
          have hR : readBuffer s11 288 32 = sibD := by
            rw [hsibD_eq]
            have hsh_eq : readBuffer s11 288 32 =
                readBuffer (s10.setHalfword (BitVec.ofNat 64 (288 + 30)) 0#16) 288 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s11, execInstrBr, ha167, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh_eq]
            apply sh_zero_readBuffer30 s10 s0 288 (11341403200 + pCur) (by decide) (by decide)
            intro j hj
            have hc := hcopy10 j hj
            simp only [MachineState.getByte, MachineState.getMem, hmem9] at hc ⊢
            exact hc.trans (hhigh (11341403200 + pCur + j) (by omega) (by omega))
          rw [hL, hR]; simp only [inpL, heven, ite_true]
        refine hcall168 s11 185 (by decide)
          (by simpa using (hst164.trans hs10).trans hst167) hpc11
          (hfix.of_agree (fun r hr => hreg11 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur11 (hout_all.mono (by omega) (by omega))
          (by rw [hreg11_10, hreg10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]
              simp only [s9, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x22), hx22_8])
          ((hreg11 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg11 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg11 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg11 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg11 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp11 hgap11
      · -- Odd: fall through to pc[151..163] -> pc[168]
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
        have hst159 := step_ordinary oracle s9 159 (.ADDI .x12 .x21 0#12) (by decide) hpc9 rfl (by intro h; cases h) rfl
        let s10 := execInstrBr s9 (.ADDI .x12 .x21 0#12)
        have hpc10 : s10.pc = pcWord 160 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
        obtain ⟨s11, hs11, hpc11, hx25_11, hreg11, hcopy11, hout11⟩ :=
          step_call_read_n oracle 160 30 s10 (11341403200 + pCur) 256 (by decide) (by decide) (by decide)
            rfl rfl hpc10
            (by simp only [s10, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg9 .x25 (by decide),
                  hreg8 .x25 (by decide) (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s10, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg9 .x21 (by decide),
                  hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hx21_11 : s11.getReg .x21 = 256#64 := by
          rw [hreg11 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp only [s10, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg9 .x21 (by decide),
            hreg8 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21]
        have ha162 : s11.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
          rw [hx21_11]; decide
        have hv162 : memoryArgumentsValid s11 (.SH .x21 .x0 30#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha162]
          exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; decide) (by decide)
        have hst162 := step_ordinary oracle s11 162 (.SH .x21 .x0 30#12) (by decide) hpc11 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv162])
        let s12 := execInstrBr s11 (.SH .x21 .x0 30#12)
        have hpc12 : s12.pc = pcWord 163 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
        have hst163 := step_ordinary oracle s12 163 (.JAL .x0 20#21) (by decide) hpc12 rfl (by intro h; cases h) rfl
        let s13 := execInstrBr s12 (.JAL .x0 20#21)
        have hpc13 : s13.pc = pcWord 168 := by simp only [s13, execInstrBr, MachineState.setPC, hpc12]; exact pc_163_jal
        have hmem10 : s10.mem = s9.mem := by simp [s10, execInstrBr, mem_setPC, mem_setReg]
        have hmem13 : s13.mem = s12.mem := by simp [s13, execInstrBr, mem_setPC, mem_setReg]
        have hout_sh : MemEqOutside s11 s12 286 288 := by
          intro a ha hout
          simp only [s12, execInstrBr, ha162, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s11 286 _ (by decide) (by decide) a ha hout
        have hout_all : MemEqOutside s s13 256 320 :=
          (MemEqOutside.of_mem_eq hmem8 256 320).trans
            ((hout9.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem10 256 320).trans
                ((hout11.mono (by omega) (by omega)).trans
                  ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem13 256 320)))))
        have hreg13_11 : ∀ r, s13.getReg r = s11.getReg r := fun r => by
          have h1 : s13.getReg r = s12.getReg r := by simp [s13, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          have h2 : s12.getReg r = s11.getReg r := by
            simp [s12, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
          exact h1.trans h2
        have hreg13 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x25 → r ≠ .x28 →
            s13.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h22 h25 h28 => by
          rw [hreg13_11, hreg11 r h1 h6 h10 h12 h25]
          simp only [s10, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg9 r h6]
          exact hreg8 r h6 h7 h22 h28
        have hcur13 : ProofCursor s0 input.proof.length (pCur + 30) tOff s13 := by
          refine ⟨hge30, ?_, ?_, ?_, ?_⟩
          · rw [hreg13_11, hx25_11]; congr 1
          · rw [hreg13 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg13 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg13 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
        have hgap13 : readBuffer s13 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp13 : readBuffer s13 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s13 256 hgap13]
          have hL : readBuffer s13 256 32 = sibD := by
            rw [hsibD_eq, (MemEqOutside.of_mem_eq hmem13 0 0).readBuffer_eq (by decide) (by omega)]
            have hsh_eq : readBuffer s12 256 32 =
                readBuffer (s11.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s12, execInstrBr, ha162, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh_eq]
            apply sh_zero_readBuffer30 s11 s0 256 (11341403200 + pCur) (by decide) (by decide)
            intro j hj
            have h10s : MemEqOutside s s10 288 320 :=
              (MemEqOutside.of_mem_eq hmem8 288 320).trans (hout9.trans (MemEqOutside.of_mem_eq hmem10 288 320))
            exact (hcopy11 j hj).trans
              ((h10s (11341403200 + pCur + j) (by omega) (by omega)).trans
                (hhigh (11341403200 + pCur + j) (by omega) (by omega)))
          have hcur' : readBuffer s 256 32 = curD := hcurDig
          have hR : readBuffer s13 288 32 = curD := by
            rw [(MemEqOutside.of_mem_eq hmem13 0 0).readBuffer_eq (by decide) (by omega),
              hout_sh.readBuffer_eq (by decide) (by omega),
              hout11.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem10 0 0).readBuffer_eq (by decide) (by omega), ← hcur']
            apply readBuffer_congr2; intro j hj
            have hc := hcopy9 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem8] at hc ⊢
            exact hc
          rw [hL, hR]; simp only [inpL, heven, ite_false]
        refine hcall168 s13 194 (by decide)
          (by simpa using ((hs9.trans hst159).trans hs11).trans (hst162.trans hst163)) hpc13
          (hfix.of_agree (fun r hr => hreg13 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur13 hout_all
          (by rw [hreg13_11, hreg11 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]
              simp only [s10, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x22), hreg9 .x22 (by decide), hx22_8])
          ((hreg13 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg13 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg13 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg13 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg13 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp13 hgap13
  · -- Promoted (unpaired): binStepBytes g step = 0, jump directly to pc[178]
    have hsb : binStepBytes g step = 0 := by unfold binStepBytes; exact if_neg hpair
    have hpc4 : s4.pc = pcWord 178 := by
      simp only [s4, execInstrBr, hult146, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc3]; exact pc_146_branch
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult146, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult146, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
      simpa [s4, execInstrBr, hult146, hpair, MachineState.getReg_setPC] using hx22_3
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
      (by rw [hsb, Nat.add_zero]
          exact hcur.of_agree (fun r hr => hreg4 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (MemEqOutside.of_mem_eq hmem4 256 320) hx22_4
      ((hreg4 .x24 (by decide) (by decide) (by decide)).trans hx24)
      ((hreg4 .x8  (by decide) (by decide) (by decide)).trans hx8)
      ((hreg4 .x27 (by decide) (by decide) (by decide)).trans hx27)
      ((hreg4 .x29 (by decide) (by decide) (by decide)).trans hx29)
      ((hreg4 .x30 (by decide) (by decide) (by decide)).trans hx30)
      (by rw [heval_same]; exact ((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hcurDig)
      (((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
      (by rw [hlinp_nil]; simp)

/-- Phase 1D-1: L2..L5 240b binary loop (`pc[141..179]` -> `pc[180]`), `≤ 850` steps, `≤ 4` calls. -/
theorem step_pos_bin240_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 141)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl2 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 2)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 850 4
      (input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g 4 + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 4 ∧
        s'.pc = pcWord 180 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + 32 + binPathOff g 4) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> 4) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 6) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 6 ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ prev, 2 ≤ prev → prev < 6 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g pw
  -- pc[141]: ADDI x29, x2, 64; pc[142]: ADDI x30, x2, 192
  have hst141 := step_ordinary oracle s 141 (.ADDI .x29 .x2 64#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x29 .x2 64#12)
  have hpc1 : s1.pc = pcWord 142 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst142 := step_ordinary oracle s1 142 (.ADDI .x30 .x2 192#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x30 .x2 192#12)
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
  have hx30_2 : s2.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x2),
      hfix.x2, se12_192, bv64_add]
  have hloop : ∀ m ≤ 4,
      PhaseOutcome oracle s2 (212 * m) m
        (input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g m + tailBytes tOff)
        (fun s' q tr =>
          q ≤ m ∧
          s'.pc = (if m = 4 then pcWord 180 else pcWord 143) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + 32 + binPathOff g m) tOff s' ∧
          MemEqOutside s2 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> m) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + m)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 6) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + m) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev, 2 ≤ prev → prev < 2 + m → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
    intro m hm
    induction m with
    | zero =>
      exact .continued s2 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s2)
        ⟨by decide, by simpa using hpc2,
         hfix.of_agree (fun r hr => hreg2 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         by simpa [binPathOff] using hcur.of_agree (fun r hr => hreg2 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         MemEqOutside.refl s2 256 320,
         (hreg2 .x22 (by decide) (by decide)).trans hx22,
         (hreg2 .x24 (by decide) (by decide)).trans hx24,
         (hreg2 .x8  (by decide) (by decide)).trans hx8,
         (hreg2 .x27 (by decide) (by decide)).trans hx27,
         hx29_2, hx30_2,
         ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hl2,
         ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hgap,
         fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have hbin_mon : binPathOff g k ≤ binPathOff g (k + 1) := by simp only [binPathOff]; omega
      rw [show 212 * (k + 1) = 212 * k + 212 by omega]
      refine (ih (by omega)).bind_dep
        (fun hlt => by simp only [binPathOff]; omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne4 : k ≠ 4 := by omega
          simp only [hne4, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem2 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
          have hstep_k := step_pos_bin240_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega)
            (fun hlt => by
              change input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g k + binStepBytes g k + tailBytes tOff at hlt
              simp only [binPathOff]; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', by simpa [binPathOff, Nat.add_assoc] using hcur',
            hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          intro prev hp1 hp2 x hx
          by_cases hprev : prev < 2 + k
          · exact (htr_k prev hp1 hprev x hx).append_left
          · have : prev = 2 + k := by omega
            subst this; exact (htr' x hx).append_right)
  have h4 := hloop 4 (by decide)
  have hpre : StepsTo oracle s s2 2 0 [] := by simpa using hst141.trans hst142
  cases h4 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (2 + k) q tr hr (by omega) hq (by simpa using hpre.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', _, hdig', hgap', htr'⟩ := hp
    refine .continued s' (2 + k) q tr (by omega) hq (by simpa using hpre.trans hs)
      ⟨hq', by simpa using hpc', hfix', hcur',
       (MemEqOutside.of_mem_eq hmem2 256 320).trans hout',
       hx22', hx24', hx8', hx27', hx29', hdig', hgap',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-- One iteration (`step < 9`, level `l = 6 + step ∈ 6..14`) of the 238b binary loop (`pc[181..207]`). -/
theorem step_pos_bin238_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 9)
    (s : MachineState) (hpc : s.pc = pcWord 181)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32 +
        binPathOff ((posAt input.positions ord).val / 3) (4 + step))
      (tOff + binTailOff ((posAt input.positions ord).val / 3) step) s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> (4 + step)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (6 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pCur := pOff + 24 + l0Bytes i + 32 + binPathOff g (4 + step)
    let tCur := tOff + binTailOff g step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 217 1
      (input.proof.length < pCur + binStepBytes g (4 + step) + tailBytes (tCur + binStepTails g step))
      (fun s' q tr =>
        q ≤ 1 ∧
        s'.pc = (if step + 1 = 9 then pcWord 208 else pcWord 181) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + binStepBytes g (4 + step)) (tCur + binStepTails g step) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> (4 + (step + 1))) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (6 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 (6 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g pCur tCur pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_lt : g < 5592406 := by change i.val / 3 < _; omega
  have hidx_lt : g >>> (4 + step) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hidx1_lt : g >>> (step + 5) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g >>> (4 + step)) / 2 = g >>> (step + 5) := by
    simp only [Nat.shiftRight_eq_div_pow, show step + 5 = (4 + step) + 1 by omega,
      Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hshift_eq : 4 + (step + 1) = step + 5 := by omega
  -- pc[181]: SRLI x22, x22, 1; pc[182]: XORI x28, x22, 1
  have hst181 := step_ordinary oracle s 181 (.SRLI .x22 .x22 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SRLI .x22 .x22 1#6)
  have hpc1 : s1.pc = pcWord 182 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx22_1 : s1.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, show (1#6 : BitVec 6).toNat = 1 by decide,
      bv64_shr _ 1 (Nat.lt_trans hidx_lt (by decide)), Nat.pow_one, hshr_step]
  have hst182 := step_ordinary oracle s1 182 (.XORI .x28 .x22 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.XORI .x28 .x22 1#12)
  have hpc2 : s2.pc = pcWord 183 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 ((g >>> (step + 5)) ^^^ 1) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22_1, se12_1]
    exact bv64_xor_one _ hidx1_lt
  have hreg2 : ∀ r, r ≠ .x22 → r ≠ .x28 → s2.getReg r = s.getReg r := fun r h22 h28 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
  -- pc[183]: LD x7, 8(x29) -> levelSize (6 + step)
  have ha183 : s2.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475936 + (32 * (6 + step) + 8)) := by
    rw [hreg2 .x29 (by decide) (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv183 : memoryArgumentsValid s2 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha183]
    exact accessValid_ofNat (68719475936 + (32 * (6 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst183 := step_ordinary oracle s2 183 (.LD .x7 .x29 8#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv183])
  let s3 := execInstrBr s2 (.LD .x7 .x29 8#12)
  have hpc3 : s3.pc = pcWord 184 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hsz_val : s2.getMem (BitVec.ofNat 64 (68719475936 + (32 * (6 + step) + 8))) =
      BitVec.ofNat 64 (levelSize (6 + step)) := by
    have hm2 : s2.getMem (BitVec.ofNat 64 (68719475936 + (32 * (6 + step) + 8))) =
        s.getMem (BitVec.ofNat 64 (68719475936 + (32 * (6 + step) + 8))) := by
      simp [MachineState.getMem, hmem2]
    rw [hm2, hhigh.getMem_eq (by omega) (by omega) (by omega),
      check_initial_data_dword input hvalid (32 * (6 + step) + 8) (by omega)]
    exact openingData_dword_1 ⟨6 + step, by omega⟩
  have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (levelSize (6 + step)) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha183]
    rw [MachineState.getReg_setReg_eq (by decide), hsz_val]
  have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 ((g >>> (step + 5)) ^^^ 1) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_2]
  have hsib_lt64 : (g >>> (step + 5)) ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' (g >>> (step + 5)) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega
  have hsz_lt64 : levelSize (6 + step) < 2 ^ 64 := by
    interval_cases step <;> decide
  -- pc[184]: BGEU x28, x7, pc[206]
  have hst184 := step_ordinary oracle s3 184 (.BGEU .x28 .x7 88#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.BGEU .x28 .x7 88#13)
  have hult184 : BitVec.ult (s3.getReg .x28) (s3.getReg .x7) =
      decide (((g >>> (step + 5)) ^^^ 1) < levelSize (6 + step)) := by
    rw [hx28_3, hx7_3, bv64_ult_eq _ _ hsib_lt64 hsz_lt64]
  have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
  have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h22 h28 => by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg2 r h22 h28]
  have hx22_3 : s3.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22)]
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x22), hx22_1]
  have hpre4 : StepsTo oracle s s4 4 0 [] := by
    simpa using (hst181.trans hst182).trans (hst183.trans hst184)
  -- Common loop footer at pc[206..207]
  have hfooter : ∀ (s206 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 211 → qMid ≤ 1 →
      StepsTo oracle s4 s206 kMid qMid trMid →
      s206.pc = pcWord 206 →
      CheckFixedRegs s206 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g (4 + step)) (tCur + binStepTails g step) s206 →
      MemEqOutside s s206 256 320 →
      s206.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) →
      s206.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
      s206.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
      s206.getReg .x27 = BitVec.ofNat 64 rem →
      s206.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + step)) →
      s206.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) →
      readBuffer s206 256 32 = pw.evalLevel c96 (6 + (step + 1)) →
      readBuffer s206 320 32 = 0 →
      (∀ x ∈ pw.levelInput c96 (6 + step), InTrace h768 oracle trMid x) →
      PhaseOutcome oracle s 217 1
        (input.proof.length < pCur + binStepBytes g (4 + step) + tailBytes (tCur + binStepTails g step))
        (fun s' q tr =>
          q ≤ 1 ∧
          s'.pc = (if step + 1 = 9 then pcWord 208 else pcWord 181) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g (4 + step)) (tCur + binStepTails g step) s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> (4 + (step + 1))) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (6 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInput c96 (6 + step), InTrace h768 oracle tr x) := by
    intro s206 kMid qMid trMid hkMid hqMid hmid hpc206 hfix206 hcur206 hout206 h22 h24 h8 h27 h29 h30 hdig206 hgap206 htr206
    have hst206 := step_ordinary oracle s206 206 (.ADDI .x29 .x29 32#12) (by decide) hpc206 rfl (by intro h; cases h) rfl
    let s207 := execInstrBr s206 (.ADDI .x29 .x29 32#12)
    have hpc207 : s207.pc = pcWord 207 := by simp only [s207, execInstrBr, MachineState.setPC, hpc206, pcWord_add_four]
    have hx29_207 : s207.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + (step + 1))) := by
      simp only [s207, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_207 : s207.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) := by
      simp only [s207, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), h30]
    have hst207 := step_ordinary oracle s207 207 (.BNE .x29 .x30 8088#13) (by decide) hpc207 rfl (by intro h; cases h) rfl
    let sFin := execInstrBr s207 (.BNE .x29 .x30 8088#13)
    have hmemFin : sFin.mem = s206.mem := by
      simp only [sFin, execInstrBr]; split <;> simp [s207, execInstrBr, mem_setPC, mem_setReg]
    have hregFin : ∀ r, r ≠ .x29 → sFin.getReg r = s206.getReg r := fun r h29r => by
      have h208 : sFin.getReg r = s207.getReg r := by
        simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
      rw [h208]
      simp only [s207, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h29r.symm
    have hx29_Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + (step + 1))) := by
      have : sFin.getReg .x29 = s207.getReg .x29 := by
        simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
      exact this.trans hx29_207
    have hpcFin : sFin.pc = if step + 1 = 9 then pcWord 208 else pcWord 181 := by
      have hne_iff : (s207.getReg .x29 != s207.getReg .x30) = decide (step + 1 ≠ 9) := by
        rw [hx29_207, hx30_207, bv64_bne_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      by_cases hdone : step + 1 = 9
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, ite_true, MachineState.setPC, hpc207, pcWord_add_four]
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_false_eq_true, decide_true,
          ite_true, ite_false, MachineState.setPC, hpc207]; exact pc_207_branch
    have htot := (hpre4.trans hmid).trans (hst206.trans hst207)
    refine .continued sFin (4 + kMid + 2) qMid trMid (by omega) hqMid (by simpa [Nat.add_assoc] using htot)
      ⟨hqMid, hpcFin,
       hfix206.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       hcur206.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
       hout206.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       by rw [hshift_eq]; exact (hregFin .x22 (by decide)).trans h22,
       (hregFin .x24 (by decide)).trans h24,
       (hregFin .x8  (by decide)).trans h8,  (hregFin .x27 (by decide)).trans h27,
       hx29_Fin, (hregFin .x30 (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig206,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap206,
       htr206⟩
  -- Branch on whether sibling exists at level `6 + step`
  by_cases hpair : ((g >>> (step + 5)) ^^^ 1) < levelSize (6 + step)
  · -- Paired: binStepBytes g (4 + step) = 29, binStepTails g step = 1
    have hsb : binStepBytes g (4 + step) = 29 := by
      unfold binStepBytes
      rw [show 4 + step + 1 = step + 5 by omega, show 2 + (4 + step) = 6 + step by omega,
        if_pos hpair, if_neg (by omega)]
    have hst_t : binStepTails g step = 1 := by unfold binStepTails; exact if_pos hpair
    have hpc4 : s4.pc = pcWord 185 := by
      simp only [s4, execInstrBr, hult184, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult184, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult184, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) := by
      simpa [s4, execInstrBr, hult184, hpair, MachineState.getReg_setPC] using hx22_3
    -- pc[185]: ANDI x7, x22, 1; pc[186]: BEQ x7, x0, pc[198]
    have hst185 := step_ordinary oracle s4 185 (.ANDI .x7 .x22 1#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ANDI .x7 .x22 1#12)
    have hpc5 : s5.pc = pcWord 186 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hx7_5 : s5.getReg .x7 = BitVec.ofNat 64 ((g >>> (step + 5)) % 2) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hx22_4, se12_1]
      exact bv64_and_one _ (by omega)
    have hst186 := step_ordinary oracle s5 186 (.BEQ .x7 .x0 48#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BEQ .x7 .x0 48#13)
    have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
    have hst46 : StepsTo oracle s4 s6 2 0 [] := by simpa using hst185.trans hst186
    let sibD := pw.binSib (6 + step)
    have hsibD_eq : sibD = proofDigest238 s0 input.proof.length (11341403200 + pCur) tCur := by
      simp only [sibD, pw, parsePartialWitness, show 6 + step ≠ 1 by omega, ite_false,
        show ¬ (2 ≤ 6 + step ∧ 6 + step ≤ 5) by omega,
        show 6 ≤ 6 + step ∧ 6 + step ≤ 14 by omega, and_self, ite_true,
        show 6 + step - 2 = 4 + step by omega, show 6 + step - 6 = step by omega,
        pCur, tCur, Nat.add_assoc]
      dsimp only [g]
    let curD := pw.evalLevel c96 (6 + step)
    let inpL : BitVec 768 :=
      if (g >>> (step + 5)) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
    have hidx_pw : (pw.index.val / 3) >>> (6 + step - 1) = g >>> (step + 5) := by
      change g >>> (6 + step - 1) = g >>> (step + 5)
      exact congrArg (fun k => g >>> k) (by omega)
    have heval_next : pw.evalLevel c96 (6 + (step + 1)) = mask238 (c96 inpL) := by
      rw [show 6 + (step + 1) = (6 + step) + 1 by omega,
        evalLevel_succ_of_ge1 c96 pw (6 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_pos hpair]
      unfold maskLevel
      rw [if_neg (by omega), if_neg (by omega)]
    have hlinp : pw.levelInput c96 (6 + step) = [inpL] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_pos hpair]
    -- Common compression + mask238 at pc[200..205] -> pc[206]
    have hcall200 : ∀ (s200 : MachineState) (kA : Nat),
        kA ≤ 203 →
        StepsTo oracle s6 s200 kA 0 [] →
        s200.pc = pcWord 200 →
        CheckFixedRegs s200 →
        ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s200 →
        MemEqOutside s s200 256 320 →
        s200.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) →
        s200.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
        s200.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
        s200.getReg .x27 = BitVec.ofNat 64 rem →
        s200.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + step)) →
        s200.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) →
        readBuffer s200 256 96 = inpL →
        readBuffer s200 320 32 = 0 →
        PhaseOutcome oracle s 217 1
          (input.proof.length < pCur + binStepBytes g (4 + step) + tailBytes (tCur + binStepTails g step))
          (fun s' q tr =>
            q ≤ 1 ∧ s'.pc = (if step + 1 = 9 then pcWord 208 else pcWord 181) ∧
            CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length (pCur + binStepBytes g (4 + step)) (tCur + binStepTails g step) s' ∧
            MemEqOutside s s' 256 320 ∧
            s'.getReg .x22 = BitVec.ofNat 64 (g >>> (4 + (step + 1))) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + (step + 1))) ∧
            s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
            readBuffer s' 256 32 = pw.evalLevel c96 (6 + (step + 1)) ∧
            readBuffer s' 320 32 = 0 ∧
            ∀ x ∈ pw.levelInput c96 (6 + step), InTrace h768 oracle tr x) := by
      intro s200 kA hkA hmidA hpc200 hfix200 hcur200 hout200 h22 h24 h8 h27 h29 h30 hinp200 hgap200
      have hst200 := step_ordinary oracle s200 200 (.ADDI .x10 .x21 0#12) (by decide) hpc200 rfl (by intro h; cases h) rfl
      let s201 := execInstrBr s200 (.ADDI .x10 .x21 0#12)
      have hpc201 : s201.pc = pcWord 201 := by simp only [s201, execInstrBr, MachineState.setPC, hpc200, pcWord_add_four]
      have hst201 := step_ordinary oracle s201 201 (.ADDI .x12 .x21 0#12) (by decide) hpc201 rfl (by intro h; cases h) rfl
      let s202 := execInstrBr s201 (.ADDI .x12 .x21 0#12)
      have hpc202 : s202.pc = pcWord 202 := by simp only [s202, execInstrBr, MachineState.setPC, hpc201, pcWord_add_four]
      have hmem202 : s202.mem = s200.mem := by simp [s202, s201, execInstrBr, mem_setPC, mem_setReg]
      have hreg202 : ∀ r, r ≠ .x10 → r ≠ .x12 → s202.getReg r = s200.getReg r := fun r h10 h12 => by
        simp only [s202, s201, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_202 : s202.getReg .x10 = 256#64 := by
        simp only [s202, s201, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix200.x21, se12_0, BitVec.add_zero]
      have hx12_202 : s202.getReg .x12 = 256#64 := by
        simp only [s202, s201, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hfix200.x21, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h768 oracle s202 202 256 256 (by decide) hpc202 rfl
        ((hreg202 .x5 (by decide) (by decide)).trans hfix200.x5)
        ((hreg202 .x11 (by decide) (by decide)).trans hfix200.x11)
        ((hreg202 .x13 (by decide) (by decide)).trans hfix200.x13)
        hx10_202 hx12_202 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem202 0 0).readBuffer_eq (by decide) (by omega), hinp200] at hec
      let s203 := writeBits s202 (BitVec.ofNat 64 256) (c96 inpL)
      have hpc203 : s203.pc = pcWord 203 := by simp only [s203, writeBits, MachineState.setPC, hpc202, pcWord_add_four]
      have hreg203 : ∀ r, r ≠ .x10 → r ≠ .x12 → s203.getReg r = s200.getReg r := fun r h10 h12 =>
        (writeBits_register s202 _ _ r).trans (hreg202 r h10 h12)
      obtain ⟨s206, hs206, hpc206, hreg206, hdig206, hout206⟩ :=
        step_mask238 oracle 203 .x21 s203 256 (by decide) (by decide) rfl rfl rfl hpc203
          ((hreg203 .x21 (by decide) (by decide)).trans hfix200.x21)
          ((hreg203 .x9 (by decide) (by decide)).trans hfix200.x9)
          (by decide) (by unfold MEMORY_BYTES; decide)
      have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s206.getReg r = s200.getReg r :=
        fun r h6 h10 h12 => (hreg206 r h6).trans (hreg203 r h10 h12)
      have hout_all : MemEqOutside s s206 256 320 :=
        hout200.trans ((MemEqOutside.of_mem_eq hmem202 256 320).trans
          (((MemEqOutside_writeBits_digest s202 256 _ (by decide)).mono (by omega) (by omega)).trans
            (hout206.mono (by omega) (by omega))))
      have hdig_eq : readBuffer s206 256 32 = pw.evalLevel c96 (6 + (step + 1)) := by
        rw [heval_next, hdig206, writeBits_readBuffer_digest]
      have hgap206 : readBuffer s206 320 32 = 0 := by
        rw [hout206.readBuffer_eq (by decide) (by omega),
          (MemEqOutside_writeBits_digest s202 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
          (MemEqOutside.of_mem_eq hmem202 0 0).readBuffer_eq (by decide) (by omega), hgap200]
      have htot := (hst46.trans hmidA).trans (((hst200.trans hst201).trans hec).trans hs206)
      refine hfooter s206 (2 + kA + 6) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
        (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
        hpc206
        (hfix200.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (by rw [hsb, hst_t]; exact hcur200.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        hout_all
        ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
        ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
        ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
        ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
        ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
        ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
        hdig_eq hgap206 ?_
      intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
      exact InTrace.singleton h768 oracle inpL
    by_cases heven : (g >>> (step + 5)) % 2 = 0
    · -- Even: jump to pc[198..199] -> pc[200]
      have hx7z : s5.getReg .x7 = 0#64 := by rw [hx7_5, heven]
      have hpc6 : s6.pc = pcWord 198 := by
        simp only [s6, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
          MachineState.setPC, hpc5]; exact pc_186_branch
      have hmem6 : s6.mem = s.mem := by
        simpa [s6, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem5
      have hreg65 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
        simp only [s6, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
      have hreg6 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h7 h22 h28 => by
        rw [hreg65]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) := by
        rw [hreg65]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22), hx22_4]
      have hst198 := step_ordinary oracle s6 198 (.ADDI .x12 .x21 32#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ADDI .x12 .x21 32#12)
      have hpc7 : s7.pc = pcWord 199 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
      have hreg7 : ∀ r, r ≠ .x12 → s7.getReg r = s6.getReg r := fun r hr => by
        simp only [s7, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
      have hcur7 : ProofCursor s0 input.proof.length pCur tCur s7 :=
        hcur.of_agree (fun r hr => (hreg7 r (isCursorReg_ne_of_false hr rfl)).trans
          (hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 199 s7 pCur tCur 288
        (by decide) rfl hpc7 hcur7 (hhigh.trans (MemEqOutside.of_mem_eq hmem7 0 4294971392))
        (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide),
              hreg6 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
        (by decide)
      cases hread with
      | rejected kR qR trR hrR hkR hqR hhR =>
        have htot := ((hpre4.trans hst46).trans hst198).halt hhR
        exact .rejected (4 + 2 + 1 + kR) qR trR (by rw [hsb, hst_t]; exact hrR) (by omega) (by omega)
          (by simpa only [Nat.zero_add, List.nil_append] using htot)
      | continued s8 kR qR trR hkR hqR hs8 hp8 =>
        obtain ⟨rfl, rfl, hpc8, hcur8, hreg8, hdig8, hout8⟩ := hp8
        have hout_all : MemEqOutside s s8 288 320 :=
          (MemEqOutside.of_mem_eq hmem7 288 320).trans hout8
        have hreg8_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 →
            r ≠ .x22 → r ≠ .x25 → r ≠ .x28 → r ≠ .x31 → s8.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h12 h22 h25 h28 h31 =>
            (hreg8 r h1 h3 h4 h6 h7 h12 h25 h31).trans ((hreg7 r h12).trans (hreg6 r h7 h22 h28))
        have hgap8 : readBuffer s8 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp8 : readBuffer s8 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s8 256 hgap8]
          have hL : readBuffer s8 256 32 = curD :=
            (hout_all.readBuffer_eq (by decide) (by omega)).trans hcurDig
          have hR : readBuffer s8 288 32 = sibD := hdig8.trans hsibD_eq.symm
          rw [hL, hR]; simp only [inpL, heven, ite_true]
        refine hcall200 s8 (1 + kR) (by omega)
          ((hst198.trans hs8).eq_of rfl (by omega) rfl (by simp)) hpc8
          (hfix.of_agree (fun r hr => hreg8_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur8 (hout_all.mono (by omega) (by omega))
          ((hreg8 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg7 .x22 (by decide)).trans hx22_6))
          ((hreg8_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg8_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg8_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg8_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg8_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp8 hgap8
    · -- Odd: fall through to pc[187..197] -> pc[200]
      have hodd : (g >>> (step + 5)) % 2 = 1 := by omega
      have hx7o : s5.getReg .x7 = 1#64 := by rw [hx7_5, hodd]
      have hpc6 : s6.pc = pcWord 187 := by
        simp only [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s.mem := by
        simpa [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          MachineState.setPC] using hmem5
      have hreg65 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
        simp only [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
      have hreg6 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h7 h22 h28 => by
        rw [hreg65]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) := by
        rw [hreg65]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22), hx22_4]
      have hcp : ∀ j < 4,
          checkInstr (187 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
          checkInstr (187 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
      obtain ⟨s7, hs7, hpc7, hreg7, hcopy7, hout7⟩ :=
        step_copy_dwords oracle 187 4 .x21 .x21 0 32 s6 256 256 (by decide) (by decide)
          (by decide) (by decide) (by decide) hcp hpc6
          ((hreg6 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
          ((hreg6 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
      have hst195 := step_ordinary oracle s7 195 (.ADDI .x12 .x21 0#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
      let s8 := execInstrBr s7 (.ADDI .x12 .x21 0#12)
      have hpc8 : s8.pc = pcWord 196 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
      have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, mem_setPC, mem_setReg]
      have hreg8 : ∀ r, r ≠ .x12 → s8.getReg r = s7.getReg r := fun r hr => by
        simp only [s8, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
      have hcur8 : ProofCursor s0 input.proof.length pCur tCur s8 :=
        hcur.of_agree (fun r hr => (hreg8 r (isCursorReg_ne_of_false hr rfl)).trans
          ((hreg7 r (isCursorReg_ne_of_false hr rfl)).trans
            (hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))))
      have hout_s8 : MemEqOutside s s8 288 320 :=
        (MemEqOutside.of_mem_eq hmem6 288 320).trans (hout7.trans (MemEqOutside.of_mem_eq hmem8 288 320))
      have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 196 s8 pCur tCur 256
        (by decide) rfl hpc8 hcur8 (hhigh.trans (hout_s8.mono (by omega) (by omega)))
        (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide), hreg7 .x21 (by decide),
              hreg6 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
        (by decide)
      cases hread with
      | rejected kR qR trR hrR hkR hqR hhR =>
        have htot := (((hpre4.trans hst46).trans hs7).trans hst195).halt hhR
        exact .rejected (4 + 2 + 8 + 1 + kR) qR trR (by rw [hsb, hst_t]; exact hrR) (by omega) (by omega)
          (by simpa only [Nat.zero_add, List.nil_append] using htot)
      | continued s9 kR qR trR hkR hqR hs9 hp9 =>
        obtain ⟨rfl, rfl, hpc9, hcur9, hreg9, hdig9, hout9⟩ := hp9
        have hst197 := step_ordinary oracle s9 197 (.JAL .x0 12#21) (by decide) hpc9 rfl (by intro h; cases h) rfl
        let s10 := execInstrBr s9 (.JAL .x0 12#21)
        have hpc10 : s10.pc = pcWord 200 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9]; exact pc_197_jal
        have hmem10 : s10.mem = s9.mem := by simp [s10, execInstrBr, mem_setPC, mem_setReg]
        have hreg10_9 : ∀ r, s10.getReg r = s9.getReg r := fun r => by
          simp [s10, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have hout_all : MemEqOutside s s10 256 320 :=
          (hout_s8.mono (by omega) (by omega)).trans
            ((hout9.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem10 256 320))
        have hreg10_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 →
            r ≠ .x22 → r ≠ .x25 → r ≠ .x28 → r ≠ .x31 → s10.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h12 h22 h25 h28 h31 =>
            (hreg10_9 r).trans ((hreg9 r h1 h3 h4 h6 h7 h12 h25 h31).trans
              ((hreg8 r h12).trans ((hreg7 r h6).trans (hreg6 r h7 h22 h28))))
        have hgap10 : readBuffer s10 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp10 : readBuffer s10 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s10 256 hgap10]
          have hL : readBuffer s10 256 32 = sibD :=
            ((MemEqOutside.of_mem_eq hmem10 0 0).readBuffer_eq (by decide) (by omega)).trans
              (hdig9.trans hsibD_eq.symm)
          have hcur' : readBuffer s 256 32 = curD := hcurDig
          have hR : readBuffer s10 288 32 = curD := by
            rw [(MemEqOutside.of_mem_eq hmem10 0 0).readBuffer_eq (by decide) (by omega),
              hout9.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by decide) (by omega), ← hcur']
            apply readBuffer_congr2; intro j hj
            have hc := hcopy7 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem6] at hc ⊢
            exact hc
          rw [hL, hR]; simp only [inpL, heven, ite_false]
        refine hcall200 s10 (8 + 1 + kR + 1) (by omega)
          ((((hs7.trans hst195).trans hs9).trans hst197).eq_of rfl (by omega) rfl (by simp)) hpc10
          (hfix.of_agree (fun r hr => hreg10_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          (hcur9.of_agree (fun r _ => hreg10_9 r))
          hout_all
          ((hreg10_9 .x22).trans ((hreg9 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg8 .x22 (by decide)).trans ((hreg7 .x22 (by decide)).trans hx22_6))))
          ((hreg10_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg10_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg10_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg10_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg10_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp10 hgap10
  · -- Promoted (unpaired): binStepBytes = 0, binStepTails = 0, jump directly to pc[206]
    have hsb : binStepBytes g (4 + step) = 0 := by
      unfold binStepBytes
      rw [show 4 + step + 1 = step + 5 by omega, show 2 + (4 + step) = 6 + step by omega, if_neg hpair]
    have hst_t : binStepTails g step = 0 := by unfold binStepTails; exact if_neg hpair
    have hpc4 : s4.pc = pcWord 206 := by
      simp only [s4, execInstrBr, hult184, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc3]; exact pc_184_branch
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult184, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult184, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 5)) := by
      simpa [s4, execInstrBr, hult184, hpair, MachineState.getReg_setPC] using hx22_3
    have hidx_pw : (pw.index.val / 3) >>> (6 + step - 1) = g >>> (step + 5) := by
      change g >>> (6 + step - 1) = g >>> (step + 5)
      exact congrArg (fun k => g >>> k) (by omega)
    have heval_same : pw.evalLevel c96 (6 + (step + 1)) = pw.evalLevel c96 (6 + step) := by
      rw [show 6 + (step + 1) = (6 + step) + 1 by omega,
        evalLevel_succ_of_ge1 c96 pw (6 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_neg hpair]
    have hlinp_nil : pw.levelInput c96 (6 + step) = [] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_neg hpair]
    refine hfooter s4 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s4) hpc4
      (hfix.of_agree (fun r hr => hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (by rw [hsb, hst_t, Nat.add_zero, Nat.add_zero]
          exact hcur.of_agree (fun r hr => hreg4 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (MemEqOutside.of_mem_eq hmem4 256 320) hx22_4
      ((hreg4 .x24 (by decide) (by decide) (by decide)).trans hx24)
      ((hreg4 .x8  (by decide) (by decide) (by decide)).trans hx8)
      ((hreg4 .x27 (by decide) (by decide) (by decide)).trans hx27)
      ((hreg4 .x29 (by decide) (by decide) (by decide)).trans hx29)
      ((hreg4 .x30 (by decide) (by decide) (by decide)).trans hx30)
      (by rw [heval_same]; exact ((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hcurDig)
      (((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
      (by rw [hlinp_nil]; simp)

/-- Phase 1D-2: L6..L14 238b binary loop (`pc[180..207]` -> `pc[208]`), `≤ 1954` steps, `≤ 9` calls. -/
theorem step_pos_bin238_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 180)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32 +
        binPathOff ((posAt input.positions ord).val / 3) 4) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> 4))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 6))
    (hl6 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 6)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 1954 9
      (input.proof.length < pOff + recordLen i + tailBytes (tOff + recordTailCount i))
      (fun s' q tr =>
        q ≤ 9 ∧
        s'.pc = pcWord 208 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + recordLen i) (tOff + recordTailCount i) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> 13) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 15 ∧
        ∀ prev, 6 ≤ prev → prev ≤ 14 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g pw
  -- pc[180]: ADDI x30, x2, 480
  have hst180 := step_ordinary oracle s 180 (.ADDI .x30 .x2 480#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x30 .x2 480#12)
  have hpc1 : s1.pc = pcWord 181 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x30 → s1.getReg r = s.getReg r := fun r h30 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h30.symm
  have hx30_1 : s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hfix.x2, se12_480, bv64_add]
  have hloop : ∀ m ≤ 9,
      PhaseOutcome oracle s1 (217 * m) m
        (input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g (4 + m) + tailBytes (tOff + binTailOff g m))
        (fun s' q tr =>
          q ≤ m ∧
          s'.pc = (if m = 9 then pcWord 208 else pcWord 181) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + 32 + binPathOff g (4 + m)) (tOff + binTailOff g m) s' ∧
          MemEqOutside s1 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> (4 + m)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (6 + m)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (6 + m) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev, 6 ≤ prev → prev < 6 + m → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
    intro m hm
    induction m with
    | zero =>
      exact .continued s1 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s1)
        ⟨by decide, by simpa using hpc1,
         hfix.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl)),
         by simpa [binTailOff] using hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl)),
         MemEqOutside.refl s1 256 320,
         (hreg1 .x22 (by decide)).trans hx22,
         (hreg1 .x24 (by decide)).trans hx24,
         (hreg1 .x8  (by decide)).trans hx8,
         (hreg1 .x27 (by decide)).trans hx27,
         (hreg1 .x29 (by decide)).trans hx29, hx30_1,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by decide) (by omega)).trans hl6,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by decide) (by omega)).trans hgap,
         fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have hbin_mon : binPathOff g (4 + k) ≤ binPathOff g (4 + (k + 1)) := by
        rw [show 4 + (k + 1) = (4 + k) + 1 by omega]; simp only [binPathOff]; omega
      have ht_mon : tailBytes (tOff + binTailOff g k) ≤ tailBytes (tOff + binTailOff g (k + 1)) :=
        tailBytes_mono (by simp only [binTailOff]; omega)
      rw [show 217 * (k + 1) = 217 * k + 217 by omega]
      refine (ih (by omega)).bind_dep
        (fun hlt => by omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne9 : k ≠ 9 := by omega
          simp only [hne9, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem1 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
          have hstep_k := step_pos_bin238_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega)
            (fun hlt => by
              change input.proof.length <
                pOff + 24 + l0Bytes i + 32 + binPathOff g (4 + k) + binStepBytes g (4 + k) +
                  tailBytes (tOff + binTailOff g k + binStepTails g k) at hlt
              rw [show 4 + (k + 1) = (4 + k) + 1 by omega]
              simp only [binPathOff, binTailOff, Nat.add_assoc] at hlt ⊢; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', ?_, hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          · rw [show 4 + (k + 1) = (4 + k) + 1 by omega]
            simpa [binPathOff, binTailOff, Nat.add_assoc] using hcur'
          · intro prev hp1 hp2 x hx
            by_cases hprev : prev < 6 + k
            · exact (htr_k prev hp1 hprev x hx).append_left
            · have : prev = 6 + k := by omega
              subst this; exact (htr' x hx).append_right)
  have h9 := hloop 9 (by decide)
  cases h9 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (1 + k) q tr (by simpa [recordLen, recordTailCount, Nat.add_assoc] using hr) (by omega) hq
      (by simpa using hst180.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', _, _, hdig', _, htr'⟩ := hp
    refine .continued s' (1 + k) q tr (by omega) hq (by simpa using hst180.trans hs)
      ⟨hq', by simpa using hpc', hfix',
       by simpa [recordLen, recordTailCount, Nat.add_assoc] using hcur',
       (MemEqOutside.of_mem_eq hmem1 256 320).trans hout',
       hx22', hx24', hx8', hx27', hdig',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-! #### Phase 1E and Full Per-Position Loop (`pc[208..242]`, `pc[22] -> pc[243]`) -/

theorem gapOffset_disjoint {a b : Nat} (hne : a ≠ b) :
    gapOffset a + 32 ≤ gapOffset b ∨ gapOffset b + 32 ≤ gapOffset a := by
  unfold gapOffset; omega

theorem gapOffset_disjoint_gap (c q : Nat) :
    gapOffset c + 32 ≤ 96 * q + 64 ∨ 96 * q + 96 ≤ gapOffset c := by
  unfold gapOffset; omega

private def capAddrInstrs : List Instr :=
  [.SRLI .x22 .x22 1#6, .SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6,
   .SLLI .x6 .x6 5#6, .ADD .x28 .x19 .x6, .ADD .x29 .x18 .x22]

private theorem pc_242_branch : pcWord 242 + signExtend13 7312#13 = pcWord 22 := by decide
private theorem pc_226_jal : pcWord 226 + signExtend21 52#21 = pcWord 239 := by decide
private theorem pc_215_branch : pcWord 215 + signExtend13 48#13 = pcWord 227 := by decide
private theorem checkInstr_214 : checkInstr 214 = .base (.LBU .x7 .x29 0#12) := rfl
private theorem checkInstr_215 : checkInstr 215 = .base (.BNE .x7 .x0 48#13) := rfl
private theorem checkInstr_216 : checkInstr 216 = .base (.ADDI .x7 .x0 1#12) := rfl
private theorem checkInstr_217 : checkInstr 217 = .base (.SB .x29 .x7 0#12) := rfl
private theorem checkInstr_226 : checkInstr 226 = .base (.JAL .x0 52#21) := rfl
private theorem checkInstr_239 : checkInstr 239 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_240 : checkInstr 240 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_241 : checkInstr 241 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_242 : checkInstr 242 = .base (.BNE .x27 .x0 7312#13) := rfl

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
    checkInstr (208 + j) = .base (capAddrInstrs[j]'hj) := by
  intro j hj; have hj' : j < 6 := hj; interval_cases j <;> rfl

private theorem hpure_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    Instruction.base (capAddrInstrs[j]'hj) ≠ .base .ECALL ∧
    ∀ st, ordinaryStep st (.base (capAddrInstrs[j]'hj)) = some (execInstrBr st (capAddrInstrs[j]'hj)) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).mem = st.mem := by
  intro j hj; have hj' : j < 6 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩

private theorem hcode_capCopy : ∀ j < 4,
    checkInstr (218 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
    checkInstr (218 + 2 * j + 1) = .base (.SD .x28 .x6 (BitVec.ofNat 12 (0 + 8 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem hcode_capCmp : ∀ j < 4,
    checkInstr (227 + 3 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (227 + 3 * j + 1) = .base (.LD .x7 .x28 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (227 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (330 - (227 + 3 * j + 2))))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

private theorem zero64_eq_ofNat : (0#64 : Word) = BitVec.ofNat 64 0 := rfl

private theorem zero_lt_pow64 : 0 < 2 ^ 64 := Nat.pow_pos (Nat.succ_pos 1)

private theorem step_tail_239 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 239)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 240 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 239 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_239
     (by intro h; cases h) (ordinaryStep_ADDI s .x24 .x24 8#12),
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 239)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (6912218176 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 6912218176 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_240 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 240)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (7046435904 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 241 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 240 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_240
     (by intro h; cases h) (ordinaryStep_ADDI s .x8 .x8 256#12),
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 240)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (7046435904 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 7046435904 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_241 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 241)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 242 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 241 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_241
     (by intro h; cases h) (ordinaryStep_ADDI s .x27 .x27 4095#12),
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 241)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_tail_242 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 242)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 243 else pcWord 22) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x27 .x0 7312#13),
    step_ordinary oracle s 242 (.BNE .x27 .x0 7312#13) (by decide) hpc checkInstr_242
      (by intro h; cases h) (ordinaryStep_BNE s .x27 .x0 7312#13),
    ?_, execInstrBr_BNE_mem s .x27 .x0 7312#13, execInstrBr_BNE_getReg s .x27 .x0 7312#13⟩
  have hne_iff : (s.getReg .x27 != s.getReg .x0) = decide (rem1 ≠ 0) := by
    rw [getReg_x0 s, zero64_eq_ofNat, h27]
    exact bv64_bne_eq rem1 0 hrem_lt zero_lt_pow64
  by_cases hz : rem1 = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x27 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false s .x27 .x0 7312#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 242))
  · rw [if_neg hz]
    have ht : (s.getReg .x27 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true s .x27 .x0 7312#13 ht).trans
      ((congrArg (· + signExtend13 7312#13) hpc).trans pc_242_branch)

private theorem step_pos_cap_store_tail (oracle : Oracle) (s0 : MachineState)
    (proofLen ord pOffNext tOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s239 : MachineState) (hpc239 : s239.pc = pcWord 239)
    (hfix239 : CheckFixedRegs s239)
    (hcur239 : ProofCursor s0 proofLen pOffNext tOffNext s239)
    (h24 : s239.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (h8  : s239.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (h27 : s239.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s239 sFin 4 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 243 else pcWord 22) ∧
      CheckFixedRegs sFin ∧
      ProofCursor s0 proofLen pOffNext tOffNext sFin ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s239.mem := by
  obtain ⟨s240, hs1, hpc240, hmem1, hx24_1, hreg1⟩ := step_tail_239 oracle ord s239 hpc239 h24
  obtain ⟨s241, hs2, hpc241, hmem2, hx8_2, hreg2⟩ :=
    step_tail_240 oracle ord s240 hpc240 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s242, hs3, hpc242, hmem3, hx27_3, hreg3⟩ :=
    step_tail_241 oracle rem1 s241 hpc241 ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27))
  obtain ⟨sFin, hs4, hpcFin, hmem4, hreg4⟩ :=
    step_tail_242 oracle rem1 (Nat.lt_of_succ_lt hrem_lt) s242 hpc242 hx27_3
  have hsteps : StepsTo oracle s239 sFin 4 0 [] :=
    (((hs1.trans hs2).trans hs3).trans hs4).eq_of rfl rfl rfl rfl
  have hmemFin : sFin.mem = s239.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x27 → sFin.getReg r = s239.getReg r :=
    fun r h24r h8r h27r => (hreg4 r).trans ((hreg3 r h27r).trans ((hreg2 r h8r).trans (hreg1 r h24r)))
  exact ⟨sFin, hsteps, hpcFin,
    hfix239.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hcur239.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    (hreg4 .x24).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1)),
    (hreg4 .x8).trans ((hreg3 .x8 (by decide)).trans hx8_2),
    (hreg4 .x27).trans hx27_3, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 342)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 216) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 256#64)
    (hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c))
    (hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c))
    (d15 : Digest) (hd15 : readBuffer s 256 32 = d15) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 239 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
      readBuffer s7 (8192 + gapOffset c) 32 = d15 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
        (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst216 := step_ordinary oracle s3 216 (.ADDI .x7 .x0 1#12) (by decide) hpc3 checkInstr_216 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 217 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx29_4 : s4.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha217 : s4.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_4, se12_0, BitVec.add_zero]
  have hv217 : memoryArgumentsValid s4 (.SB .x29 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha217]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst217 := step_ordinary oracle s4 217 (.SB .x29 .x7 0#12) (by decide) hpc4 checkInstr_217 (by intro h; cases h)
    (by simp [ordinaryStep, hv217])
  let s5 := execInstrBr s4 (.SB .x29 .x7 0#12)
  have hpc5 : s5.pc = pcWord 218 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (4096 + c)) 1#8).getByte q := by
    intro q
    simp only [s5, execInstrBr, ha217, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
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
    step_copy_dwords oracle 218 4 .x21 .x28 0 0 s5 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCopy hpc5
      ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21)
      hx28_5 (by decide) (by omega) (by unfold MEMORY_BYTES; decide) (by omega) (by omega)
  have hst226 := step_ordinary oracle s6 226 (.JAL .x0 52#21) (by decide) hpc6 checkInstr_226 (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 239 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_226_jal
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
  refine ⟨s7, by simpa using ((hst216.trans hst217).trans hs6).trans hst226, hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1E: store or duplicate-check cap leaf at L15 and advance loop counters (`pc[208..242]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext tOffNext rem1 : Nat) (hord : ord < input.positions.card)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 208)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOffNext tOffNext s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> 13))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1))
    (marked : Bool)
    (hmark : s.getByte (BitVec.ofNat 64 (4096 + capLeafOf (posAt input.positions ord))) =
      if marked then 1#8 else 0#8)
    (d15 : Digest) (hd15 : readBuffer s 256 32 = d15) :
    let s0 := submission.initialState .check input
    let c := capLeafOf (posAt input.positions ord)
    PhaseOutcome oracle s 30 0
      (marked = true ∧ d15 ≠ readBuffer s (8192 + gapOffset c) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = (if rem1 = 0 then pcWord 243 else pcWord 22) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pOffNext tOffNext s' ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
        readBuffer s' (8192 + gapOffset c) 32 = d15 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
          (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro s0 c
  have hc_lt : c < 342 := capLeafOf_lt (posAt input.positions ord)
  have hi_lt : (posAt input.positions ord).val < 16777216 := (posAt input.positions ord).isLt
  have h13_lt : ((posAt input.positions ord).val / 3) >>> 13 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_shr : (((posAt input.positions ord).val / 3) >>> 13) / 2 = c := by
    unfold c capLeafOf
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul, show (2 ^ 13 : Nat) * 2 = 2 ^ 14 by decide]
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 208 capAddrInstrs s (by decide) hcode_capAddr hpure_capAddr hpc
  let s1 := runInstrs s capAddrInstrs
  have hs1 : StepsTo oracle s s1 6 0 [] := hs1
  have hpc1 : s1.pc = pcWord 214 := hpc1
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
  -- pc[214]: LBU x7, 0(x29)
  have ha214 : s1.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_1, se12_0, BitVec.add_zero]
  have hv214 : memoryArgumentsValid s1 (.LBU .x7 .x29 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha214]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst214 := step_ordinary oracle s1 214 (.LBU .x7 .x29 0#12) (by decide) hpc1 checkInstr_214 (by intro h; cases h)
    (by simp [ordinaryStep, hv214])
  let s2 := execInstrBr s1 (.LBU .x7 .x29 0#12)
  have hpc2 : s2.pc = pcWord 215 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1'
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha214]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s1.getByte (BitVec.ofNat 64 (4096 + c)) = if marked then 1#8 else 0#8 := by
      simpa only [c, MachineState.getByte, MachineState.getMem, hmem1'] using hmark
    rw [hb, bool_byte_zeroExtend]
  have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s2.getReg r = s.getReg r :=
    fun r h6 h7 h22 h28 h29 => by
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg1 r h6 h22 h28 h29
  -- pc[215]: BNE x7, x0, pc[227]
  have hst215 := step_ordinary oracle s2 215 (.BNE .x7 .x0 48#13) (by decide) hpc2 checkInstr_215 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 8 0 [] := by simpa using hs1.trans (hst214.trans hst215)
  cases marked with
  | false =>
    have hpc3 : s3.pc = pcWord 216 := by
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
    have hfix7 : CheckFixedRegs s7 :=
      hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    have hcur7 : ProofCursor s0 input.proof.length pOffNext tOffNext s7 :=
      hcur.of_agree (fun r hr => hreg7 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
    obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
      step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s7 hpc7 hfix7 hcur7
        ((hreg7 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7 .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
    exact .continued sFin 23 0 [] (by decide) (by decide)
      (by simpa using (hs03.trans hs7).trans hsFin)
      ⟨rfl, rfl, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hm7,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)).trans hv7,
       fun a ha hne hout => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout7 a ha hne hout,
       fun h => by cases h⟩
  | true =>
    have hpc3 : s3.pc = pcWord 227 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_215_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.setPC] using hmem2
    have hreg3 : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.getReg_setPC]
    have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [hreg3]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
    have hcmp := step_compare4 oracle 227 .x21 .x28 s3 256 (8192 + gapOffset c)
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
      have hfix4 : CheckFixedRegs s4 :=
        hfix.of_agree (fun r hr => hreg4s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
      have hcur4 : ProofCursor s0 input.proof.length pOffNext tOffNext s4 :=
        hcur.of_agree (fun r hr => hreg4s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
        step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s4 hpc4 hfix4 hcur4
          ((hreg4s .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg4s .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg4s .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
      have hmemFins : sFin.mem = s.mem := hmemFin.trans hmem4s
      exact .continued sFin (8 + k + 4) 0 [] (by omega) (by decide)
        (by simpa [Nat.add_assoc] using (hs03.trans hs4).trans hsFin)
        ⟨rfl, rfl, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin,
         by simpa [MachineState.getByte, MachineState.getMem, hmemFins] using hmark,
         by rw [(MemEqOutside.of_mem_eq hmemFins 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← heq_dig],
         fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmemFins],
         fun _ => hmemFins⟩

/-! #### Per-Position Loop Invariant and Induction (`pc[22] -> pc[243]`) -/

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
  posRecordOff input.positions n + tailBytes (posTailOff input.positions n) ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions j1) (posTailOff input.positions j1)
      (posAt input.positions j1) (valAt input j1)).evalLevel c96 15 =
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions j2) (posTailOff input.positions j2)
      (posAt input.positions j2) (valAt input j2)).evalLevel c96 15

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff input.positions n) (posTailOff input.positions n) s
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if n = input.positions.card then pcWord 243 else pcWord 22
  x24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * n)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (input.positions.card - n)
  mark15 : ∀ c < 342, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if posMarked15 input.positions n c then 1#8 else 0#8
  mark_hi_zero : ∀ a, 4096 + 342 ≤ a → a < 4824 → s.getByte (BitVec.ofNat 64 a) = 0#8
  val15_gap_zero : ∀ q < 171, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + 96 * q + 64 + b)) = 0#8
  val_hi_zero : ∀ a, 8192 + capValOff 16 ≤ a → a < 8192 + 33152 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  witnesses : ∀ j < n,
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness (submission.initialState .check input) input.proof.length
      (posRecordOff input.positions j) (posTailOff input.positions j) (posAt input.positions j) (valAt input j)
    pw.evalLevel c96 15 = readBuffer s (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) ∧
    ((posAt input.positions j).val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96)) ∧
    (∀ prev, 1 ≤ prev → prev ≤ 14 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x)

private theorem binPathOff_mono (g : Nat) {a b : Nat} (hab : a ≤ b) :
    binPathOff g a ≤ binPathOff g b := by
  induction hab with
  | refl => exact le_refl _
  | step _ ih => simp only [binPathOff]; omega

/-- Complete per-position verification loop (`pc[22]` -> `pc[243]`), `≤ 3668 * k` steps, `≤ 19 * k` calls. -/
theorem step_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0)
    (sInit : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sInit (3668 * input.positions.card) (19 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' q tr => q ≤ 19 * input.positions.card ∧ PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (3668 * n) (19 * n)
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
        have hp_m := posRecordOff_mono input.positions (show k ≤ k + 1 by omega)
        have ht_m := tailBytes_mono (posTailOff_mono input.positions (show k ≤ k + 1 by omega))
        refine ⟨by have := hcons.1; omega, ?_⟩
        intro j1 j2 hj1 hj2 hc
        exact hcons.2 j1 j2 (by omega) (by omega) hc
      rw [show 3668 * (k + 1) = 3668 * k + 3668 by omega,
        show 19 * (k + 1) = 19 * k + 19 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hlt_k : k < input.positions.card := by omega
        have hpc_k : sk.pc = pcWord 22 := by
          have := hinv_k.pc
          rwa [if_neg (by omega : k ≠ input.positions.card)] at this
        let pOff := posRecordOff input.positions k
        let tOff := posTailOff input.positions k
        let i := posAt input.positions k
        let g := i.val / 3
        let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input k)
        let rem1 := input.positions.card - (k + 1)
        have hrem_eq : input.positions.card - k = rem1 + 1 := by omega
        have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
          rw [hinv_k.x27, hrem_eq]
        have htb_step : tailBytes tOff ≤ tailBytes (tOff + recordTailCount i) :=
          tailBytes_mono (by omega)
        have hbp4_le : binPathOff g 4 ≤ binPathOff g 13 := binPathOff_mono g (by decide)
        -- 1A: leaf (190 steps, 4 calls)
        have h1a := step_pos_leaf h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
          sk hpc_k hinv_k.fixed hinv_k.cursor hinv_k.high hinv_k.x24 hinv_k.x8 hx27_k
        have hcan_leaf : input.proof.length < pOff + 24 + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
          intro hlt hcons
          have h1 := hcons.1
          rw [posRecordOff_succ, posTailOff_succ] at h1
          change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
          unfold recordLen at h1; omega
        -- Chain 1A -> 1B -> 1C -> 1D-1 -> 1D-2 -> 1E
        refine PhaseOutcome.weaken
          (K1 := 190 + (420 + (220 + (850 + (1954 + 30))))) (Q1 := 4 + (1 + (1 + (4 + (9 + 0)))))
          ?_ (by decide) (by decide) id (fun _ _ _ h => h)
        refine h1a.bind_dep hcan_leaf (fun s1 qA trA ⟨hqA, hpcA, hfixA, hcurA, houtA, hx20A, hx24A, hx8A, hx27A, hleafA, htrA⟩ => by
          have hhighA : HighMemPreserved s0 s1 := hinv_k.high.trans (houtA.mono (by omega) (by omega))
          have h1b := step_pos_l0 h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
            s1 hpcA hfixA hcurA hhighA hx20A hx24A hx8A hx27A hleafA
          have hcan_l0 : input.proof.length < pOff + 24 + l0Bytes i + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
            intro hlt hcons
            have h1 := hcons.1
            rw [posRecordOff_succ, posTailOff_succ] at h1
            change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
            unfold recordLen at h1; omega
          refine h1b.bind_dep hcan_l0 (fun s2 qB trB ⟨hqB, hpcB, hfixB, hcurB, houtB, hx22B, hx24B, hx8B, hx27B, hl1B, htrB⟩ => by
            have hhighB : HighMemPreserved s0 s2 := hhighA.trans (houtB.mono (by omega) (by omega))
            have h1c := step_pos_l1 h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
              s2 hpcB hfixB hcurB hhighB hx22B hx24B hx8B hx27B hl1B
            have hcan_l1 : input.proof.length < pOff + 24 + l0Bytes i + 32 + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
              intro hlt hcons
              have h1 := hcons.1
              rw [posRecordOff_succ, posTailOff_succ] at h1
              change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
              unfold recordLen at h1; omega
            refine h1c.bind_dep hcan_l1 (fun s3 qC trC ⟨hqC, hpcC, hfixC, hcurC, houtC, hx22C, hx24C, hx8C, hx27C, hl2C, hgapC, htrC⟩ => by
              have hhighC : HighMemPreserved s0 s3 := hhighB.trans (houtC.mono (by omega) (by omega))
              have h1d1 := step_pos_bin240_loop h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
                s3 hpcC hfixC hcurC hhighC hx22C hx24C hx8C hx27C hl2C hgapC
              have hcan_b240 : input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g 4 + tailBytes tOff →
                  ¬ PosConsistent c96 s0 input (k + 1) := by
                intro hlt hcons
                have h1 := hcons.1
                rw [posRecordOff_succ, posTailOff_succ] at h1
                change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
                unfold recordLen at h1
                change pOff + (24 + l0Bytes i + 32 + binPathOff g 13) + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
                omega
              refine h1d1.bind_dep hcan_b240 (fun s3b qD1 trD1 ⟨hqD1, hpcD1, hfixD1, hcurD1, houtD1, hx22D1, hx24D1, hx8D1, hx27D1, hx29D1, hl6D1, hgapD1, htrD1⟩ => by
                have hhighD1 : HighMemPreserved s0 s3b := hhighC.trans (houtD1.mono (by omega) (by omega))
                have h1d2 := step_pos_bin238_loop h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
                  s3b hpcD1 hfixD1 hcurD1 hhighD1 hx22D1 hx24D1 hx8D1 hx27D1 hx29D1 hl6D1 hgapD1
                have hcan_b238 : input.proof.length < pOff + recordLen i + tailBytes (tOff + recordTailCount i) →
                    ¬ PosConsistent c96 s0 input (k + 1) := by
                  intro hlt hcons
                  have h1 := hcons.1
                  rw [posRecordOff_succ, posTailOff_succ] at h1
                  change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1; omega
                refine h1d2.bind_dep hcan_b238 (fun s4 qD2 trD2 ⟨hqD2, hpcD2, hfixD2, hcurD2, houtD2, hx22D2, hx24D2, hx8D2, hx27D2, hd15D, htrD2⟩ => by
                  have hout_sk4 : MemEqOutside sk s4 256 448 :=
                    houtA.trans ((houtB.mono (by omega) (by omega)).trans
                      ((houtC.mono (by omega) (by omega)).trans
                        ((houtD1.mono (by omega) (by omega)).trans (houtD2.mono (by omega) (by omega)))))
                  have hc_lt : capLeafOf i < 342 := capLeafOf_lt i
                  have hmark4 : s4.getByte (BitVec.ofNat 64 (4096 + capLeafOf i)) =
                      if posMarked15 input.positions k (capLeafOf i) then 1#8 else 0#8 :=
                    (hout_sk4 (4096 + capLeafOf i) (by omega) (by omega)).trans (hinv_k.mark15 (capLeafOf i) hc_lt)
                  have h1e := step_pos_cap_store oracle input k (pOff + recordLen i) (tOff + recordTailCount i) rem1 hlt_k (by omega)
                    s4 hpcD2 hfixD2 hcurD2 hx22D2 hx24D2 hx8D2 hx27D2 (posMarked15 input.positions k (capLeafOf i))
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
                  rintro s5 qE trE ⟨rfl, rfl, hpcE, hfixE, hcurE, hx24E, hx8E, hx27E, hmark5, hval5, hout5, hmeq5⟩
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
                  refine ⟨hfixE, by simpa only [posRecordOff_succ, posTailOff_succ, pOff, tOff] using hcurE,
                    hhigh5, ?_, hx24E, hx8E, hx27E, ?_, ?_, ?_, ?_, ?_⟩
                  · by_cases hdone : k + 1 = input.positions.card
                    · have hz : rem1 = 0 := by omega
                      simp [hdone, hz, hpcE]
                    · have hnz : rem1 ≠ 0 := by omega
                      simp [hdone, hnz, hpcE]
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
                        · by_cases hp_lt6 : prev < 6
                          · exact ((((((htrD1 prev (by omega) hp_lt6 x hx).append_left).append_right).append_right).append_right).append_right)
                          · exact (((((((htrD2 prev (by omega) hp2 x hx).append_left).append_right).append_right).append_right).append_right).append_right)))))))
  exact hind input.positions.card (le_refl _)

end CommitGolfCandidate
