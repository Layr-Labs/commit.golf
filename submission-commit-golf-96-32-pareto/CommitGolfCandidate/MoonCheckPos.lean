import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the unified L2..L13 binary loop (with variable-width digests and
domain-separated hash chains), L14 cap-store, and full per-position loop (`pc[138..208]`,
`pc[19] -> pc[209]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem evalLevel_succ_of_ge1 (c : Comp96) (w : WitnessPath) (l : Nat) (hl : 1 ≤ l) :
    w.evalLevel c (l + 1) =
      let cur := w.evalLevel c l
      let idx := (w.index.val / 3) >>> (l - 1)
      if (idx ^^^ 1) < levelSize l then
        if idx % 2 = 0 then chainHash c (l + 1) cur (w.binSib l)
        else chainHash c (l + 1) (w.binSib l) cur
      else if l + 1 < 9 then
        cur
      else
        chainHash c (l + 1) cur 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rfl

private theorem pc_143_branch : pcWord 143 + signExtend13 76#13 = pcWord 162 := by decide
private theorem pc_145_branch : pcWord 145 + signExtend13 52#13 = pcWord 158 := by decide
private theorem pc_157_jal : pcWord 157 + signExtend21 44#21 = pcWord 168 := by decide
private theorem pc_161_jal : pcWord 161 + signExtend21 28#21 = pcWord 168 := by decide
private theorem pc_163_branch : pcWord 163 + signExtend13 36#13 = pcWord 172 := by decide
private theorem pc_173_branch : pcWord 173 + signExtend13 8060#13 = pcWord 140 := by decide

private theorem pc_181_branch : pcWord 181 + signExtend13 48#13 = pcWord 193 := by decide
private theorem pc_192_jal : pcWord 192 + signExtend21 52#21 = pcWord 205 := by decide
private theorem pc_208_branch : pcWord 208 + signExtend13 7436#13 = pcWord 19 := by decide

private theorem bne_mem_pos (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    (execInstrBr st (.BNE r1 r2 off)).mem = st.mem := by
  simp only [execInstrBr]; split <;> rfl

private theorem bne_getReg_pos (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr st (.BNE r1 r2 off)).getReg r = st.getReg r := by
  simp only [execInstrBr]; split <;> simp only [MachineState.getReg_setPC]

private theorem checkInstr_156 : checkInstr 156 = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (297 - 156)))) := rfl
private theorem checkInstr_160 : checkInstr 160 = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (297 - 160)))) := rfl
private theorem checkInstr_171 : checkInstr 171 = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (325 - 171)))) := rfl
private theorem checkInstr_180 : checkInstr 180 = .base (.LBU .x7 .x29 0#12) := rfl
private theorem checkInstr_181 : checkInstr 181 = .base (.BNE .x7 .x0 48#13) := rfl
private theorem checkInstr_182 : checkInstr 182 = .base (.ADDI .x7 .x0 1#12) := rfl
private theorem checkInstr_183 : checkInstr 183 = .base (.SB .x29 .x7 0#12) := rfl
private theorem checkInstr_192 : checkInstr 192 = .base (.JAL .x0 52#21) := rfl
private theorem checkInstr_205 : checkInstr 205 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_206 : checkInstr 206 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_207 : checkInstr 207 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_208 : checkInstr 208 = .base (.BNE .x27 .x0 7436#13) := rfl

private theorem binLoop_calls_sum :
    ∑ step ∈ Finset.range 12, levelChain (3 + step) = 64 := by
  decide

/-! #### Unified Binary Loop (`L2..L13`, 12 iterations, `pc[138..173] -> pc[174]`) -/

/-- One iteration (`step < 12`, level `l = 2 + step ∈ 2..13`, output `lvl = 3 + step ∈ 3..14`)
of the unified binary loop (`pc[140..173]`). -/
theorem step_pos_bin_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff bitOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 12)
    (s : MachineState) (hpc : s.pc = pcWord 140)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32 +
        binPathOff ((posAt input.positions ord).val / 3) step)
      (bitOff + binTailBitsOff ((posAt input.positions ord).val / 3) step) s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hzero : ChainScratchZero s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff bitOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (2 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pCur := pOff + 24 + l0Bytes i + 32 + binPathOff g step
    let bCur := bitOff + binTailBitsOff g step
    let pw := parsePartialWitness s0 input.proof.length pOff bitOff i (valAt input ord)
    PhaseOutcome oracle s 320 (levelChain (3 + step))
      (input.proof.length < pCur + binStepBytes g step + tailBytesBits (bCur + binStepTailBits g step))
      (fun s' q tr =>
        q ≤ levelChain (3 + step) ∧
        s'.pc = (if step + 1 = 12 then pcWord 174 else pcWord 140) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + binStepBytes g step) (bCur + binStepTailBits g step) s' ∧
        ChainScratchZero s' ∧
        MemEqOutside s s' 256 608 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInputs c96 (2 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g pCur bCur pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hle_cur : pCur + tailBytesBits bCur ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_lt : g < 5592406 := by change i.val / 3 < _; omega
  have hidx_lt : g >>> step < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hidx1_lt : g >>> (step + 1) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g >>> step) / 2 = g >>> (step + 1) := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  -- pc[140]: SRLI x22, x22, 1; pc[141]: XORI x28, x22, 1
  have hst140 := step_ordinary oracle s 140 (.SRLI .x22 .x22 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SRLI .x22 .x22 1#6)
  have hpc1 : s1.pc = pcWord 141 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx22_1 : s1.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, show (1#6 : BitVec 6).toNat = 1 by decide,
      bv64_shr _ 1 (Nat.lt_trans hidx_lt (by decide)), Nat.pow_one, hshr_step]
  have hst141 := step_ordinary oracle s1 141 (.XORI .x28 .x22 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.XORI .x28 .x22 1#12)
  have hpc2 : s2.pc = pcWord 142 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 ((g >>> (step + 1)) ^^^ 1) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22_1, se12_1]
    exact bv64_xor_one _ hidx1_lt
  have hreg2 : ∀ r, r ≠ .x22 → r ≠ .x28 → s2.getReg r = s.getReg r := fun r h22 h28 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
  -- pc[142]: LD x7, 8(x29) -> levelSize (2 + step)
  have ha142 : s2.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 8)) := by
    rw [hreg2 .x29 (by decide) (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv142 : memoryArgumentsValid s2 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha142]
    exact accessValid_ofNat (68719475728 + (40 * (2 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst142 := step_ordinary oracle s2 142 (.LD .x7 .x29 8#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv142])
  let s3 := execInstrBr s2 (.LD .x7 .x29 8#12)
  have hpc3 : s3.pc = pcWord 143 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hsz_val : s2.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 8))) =
      BitVec.ofNat 64 (levelSize (2 + step)) := by
    have hm2 : s2.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 8))) =
        s.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 8))) := by
      simp [MachineState.getMem, hmem2]
    rw [hm2, hhigh.getMem_eq (by omega) (by omega) (by omega),
      check_initial_data_dword input hvalid (40 * (2 + step) + 8) (by omega)]
    exact openingData_dword_1 ⟨2 + step, by omega⟩
  have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (levelSize (2 + step)) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha142]
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
  -- pc[143]: BGEU x28, x7, pc[162]
  have hst143 := step_ordinary oracle s3 143 (.BGEU .x28 .x7 76#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.BGEU .x28 .x7 76#13)
  have hult143 : BitVec.ult (s3.getReg .x28) (s3.getReg .x7) =
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
  have hpre4 : StepsTo oracle s s4 4 0 [] :=
    ((hst140.trans hst141).trans (hst142.trans hst143)).eq_of rfl (by decide) (by decide) (by simp)
  -- Common loop footer at pc[172..173]
  have hfooter : ∀ (s172 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 314 → qMid ≤ levelChain (3 + step) →
      StepsTo oracle s4 s172 kMid qMid trMid →
      s172.pc = pcWord 172 →
      CheckFixedRegs s172 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g step) (bCur + binStepTailBits g step) s172 →
      ChainScratchZero s172 →
      MemEqOutside s s172 256 608 →
      s172.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) →
      s172.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
      s172.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
      s172.getReg .x27 = BitVec.ofNat 64 rem →
      s172.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + step)) →
      s172.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) →
      readBuffer s172 256 32 = pw.evalLevel c96 (2 + (step + 1)) →
      readBuffer s172 320 32 = 0 →
      (∀ x ∈ pw.levelInputs c96 (2 + step), InTrace h768 oracle trMid x) →
      PhaseOutcome oracle s 320 (levelChain (3 + step))
        (input.proof.length < pCur + binStepBytes g step + tailBytesBits (bCur + binStepTailBits g step))
        (fun s' q tr =>
          q ≤ levelChain (3 + step) ∧
          s'.pc = (if step + 1 = 12 then pcWord 174 else pcWord 140) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g step) (bCur + binStepTailBits g step) s' ∧
          ChainScratchZero s' ∧
          MemEqOutside s s' 256 608 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInputs c96 (2 + step), InTrace h768 oracle tr x) := by
    intro s172 kMid qMid trMid hkMid hqMid hmid hpc172 hfix172 hcur172 hzero172 hout172
      h22 h24 h8 h27 h29 h30 hdig172 hgap172 htr172
    have hst172 := step_ordinary oracle s172 172 (.ADDI .x29 .x29 40#12) (by decide) hpc172 rfl (by intro h; cases h) rfl
    let s173 := execInstrBr s172 (.ADDI .x29 .x29 40#12)
    have hpc173 : s173.pc = pcWord 173 := by simp only [s173, execInstrBr, MachineState.setPC, hpc172, pcWord_add_four]
    have hx29_173 : s173.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) := by
      simp only [s173, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h29, se12_40]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 40 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_173 : s173.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) := by
      simp only [s173, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), h30]
    have hst173 := step_ordinary oracle s173 173 (.BNE .x29 .x30 8060#13) (by decide) hpc173 rfl (by intro h; cases h) rfl
    let sFin := execInstrBr s173 (.BNE .x29 .x30 8060#13)
    have hmemFin : sFin.mem = s172.mem :=
      (bne_mem_pos s173 .x29 .x30 8060#13).trans (by simp [s173, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x29 → sFin.getReg r = s172.getReg r := fun r h29r => by
      rw [bne_getReg_pos s173 .x29 .x30 8060#13 r]
      simp only [s173, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h29r.symm
    have hx29_Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) :=
      (bne_getReg_pos s173 .x29 .x30 8060#13 .x29).trans hx29_173
    have hpcFin : sFin.pc = if step + 1 = 12 then pcWord 174 else pcWord 140 := by
      have hne_iff : (s173.getReg .x29 != s173.getReg .x30) = decide (step + 1 ≠ 12) := by
        rw [hx29_173, hx30_173, bv64_bne_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      by_cases hdone : step + 1 = 12
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, ite_true, MachineState.setPC, hpc173, pcWord_add_four]
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_false_eq_true, decide_true,
          ite_true, ite_false, MachineState.setPC, hpc173]; exact pc_173_branch
    have htot := (hpre4.trans hmid).trans (hst172.trans hst173)
    refine .continued sFin (4 + kMid + 2) qMid trMid (by omega) hqMid
      (htot.eq_of rfl (by omega) (by omega) (by simp))
      ⟨hqMid, hpcFin,
       hfix172.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       hcur172.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
       hzero172.of_mem_eq hmemFin,
       hout172.trans (MemEqOutside.of_mem_eq hmemFin 256 608),
       (hregFin .x22 (by decide)).trans h22, (hregFin .x24 (by decide)).trans h24,
       (hregFin .x8  (by decide)).trans h8,  (hregFin .x27 (by decide)).trans h27,
       hx29_Fin, (hregFin .x30 (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig172,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap172,
       htr172⟩
  -- Common hash call at pc[168..171] -> pc[172] for lvl = 3 + step
  have hhash168 : ∀ (s168 : MachineState) (kA : Nat) (dL dR : Digest),
      kA ≤ 227 →
      StepsTo oracle s4 s168 kA 0 [] →
      s168.pc = pcWord 168 →
      CheckFixedRegs s168 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g step) (bCur + binStepTailBits g step) s168 →
      ChainScratchZero s168 →
      MemEqOutside s s168 256 608 →
      s168.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) →
      s168.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
      s168.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
      s168.getReg .x27 = BitVec.ofNat 64 rem →
      s168.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + step)) →
      s168.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) →
      readBuffer s168 256 32 = dL →
      readBuffer s168 288 32 = dR →
      readBuffer s168 320 32 = 0 →
      pw.evalLevel c96 (2 + (step + 1)) = chainHash c96 (3 + step) dL dR →
      pw.levelInputs c96 (2 + step) = chainInputs c96 (3 + step) dL dR →
      PhaseOutcome oracle s 320 (levelChain (3 + step))
        (input.proof.length < pCur + binStepBytes g step + tailBytesBits (bCur + binStepTailBits g step))
        (fun s' q tr =>
          q ≤ levelChain (3 + step) ∧
          s'.pc = (if step + 1 = 12 then pcWord 174 else pcWord 140) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g step) (bCur + binStepTailBits g step) s' ∧
          ChainScratchZero s' ∧
          MemEqOutside s s' 256 608 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInputs c96 (2 + step), InTrace h768 oracle tr x) := by
    intro s168 kA dL dR hkA hmidA hpc168 hfix168 hcur168 hzero168 hout168
      h22 h24 h8 h27 h29 h30 hdL hdR hgap168 heval_eq hlinp_eq
    have hhigh168 : HighMemPreserved s0 s168 := hhigh.trans (hout168.mono (by omega) (by omega))
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
    have ha170 : s170.getReg .x29 + signExtend12 72#12 =
        BitVec.ofNat 64 (68719475728 + (40 * (3 + step) + 32)) := by
      rw [hreg170 .x29 (by decide) (by decide), h29, se12_72]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 72 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hv170 : memoryArgumentsValid s170 (.LD .x6 .x29 72#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha170]
      exact accessValid_ofNat (68719475728 + (40 * (3 + step) + 32)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
    have hst170 := step_ordinary oracle s170 170 (.LD .x6 .x29 72#12) (by decide) hpc170 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv170])
    let s171 := execInstrBr s170 (.LD .x6 .x29 72#12)
    have hpc171 : s171.pc = pcWord 171 := by simp only [s171, execInstrBr, MachineState.setPC, hpc170, pcWord_add_four]
    have hmem171 : s171.mem = s168.mem := by simpa [s171, execInstrBr, mem_setPC, mem_setReg] using hmem170
    have hreg171 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s171.getReg r = s168.getReg r := fun r h6 h10 h12 => by
      simp only [s171, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, hreg170 r h10 h12]
    have hx10_171 : s171.getReg .x10 = 256#64 := by
      simp only [s171, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x10)]
      simp only [s170, s169, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hfix168.x21, se12_0, BitVec.add_zero]
    have hx12_171 : s171.getReg .x12 = 256#64 := by
      simp only [s171, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12)]
      simp only [s170, s169, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21), hfix168.x21, se12_0, BitVec.add_zero]
    have hx6_171 : s171.getReg .x6 = BitVec.ofNat 64 (levelMetaOC (3 + step)) := by
      simp only [s171, execInstrBr, MachineState.getReg_setPC, ha170]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hm : s170.getMem (BitVec.ofNat 64 (68719475728 + (40 * (3 + step) + 32))) =
          s0.getMem (BitVec.ofNat 64 (68719475728 + (40 * (3 + step) + 32))) := by
        have : s170.getMem (BitVec.ofNat 64 (68719475728 + (40 * (3 + step) + 32))) =
            s168.getMem (BitVec.ofNat 64 (68719475728 + (40 * (3 + step) + 32))) := by simp [MachineState.getMem, hmem170]
        rw [this]
        exact hhigh168.getMem_eq (by omega) (by omega) (by omega)
      rw [hm, check_initial_data_dword input hvalid (40 * (3 + step) + 32) (by omega)]
      exact openingData_dword_4 ⟨3 + step, by omega⟩
    have hfix171 : CheckFixedRegs s171 :=
      hfix168.of_agree (fun r hr => hreg171 r (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    obtain ⟨s172, kH, trH, hkH, hstepH, hpc172, hregH, hdigH, hzero172, houtH, htrH⟩ :=
      step_call_hashLevelNode h768 oracle 171 s171 256 256 (3 + step) (by omega) (by omega) (by decide)
        checkInstr_171 hpc171 hfix171 hx6_171 hx10_171 hx12_171
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by rw [(MemEqOutside.of_mem_eq hmem171 0 0).readBuffer_eq (by decide) (by omega)]; exact hgap168)
        (hzero168.of_mem_eq hmem171)
    have hdL171 : readBuffer s171 256 32 = dL :=
      ((MemEqOutside.of_mem_eq hmem171 0 0).readBuffer_eq (by decide) (by omega)).trans hdL
    have hdR171 : readBuffer s171 288 32 = dR :=
      ((MemEqOutside.of_mem_eq hmem171 0 0).readBuffer_eq (by decide) (by omega)).trans hdR
    rw [hdL171, hdR171] at hdigH htrH
    have hreg172 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 →
        s172.getReg r = s168.getReg r := fun r h1 h6 h7 h9 h10 h12 h28 =>
      (hregH r h1 h7 h9 h10 h12 h28).trans (hreg171 r h6 h10 h12)
    have hout172 : MemEqOutside s s172 256 608 := fun a ha hout => by
      rw [houtH a ha (by omega) (by omega)]
      have h171_168 : s171.getByte (BitVec.ofNat 64 a) = s168.getByte (BitVec.ofNat 64 a) := by
        simp [MachineState.getByte, MachineState.getMem, hmem171]
      rw [h171_168]
      exact hout168 a ha hout
    have hgap172 : readBuffer s172 320 32 = 0 := by
      rw [← hgap168]
      apply readBuffer_congr2; intro j hj
      rw [houtH (320 + j) (by omega) (by omega) (by omega)]
      simp [MachineState.getByte, MachineState.getMem, hmem171]
    refine hfooter s172 (kA + 3 + kH) (levelChain (3 + step)) trH (by omega) (le_refl _)
      ((hmidA.trans (((hst168.trans hst169).trans hst170).trans hstepH)).eq_of rfl (by omega) (by omega) (by simp))
      hpc172
      (hfix168.of_agree (fun r hr => hreg172 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (hcur168.of_agree (fun r hr => hreg172 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      hzero172 hout172
      ((hreg172 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22)
      ((hreg172 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24)
      ((hreg172 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8)
      ((hreg172 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27)
      ((hreg172 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29)
      ((hreg172 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30)
      (hdigH.trans heval_eq.symm) hgap172 ?_
    intro x hx
    rw [hlinp_eq] at hx
    exact htrH x hx
  -- Branch on whether sibling exists at level `2 + step`
  have hidx_pw : (pw.index.val / 3) >>> (2 + step - 1) = g >>> (step + 1) := by
    change g >>> (2 + step - 1) = g >>> (step + 1)
    exact congrArg (fun k => g >>> k) (by omega)
  by_cases hpair : ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
  · -- Paired branch: read variable-width sibling at level `2 + step` and hash at `3 + step`
    have hsb : binStepBytes g step = levelBodyBytes (2 + step) := by
      unfold binStepBytes; exact if_pos hpair
    have hst_bits : binStepTailBits g step = levelTailBits (2 + step) := by
      unfold binStepTailBits; exact if_pos hpair
    have hpc4 : s4.pc = pcWord 144 := by
      simp only [s4, execInstrBr, hult143, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult143, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult143, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
      simpa [s4, execInstrBr, hult143, hpair, MachineState.getReg_setPC] using hx22_3
    -- pc[144]: ANDI x7, x22, 1; pc[145]: BEQ x7, x0, pc[158]
    have hst144 := step_ordinary oracle s4 144 (.ANDI .x7 .x22 1#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ANDI .x7 .x22 1#12)
    have hpc5 : s5.pc = pcWord 145 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hx7_5 : s5.getReg .x7 = BitVec.ofNat 64 ((g >>> (step + 1)) % 2) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hx22_4, se12_1]
      exact bv64_and_one _ (by omega)
    have hst145 := step_ordinary oracle s5 145 (.BEQ .x7 .x0 52#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BEQ .x7 .x0 52#13)
    have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
    let sibD := pw.binSib (2 + step)
    have hsibD_eq : sibD = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur (2 + step) := by
      simp only [sibD, pw, parsePartialWitness, show 2 + step ≠ 1 by omega, ite_false,
        show 2 ≤ 2 + step ∧ 2 + step ≤ 13 by omega, and_self, ite_true,
        show 2 + step - 2 = step by omega, pCur, bCur, Nat.add_assoc]
      dsimp only [g]
    let curD := pw.evalLevel c96 (2 + step)
    by_cases heven : (g >>> (step + 1)) % 2 = 0
    · -- Even: jump to pc[158..161] -> pc[168]
      have hx7z : s5.getReg .x7 = 0#64 := by rw [hx7_5, heven]
      have hpc6 : s6.pc = pcWord 158 := by
        simp only [s6, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc5]
        exact pc_145_branch
      have hmem6 : s6.mem = s.mem := by
        simpa [s6, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h7 h22 h28 => by
        have h65 : s6.getReg r = s5.getReg r := by
          simp only [s6, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        have h65 : s6.getReg .x22 = s5.getReg .x22 := by
          simp only [s6, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22), hx22_4]
      -- pc[158]: ADDI x12, x21, 32; pc[159]: LD x6, 32(x29)
      have hst158 := step_ordinary oracle s6 158 (.ADDI .x12 .x21 32#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ADDI .x12 .x21 32#12)
      have hpc7 : s7.pc = pcWord 159 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
      have ha159 : s7.getReg .x29 + signExtend12 32#12 =
          BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32)) := by
        simp only [s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x29),
          hreg6 .x29 (by decide) (by decide) (by decide), hx29, se12_32]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hv159 : memoryArgumentsValid s7 (.LD .x6 .x29 32#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha159]
        exact accessValid_ofNat (68719475728 + (40 * (2 + step) + 32)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst159 := step_ordinary oracle s7 159 (.LD .x6 .x29 32#12) (by decide) hpc7 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv159])
      let s8 := execInstrBr s7 (.LD .x6 .x29 32#12)
      have hpc8 : s8.pc = pcWord 160 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
      have hmem8 : s8.mem = s.mem := by simpa [s8, execInstrBr, mem_setPC, mem_setReg] using hmem7
      have hreg8 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x22 → r ≠ .x28 → s8.getReg r = s.getReg r :=
        fun r h6 h7 h12 h22 h28 => by
          simp only [s8, s7, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
          exact hreg6 r h7 h22 h28
      have hx22_8 : s8.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        simp only [s8, s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x22), MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x22), hx22_6]
      have hx12_8 : s8.getReg .x12 = BitVec.ofNat 64 288 := by
        simp only [s8, s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_32]
        decide
      have hx6_8 : s8.getReg .x6 = BitVec.ofNat 64 (levelMetaOC (2 + step)) := by
        simp only [s8, execInstrBr, MachineState.getReg_setPC, ha159]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have hm : s7.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32))) =
            s.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32))) := by simp [MachineState.getMem, hmem7]
        rw [hm, hhigh.getMem_eq (by omega) (by omega) (by omega),
          check_initial_data_dword input hvalid (40 * (2 + step) + 32) (by omega)]
        exact openingData_dword_4 ⟨2 + step, by omega⟩
      have hcur8 : ProofCursor s0 input.proof.length pCur bCur s8 :=
        hcur.of_agree (fun r hr => hreg8 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
      have hcall := step_call_readVarDigest oracle s0 input.proof.length hvalid 160 s8 pCur bCur 288 (2 + step)
        (by omega) (by omega) (by decide) checkInstr_160 hpc8 hx6_8 hcur8
        (hhigh.trans (MemEqOutside.of_mem_eq hmem8 0 4294971392)) hx12_8 (by decide) (by decide)
      cases hcall with
      | rejected kR qR trR hshort hkR hqR hhR =>
        rw [← hsb, ← hst_bits] at hshort
        exact .rejected (4 + 4 + kR) qR trR hshort (by omega) (by omega)
          (by simpa [Nat.add_assoc] using (hpre4.trans ((hst144.trans hst145).trans (hst158.trans hst159))).halt hhR)
      | continued s9 kR qR trR hkR hqR hs9 hp9 =>
        obtain ⟨rfl, rfl, hpc9, hcur9, hreg9, hdig9, hout9⟩ := hp9
        have hst161 := step_ordinary oracle s9 161 (.JAL .x0 28#21) (by decide) hpc9 rfl (by intro h; cases h) rfl
        let s10 := execInstrBr s9 (.JAL .x0 28#21)
        have hpc10 : s10.pc = pcWord 168 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9]; exact pc_161_jal
        have hmem10 : s10.mem = s9.mem := by simp [s10, execInstrBr, mem_setPC, mem_setReg]
        have hreg10 : ∀ r, s10.getReg r = s9.getReg r := fun r => by
          simp [s10, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have hreg10_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 →
            r ≠ .x12 → r ≠ .x22 → r ≠ .x25 → r ≠ .x28 → r ≠ .x31 → s10.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h9 h12 h22 h25 h28 h31 =>
            (hreg10 r).trans ((hreg9 r h1 h3 h4 h7 h9 h12 h25 h31).trans (hreg8 r h6 h7 h12 h22 h28))
        have hout_s10 : MemEqOutside s s10 288 320 :=
          (MemEqOutside.of_mem_eq hmem8 288 320).trans (hout9.trans (MemEqOutside.of_mem_eq hmem10 288 320))
        have heval_eq : pw.evalLevel c96 (2 + (step + 1)) = chainHash c96 (3 + step) curD sibD := by
          rw [show 2 + (step + 1) = (2 + step) + 1 by omega, evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
          dsimp only; rw [hidx_pw, if_pos hpair, if_pos heven, show 2 + step + 1 = 3 + step by omega]
        have hlinp_eq : pw.levelInputs c96 (2 + step) = chainInputs c96 (3 + step) curD sibD := by
          unfold WitnessPath.levelInputs; dsimp only
          rw [hidx_pw, if_pos hpair, if_pos heven, show 2 + step + 1 = 3 + step by omega]
        refine hhash168 s10 (4 + kR + 1) curD sibD (by omega)
          ((((hst144.trans hst145).trans (hst158.trans hst159)).trans hs9).trans hst161 |>.eq_of rfl (by omega) (by decide) (by simp))
          hpc10
          (hfix.of_agree (fun r hr => hreg10_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          (by rw [hsb, hst_bits]; exact hcur9.of_agree (fun r _ => hreg10 r))
          (hzero.of_outside hout_s10 (by omega) (by omega))
          (hout_s10.mono (by omega) (by omega))
          ((hreg10 .x22).trans ((hreg9 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_8))
          ((hreg10_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg10_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg10_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg10_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg10_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          ((hout_s10.readBuffer_eq (by decide) (by omega)).trans hcurDig)
          (((MemEqOutside.of_mem_eq hmem10 0 0).readBuffer_eq (by decide) (by omega)).trans (hdig9.trans hsibD_eq.symm))
          ((hout_s10.readBuffer_eq (by decide) (by omega)).trans hgap)
          heval_eq hlinp_eq
    · -- Odd: fall through to pc[146..157] -> pc[168]
      have hodd : (g >>> (step + 1)) % 2 = 1 := by omega
      have hx7o : s5.getReg .x7 = 1#64 := by rw [hx7_5, hodd]
      have hpc6 : s6.pc = pcWord 146 := by
        simp only [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s.mem := by
        simpa [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h7 h22 h28 => by
        have h65 : s6.getReg r = s5.getReg r := by
          simp only [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        have h65 : s6.getReg .x22 = s5.getReg .x22 := by
          simp only [s6, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x22), hx22_4]
      -- pc[146..153]: copy 4 dwords S[0..32) -> S[32..64)
      have hcp : ∀ j < 4,
          checkInstr (146 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
          checkInstr (146 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
      obtain ⟨s7, hs7, hpc7, hreg7, hcopy7, hout7⟩ :=
        step_copy_dwords oracle 146 4 .x21 .x21 0 32 s6 256 256 (by decide) (by decide)
          (by decide) (by decide) (by decide) hcp hpc6
          ((hreg6 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
          ((hreg6 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
      -- pc[154]: ADDI x12, x21, 0; pc[155]: LD x6, 32(x29)
      have hst154 := step_ordinary oracle s7 154 (.ADDI .x12 .x21 0#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
      let s8 := execInstrBr s7 (.ADDI .x12 .x21 0#12)
      have hpc8 : s8.pc = pcWord 155 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
      have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, mem_setPC, mem_setReg]
      have ha155 : s8.getReg .x29 + signExtend12 32#12 =
          BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32)) := by
        simp only [s8, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x29),
          hreg7 .x29 (by decide), hreg6 .x29 (by decide) (by decide) (by decide), hx29, se12_32]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hv155 : memoryArgumentsValid s8 (.LD .x6 .x29 32#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha155]
        exact accessValid_ofNat (68719475728 + (40 * (2 + step) + 32)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst155 := step_ordinary oracle s8 155 (.LD .x6 .x29 32#12) (by decide) hpc8 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv155])
      let s9 := execInstrBr s8 (.LD .x6 .x29 32#12)
      have hpc9 : s9.pc = pcWord 156 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
      have hmem9 : s9.mem = s7.mem := by simpa [s9, execInstrBr, mem_setPC, mem_setReg] using hmem8
      have hout7' : MemEqOutside s6 s7 288 320 := by simpa only [Nat.add_zero] using hout7
      have hout_s9 : MemEqOutside s s9 288 320 :=
        (MemEqOutside.of_mem_eq hmem6 288 320).trans
          (hout7'.trans (MemEqOutside.of_mem_eq hmem9 288 320))
      have hreg9_s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x22 → r ≠ .x28 → s9.getReg r = s.getReg r :=
        fun r h6 h7 h12 h22 h28 => by
          simp only [s9, s8, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg7 r h6]
          exact hreg6 r h7 h22 h28
      have hx22_9 : s9.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        simp only [s9, s8, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x22), MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x22), hreg7 .x22 (by decide), hx22_6]
      have hx12_9 : s9.getReg .x12 = BitVec.ofNat 64 256 := by
        simp only [s9, s8, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hreg7 .x21 (by decide),
          hreg6 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero]
      have hx6_9 : s9.getReg .x6 = BitVec.ofNat 64 (levelMetaOC (2 + step)) := by
        simp only [s9, execInstrBr, MachineState.getReg_setPC, ha155]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have hm : s8.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32))) =
            s.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32))) := by
          have : s8.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32))) =
              s7.getMem (BitVec.ofNat 64 (68719475728 + (40 * (2 + step) + 32))) := by simp [MachineState.getMem, hmem8]
          rw [this]
          exact ((MemEqOutside.of_mem_eq hmem6 288 320).trans hout7').getMem_eq
            (by omega) (by omega) (by omega)
        rw [hm, hhigh.getMem_eq (by omega) (by omega) (by omega),
          check_initial_data_dword input hvalid (40 * (2 + step) + 32) (by omega)]
        exact openingData_dword_4 ⟨2 + step, by omega⟩
      have hcur9 : ProofCursor s0 input.proof.length pCur bCur s9 :=
        hcur.of_agree (fun r hr => hreg9_s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
      have hcall := step_call_readVarDigest oracle s0 input.proof.length hvalid 156 s9 pCur bCur 256 (2 + step)
        (by omega) (by omega) (by decide) checkInstr_156 hpc9 hx6_9 hcur9
        (hhigh.trans (hout_s9.mono (by omega) (by omega))) hx12_9 (by decide) (by decide)
      cases hcall with
      | rejected kR qR trR hshort hkR hqR hhR =>
        rw [← hsb, ← hst_bits] at hshort
        exact .rejected (4 + 12 + kR) qR trR hshort (by omega) (by omega)
          (by simpa [Nat.add_assoc] using (hpre4.trans (((hst144.trans hst145).trans hs7).trans (hst154.trans hst155))).halt hhR)
      | continued s10 kR qR trR hkR hqR hs10 hp10 =>
        obtain ⟨rfl, rfl, hpc10, hcur10, hreg10, hdig10, hout10⟩ := hp10
        have hst157 := step_ordinary oracle s10 157 (.JAL .x0 44#21) (by decide) hpc10 rfl (by intro h; cases h) rfl
        let s11 := execInstrBr s10 (.JAL .x0 44#21)
        have hpc11 : s11.pc = pcWord 168 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10]; exact pc_157_jal
        have hmem11 : s11.mem = s10.mem := by simp [s11, execInstrBr, mem_setPC, mem_setReg]
        have hreg11 : ∀ r, s11.getReg r = s10.getReg r := fun r => by
          simp [s11, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have hreg11_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 →
            r ≠ .x12 → r ≠ .x22 → r ≠ .x25 → r ≠ .x28 → r ≠ .x31 → s11.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h9 h12 h22 h25 h28 h31 =>
            (hreg11 r).trans ((hreg10 r h1 h3 h4 h7 h9 h12 h25 h31).trans (hreg9_s r h6 h7 h12 h22 h28))
        have hout_s11 : MemEqOutside s s11 256 320 :=
          (hout_s9.mono (by omega) (by omega)).trans
            ((hout10.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem11 256 320))
        have hR11 : readBuffer s11 288 32 = curD := by
          dsimp only [curD]
          rw [← hcurDig]
          apply readBuffer_congr2; intro j hj
          have h11_9 : s11.getByte (BitVec.ofNat 64 (288 + j)) = s9.getByte (BitVec.ofNat 64 (288 + j)) := by
            simp only [MachineState.getByte, MachineState.getMem, hmem11]
            exact hout10 (288 + j) (by omega) (by omega)
          rw [h11_9]
          have h9_7 : s9.getByte (BitVec.ofNat 64 (288 + j)) = s7.getByte (BitVec.ofNat 64 (288 + j)) := by
            simp [MachineState.getByte, MachineState.getMem, hmem9]
          rw [h9_7]
          have hc := hcopy7 j hj
          simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem6] at hc ⊢
          exact hc
        have heval_eq : pw.evalLevel c96 (2 + (step + 1)) = chainHash c96 (3 + step) sibD curD := by
          rw [show 2 + (step + 1) = (2 + step) + 1 by omega, evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
          dsimp only; rw [hidx_pw, if_pos hpair, if_neg heven, show 2 + step + 1 = 3 + step by omega]
        have hlinp_eq : pw.levelInputs c96 (2 + step) = chainInputs c96 (3 + step) sibD curD := by
          unfold WitnessPath.levelInputs; dsimp only
          rw [hidx_pw, if_pos hpair, if_neg heven, show 2 + step + 1 = 3 + step by omega]
        refine hhash168 s11 (12 + kR + 1) sibD curD (by omega)
          (((((hst144.trans hst145).trans hs7).trans (hst154.trans hst155)).trans hs10).trans hst157
            |>.eq_of rfl (by omega) (by decide) (by simp))
          hpc11
          (hfix.of_agree (fun r hr => hreg11_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          (by rw [hsb, hst_bits]; exact hcur10.of_agree (fun r _ => hreg11 r))
          (hzero.of_outside hout_s11 (by omega) (by omega))
          (hout_s11.mono (by omega) (by omega))
          ((hreg11 .x22).trans ((hreg10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_9))
          ((hreg11_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg11_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg11_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg11_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg11_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          (((MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega)).trans (hdig10.trans hsibD_eq.symm))
          hR11
          ((hout_s11.readBuffer_eq (by decide) (by omega)).trans hgap)
          heval_eq hlinp_eq
  · -- Odd-node branch (`pc[162..167]`): `binStepBytes = 0`, `binStepTailBits = 0`
    have hsb : binStepBytes g step = 0 := by unfold binStepBytes; exact if_neg hpair
    have hst_bits : binStepTailBits g step = 0 := by unfold binStepTailBits; exact if_neg hpair
    have hpc4 : s4.pc = pcWord 162 := by
      simp only [s4, execInstrBr, hult143, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc3]; exact pc_143_branch
    have hmem4 : s4.mem = s.mem := by
      simpa [s4, execInstrBr, hult143, hpair, MachineState.setPC] using hmem3
    have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s4.getReg r = s.getReg r := fun r h7 h22 h28 => by
      simpa [s4, execInstrBr, hult143, hpair, MachineState.getReg_setPC] using hreg3 r h7 h22 h28
    have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
      simpa [s4, execInstrBr, hult143, hpair, MachineState.getReg_setPC] using hx22_3
    -- pc[162]: ADDI x6, x2, 320; pc[163]: BLTU x29, x6, pc[172]
    have hst162 := step_ordinary oracle s4 162 (.ADDI .x6 .x2 320#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ADDI .x6 .x2 320#12)
    have hpc5 : s5.pc = pcWord 163 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hx6_5 : s5.getReg .x6 = BitVec.ofNat 64 (68719475728 + 320) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg4 .x2 (by decide) (by decide) (by decide), hfix.x2, se12_320]
      exact bv64_add 68719475728 320
    have hx29_5 : s5.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + step)) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hreg4 .x29 (by decide) (by decide) (by decide), hx29]
    have hst163 := step_ordinary oracle s5 163 (.BLTU .x29 .x6 36#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BLTU .x29 .x6 36#13)
    have hult163 : BitVec.ult (s5.getReg .x29) (s5.getReg .x6) = decide (3 + step < 9) := by
      rw [hx29_5, hx6_5, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
    by_cases hlt9 : 3 + step < 9
    · -- Unchained level (`l < 8`, `lvl < 9`): promote cur directly to pc[172], 0 calls
      have hpc6 : s6.pc = pcWord 172 := by
        simp only [s6, execInstrBr, hult163, hlt9, decide_true, ite_true, MachineState.setPC, hpc5]
        exact pc_163_branch
      have hmem6 : s6.mem = s.mem := by
        simpa [s6, execInstrBr, hult163, hlt9, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h6 h7 h22 h28 => by
        have h65 : s6.getReg r = s5.getReg r := by
          simp only [s6, execInstrBr, hult163, hlt9, decide_true, ite_true, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        have h65 : s6.getReg .x22 = s5.getReg .x22 := by
          simp only [s6, execInstrBr, hult163, hlt9, decide_true, ite_true, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x22), hx22_4]
      have heval_eq : pw.evalLevel c96 (2 + (step + 1)) = pw.evalLevel c96 (2 + step) := by
        rw [show 2 + (step + 1) = (2 + step) + 1 by omega, evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
        dsimp only; rw [hidx_pw, if_neg hpair, if_pos (by omega)]
      have hlinp_eq : pw.levelInputs c96 (2 + step) = [] := by
        unfold WitnessPath.levelInputs; dsimp only
        rw [hidx_pw, if_neg hpair, if_pos (by omega)]
      refine hfooter s6 2 0 [] (by decide) (Nat.zero_le _)
        (by simpa using hst162.trans hst163) hpc6
        (hfix.of_agree (fun r hr => hreg6 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (by rw [hsb, hst_bits, Nat.add_zero, Nat.add_zero]
            exact hcur.of_agree (fun r hr => hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        (hzero.of_mem_eq hmem6)
        (MemEqOutside.of_mem_eq hmem6 256 608)
        hx22_6
        ((hreg6 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg6 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg6 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg6 .x29 (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg6 .x30 (by decide) (by decide) (by decide) (by decide)).trans hx30)
        (by rw [heval_eq, (MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by decide) (by omega), hcurDig])
        (((MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
        (fun x hx => by rw [hlinp_eq] at hx; cases hx)
    · -- Chained level (`l ≥ 8`, `lvl ≥ 9`): zero S[32..64) at pc[164..167] and hash `(cur, 0)` at pc[168..171]
      have hpc6 : s6.pc = pcWord 164 := by
        simp only [s6, execInstrBr, hult163, hlt9, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s.mem := by
        simpa [s6, execInstrBr, hult163, hlt9, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h6 h7 h22 h28 => by
        have h65 : s6.getReg r = s5.getReg r := by
          simp only [s6, execInstrBr, hult163, hlt9, decide_false, Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg4 r h7 h22 h28
      have hx22_6 : s6.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) := by
        have h65 : s6.getReg .x22 = s5.getReg .x22 := by
          simp only [s6, execInstrBr, hult163, hlt9, decide_false, Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        rw [h65]; simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x22), hx22_4]
      obtain ⟨s7, hs7, hpc7, hreg7, hright7, hout7⟩ :=
        step_zero_right oracle s6 hpc6 ((hreg6 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
      have hout_s7 : MemEqOutside s s7 288 320 :=
        (MemEqOutside.of_mem_eq hmem6 288 320).trans hout7
      have heval_eq : pw.evalLevel c96 (2 + (step + 1)) = chainHash c96 (3 + step) (pw.evalLevel c96 (2 + step)) 0 := by
        rw [show 2 + (step + 1) = (2 + step) + 1 by omega, evalLevel_succ_of_ge1 c96 pw (2 + step) (by omega)]
        dsimp only; rw [hidx_pw, if_neg hpair, if_neg (by omega), show 2 + step + 1 = 3 + step by omega]
      have hlinp_eq : pw.levelInputs c96 (2 + step) = chainInputs c96 (3 + step) (pw.evalLevel c96 (2 + step)) 0 := by
        unfold WitnessPath.levelInputs; dsimp only
        rw [hidx_pw, if_neg hpair, if_neg (by omega), show 2 + step + 1 = 3 + step by omega]
      refine hhash168 s7 6 (pw.evalLevel c96 (2 + step)) 0 (by decide)
        (((hst162.trans hst163).trans hs7).eq_of rfl (by decide) (by decide) (by simp))
        hpc7
        (hfix.of_agree (fun r hr => (hreg7 r).trans (hreg6 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
        (by rw [hsb, hst_bits, Nat.add_zero, Nat.add_zero]
            exact hcur.of_agree (fun r hr => (hreg7 r).trans (hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))))
        (hzero.of_outside hout_s7 (by omega) (by omega))
        (hout_s7.mono (by omega) (by omega))
        ((hreg7 .x22).trans hx22_6)
        ((hreg7 .x24).trans ((hreg6 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
        ((hreg7 .x8 ).trans ((hreg6 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
        ((hreg7 .x27).trans ((hreg6 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
        ((hreg7 .x29).trans ((hreg6 .x29 (by decide) (by decide) (by decide) (by decide)).trans hx29))
        ((hreg7 .x30).trans ((hreg6 .x30 (by decide) (by decide) (by decide) (by decide)).trans hx30))
        ((hout_s7.readBuffer_eq (by decide) (by omega)).trans hcurDig)
        hright7
        ((hout_s7.readBuffer_eq (by decide) (by omega)).trans hgap)
        heval_eq hlinp_eq

/-- Full unified binary loop (`L2..L13`, 12 iterations, `pc[138..173]` -> `pc[174]`),
`≤ 3842` steps, `≤ 64` oracle calls. -/
theorem step_pos_bin_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff bitOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 138)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + 32) bitOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hzero : ChainScratchZero s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl2 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff bitOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 2)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g := i.val / 3
    let pw := parsePartialWitness s0 input.proof.length pOff bitOff i (valAt input ord)
    PhaseOutcome oracle s 3842 64
      (input.proof.length < pOff + recordLen i + tailBytesBits (bitOff + recordTailBits i))
      (fun s' q tr =>
        q ≤ 64 ∧
        s'.pc = pcWord 174 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + recordLen i) (bitOff + recordTailBits i) s' ∧
        ChainScratchZero s' ∧
        MemEqOutside s s' 256 608 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g >>> 12) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 14 ∧
        ∀ prev, 2 ≤ prev → prev ≤ 13 → ∀ x ∈ pw.levelInputs c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g pw
  -- pc[138..139]: x29 = x2 + 80, x30 = x2 + 560
  have hst138 := step_ordinary oracle s 138 (.ADDI .x29 .x2 80#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x29 .x2 80#12)
  have hpc1 : s1.pc = pcWord 139 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst139 := step_ordinary oracle s1 139 (.ADDI .x30 .x2 560#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x30 .x2 560#12)
  have hpc2 : s2.pc = pcWord 140 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x29 → r ≠ .x30 → s2.getReg r = s.getReg r := fun r h29 h30 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h30.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h29.symm]
  have hx29_2 : s2.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * 2) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x29), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hfix.x2, se12_80]
    exact bv64_add 68719475728 80
  have hx30_2 : s2.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x2), hfix.x2, se12_560]
    exact bv64_add 68719475728 560
  have hind : ∀ n ≤ 12,
      PhaseOutcome oracle s2 (320 * n) (∑ j ∈ Finset.range n, levelChain (3 + j))
        (input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g n + tailBytesBits (bitOff + binTailBitsOff g n))
        (fun s' q tr =>
          q ≤ ∑ j ∈ Finset.range n, levelChain (3 + j) ∧
          s'.pc = (if n = 12 then pcWord 174 else pcWord 140) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length
            (pOff + 24 + l0Bytes i + 32 + binPathOff g n) (bitOff + binTailBitsOff g n) s' ∧
          ChainScratchZero s' ∧
          MemEqOutside s2 s' 256 608 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g >>> n) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + n)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + n) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ j < n, ∀ x ∈ pw.levelInputs c96 (2 + j), InTrace h768 oracle tr x) := by
    intro n hn
    induction n with
    | zero =>
      refine .continued s2 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s2)
        ⟨by simp, by simpa using hpc2,
         hfix.of_agree (fun r hr => hreg2 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         by simpa [binPathOff, binTailBitsOff] using
           hcur.of_agree (fun r hr => hreg2 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         hzero.of_mem_eq hmem2,
         MemEqOutside.refl s2 256 608,
         by simpa using (hreg2 .x22 (by decide) (by decide)).trans hx22,
         (hreg2 .x24 (by decide) (by decide)).trans hx24,
         (hreg2 .x8  (by decide) (by decide)).trans hx8,
         (hreg2 .x27 (by decide) (by decide)).trans hx27,
         hx29_2, hx30_2,
         ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hl2,
         ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hgap,
         fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      have hcan_mono :
          input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g k + tailBytesBits (bitOff + binTailBitsOff g k) →
          input.proof.length < pOff + 24 + l0Bytes i + 32 + binPathOff g (k + 1) + tailBytesBits (bitOff + binTailBitsOff g (k + 1)) := by
        intro hlt
        have htb : tailBytesBits (bitOff + binTailBitsOff g k) ≤ tailBytesBits (bitOff + binTailBitsOff g (k + 1)) :=
          tailBytesBits_mono (by simp only [binTailBitsOff]; omega)
        simp only [binPathOff]; omega
      rw [show 320 * (k + 1) = 320 * k + 320 by omega, Finset.sum_range_succ]
      refine (ih (by omega)).bind_dep hcan_mono (fun sk q1 tr1 ⟨hq1, hpc_k, hfix_k, hcur_k, hzero_k, hout_k,
          hx22_k, hx24_k, hx8_k, hx27_k, hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ => by
        have hpc_140 : sk.pc = pcWord 140 := by rwa [if_neg (by omega : k ≠ 12)] at hpc_k
        have hhigh_k : HighMemPreserved s0 sk :=
          hhigh.trans ((MemEqOutside.of_mem_eq hmem2 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
        have hstep1 := step_pos_bin_iter h768 oracle input hvalid ord pOff bitOff rem k hord (by omega)
          sk hpc_140 hfix_k hcur_k hhigh_k hzero_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
        refine hstep1.weaken (le_refl _) (le_refl _)
          (fun h => by simpa only [binPathOff, binTailBitsOff, Nat.add_assoc] using h) ?_
        rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hzero', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
        refine ⟨by omega, hpc', hfix', by simpa only [binPathOff, binTailBitsOff, Nat.add_assoc] using hcur',
          hzero', hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
        intro j hj x hx
        by_cases hjk : j < k
        · exact (htr_k j hjk x hx).append_left
        · have : j = k := by omega
          subst this; exact (htr' x hx).append_right)
  have h12 := (hst138.trans hst139).prepend_pure (hind 12 (le_refl _))
  refine h12.weaken (by omega) (by rw [binLoop_calls_sum])
    (fun h => by unfold recordLen recordTailBits; simpa only [Nat.add_assoc] using h) ?_
  rintro s' q tr ⟨hq, hpc', hfix', hcur', hzero', hout', hx22', hx24', hx8', hx27', _, _, hdig', _, htr'⟩
  refine ⟨by rw [binLoop_calls_sum] at hq; exact hq,
    by simpa using hpc', hfix',
    by unfold recordLen recordTailBits; simpa only [Nat.add_assoc] using hcur',
    hzero', (MemEqOutside.of_mem_eq hmem2 256 608).trans hout',
    hx22', hx24', hx8', hx27', hdig', ?_⟩
  intro prev hp1 hp2 x hx
  have hpeq : 2 + (prev - 2) = prev := by omega
  exact htr' (prev - 2) (by omega) x (by rwa [hpeq])

/-! #### Phase 1E: L14 Cap Store (`683` cap leaves, `pc[174..208]`) -/

private def capAddrInstrs : List Instr :=
  [.SRLI .x22 .x22 1#6, .SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6,
   .SLLI .x6 .x6 5#6, .ADD .x28 .x19 .x6, .ADD .x29 .x18 .x22]

private theorem ordinaryStep_ADDI (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    ordinaryStep st (.base (.ADDI rd rs imm)) = some (execInstrBr st (.ADDI rd rs imm)) := rfl

private theorem ordinaryStep_BNE (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    ordinaryStep st (.base (.BNE r1 r2 off)) = some (execInstrBr st (.BNE r1 r2 off)) := rfl

private theorem execInstrBr_ADDI_pc (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr st (.ADDI rd rs imm)).pc = st.pc + (4 : Word) := rfl

private theorem execInstrBr_ADDI_mem (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr st (.ADDI rd rs imm)).mem = st.mem := by
  simp [execInstrBr, mem_setPC, mem_setReg]

private theorem execInstrBr_ADDI_getReg_eq (st : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (h0 : rd ≠ .x0) :
    (execInstrBr st (.ADDI rd rs imm)).getReg rd = st.getReg rs + signExtend12 imm := by
  simp only [execInstrBr, MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_eq h0

private theorem execInstrBr_ADDI_getReg_ne (st : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (r : Reg) (hne : rd ≠ r) :
    (execInstrBr st (.ADDI rd rs imm)).getReg r = st.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_ne st rd r _ hne

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
    checkInstr (193 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (287 - (193 + 3 * j + 2))))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

private theorem zero64_eq_ofNat : (0#64 : Word) = BitVec.ofNat 64 0 := rfl
private theorem zero_lt_pow64 : 0 < 2 ^ 64 := Nat.pow_pos (Nat.succ_pos 1)

private theorem step_tail_205 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 205)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 206 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 205 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_205
     (by intro h; cases h) (ordinaryStep_ADDI s .x24 .x24 8#12),
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 205)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (6912218176 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 6912218176 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_206 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 206)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (7046435904 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 207 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 206 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_206
     (by intro h; cases h) (ordinaryStep_ADDI s .x8 .x8 256#12),
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 206)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (7046435904 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 7046435904 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_207 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 207)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 208 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 207 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_207
     (by intro h; cases h) (ordinaryStep_ADDI s .x27 .x27 4095#12),
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 207)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_tail_208 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 208)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 209 else pcWord 19) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x27 .x0 7436#13),
    step_ordinary oracle s 208 (.BNE .x27 .x0 7436#13) (by decide) hpc checkInstr_208
      (by intro h; cases h) (ordinaryStep_BNE s .x27 .x0 7436#13),
    ?_, execInstrBr_BNE_mem s .x27 .x0 7436#13, execInstrBr_BNE_getReg s .x27 .x0 7436#13⟩
  have hne_iff : (s.getReg .x27 != s.getReg .x0) = decide (rem1 ≠ 0) := by
    rw [getReg_x0 s, zero64_eq_ofNat, h27]
    exact bv64_bne_eq rem1 0 hrem_lt zero_lt_pow64
  by_cases hz : rem1 = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x27 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false s .x27 .x0 7436#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 208))
  · rw [if_neg hz]
    have ht : (s.getReg .x27 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true s .x27 .x0 7436#13 ht).trans
      ((congrArg (· + signExtend13 7436#13) hpc).trans pc_208_branch)

private theorem step_pos_cap_store_tail (oracle : Oracle) (s0 : MachineState)
    (proofLen ord pOffNext bitOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s205 : MachineState) (hpc205 : s205.pc = pcWord 205)
    (hfix205 : CheckFixedRegs s205)
    (hcur205 : ProofCursor s0 proofLen pOffNext bitOffNext s205)
    (h24 : s205.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (h8  : s205.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (h27 : s205.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s205 sFin 4 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 209 else pcWord 19) ∧
      CheckFixedRegs sFin ∧
      ProofCursor s0 proofLen pOffNext bitOffNext sFin ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s205.mem := by
  obtain ⟨s206, hs1, hpc206, hmem1, hx24_1, hreg1⟩ := step_tail_205 oracle ord s205 hpc205 h24
  obtain ⟨s207, hs2, hpc207, hmem2, hx8_2, hreg2⟩ :=
    step_tail_206 oracle ord s206 hpc206 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s208, hs3, hpc208, hmem3, hx27_3, hreg3⟩ :=
    step_tail_207 oracle rem1 s207 hpc207 ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27))
  obtain ⟨sFin, hs4, hpcFin, hmem4, hreg4⟩ :=
    step_tail_208 oracle rem1 (Nat.lt_of_succ_lt hrem_lt) s208 hpc208 hx27_3
  have hsteps : StepsTo oracle s205 sFin 4 0 [] :=
    (((hs1.trans hs2).trans hs3).trans hs4).eq_of rfl rfl rfl rfl
  have hmemFin : sFin.mem = s205.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x27 → sFin.getReg r = s205.getReg r :=
    fun r h24r h8r h27r => (hreg4 r).trans ((hreg3 r h27r).trans ((hreg2 r h8r).trans (hreg1 r h24r)))
  exact ⟨sFin, hsteps, hpcFin,
    hfix205.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hcur205.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    (hreg4 .x24).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1)),
    (hreg4 .x8).trans ((hreg3 .x8 (by decide)).trans hx8_2),
    (hreg4 .x27).trans hx27_3, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 683)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 182) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 256#64)
    (hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c))
    (hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c))
    (d14 : Digest) (hd14 : readBuffer s 256 32 = d14) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 205 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
      readBuffer s7 (8192 + gapOffset c) 32 = d14 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
        (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst182 := step_ordinary oracle s3 182 (.ADDI .x7 .x0 1#12) (by decide) hpc3 checkInstr_182 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 183 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx29_4 : s4.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha183 : s4.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_4, se12_0, BitVec.add_zero]
  have hv183 : memoryArgumentsValid s4 (.SB .x29 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha183]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst183 := step_ordinary oracle s4 183 (.SB .x29 .x7 0#12) (by decide) hpc4 checkInstr_183 (by intro h; cases h)
    (by simp [ordinaryStep, hv183])
  let s5 := execInstrBr s4 (.SB .x29 .x7 0#12)
  have hpc5 : s5.pc = pcWord 184 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (4096 + c)) 1#8).getByte q := by
    intro q
    simp only [s5, execInstrBr, ha183, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
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
  have hst192 := step_ordinary oracle s6 192 (.JAL .x0 52#21) (by decide) hpc6 checkInstr_192 (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 205 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_192_jal
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
  have hv7 : readBuffer s7 (8192 + gapOffset c) 32 = d14 := by
    rw [(MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← hd14]
    apply readBuffer_congr2; intro j hj
    have hc := hcopy6 j hj
    simp only [Nat.add_zero] at hc
    rw [hc]
    exact hout5 (256 + j) (by omega) (by omega)
  refine ⟨s7, by simpa using ((hst182.trans hst183).trans hs6).trans hst192, hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1E: store or duplicate-check cap leaf at L14 (`683` leaves) and advance loop counters (`pc[174..208]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext bitOffNext rem1 : Nat) (hord : ord < input.positions.card)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 174)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOffNext bitOffNext s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) >>> 12))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1))
    (marked : Bool)
    (hmark : s.getByte (BitVec.ofNat 64 (4096 + capLeafOf (posAt input.positions ord))) =
      if marked then 1#8 else 0#8)
    (d14 : Digest) (hd14 : readBuffer s 256 32 = d14) :
    let s0 := submission.initialState .check input
    let c := capLeafOf (posAt input.positions ord)
    PhaseOutcome oracle s 30 0
      (marked = true ∧ d14 ≠ readBuffer s (8192 + gapOffset c) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = (if rem1 = 0 then pcWord 209 else pcWord 19) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pOffNext bitOffNext s' ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * (ord + 1)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
        readBuffer s' (8192 + gapOffset c) 32 = d14 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
          (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro s0 c
  have hc_lt : c < 683 := capLeafOf_lt (posAt input.positions ord)
  have hi_lt : (posAt input.positions ord).val < 16777216 := (posAt input.positions ord).isLt
  have h12_lt : ((posAt input.positions ord).val / 3) >>> 12 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_shr : (((posAt input.positions ord).val / 3) >>> 12) / 2 = c := by
    unfold c capLeafOf
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul, show (2 ^ 12 : Nat) * 2 = 2 ^ 13 by decide]
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
      rw [hx22, bv64_shr _ 1 h12_lt, Nat.pow_one, hc_shr]
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22_a, hfix.x19,
      show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide] using hcomp
  have hx29_1 : s1.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    have hcomp : (4096#64 : Word) + BitVec.ofNat 64 c = BitVec.ofNat 64 (4096 + c) := by
      change BitVec.ofNat 64 4096 + BitVec.ofNat 64 c = _; exact bv64_add 4096 c
    have hx22_a : (s.getReg .x22 >>> (1#6 : BitVec 6).toNat) = BitVec.ofNat 64 c := by
      rw [hx22, show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr _ 1 h12_lt, Nat.pow_one, hc_shr]
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
  have ha180 : s1.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_1, se12_0, BitVec.add_zero]
  have hv180 : memoryArgumentsValid s1 (.LBU .x7 .x29 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha180]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst180 := step_ordinary oracle s1 180 (.LBU .x7 .x29 0#12) (by decide) hpc1 checkInstr_180 (by intro h; cases h)
    (by simp [ordinaryStep, hv180])
  let s2 := execInstrBr s1 (.LBU .x7 .x29 0#12)
  have hpc2 : s2.pc = pcWord 181 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1'
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha180]
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
  have hst181 := step_ordinary oracle s2 181 (.BNE .x7 .x0 48#13) (by decide) hpc2 checkInstr_181 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 8 0 [] := by simpa using hs1.trans (hst180.trans hst181)
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
        hfix.x21 hx28_3 hx29_3 d14 hd14
    have hfix7 : CheckFixedRegs s7 :=
      hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    have hcur7 : ProofCursor s0 input.proof.length pOffNext bitOffNext s7 :=
      hcur.of_agree (fun r hr => hreg7 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
    obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
      step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext bitOffNext rem1 hrem_lt s7 hpc7 hfix7 hcur7
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
    have hpc3 : s3.pc = pcWord 193 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_181_branch
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
    have hrb_s3_a : readBuffer s3 256 32 = d14 :=
      ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hd14
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
      have hcur4 : ProofCursor s0 input.proof.length pOffNext bitOffNext s4 :=
        hcur.of_agree (fun r hr => hreg4s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
        step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext bitOffNext rem1 hrem_lt s4 hpc4 hfix4 hcur4
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

/-! #### Per-Position Loop Invariant and Induction (`pc[19] -> pc[209]`) -/

def posMarked14 (positions : Positions) (n c : Nat) : Bool :=
  decide (∃ j < n, capLeafOf (posAt positions j) = c)

theorem posMarked14_zero (positions : Positions) (c : Nat) :
    posMarked14 positions 0 c = false := by
  simp [posMarked14]

theorem posMarked14_succ (positions : Positions) (n c : Nat) :
    posMarked14 positions (n + 1) c =
      (posMarked14 positions n c || decide (capLeafOf (posAt positions n) = c)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [posMarked14, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hc⟩
    by_cases hjn : j < n
    · exact Or.inl ⟨j, hjn, hc⟩
    · have hjeq : j = n := by omega
      subst hjeq; exact Or.inr hc
  · rintro (⟨j, hj, hc⟩ | hc)
    · exact ⟨j, by omega, hc⟩
    · exact ⟨n, by omega, hc⟩

theorem posMarked14_card_eq_capMark (positions : Positions) (c : Nat) :
    posMarked14 positions positions.card c = capMark positions 14 c := by
  unfold posMarked14
  rw [capMark_14]
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
  posRecordOff input.positions n + tailBytesBits (posTailBitsOff input.positions n) ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions j1) (posTailBitsOff input.positions j1)
      (posAt input.positions j1) (valAt input j1)).evalLevel c96 14 =
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions j2) (posTailBitsOff input.positions j2)
      (posAt input.positions j2) (valAt input j2)).evalLevel c96 14

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff input.positions n) (posTailBitsOff input.positions n) s
  high : HighMemPreserved (submission.initialState .check input) s
  zero : ChainScratchZero s
  pc : s.pc = if n = input.positions.card then pcWord 209 else pcWord 19
  x24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * n)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (input.positions.card - n)
  mark14 : ∀ c < 683, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if posMarked14 input.positions n c then 1#8 else 0#8
  mark_hi_zero : ∀ a, 4096 + 683 ≤ a → a < 4096 + 1416 → s.getByte (BitVec.ofNat 64 a) = 0#8
  val14_gap_zero : ∀ q < 342, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + 96 * q + 64 + b)) = 0#8
  val14_odd_right_zero : ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + 96 * 341 + 32 + b)) = 0#8
  val_hi_zero : ∀ a, 8192 + capValOff 15 ≤ a → a < 8192 + 65984 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  witnesses : ∀ j < n,
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness (submission.initialState .check input) input.proof.length
      (posRecordOff input.positions j) (posTailBitsOff input.positions j) (posAt input.positions j) (valAt input j)
    pw.evalLevel c96 14 = readBuffer s (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) ∧
    ((posAt input.positions j).val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96)) ∧
    (∀ prev, 1 ≤ prev → prev ≤ 13 → ∀ x ∈ pw.levelInputs c96 prev, InTrace h768 oracle tr x)

private theorem gapOffset_disjoint_of_ne {c1 c2 : Nat} (hne : c1 ≠ c2) :
    gapOffset c1 + 32 ≤ gapOffset c2 ∨ gapOffset c2 + 32 ≤ gapOffset c1 := by
  unfold gapOffset; omega

private theorem gapOffset_disjoint_gap (c q b : Nat) (hb : b < 32) :
    8192 + 96 * q + 64 + b < 8192 + gapOffset c ∨
    8192 + gapOffset c + 32 ≤ 8192 + 96 * q + 64 + b := by
  unfold gapOffset
  rcases Nat.even_or_odd' c with ⟨k, rfl | rfl⟩ <;> omega

private theorem gapOffset_lt_odd_right (c : Nat) (hc : c < 683) :
    gapOffset c + 32 ≤ 96 * 341 + 32 := by
  unfold gapOffset; omega

private theorem capValOff_15_eq : capValOff 15 = 32832 := by decide

/-- Complete per-position verification loop (`pc[19]` -> `pc[209]`), `≤ 4792 * k` steps, `≤ 70 * k` calls. -/
theorem step_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0)
    (sInit : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sInit (4792 * input.positions.card) (70 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' q tr => q ≤ 70 * input.positions.card ∧ PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (4792 * n) (70 * n)
        (¬ PosConsistent c96 s0 input n)
        (fun s' q tr => q ≤ 70 * n ∧ PosLoopInv h768 oracle input n s' tr) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued sInit 0 0 [] (by decide) (by decide) (StepsTo.refl oracle sInit) ⟨by decide, hinit⟩
    | succ k ih =>
      have hcons_sub : ¬ PosConsistent c96 s0 input k → ¬ PosConsistent c96 s0 input (k + 1) := by
        intro hnot hcons
        apply hnot
        have hp_m := posRecordOff_mono input.positions (show k ≤ k + 1 by omega)
        have ht_m := tailBytesBits_mono (posTailBitsOff_mono input.positions (show k ≤ k + 1 by omega))
        refine ⟨by have := hcons.1; omega, ?_⟩
        intro j1 j2 hj1 hj2 hc
        exact hcons.2 j1 j2 (by omega) (by omega) hc
      rw [show 4792 * (k + 1) = 4792 * k + 4792 by omega,
        show 70 * (k + 1) = 70 * k + 70 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hlt_k : k < input.positions.card := by omega
        have hpc_k : sk.pc = pcWord 19 := by
          have := hinv_k.pc
          rwa [if_neg (by omega : k ≠ input.positions.card)] at this
        let pOff := posRecordOff input.positions k
        let bitOff := posTailBitsOff input.positions k
        let i := posAt input.positions k
        let g := i.val / 3
        let pw := parsePartialWitness s0 input.proof.length pOff bitOff i (valAt input k)
        let rem1 := input.positions.card - (k + 1)
        have hrem_eq : input.positions.card - k = rem1 + 1 := by omega
        have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
          rw [hinv_k.x27, hrem_eq]
        have htb_step : tailBytesBits bitOff ≤ tailBytesBits (bitOff + recordTailBits i) :=
          tailBytesBits_mono (by omega)
        -- Chain 1A (190, 4) -> 1B (420, 1) -> 1C (310, 1) -> 1D (3842, 64) -> 1E (30, 0)
        refine PhaseOutcome.weaken
          (K1 := 190 + (420 + (310 + (3842 + 30)))) (Q1 := 4 + (1 + (1 + (64 + 0))))
          ?_ (by decide) (by decide) id (fun _ _ _ h => h)
        have h1a := step_pos_leaf h768 oracle input hvalid k pOff bitOff (rem1 + 1) hlt_k
          sk hpc_k hinv_k.fixed hinv_k.cursor hinv_k.high hinv_k.x24 hinv_k.x8 hx27_k
        have hcan_leaf : input.proof.length < pOff + 24 + tailBytesBits bitOff → ¬ PosConsistent c96 s0 input (k + 1) := by
          intro hlt hcons
          have h1 := hcons.1
          rw [posRecordOff_succ, posTailBitsOff_succ] at h1
          change pOff + recordLen i + tailBytesBits (bitOff + recordTailBits i) ≤ input.proof.length at h1
          unfold recordLen at h1; omega
        refine h1a.bind_dep hcan_leaf (fun s1 qA trA ⟨hqA, hpcA, hfixA, hcurA, houtA, hx20A, hx24A, hx8A, hx27A, hleafA, htrA⟩ => by
          have hhighA : HighMemPreserved s0 s1 := hinv_k.high.trans (houtA.mono (by omega) (by omega))
          have hzeroA : ChainScratchZero s1 := hinv_k.zero.of_outside houtA (by omega) (by omega)
          have h1b := step_pos_l0 h768 oracle input hvalid k pOff bitOff (rem1 + 1) hlt_k
            s1 hpcA hfixA hcurA hhighA hx20A hx24A hx8A hx27A hleafA
          have hcan_l0 : input.proof.length < pOff + 24 + l0Bytes i + tailBytesBits bitOff → ¬ PosConsistent c96 s0 input (k + 1) := by
            intro hlt hcons
            have h1 := hcons.1
            rw [posRecordOff_succ, posTailBitsOff_succ] at h1
            change pOff + recordLen i + tailBytesBits (bitOff + recordTailBits i) ≤ input.proof.length at h1
            unfold recordLen at h1; omega
          refine h1b.bind_dep hcan_l0 (fun s2 qB trB ⟨hqB, hpcB, hfixB, hcurB, houtB, hx22B, hx24B, hx8B, hx27B, hl1B, htrB⟩ => by
            have hhighB : HighMemPreserved s0 s2 := hhighA.trans (houtB.mono (by omega) (by omega))
            have hzeroB : ChainScratchZero s2 := hzeroA.of_outside houtB (by omega) (by omega)
            have h1c := step_pos_l1 h768 oracle input hvalid k pOff bitOff (rem1 + 1) hlt_k
              s2 hpcB hfixB hcurB hhighB hzeroB hx22B hx24B hx8B hx27B hl1B
            have hcan_l1 : input.proof.length < pOff + 24 + l0Bytes i + 32 + tailBytesBits bitOff → ¬ PosConsistent c96 s0 input (k + 1) := by
              intro hlt hcons
              have h1 := hcons.1
              rw [posRecordOff_succ, posTailBitsOff_succ] at h1
              change pOff + recordLen i + tailBytesBits (bitOff + recordTailBits i) ≤ input.proof.length at h1
              unfold recordLen at h1; omega
            refine h1c.bind_dep hcan_l1 (fun s3 qC trC ⟨hqC, hpcC, hfixC, hcurC, hzeroC, houtC, hx22C, hx24C, hx8C, hx27C, hl2C, hgapC, htrC⟩ => by
              have hhighC : HighMemPreserved s0 s3 := hhighB.trans (houtC.mono (by omega) (by omega))
              have h1d := step_pos_bin_loop h768 oracle input hvalid k pOff bitOff (rem1 + 1) hlt_k
                s3 hpcC hfixC hcurC hhighC hzeroC hx22C hx24C hx8C hx27C hl2C hgapC
              have hcan_bin : input.proof.length < pOff + recordLen i + tailBytesBits (bitOff + recordTailBits i) →
                  ¬ PosConsistent c96 s0 input (k + 1) := by
                intro hlt hcons
                have h1 := hcons.1
                rw [posRecordOff_succ, posTailBitsOff_succ] at h1
                change pOff + recordLen i + tailBytesBits (bitOff + recordTailBits i) ≤ input.proof.length at h1; omega
              refine h1d.bind_dep hcan_bin (fun s4 qD trD ⟨hqD, hpcD, hfixD, hcurD, hzeroD, houtD, hx22D, hx24D, hx8D, hx27D, hd14D, htrD⟩ => by
                have hout_sk4 : MemEqOutside sk s4 256 608 :=
                  (houtA.mono (by omega) (by omega)).trans
                    ((houtB.mono (by omega) (by omega)).trans (houtC.trans houtD))
                have hc_lt : capLeafOf i < 683 := capLeafOf_lt i
                have hmark4 : s4.getByte (BitVec.ofNat 64 (4096 + capLeafOf i)) =
                    if posMarked14 input.positions k (capLeafOf i) then 1#8 else 0#8 :=
                  (hout_sk4 (4096 + capLeafOf i) (by omega) (by omega)).trans (hinv_k.mark14 (capLeafOf i) hc_lt)
                have h1e := step_pos_cap_store oracle input k (pOff + recordLen i) (bitOff + recordTailBits i) rem1 hlt_k (by omega)
                  s4 hpcD hfixD hcurD hx22D hx24D hx8D hx27D (posMarked14 input.positions k (capLeafOf i))
                  hmark4 (pw.evalLevel c96 14) hd14D
                have hcan_dup : (posMarked14 input.positions k (capLeafOf i) = true ∧
                    pw.evalLevel c96 14 ≠ readBuffer s4 (8192 + gapOffset (capLeafOf i)) 32) →
                    ¬ PosConsistent c96 s0 input (k + 1) := by
                  rintro ⟨hm, hne_d⟩ hcons
                  have hex : ∃ j < k, capLeafOf (posAt input.positions j) = capLeafOf i :=
                    of_decide_eq_true hm
                  obtain ⟨j, hjk, hcj⟩ := hex
                  have hwj := (hinv_k.witnesses j hjk).1
                  have hrb_eq : readBuffer s4 (8192 + gapOffset (capLeafOf i)) 32 =
                      readBuffer sk (8192 + gapOffset (capLeafOf i)) 32 :=
                    hout_sk4.readBuffer_eq (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                  have heq_cons := hcons.2 j k (by omega) (by omega) hcj
                  apply hne_d
                  rw [hrb_eq, ← hcj, ← hwj]
                  exact heq_cons.symm
                refine h1e.weaken (le_refl _) (le_refl _) hcan_dup ?_
                rintro s5 qE trE ⟨rfl, rfl, hpcE, hfixE, hcurE, hx24E, hx8E, hx27E, hmarkE, hvalE, houtE, hmemE⟩
                have hout_s5_sk : ∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + capLeafOf i →
                    (a < 256 ∨ 608 ≤ a) →
                    (a < 8192 + gapOffset (capLeafOf i) ∨ 8192 + gapOffset (capLeafOf i) + 32 ≤ a) →
                    s5.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a ha hneM hlow hcap =>
                  (houtE a ha hneM hcap).trans (hout_sk4 a ha hlow)
                have hgo_bd : gapOffset (capLeafOf i) + 32 ≤ 32832 := by unfold gapOffset; omega
                refine ⟨by omega, ⟨hfixE,
                  by rw [posRecordOff_succ, posTailBitsOff_succ]; exact hcurE,
                  fun a ha hout => by
                    rw [hout_s5_sk a ha (by omega) (by omega) (by omega)]
                    exact hinv_k.high a ha hout,
                  ⟨fun a h1 h2 => (houtE a (by omega) (by omega) (by omega)).trans (hzeroD.1 a h1 h2),
                   fun a h1 h2 => (houtE a (by omega) (by omega) (by omega)).trans (hzeroD.2 a h1 h2)⟩,
                  by rw [hpcE]; exact if_congr (by omega) rfl rfl,
                  hx24E, hx8E, by simpa only [rem1] using hx27E,
                  ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
                · intro c hc
                  rw [posMarked14_succ]
                  change _ = if (posMarked14 input.positions k c || decide (capLeafOf i = c)) then 1#8 else 0#8
                  by_cases heqc : c = capLeafOf i
                  · subst heqc; simp only [decide_true, Bool.or_true, ite_true]; exact hmarkE
                  · have hneq : capLeafOf i ≠ c := fun h => heqc h.symm
                    simp only [decide_eq_false hneq, Bool.or_false]
                    rw [hout_s5_sk (4096 + c) (by omega) (by omega) (by omega) (by unfold gapOffset; omega)]
                    exact hinv_k.mark14 c hc
                · intro a ha1 ha2
                  rw [hout_s5_sk a (by omega) (by omega) (by omega) (by unfold gapOffset; omega)]
                  exact hinv_k.mark_hi_zero a ha1 ha2
                · intro q hq b hb
                  rw [hout_s5_sk (8192 + 96 * q + 64 + b) (by omega) (by omega) (by omega)
                    (gapOffset_disjoint_gap (capLeafOf i) q b hb)]
                  exact hinv_k.val14_gap_zero q hq b hb
                · intro b hb
                  have hlt_or := gapOffset_lt_odd_right (capLeafOf i) hc_lt
                  rw [hout_s5_sk (8192 + 96 * 341 + 32 + b) (by omega) (by omega) (by omega) (by omega)]
                  exact hinv_k.val14_odd_right_zero b hb
                · intro a ha1 ha2
                  rw [capValOff_15_eq] at ha1
                  rw [hout_s5_sk a (by omega) (by omega) (by omega) (by omega)]
                  exact hinv_k.val_hi_zero a (by rw [capValOff_15_eq]; exact ha1) ha2
                · intro j hj
                  by_cases hjk : j < k
                  · obtain ⟨hwj_ev, hwj_leaf, hwj_l0, hwj_bin⟩ := hinv_k.witnesses j hjk
                    refine ⟨?_,
                      fun x hx => (hwj_leaf x hx).append_left,
                      fun hf => (hwj_l0 hf).append_left,
                      fun prev hp1 hp2 x hx => (hwj_bin prev hp1 hp2 x hx).append_left⟩
                    by_cases hcj : capLeafOf (posAt input.positions j) = capLeafOf i
                    · have hm_true : posMarked14 input.positions k (capLeafOf i) = true := by
                        unfold posMarked14; rw [decide_eq_true_eq]; exact ⟨j, hjk, hcj⟩
                      have hmem54 : s5.mem = s4.mem := hmemE hm_true
                      rw [hwj_ev, hcj]
                      apply readBuffer_congr2; intro b hb
                      have h54 : s5.getByte (BitVec.ofNat 64 (8192 + gapOffset (capLeafOf i) + b)) =
                          s4.getByte (BitVec.ofNat 64 (8192 + gapOffset (capLeafOf i) + b)) := by
                        simp [MachineState.getByte, MachineState.getMem, hmem54]
                      rw [h54, hout_sk4 (8192 + gapOffset (capLeafOf i) + b) (by unfold gapOffset; omega) (by unfold gapOffset; omega)]
                    · rw [hwj_ev]
                      apply readBuffer_congr2; intro b hb
                      have hdisj := gapOffset_disjoint_of_ne hcj
                      exact (hout_s5_sk (8192 + gapOffset (capLeafOf (posAt input.positions j)) + b)
                        (by unfold gapOffset; have := capLeafOf_lt (posAt input.positions j); omega)
                        (by unfold gapOffset; omega) (by unfold gapOffset; omega) (by omega)).symm
                  · have hjeq : j = k := by omega
                    subst hjeq
                    refine ⟨hvalE.symm,
                      fun x hx => (htrA x hx).append_left.append_right,
                      fun hf => (htrB hf).append_left.append_right.append_right, ?_⟩
                    intro prev hp1 hp2 x hx
                    by_cases hp1e : prev = 1
                    · subst hp1e
                      exact (htrC x hx).append_left.append_right.append_right.append_right
                    · exact (htrD prev (by omega) hp2 x hx).append_left.append_right.append_right.append_right.append_right)))))
  exact hind input.positions.card (le_refl _)

end CommitGolfCandidate
