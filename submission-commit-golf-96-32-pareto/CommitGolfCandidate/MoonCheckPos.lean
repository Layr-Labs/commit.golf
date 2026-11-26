import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the L2..L4 (256b), L5..L8 (240b), and L9..L13 (238b) binary loops,
L14 cap-store, and full per-position loop (`pc[159..295]`, `pc[22] -> pc[296]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem evalLevel_succ_of_ge2 (c : Comp96) (w : WitnessPath) (l : Nat) (hl : 2 ≤ l) :
    w.evalLevel c (l + 1) =
      let cur := w.evalLevel c l
      let idx := ((w.index.val / 3) / 3) >>> (l - 2)
      if (idx ^^^ 1) < levelSize l then
        let inp := if idx % 2 = 0 then binaryInput cur (w.binSib l)
                   else binaryInput (w.binSib l) cur
        maskLevel (l + 1) (c inp)
      else cur := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
  rfl

private theorem pc_167_branch : pcWord 167 + signExtend13 104#13 = pcWord 193 := by decide
private theorem pc_169_branch : pcWord 169 + signExtend13 856#13 = pcWord 383 := by decide
private theorem pc_171_branch : pcWord 171 + signExtend13 52#13 = pcWord 184 := by decide
private theorem pc_183_jal : pcWord 183 + signExtend21 16#21 = pcWord 187 := by decide
private theorem pc_191_branch : pcWord 191 + signExtend13 8#13 = pcWord 193 := by decide
private theorem pc_195_branch : pcWord 195 + signExtend13 8072#13 = pcWord 165 := by decide

private theorem pc_199_branch : pcWord 199 + signExtend13 128#13 = pcWord 231 := by decide
private theorem pc_201_branch : pcWord 201 + signExtend13 728#13 = pcWord 383 := by decide
private theorem pc_203_branch : pcWord 203 + signExtend13 56#13 = pcWord 217 := by decide
private theorem pc_216_jal : pcWord 216 + signExtend21 20#21 = pcWord 221 := by decide
private theorem pc_225_branch : pcWord 225 + signExtend13 12#13 = pcWord 228 := by decide
private theorem pc_227_jal : pcWord 227 + signExtend21 16#21 = pcWord 231 := by decide
private theorem pc_233_branch : pcWord 233 + signExtend13 8048#13 = pcWord 197 := by decide

private theorem pc_237_branch : pcWord 237 + signExtend13 88#13 = pcWord 259 := by decide
private theorem pc_239_branch : pcWord 239 + signExtend13 48#13 = pcWord 251 := by decide
private theorem pc_250_jal : pcWord 250 + signExtend21 12#21 = pcWord 253 := by decide
private theorem pc_261_branch : pcWord 261 + signExtend13 8088#13 = pcWord 235 := by decide

/-! #### Phase 1D-0: L2..L4 256b Binary Loop (`pc[159..195]` -> `pc[196]`) -/

/-- One iteration (`step < 3`, level `l = 2 + step ∈ 2..4`) of the 256b binary loop (`pc[165..195]`). -/
theorem step_pos_bin256_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 3)
    (s : MachineState) (hpc : s.pc = pcWord 165)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord) +
        binPathOff (((posAt input.positions ord).val / 3) / 3) step) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((posAt input.positions ord).val / 3) / 3) >>> step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (2 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g1 := (i.val / 3) / 3
    let pCur := pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 225 1 (input.proof.length < pCur + binStepBytes g1 step + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 1 ∧
        s'.pc = (if step + 1 = 3 then pcWord 196 else pcWord 165) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + binStepBytes g1 step) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g1 pCur pw
  have hplen_bd : input.proof.length ≤ 8669633152 := hvalid
  have hle_cur : pCur + tailBytes tOff ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hg1_lt : g1 < 1864136 := by change (i.val / 3) / 3 < _; omega
  have hidx_lt : g1 >>> step < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g1 >>> step) / 2 = g1 >>> (step + 1) := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  -- pc[165]: XORI x28, x22, 1; pc[166]: LD x7, 8(x29); pc[167]: BGEU x28, x7, pc[193]
  have hst165 := step_ordinary oracle s 165 (.XORI .x28 .x22 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.XORI .x28 .x22 1#12)
  have hpc1 : s1.pc = pcWord 166 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 ((g1 >>> step) ^^^ 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, se12_1]
    exact bv64_xor_one _ hidx_lt
  have hreg1 : ∀ r, r ≠ .x28 → s1.getReg r = s.getReg r := fun r h28 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h28.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha166 : s1.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475968 + (32 * (2 + step) + 8)) := by
    rw [hreg1 .x29 (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv166 : memoryArgumentsValid s1 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha166]
    exact accessValid_ofNat (68719475968 + (32 * (2 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst166 := step_ordinary oracle s1 166 (.LD .x7 .x29 8#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv166])
  let s2 := execInstrBr s1 (.LD .x7 .x29 8#12)
  have hpc2 : s2.pc = pcWord 167 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hsz_val : s1.getMem (BitVec.ofNat 64 (68719475968 + (32 * (2 + step) + 8))) =
      BitVec.ofNat 64 (levelSize (2 + step)) := by
    have hm1 : s1.getMem (BitVec.ofNat 64 (68719475968 + (32 * (2 + step) + 8))) =
        s.getMem (BitVec.ofNat 64 (68719475968 + (32 * (2 + step) + 8))) := by
      simp [MachineState.getMem, hmem1]
    rw [hm1, hhigh.getMem_eq (by omega) (by omega) (by omega),
      check_initial_data_dword input hvalid (32 * (2 + step) + 8) (by omega)]
    exact openingData_dword_1 ⟨2 + step, by omega⟩
  have hx7_2 : s2.getReg .x7 = BitVec.ofNat 64 (levelSize (2 + step)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha166]
    rw [MachineState.getReg_setReg_eq (by decide), hsz_val]
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 ((g1 >>> step) ^^^ 1) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
  have hsib_lt64 : (g1 >>> step) ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' (g1 >>> step) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega
  have hsz_lt64 : levelSize (2 + step) < 2 ^ 64 := by
    interval_cases step <;> decide
  have hst167 := step_ordinary oracle s2 167 (.BGEU .x28 .x7 104#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BGEU .x28 .x7 104#13)
  have hult167 : BitVec.ult (s2.getReg .x28) (s2.getReg .x7) =
      decide (((g1 >>> step) ^^^ 1) < levelSize (2 + step)) := by
    rw [hx28_2, hx7_2, bv64_ult_eq _ _ hsib_lt64 hsz_lt64]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1
  have hreg2 : ∀ r, r ≠ .x7 → r ≠ .x28 → s2.getReg r = s.getReg r := fun r h7 h28 => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg1 r h28]
  have hpre3 : StepsTo oracle s s3 3 0 [] := by
    simpa using (hst165.trans hst166).trans hst167
  -- Common loop footer at pc[193..195]: SRLI x22, x22, 1; ADDI x29, x29, 32; BNE x29, x30, pc[165]
  have hfooter : ∀ (s193 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 219 → qMid ≤ 1 →
      StepsTo oracle s3 s193 kMid qMid trMid →
      s193.pc = pcWord 193 →
      CheckFixedRegs s193 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g1 step) tOff s193 →
      MemEqOutside s s193 256 320 →
      s193.getReg .x22 = BitVec.ofNat 64 (g1 >>> step) →
      s193.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) →
      s193.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) →
      s193.getReg .x27 = BitVec.ofNat 64 rem →
      s193.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + step)) →
      s193.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) →
      readBuffer s193 256 32 = pw.evalLevel c96 (2 + (step + 1)) →
      readBuffer s193 320 32 = 0 →
      (∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle trMid x) →
      PhaseOutcome oracle s 225 1 (input.proof.length < pCur + binStepBytes g1 step + tailBytes tOff)
        (fun s' q tr =>
          q ≤ 1 ∧
          s'.pc = (if step + 1 = 3 then pcWord 196 else pcWord 165) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g1 step) tOff s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (step + 1)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
    intro s193 kMid qMid trMid hkMid hqMid hmid hpc193 hfix193 hcur193 hout193 h22 h24 h8 h27 h29 h30 hdig193 hgap193 htr193
    have hst193 := step_ordinary oracle s193 193 (.SRLI .x22 .x22 1#6) (by decide) hpc193 rfl (by intro h; cases h) rfl
    let s194 := execInstrBr s193 (.SRLI .x22 .x22 1#6)
    have hpc194 : s194.pc = pcWord 194 := by simp only [s194, execInstrBr, MachineState.setPC, hpc193, pcWord_add_four]
    have hx22_194 : s194.getReg .x22 = BitVec.ofNat 64 (g1 >>> (step + 1)) := by
      simp only [s194, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h22, show (1#6 : BitVec 6).toNat = 1 by decide,
        bv64_shr _ 1 (by omega), Nat.pow_one, hshr_step]
    have hst194 := step_ordinary oracle s194 194 (.ADDI .x29 .x29 32#12) (by decide) hpc194 rfl (by intro h; cases h) rfl
    let s195 := execInstrBr s194 (.ADDI .x29 .x29 32#12)
    have hpc195 : s195.pc = pcWord 195 := by simp only [s195, execInstrBr, MachineState.setPC, hpc194, pcWord_add_four]
    have hx29_195 : s195.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) := by
      simp only [s195, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide)]
      simp only [s194, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x29), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_195 : s195.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) := by
      simp only [s195, s194, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x30), h30]
    obtain ⟨sFin, hst195, hpcFin_raw, hregFin195, hmemFin195⟩ :=
      step_bne_reg oracle 195 165 .x29 .x30 8072#13 (by decide) rfl pc_195_branch
        s195 (68719475968 + 32 * (2 + (step + 1))) (68719475968 + 32 * 5) (by omega) (by omega)
        hpc195 hx29_195 hx30_195
    have hmemFin : sFin.mem = s193.mem :=
      hmemFin195.trans (by simp [s195, s194, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x22 → r ≠ .x29 → sFin.getReg r = s193.getReg r := fun r h22r h29r => by
      rw [hregFin195 r]
      simp only [s195, s194, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h29r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h22r.symm]
    have hx22Fin : sFin.getReg .x22 = BitVec.ofNat 64 (g1 >>> (step + 1)) := by
      rw [hregFin195 .x22]
      simp only [s195, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x22), hx22_194]
    have hx29Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) :=
      (hregFin195 .x29).trans hx29_195
    have hpcFin : sFin.pc = if step + 1 = 3 then pcWord 196 else pcWord 165 := by
      rw [hpcFin_raw]
      by_cases hdone : step + 1 = 3
      · simp [hdone]
      · have hne : 68719475968 + 32 * (2 + (step + 1)) ≠ 68719475968 + 32 * 5 := by omega
        simp [hdone, hne]
    have htot := (hpre3.trans hmid).trans ((hst193.trans hst194).trans hst195)
    refine .continued sFin (3 + kMid + 3) qMid trMid (by omega) hqMid (by simpa [Nat.add_assoc] using htot)
      ⟨hqMid, hpcFin,
       hfix193.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       hcur193.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
       hout193.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       hx22Fin,
       (hregFin .x24 (by decide) (by decide)).trans h24,
       (hregFin .x8  (by decide) (by decide)).trans h8,
       (hregFin .x27 (by decide) (by decide)).trans h27,
       hx29Fin, (hregFin .x30 (by decide) (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig193,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap193,
       htr193⟩
  -- Branch on whether sibling exists at level `2 + step`
  by_cases hpair : ((g1 >>> step) ^^^ 1) < levelSize (2 + step)
  · -- Paired: binStepBytes g1 step = 32
    have hsb : binStepBytes g1 step = 32 := by
      unfold binStepBytes; simp [hpair, show 2 + step < 5 by omega]
    have hpc3 : s3.pc = pcWord 168 := by
      simp only [s3, execInstrBr, hult167, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hult167, hpair, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h28 => by
      simpa [s3, execInstrBr, hult167, hpair, MachineState.getReg_setPC] using hreg2 r h7 h28
    -- pc[168]: ADDI x6, x25, 32; pc[169]: BLTU x31, x6, pc[383]
    have hst168 := step_ordinary oracle s3 168 (.ADDI .x6 .x25 32#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x6 .x25 32#12)
    have hpc4 : s4.pc = pcWord 169 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hx6_4 : s4.getReg .x6 = BitVec.ofNat 64 (11162446080 + pCur + 32) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x25 (by decide) (by decide), hcur.x25, se12_32]
      change BitVec.ofNat 64 (11162446080 + pCur) + BitVec.ofNat 64 32 = _
      exact bv64_add _ 32
    have hx31_4 : s4.getReg .x31 = BitVec.ofNat 64 (11162446080 + (input.proof.length - tailBytes tOff)) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
        hreg3 .x31 (by decide) (by decide), hcur.x31]
    have hst169 := step_ordinary oracle s4 169 (.BLTU .x31 .x6 856#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.BLTU .x31 .x6 856#13)
    have hult169 : BitVec.ult (s4.getReg .x31) (s4.getReg .x6) =
        decide (input.proof.length < pCur + 32 + tailBytes tOff) := by
      rw [hx31_4, hx6_4, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases hshort : input.proof.length < pCur + 32 + tailBytes tOff
    · have hpc5 : s5.pc = pcWord 383 := by
        simp only [s5, execInstrBr, hult169, hshort, decide_true, ite_true, MachineState.setPC, hpc4]
        exact pc_169_branch
      have hrej := (hpre3.trans (hst168.trans hst169)).halt (halt_reject oracle s5 hpc5)
      exact .rejected 8 0 [] (by rw [hsb]; exact hshort) (by decide) (by decide) (by simpa using hrej)
    · have hge32 : pCur + 32 + tailBytes tOff ≤ input.proof.length := by omega
      have hpc5 : s5.pc = pcWord 170 := by
        simp only [s5, execInstrBr, hult169, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc4, pcWord_add_four]
      have hmem5 : s5.mem = s.mem := by
        have h54 : s5.mem = s4.mem := by
          simp only [s5, execInstrBr, hult169, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
        have h43 : s4.mem = s3.mem := by simp only [s4, execInstrBr, mem_setPC, mem_setReg]
        exact h54.trans (h43.trans hmem3)
      have hreg54 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
        simp only [s5, execInstrBr, hult169, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → s5.getReg r = s.getReg r := fun r h6 h7 h28 => by
        rw [hreg54]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg3 r h7 h28
      -- pc[170]: ANDI x7, x22, 1; pc[171]: BEQ x7, x0, pc[184]
      have hst170 := step_ordinary oracle s5 170 (.ANDI .x7 .x22 1#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ANDI .x7 .x22 1#12)
      have hpc6 : s6.pc = pcWord 171 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      have hx7_6 : s6.getReg .x7 = BitVec.ofNat 64 ((g1 >>> step) % 2) := by
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg5 .x22 (by decide) (by decide) (by decide), hx22, se12_1]
        exact bv64_and_one (g1 >>> step) (by omega)
      have hst171 := step_ordinary oracle s6 171 (.BEQ .x7 .x0 52#13) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.BEQ .x7 .x0 52#13)
      have hmem6 : s6.mem = s.mem := by simpa [s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
      let sibD := pw.binSib (2 + step)
      have hsibD_eq : sibD = readBuffer s0 (11162446080 + pCur) 32 := by
        simp only [sibD, pw, parsePartialWitness,
          show 2 ≤ 2 + step ∧ 2 + step ≤ 4 by omega, and_self, ite_true,
          show 2 + step - 2 = step by omega, pCur, Nat.add_assoc]
        dsimp only [g1]
      let curD := pw.evalLevel c96 (2 + step)
      let inpL : BitVec 768 :=
        if (g1 >>> step) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
      have hidx_pw : ((pw.index.val / 3) / 3) >>> (2 + step - 2) = g1 >>> step := by
        change g1 >>> (2 + step - 2) = g1 >>> step
        exact congrArg (fun k => g1 >>> k) (by omega)
      have heval_next : pw.evalLevel c96 (2 + (step + 1)) = maskLevel (2 + (step + 1)) (c96 inpL) := by
        rw [show 2 + (step + 1) = (2 + step) + 1 by omega,
          evalLevel_succ_of_ge2 c96 pw (2 + step) (by omega)]
        dsimp only
        rw [hidx_pw, if_pos hpair]
      have hlinp : pw.levelInput c96 (2 + step) = [inpL] := by
        unfold WitnessPath.levelInput
        dsimp only
        rw [hidx_pw, if_pos hpair]
      -- Common compression + conditional mask240 (step = 2 -> L5) at pc[187..192] -> pc[193]
      have hcall187 : ∀ (s187 : MachineState) (kA : Nat),
          kA ≤ 209 →
          StepsTo oracle s7 s187 kA 0 [] →
          s187.pc = pcWord 187 →
          CheckFixedRegs s187 →
          ProofCursor s0 input.proof.length (pCur + 32) tOff s187 →
          MemEqOutside s s187 256 320 →
          s187.getReg .x22 = BitVec.ofNat 64 (g1 >>> step) →
          s187.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) →
          s187.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) →
          s187.getReg .x27 = BitVec.ofNat 64 rem →
          s187.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + step)) →
          s187.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) →
          readBuffer s187 256 96 = inpL →
          readBuffer s187 320 32 = 0 →
          PhaseOutcome oracle s 225 1 (input.proof.length < pCur + binStepBytes g1 step + tailBytes tOff)
            (fun s' q tr =>
              q ≤ 1 ∧ s'.pc = (if step + 1 = 3 then pcWord 196 else pcWord 165) ∧
              CheckFixedRegs s' ∧
              ProofCursor s0 input.proof.length (pCur + binStepBytes g1 step) tOff s' ∧
              MemEqOutside s s' 256 320 ∧
              s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (step + 1)) ∧
              s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
              s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
              s'.getReg .x27 = BitVec.ofNat 64 rem ∧
              s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) ∧
              s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
              readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
              readBuffer s' 320 32 = 0 ∧
              ∀ x ∈ pw.levelInput c96 (2 + step), InTrace h768 oracle tr x) := by
        intro s187 kA hkA hmidA hpc187 hfix187 hcur187 hout187 h22 h24 h8 h27 h29 h30 hinp187 hgap187
        have hst187 := step_ordinary oracle s187 187 (.ADDI .x10 .x21 0#12) (by decide) hpc187 rfl (by intro h; cases h) rfl
        let s188 := execInstrBr s187 (.ADDI .x10 .x21 0#12)
        have hpc188 : s188.pc = pcWord 188 := by simp only [s188, execInstrBr, MachineState.setPC, hpc187, pcWord_add_four]
        have hst188 := step_ordinary oracle s188 188 (.ADDI .x12 .x21 0#12) (by decide) hpc188 rfl (by intro h; cases h) rfl
        let s189 := execInstrBr s188 (.ADDI .x12 .x21 0#12)
        have hpc189 : s189.pc = pcWord 189 := by simp only [s189, execInstrBr, MachineState.setPC, hpc188, pcWord_add_four]
        have hmem189 : s189.mem = s187.mem := by simp [s189, s188, execInstrBr, mem_setPC, mem_setReg]
        have hreg189 : ∀ r, r ≠ .x10 → r ≠ .x12 → s189.getReg r = s187.getReg r := fun r h10 h12 => by
          simp only [s189, s188, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
        have hx10_189 : s189.getReg .x10 = 256#64 := by
          simp only [s189, s188, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide), hfix187.x21, se12_0, BitVec.add_zero]
        have hx12_189 : s189.getReg .x12 = 256#64 := by
          simp only [s189, s188, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
            hfix187.x21, se12_0, BitVec.add_zero]
        have hec := step_ecall_compress h768 oracle s189 189 256 256 (by decide) hpc189 rfl
          ((hreg189 .x5 (by decide) (by decide)).trans hfix187.x5)
          ((hreg189 .x11 (by decide) (by decide)).trans hfix187.x11)
          ((hreg189 .x13 (by decide) (by decide)).trans hfix187.x13)
          hx10_189 hx12_189 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
        rw [(MemEqOutside.of_mem_eq hmem189 0 0).readBuffer_eq (by decide) (by omega), hinp187] at hec
        let s190 := writeBits s189 (BitVec.ofNat 64 256) (c96 inpL)
        have hpc190 : s190.pc = pcWord 190 := by simp only [s190, writeBits, MachineState.setPC, hpc189, pcWord_add_four]
        have hreg190 : ∀ r, r ≠ .x10 → r ≠ .x12 → s190.getReg r = s187.getReg r := fun r h10 h12 =>
          (writeBits_register s189 _ _ r).trans (hreg189 r h10 h12)
        -- pc[190]: ADDI x6, x2, 128; pc[191]: BNE x29, x6, pc[193]
        have hst190 := step_ordinary oracle s190 190 (.ADDI .x6 .x2 128#12) (by decide) hpc190 rfl (by intro h; cases h) rfl
        let s191 := execInstrBr s190 (.ADDI .x6 .x2 128#12)
        have hpc191 : s191.pc = pcWord 191 := by simp only [s191, execInstrBr, MachineState.setPC, hpc190, pcWord_add_four]
        have hx6_191 : s191.getReg .x6 = BitVec.ofNat 64 (68719475968 + 128) := by
          simp only [s191, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hreg190 .x2 (by decide) (by decide), hfix187.x2, se12_128, bv64_add]
        have hx29_191 : s191.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + step)) := by
          simp only [s191, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hreg190 .x29 (by decide) (by decide), h29]
        have hst191 := step_ordinary oracle s191 191 (.BNE .x29 .x6 8#13) (by decide) hpc191 rfl (by intro h; cases h) rfl
        let s192 := execInstrBr s191 (.BNE .x29 .x6 8#13)
        have hne2 : (s191.getReg .x29 != s191.getReg .x6) = decide (step ≠ 2) := by
          rw [hx29_191, hx6_191, bv64_bne_eq _ _ (by omega) (by omega)]
          exact decide_eq_decide.mpr (by omega)
        have hmem192 : s192.mem = s190.mem := by
          simp only [s192, execInstrBr]; split <;> simp [s191, execInstrBr, mem_setPC, mem_setReg]
        have hreg192 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s192.getReg r = s187.getReg r := fun r h6 h10 h12 => by
          have : s192.getReg r = s191.getReg r := by simp only [s192, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
          rw [this]; simp only [s191, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
          exact hreg190 r h10 h12
        have hpre192 := (((hst168.trans hst169).trans (hst170.trans hst171)).trans hmidA).trans
          (((hst187.trans hst188).trans hec).trans (hst190.trans hst191))
        by_cases hs2 : step = 2
        · -- step = 2 (l = 4 -> L5): fall through to pc[192]: SH x21, x0, 30 (mask240) -> pc[193]
          have hpc192 : s192.pc = pcWord 192 := by
            simp only [s192, execInstrBr, hne2, hs2, ne_eq, not_true_eq_false, decide_false,
              Bool.false_eq_true, ite_false, MachineState.setPC, hpc191, pcWord_add_four]
          have ha192 : s192.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
            rw [hreg192 .x21 (by decide) (by decide) (by decide), hfix187.x21]; decide
          have hv192 : memoryArgumentsValid s192 (.SH .x21 .x0 30#12) = true := by
            simp only [memoryArgumentsValid, memAccess, ha192]
            exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; omega) (by decide)
          have hst192 := step_ordinary oracle s192 192 (.SH .x21 .x0 30#12) (by decide) hpc192 rfl (by intro h; cases h)
            (by simp [ordinaryStep, hv192])
          let s193 := execInstrBr s192 (.SH .x21 .x0 30#12)
          have hpc193 : s193.pc = pcWord 193 := by simp only [s193, execInstrBr, MachineState.setPC, hpc192, pcWord_add_four]
          have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s193.getReg r = s187.getReg r := fun r h6 h10 h12 => by
            have : s193.getReg r = s192.getReg r := by
              simp [s193, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
            exact this.trans (hreg192 r h6 h10 h12)
          have hout_sh : MemEqOutside s192 s193 286 288 := by
            intro a ha hout
            simp only [s193, execInstrBr, ha192, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
            exact MemEqOutside_setHalfword s192 286 _ (by decide) (by decide) a ha hout
          have hout_all : MemEqOutside s s193 256 320 :=
            hout187.trans ((MemEqOutside.of_mem_eq hmem189 256 320).trans
              (((MemEqOutside_writeBits_digest s189 256 _ (by decide)).mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem192 256 320).trans (hout_sh.mono (by omega) (by omega)))))
          have hdig_eq : readBuffer s193 256 32 = pw.evalLevel c96 (2 + (step + 1)) := by
            rw [heval_next]
            have hsh : readBuffer s193 256 32 =
                readBuffer (s190.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s193, execInstrBr, ha192, MachineState.getByte, MachineState.setHalfword,
                MachineState.getMem, MachineState.setMem, mem_setPC, hmem192, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh, sh_zero_mask240 s190 256 (by decide) (by decide), writeBits_readBuffer_digest]
            unfold maskLevel
            rw [if_neg (by omega), if_pos (by omega)]
          have hgap193 : readBuffer s193 320 32 = 0 := by
            rw [hout_sh.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem192 0 0).readBuffer_eq (by decide) (by omega),
              (MemEqOutside_writeBits_digest s189 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem189 0 0).readBuffer_eq (by decide) (by omega), hgap187]
          refine hfooter s193 (4 + kA + 5 + 1) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
            ((hpre192.trans hst192).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
            hpc193
            (hfix187.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
            (by rw [hsb]; exact hcur187.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
            hout_all
            ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
            ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
            ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
            ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
            ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
            ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
            hdig_eq hgap193 ?_
          intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
          exact InTrace.singleton h768 oracle inpL
        · -- step < 2 (l ∈ 2..3 -> L3..L4): BNE taken to pc[193], unmasked 256b
          have hpc193 : s192.pc = pcWord 193 := by
            simp only [s192, execInstrBr, hne2, hs2, ne_eq, not_false_eq_true, decide_true,
              ite_true, MachineState.setPC, hpc191]; exact pc_191_branch
          have hout_all : MemEqOutside s s192 256 320 :=
            hout187.trans ((MemEqOutside.of_mem_eq hmem189 256 320).trans
              (((MemEqOutside_writeBits_digest s189 256 _ (by decide)).mono (by omega) (by omega)).trans
                (MemEqOutside.of_mem_eq hmem192 256 320)))
          have hdig_eq : readBuffer s192 256 32 = pw.evalLevel c96 (2 + (step + 1)) := by
            rw [heval_next, (MemEqOutside.of_mem_eq hmem192 0 0).readBuffer_eq (by decide) (by omega),
              writeBits_readBuffer_digest]
            unfold maskLevel
            rw [if_pos (by omega)]
          have hgap193 : readBuffer s192 320 32 = 0 := by
            rw [(MemEqOutside.of_mem_eq hmem192 0 0).readBuffer_eq (by decide) (by omega),
              (MemEqOutside_writeBits_digest s189 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem189 0 0).readBuffer_eq (by decide) (by omega), hgap187]
          refine hfooter s192 (4 + kA + 5) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
            (hpre192.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
            hpc193
            (hfix187.of_agree (fun r hr => hreg192 r (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
            (by rw [hsb]; exact hcur187.of_agree (fun r hr => hreg192 r (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
            hout_all
            ((hreg192 .x22 (by decide) (by decide) (by decide)).trans h22)
            ((hreg192 .x24 (by decide) (by decide) (by decide)).trans h24)
            ((hreg192 .x8  (by decide) (by decide) (by decide)).trans h8)
            ((hreg192 .x27 (by decide) (by decide) (by decide)).trans h27)
            ((hreg192 .x29 (by decide) (by decide) (by decide)).trans h29)
            ((hreg192 .x30 (by decide) (by decide) (by decide)).trans h30)
            hdig_eq hgap193 ?_
          intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
          exact InTrace.singleton h768 oracle inpL
      by_cases heven : (g1 >>> step) % 2 = 0
      · -- Even: jump to pc[184..186] -> pc[187]
        have hx7z : s6.getReg .x7 = 0#64 := by rw [hx7_6, heven]
        have hpc7 : s7.pc = pcWord 184 := by
          simp only [s7, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
            MachineState.setPC, hpc6]; exact pc_171_branch
        have hmem7 : s7.mem = s.mem := by
          simpa [s7, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem6
        have hreg76 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
          simp only [s7, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → s7.getReg r = s.getReg r := fun r h6 h7 h28 => by
          rw [hreg76]
          simp only [s6, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
          exact hreg5 r h6 h7 h28
        have hst184 := step_ordinary oracle s7 184 (.ADDI .x12 .x21 32#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
        let s8 := execInstrBr s7 (.ADDI .x12 .x21 32#12)
        have hpc8 : s8.pc = pcWord 185 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
        obtain ⟨s9, hs9, hpc9, hx25_9, hreg9, hcopy9, hout9⟩ :=
          step_call_read_n oracle 185 32 s8 (11162446080 + pCur) 288 (by decide) (by decide) (by decide)
            rfl rfl hpc8
            (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                  hreg7 .x25 (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide),
                  hreg7 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
        have hmem8 : s8.mem = s.mem := by simpa [s8, execInstrBr, mem_setPC, mem_setReg] using hmem7
        have hout_all : MemEqOutside s s9 288 320 :=
          (MemEqOutside.of_mem_eq hmem8 288 320).trans (hout9.mono (by omega) (by omega))
        have hreg9_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x28 →
            s9.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 h28 => by
          rw [hreg9 r h1 h6 h10 h12 h25]
          simp only [s8, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
          exact hreg7 r h6 h7 h28
        have hcur9 : ProofCursor s0 input.proof.length (pCur + 32) tOff s9 := by
          refine ⟨hge32, ?_, ?_, ?_, ?_⟩
          · rw [hx25_9]; congr 1
          · rw [hreg9_s .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg9_s .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg9_s .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
        have hgap9 : readBuffer s9 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp9 : readBuffer s9 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s9 256 hgap9]
          have hL : readBuffer s9 256 32 = curD :=
            (hout_all.readBuffer_eq (by decide) (by omega)).trans hcurDig
          have hR : readBuffer s9 288 32 = sibD := by
            rw [hsibD_eq]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy9 j hj
            simp only [MachineState.getByte, MachineState.getMem, hmem8] at hc ⊢
            exact hc.trans (hhigh (11162446080 + pCur + j) (by omega) (by omega))
          rw [hL, hR]; simp only [inpL, heven, ite_true]
        refine hcall187 s9 196 (by decide) (by simpa using hst184.trans hs9) hpc9
          (hfix.of_agree (fun r hr => hreg9_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur9 (hout_all.mono (by omega) (by omega))
          ((hreg9_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
          ((hreg9_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg9_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg9_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg9_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg9_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp9 hgap9
      · -- Odd: fall through to pc[172..183] -> pc[187]
        have hodd : (g1 >>> step) % 2 = 1 := by omega
        have hx7o : s6.getReg .x7 = 1#64 := by rw [hx7_6, hodd]
        have hpc7 : s7.pc = pcWord 172 := by
          simp only [s7, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc6, pcWord_add_four]
        have hmem7 : s7.mem = s.mem := by
          simpa [s7, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            MachineState.setPC] using hmem6
        have hreg76 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
          simp only [s7, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → s7.getReg r = s.getReg r := fun r h6 h7 h28 => by
          rw [hreg76]
          simp only [s6, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
          exact hreg5 r h6 h7 h28
        have hcp : ∀ j < 4,
            checkInstr (172 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (172 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s8, hs8, hpc8, hreg8, hcopy8, hout8⟩ :=
          step_copy_dwords oracle 172 4 .x21 .x21 0 32 s7 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp hpc7
            ((hreg7 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
            ((hreg7 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
            (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by decide)
        have hst180 := step_ordinary oracle s8 180 (.ADDI .x12 .x21 0#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 0#12)
        have hpc9 : s9.pc = pcWord 181 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hx25_10, hreg10, hcopy10, hout10⟩ :=
          step_call_read_n oracle 181 32 s9 (11162446080 + pCur) 256 (by decide) (by decide) (by decide)
            rfl rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg8 .x25 (by decide),
                  hreg7 .x25 (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg8 .x21 (by decide),
                  hreg7 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
        have hst183 := step_ordinary oracle s10 183 (.JAL .x0 16#21) (by decide) hpc10 rfl (by intro h; cases h) rfl
        let s11 := execInstrBr s10 (.JAL .x0 16#21)
        have hpc11 : s11.pc = pcWord 187 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10]; exact pc_183_jal
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hmem11 : s11.mem = s10.mem := by simp [s11, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s s11 256 320 :=
          (MemEqOutside.of_mem_eq hmem7 256 320).trans
            ((hout8.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem9 256 320).trans
                ((hout10.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem11 256 320))))
        have hreg11_10 : ∀ r, s11.getReg r = s10.getReg r := fun r => by
          simp [s11, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have hreg11 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x28 →
            s11.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 h28 => by
          rw [hreg11_10, hreg10 r h1 h6 h10 h12 h25]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg8 r h6]
          exact hreg7 r h6 h7 h28
        have hcur11 : ProofCursor s0 input.proof.length (pCur + 32) tOff s11 := by
          refine ⟨hge32, ?_, ?_, ?_, ?_⟩
          · rw [hreg11_10, hx25_10]; congr 1
          · rw [hreg11 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg11 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg11 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
        have hgap11 : readBuffer s11 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp11 : readBuffer s11 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s11 256 hgap11]
          have hL : readBuffer s11 256 32 = sibD := by
            rw [hsibD_eq, (MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega)]
            apply readBuffer_congr2; intro j hj
            have h9s : MemEqOutside s s9 288 320 :=
              (MemEqOutside.of_mem_eq hmem7 288 320).trans (hout8.trans (MemEqOutside.of_mem_eq hmem9 288 320))
            exact (hcopy10 j hj).trans
              ((h9s (11162446080 + pCur + j) (by omega) (by omega)).trans
                (hhigh (11162446080 + pCur + j) (by omega) (by omega)))
          have hcur' : readBuffer s 256 32 = curD := hcurDig
          have hR : readBuffer s11 288 32 = curD := by
            rw [(MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega),
              hout10.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hcur']
            apply readBuffer_congr2; intro j hj
            have hc := hcopy8 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem7] at hc ⊢
            exact hc
          rw [hL, hR]; simp only [inpL, heven, ite_false]
        refine hcall187 s11 205 (by decide)
          (by simpa using ((hs8.trans hst180).trans hs10).trans hst183) hpc11
          (hfix.of_agree (fun r hr => hreg11 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur11 hout_all
          ((hreg11 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
          ((hreg11 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg11 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg11 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg11 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg11 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp11 hgap11
  · -- Promoted (unpaired): binStepBytes g1 step = 0, jump directly to pc[193]
    have hsb : binStepBytes g1 step = 0 := by unfold binStepBytes; simp [hpair]
    have hpc3 : s3.pc = pcWord 193 := by
      simp only [s3, execInstrBr, hult167, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc2]; exact pc_167_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hult167, hpair, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h28 => by
      simpa [s3, execInstrBr, hult167, hpair, MachineState.getReg_setPC] using hreg2 r h7 h28
    have hidx_pw : ((pw.index.val / 3) / 3) >>> (2 + step - 2) = g1 >>> step := by
      change g1 >>> (2 + step - 2) = g1 >>> step
      exact congrArg (fun k => g1 >>> k) (by omega)
    have heval_same : pw.evalLevel c96 (2 + (step + 1)) = pw.evalLevel c96 (2 + step) := by
      rw [show 2 + (step + 1) = (2 + step) + 1 by omega,
        evalLevel_succ_of_ge2 c96 pw (2 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_neg hpair]
    have hlinp_nil : pw.levelInput c96 (2 + step) = [] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_neg hpair]
    refine hfooter s3 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s3) hpc3
      (hfix.of_agree (fun r hr => hreg3 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (by rw [hsb, Nat.add_zero]
          exact hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (MemEqOutside.of_mem_eq hmem3 256 320)
      ((hreg3 .x22 (by decide) (by decide)).trans hx22)
      ((hreg3 .x24 (by decide) (by decide)).trans hx24)
      ((hreg3 .x8  (by decide) (by decide)).trans hx8)
      ((hreg3 .x27 (by decide) (by decide)).trans hx27)
      ((hreg3 .x29 (by decide) (by decide)).trans hx29)
      ((hreg3 .x30 (by decide) (by decide)).trans hx30)
      (by rw [heval_same]; exact ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hcurDig)
      (((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
      (by rw [hlinp_nil]; simp)

/-- Phase 1D-0: zero gap `S[64..96)` + L2..L4 256b binary loop (`pc[159..195]` -> `pc[196]`), `≤ 685` steps, `≤ 3` calls. -/
theorem step_pos_bin256_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 159)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord)) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl2 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 2) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g1 := (i.val / 3) / 3
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 685 3
      (input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 3 + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 3 ∧
        s'.pc = pcWord 196 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 3) tOff s' ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> 3) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 5 ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ prev, 2 ≤ prev → prev < 5 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g1 pw
  -- pc[159..162]: zero gap S[64..96)
  obtain ⟨s0', hs0', hpc0', hreg0', hgap0', hout0'⟩ := step_zero_gap oracle s hpc hfix.x21
  -- pc[163]: ADDI x29, x2, 64; pc[164]: ADDI x30, x2, 160
  have hst163 := step_ordinary oracle s0' 163 (.ADDI .x29 .x2 64#12) (by decide) hpc0' rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s0' (.ADDI .x29 .x2 64#12)
  have hpc1 : s1.pc = pcWord 164 := by simp only [s1, execInstrBr, MachineState.setPC, hpc0', pcWord_add_four]
  have hst164 := step_ordinary oracle s1 164 (.ADDI .x30 .x2 160#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x30 .x2 160#12)
  have hpc2 : s2.pc = pcWord 165 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s0'.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x29 → r ≠ .x30 → s2.getReg r = s.getReg r := fun r h29 h30 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h30.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h29.symm, hreg0' r]
  have hx29_2 : s2.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 2) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x29), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hreg0' .x2, hfix.x2, se12_64]
    change BitVec.ofNat 64 68719475968 + BitVec.ofNat 64 64 = _
    rw [bv64_add]
  have hx30_2 : s2.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x2),
      hreg0' .x2, hfix.x2, se12_160, bv64_add]
  have hhigh2 : HighMemPreserved s0 s2 :=
    hhigh.trans ((hout0'.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem2 0 4294971392))
  have hl2_2 : readBuffer s2 256 32 = pw.evalLevel c96 2 :=
    ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans
      ((hout0'.readBuffer_eq (by decide) (by omega)).trans hl2)
  have hgap2 : readBuffer s2 320 32 = 0 :=
    ((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hgap0'
  have hloop : ∀ m ≤ 3,
      PhaseOutcome oracle s2 (225 * m) m
        (input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 m + tailBytes tOff)
        (fun s' q tr =>
          q ≤ m ∧
          s'.pc = (if m = 3 then pcWord 196 else pcWord 165) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 m) tOff s' ∧
          MemEqOutside s2 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> m) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + m)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
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
         hx29_2, hx30_2, hl2_2, hgap2, fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have hbin_mon : binPathOff g1 k ≤ binPathOff g1 (k + 1) := by simp only [binPathOff]; omega
      rw [show 225 * (k + 1) = 225 * k + 225 by omega]
      refine (ih (by omega)).bind_dep
        (fun hlt => by simp only [binPathOff]; omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne3 : k ≠ 3 := by omega
          simp only [hne3, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh2.trans (hout_k.mono (by omega) (by omega))
          have hstep_k := step_pos_bin256_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega)
            (fun hlt => by
              change input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 k + binStepBytes g1 k + tailBytes tOff at hlt
              simp only [binPathOff]; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', by simpa [binPathOff, Nat.add_assoc] using hcur',
            hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          intro prev hp1 hp2 x hx
          by_cases hprev : prev < 2 + k
          · exact (htr_k prev hp1 hprev x hx).append_left
          · have : prev = 2 + k := by omega
            subst this; exact (htr' x hx).append_right)
  have h3 := hloop 3 (by decide)
  have hpre : StepsTo oracle s s2 6 0 [] := by simpa using hs0'.trans (hst163.trans hst164)
  cases h3 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (6 + k) q tr hr (by omega) hq (by simpa using hpre.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', _, hdig', hgap', htr'⟩ := hp
    refine .continued s' (6 + k) q tr (by omega) hq (by simpa using hpre.trans hs)
      ⟨hq', by simpa using hpc', hfix', hcur',
       (hout0'.mono (by omega) (by omega)).trans ((MemEqOutside.of_mem_eq hmem2 256 352).trans (hout'.mono (by omega) (by omega))),
       hx22', hx24', hx8', hx27', hx29', hdig', hgap',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-! #### Phase 1D-1: L5..L8 240b Binary Loop (`pc[196..233]` -> `pc[234]`) -/

/-- One iteration (`step < 4`, level `l = 5 + step ∈ 5..8`) of the 240b binary loop (`pc[197..233]`). -/
theorem step_pos_bin240_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 4)
    (s : MachineState) (hpc : s.pc = pcWord 197)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord) +
        binPathOff (((posAt input.positions ord).val / 3) / 3) (3 + step)) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((posAt input.positions ord).val / 3) / 3) >>> (3 + step)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (5 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g1 := (i.val / 3) / 3
    let pCur := pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (3 + step)
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 215 1 (input.proof.length < pCur + binStepBytes g1 (3 + step) + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 1 ∧
        s'.pc = (if step + 1 = 4 then pcWord 234 else pcWord 197) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (3 + step)) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (5 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 (5 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g1 pCur pw
  have hplen_bd : input.proof.length ≤ 8669633152 := hvalid
  have hle_cur : pCur + tailBytes tOff ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hg1_lt : g1 < 1864136 := by change (i.val / 3) / 3 < _; omega
  have hidx_lt : g1 >>> (3 + step) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g1 >>> (3 + step)) / 2 = g1 >>> (3 + (step + 1)) := by
    simp only [Nat.shiftRight_eq_div_pow, show 3 + (step + 1) = (3 + step) + 1 by omega,
      Nat.pow_succ, Nat.div_div_eq_div_mul]
  -- pc[197]: XORI x28, x22, 1; pc[198]: LD x7, 8(x29); pc[199]: BGEU x28, x7, pc[231]
  have hst197 := step_ordinary oracle s 197 (.XORI .x28 .x22 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.XORI .x28 .x22 1#12)
  have hpc1 : s1.pc = pcWord 198 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 ((g1 >>> (3 + step)) ^^^ 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, se12_1]
    exact bv64_xor_one _ hidx_lt
  have hreg1 : ∀ r, r ≠ .x28 → s1.getReg r = s.getReg r := fun r h28 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h28.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha198 : s1.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475968 + (32 * (5 + step) + 8)) := by
    rw [hreg1 .x29 (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv198 : memoryArgumentsValid s1 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha198]
    exact accessValid_ofNat (68719475968 + (32 * (5 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst198 := step_ordinary oracle s1 198 (.LD .x7 .x29 8#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv198])
  let s2 := execInstrBr s1 (.LD .x7 .x29 8#12)
  have hpc2 : s2.pc = pcWord 199 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hsz_val : s1.getMem (BitVec.ofNat 64 (68719475968 + (32 * (5 + step) + 8))) =
      BitVec.ofNat 64 (levelSize (5 + step)) := by
    have hm1 : s1.getMem (BitVec.ofNat 64 (68719475968 + (32 * (5 + step) + 8))) =
        s.getMem (BitVec.ofNat 64 (68719475968 + (32 * (5 + step) + 8))) := by
      simp [MachineState.getMem, hmem1]
    rw [hm1, hhigh.getMem_eq (by omega) (by omega) (by omega),
      check_initial_data_dword input hvalid (32 * (5 + step) + 8) (by omega)]
    exact openingData_dword_1 ⟨5 + step, by omega⟩
  have hx7_2 : s2.getReg .x7 = BitVec.ofNat 64 (levelSize (5 + step)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha198]
    rw [MachineState.getReg_setReg_eq (by decide), hsz_val]
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 ((g1 >>> (3 + step)) ^^^ 1) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
  have hsib_lt64 : (g1 >>> (3 + step)) ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' (g1 >>> (3 + step)) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega
  have hsz_lt64 : levelSize (5 + step) < 2 ^ 64 := by
    interval_cases step <;> decide
  have hst199 := step_ordinary oracle s2 199 (.BGEU .x28 .x7 128#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BGEU .x28 .x7 128#13)
  have hult199 : BitVec.ult (s2.getReg .x28) (s2.getReg .x7) =
      decide (((g1 >>> (3 + step)) ^^^ 1) < levelSize (5 + step)) := by
    rw [hx28_2, hx7_2, bv64_ult_eq _ _ hsib_lt64 hsz_lt64]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1
  have hreg2 : ∀ r, r ≠ .x7 → r ≠ .x28 → s2.getReg r = s.getReg r := fun r h7 h28 => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg1 r h28]
  have hpre3 : StepsTo oracle s s3 3 0 [] := by
    simpa using (hst197.trans hst198).trans hst199
  -- Common loop footer at pc[231..233]: SRLI x22, x22, 1; ADDI x29, x29, 32; BNE x29, x30, pc[197]
  have hfooter : ∀ (s231 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 209 → qMid ≤ 1 →
      StepsTo oracle s3 s231 kMid qMid trMid →
      s231.pc = pcWord 231 →
      CheckFixedRegs s231 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (3 + step)) tOff s231 →
      MemEqOutside s s231 256 320 →
      s231.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + step)) →
      s231.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) →
      s231.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) →
      s231.getReg .x27 = BitVec.ofNat 64 rem →
      s231.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + step)) →
      s231.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) →
      readBuffer s231 256 32 = pw.evalLevel c96 (5 + (step + 1)) →
      readBuffer s231 320 32 = 0 →
      (∀ x ∈ pw.levelInput c96 (5 + step), InTrace h768 oracle trMid x) →
      PhaseOutcome oracle s 215 1 (input.proof.length < pCur + binStepBytes g1 (3 + step) + tailBytes tOff)
        (fun s' q tr =>
          q ≤ 1 ∧
          s'.pc = (if step + 1 = 4 then pcWord 234 else pcWord 197) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (3 + step)) tOff s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (5 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInput c96 (5 + step), InTrace h768 oracle tr x) := by
    intro s231 kMid qMid trMid hkMid hqMid hmid hpc231 hfix231 hcur231 hout231 h22 h24 h8 h27 h29 h30 hdig231 hgap231 htr231
    have hst231 := step_ordinary oracle s231 231 (.SRLI .x22 .x22 1#6) (by decide) hpc231 rfl (by intro h; cases h) rfl
    let s232 := execInstrBr s231 (.SRLI .x22 .x22 1#6)
    have hpc232 : s232.pc = pcWord 232 := by simp only [s232, execInstrBr, MachineState.setPC, hpc231, pcWord_add_four]
    have hx22_232 : s232.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) := by
      simp only [s232, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h22, show (1#6 : BitVec 6).toNat = 1 by decide,
        bv64_shr _ 1 (by omega), Nat.pow_one, hshr_step]
    have hst232 := step_ordinary oracle s232 232 (.ADDI .x29 .x29 32#12) (by decide) hpc232 rfl (by intro h; cases h) rfl
    let s233 := execInstrBr s232 (.ADDI .x29 .x29 32#12)
    have hpc233 : s233.pc = pcWord 233 := by simp only [s233, execInstrBr, MachineState.setPC, hpc232, pcWord_add_four]
    have hx29_233 : s233.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) := by
      simp only [s233, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide)]
      simp only [s232, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x29), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_233 : s233.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) := by
      simp only [s233, s232, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x30), h30]
    obtain ⟨sFin, hst233, hpcFin_raw, hregFin233, hmemFin233⟩ :=
      step_bne_reg oracle 233 197 .x29 .x30 8048#13 (by decide) rfl pc_233_branch
        s233 (68719475968 + 32 * (5 + (step + 1))) (68719475968 + 32 * 9) (by omega) (by omega)
        hpc233 hx29_233 hx30_233
    have hmemFin : sFin.mem = s231.mem :=
      hmemFin233.trans (by simp [s233, s232, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x22 → r ≠ .x29 → sFin.getReg r = s231.getReg r := fun r h22r h29r => by
      rw [hregFin233 r]
      simp only [s233, s232, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h29r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h22r.symm]
    have hx22Fin : sFin.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) := by
      rw [hregFin233 .x22]
      simp only [s233, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x22), hx22_232]
    have hx29Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) :=
      (hregFin233 .x29).trans hx29_233
    have hpcFin : sFin.pc = if step + 1 = 4 then pcWord 234 else pcWord 197 := by
      rw [hpcFin_raw]
      by_cases hdone : step + 1 = 4
      · simp [hdone]
      · have hne : 68719475968 + 32 * (5 + (step + 1)) ≠ 68719475968 + 32 * 9 := by omega
        simp [hdone, hne]
    have htot := (hpre3.trans hmid).trans ((hst231.trans hst232).trans hst233)
    refine .continued sFin (3 + kMid + 3) qMid trMid (by omega) hqMid (by simpa [Nat.add_assoc] using htot)
      ⟨hqMid, hpcFin,
       hfix231.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       hcur231.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
       hout231.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       hx22Fin,
       (hregFin .x24 (by decide) (by decide)).trans h24,
       (hregFin .x8  (by decide) (by decide)).trans h8,
       (hregFin .x27 (by decide) (by decide)).trans h27,
       hx29Fin, (hregFin .x30 (by decide) (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig231,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap231,
       htr231⟩
  -- Branch on whether sibling exists at level `5 + step`
  by_cases hpair : ((g1 >>> (3 + step)) ^^^ 1) < levelSize (5 + step)
  · -- Paired: binStepBytes g1 (3 + step) = 30
    have hsb : binStepBytes g1 (3 + step) = 30 := by
      unfold binStepBytes
      rw [show 2 + (3 + step) = 5 + step by omega]
      simp [hpair, show ¬ (5 + step < 5) by omega, show 5 + step < 9 by omega]
    have hpc3 : s3.pc = pcWord 200 := by
      simp only [s3, execInstrBr, hult199, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hult199, hpair, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h28 => by
      simpa [s3, execInstrBr, hult199, hpair, MachineState.getReg_setPC] using hreg2 r h7 h28
    -- pc[200]: ADDI x6, x25, 30; pc[201]: BLTU x31, x6, pc[383]
    have hst200 := step_ordinary oracle s3 200 (.ADDI .x6 .x25 30#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x6 .x25 30#12)
    have hpc4 : s4.pc = pcWord 201 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hx6_4 : s4.getReg .x6 = BitVec.ofNat 64 (11162446080 + pCur + 30) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x25 (by decide) (by decide),
        hcur.x25, se12_30_ofNat]
      change BitVec.ofNat 64 (11162446080 + pCur) + BitVec.ofNat 64 30 = _
      exact bv64_add _ 30
    have hx31_4 : s4.getReg .x31 = BitVec.ofNat 64 (11162446080 + (input.proof.length - tailBytes tOff)) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
        hreg3 .x31 (by decide) (by decide), hcur.x31]
    have hst201 := step_ordinary oracle s4 201 (.BLTU .x31 .x6 728#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.BLTU .x31 .x6 728#13)
    have hult201 : BitVec.ult (s4.getReg .x31) (s4.getReg .x6) =
        decide (input.proof.length < pCur + 30 + tailBytes tOff) := by
      rw [hx31_4, hx6_4, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases hshort : input.proof.length < pCur + 30 + tailBytes tOff
    · have hpc5 : s5.pc = pcWord 383 := by
        simp only [s5, execInstrBr, hult201, hshort, decide_true, ite_true, MachineState.setPC, hpc4]
        exact pc_201_branch
      have hrej := (hpre3.trans (hst200.trans hst201)).halt (halt_reject oracle s5 hpc5)
      exact .rejected 8 0 [] (by rw [hsb]; exact hshort) (by decide) (by decide) (by simpa using hrej)
    · have hge30 : pCur + 30 + tailBytes tOff ≤ input.proof.length := by omega
      have hpc5 : s5.pc = pcWord 202 := by
        simp only [s5, execInstrBr, hult201, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc4, pcWord_add_four]
      have hmem5 : s5.mem = s.mem := by
        have h54 : s5.mem = s4.mem := by
          simp only [s5, execInstrBr, hult201, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
        have h43 : s4.mem = s3.mem := by simp only [s4, execInstrBr, mem_setPC, mem_setReg]
        exact h54.trans (h43.trans hmem3)
      have hreg54 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
        simp only [s5, execInstrBr, hult201, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → s5.getReg r = s.getReg r := fun r h6 h7 h28 => by
        rw [hreg54]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg3 r h7 h28
      -- pc[202]: ANDI x7, x22, 1; pc[203]: BEQ x7, x0, pc[217]
      have hst202 := step_ordinary oracle s5 202 (.ANDI .x7 .x22 1#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ANDI .x7 .x22 1#12)
      have hpc6 : s6.pc = pcWord 203 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      have hx7_6 : s6.getReg .x7 = BitVec.ofNat 64 ((g1 >>> (3 + step)) % 2) := by
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg5 .x22 (by decide) (by decide) (by decide), hx22, se12_1]
        exact bv64_and_one (g1 >>> (3 + step)) (by omega)
      have hst203 := step_ordinary oracle s6 203 (.BEQ .x7 .x0 56#13) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.BEQ .x7 .x0 56#13)
      have hmem6 : s6.mem = s.mem := by simpa [s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
      let sibD := pw.binSib (5 + step)
      have hsibD_eq : sibD = proofDigest30 s0 (11162446080 + pCur) := by
        simp only [sibD, pw, parsePartialWitness,
          show ¬ (2 ≤ 5 + step ∧ 5 + step ≤ 4) by omega, ite_false,
          show 5 ≤ 5 + step ∧ 5 + step ≤ 8 by omega, and_self, ite_true,
          show 5 + step - 2 = 3 + step by omega, pCur, Nat.add_assoc]
        dsimp only [g1]
      let curD := pw.evalLevel c96 (5 + step)
      let inpL : BitVec 768 :=
        if (g1 >>> (3 + step)) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
      have hidx_pw : ((pw.index.val / 3) / 3) >>> (5 + step - 2) = g1 >>> (3 + step) := by
        change g1 >>> (5 + step - 2) = g1 >>> (3 + step)
        exact congrArg (fun k => g1 >>> k) (by omega)
      have heval_next : pw.evalLevel c96 (5 + (step + 1)) = maskLevel (5 + (step + 1)) (c96 inpL) := by
        rw [show 5 + (step + 1) = (5 + step) + 1 by omega,
          evalLevel_succ_of_ge2 c96 pw (5 + step) (by omega)]
        dsimp only
        rw [hidx_pw, if_pos hpair]
      have hlinp : pw.levelInput c96 (5 + step) = [inpL] := by
        unfold WitnessPath.levelInput
        dsimp only
        rw [hidx_pw, if_pos hpair]
      -- Common compression + mask (240b for step < 3, 238b for step = 3) at pc[221..230] -> pc[231]
      have hcall221 : ∀ (s221 : MachineState) (kA : Nat),
          kA ≤ 194 →
          StepsTo oracle s7 s221 kA 0 [] →
          s221.pc = pcWord 221 →
          CheckFixedRegs s221 →
          ProofCursor s0 input.proof.length (pCur + 30) tOff s221 →
          MemEqOutside s s221 256 320 →
          s221.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + step)) →
          s221.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) →
          s221.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) →
          s221.getReg .x27 = BitVec.ofNat 64 rem →
          s221.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + step)) →
          s221.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) →
          readBuffer s221 256 96 = inpL →
          readBuffer s221 320 32 = 0 →
          PhaseOutcome oracle s 215 1 (input.proof.length < pCur + binStepBytes g1 (3 + step) + tailBytes tOff)
            (fun s' q tr =>
              q ≤ 1 ∧ s'.pc = (if step + 1 = 4 then pcWord 234 else pcWord 197) ∧
              CheckFixedRegs s' ∧
              ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (3 + step)) tOff s' ∧
              MemEqOutside s s' 256 320 ∧
              s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) ∧
              s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
              s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
              s'.getReg .x27 = BitVec.ofNat 64 rem ∧
              s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) ∧
              s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
              readBuffer s' 256 32 = pw.evalLevel c96 (5 + (step + 1)) ∧
              readBuffer s' 320 32 = 0 ∧
              ∀ x ∈ pw.levelInput c96 (5 + step), InTrace h768 oracle tr x) := by
        intro s221 kA hkA hmidA hpc221 hfix221 hcur221 hout221 h22 h24 h8 h27 h29 h30 hinp221 hgap221
        have hst221 := step_ordinary oracle s221 221 (.ADDI .x10 .x21 0#12) (by decide) hpc221 rfl (by intro h; cases h) rfl
        let s222 := execInstrBr s221 (.ADDI .x10 .x21 0#12)
        have hpc222 : s222.pc = pcWord 222 := by simp only [s222, execInstrBr, MachineState.setPC, hpc221, pcWord_add_four]
        have hst222 := step_ordinary oracle s222 222 (.ADDI .x12 .x21 0#12) (by decide) hpc222 rfl (by intro h; cases h) rfl
        let s223 := execInstrBr s222 (.ADDI .x12 .x21 0#12)
        have hpc223 : s223.pc = pcWord 223 := by simp only [s223, execInstrBr, MachineState.setPC, hpc222, pcWord_add_four]
        have hmem223 : s223.mem = s221.mem := by simp [s223, s222, execInstrBr, mem_setPC, mem_setReg]
        have hreg223 : ∀ r, r ≠ .x10 → r ≠ .x12 → s223.getReg r = s221.getReg r := fun r h10 h12 => by
          simp only [s223, s222, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
        have hx10_223 : s223.getReg .x10 = 256#64 := by
          simp only [s223, s222, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide), hfix221.x21, se12_0, BitVec.add_zero]
        have hx12_223 : s223.getReg .x12 = 256#64 := by
          simp only [s223, s222, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
            hfix221.x21, se12_0, BitVec.add_zero]
        have hec := step_ecall_compress h768 oracle s223 223 256 256 (by decide) hpc223 rfl
          ((hreg223 .x5 (by decide) (by decide)).trans hfix221.x5)
          ((hreg223 .x11 (by decide) (by decide)).trans hfix221.x11)
          ((hreg223 .x13 (by decide) (by decide)).trans hfix221.x13)
          hx10_223 hx12_223 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
        rw [(MemEqOutside.of_mem_eq hmem223 0 0).readBuffer_eq (by decide) (by omega), hinp221] at hec
        let s224 := writeBits s223 (BitVec.ofNat 64 256) (c96 inpL)
        have hpc224 : s224.pc = pcWord 224 := by simp only [s224, writeBits, MachineState.setPC, hpc223, pcWord_add_four]
        have hreg224 : ∀ r, r ≠ .x10 → r ≠ .x12 → s224.getReg r = s221.getReg r := fun r h10 h12 =>
          (writeBits_register s223 _ _ r).trans (hreg223 r h10 h12)
        -- pc[224]: ADDI x6, x2, 256; pc[225]: BEQ x29, x6, pc[228]
        have hst224 := step_ordinary oracle s224 224 (.ADDI .x6 .x2 256#12) (by decide) hpc224 rfl (by intro h; cases h) rfl
        let s225 := execInstrBr s224 (.ADDI .x6 .x2 256#12)
        have hpc225 : s225.pc = pcWord 225 := by simp only [s225, execInstrBr, MachineState.setPC, hpc224, pcWord_add_four]
        have hx6_225 : s225.getReg .x6 = BitVec.ofNat 64 (68719475968 + 256) := by
          simp only [s225, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hreg224 .x2 (by decide) (by decide), hfix221.x2, se12_256, bv64_add]
        have hx29_225 : s225.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + step)) := by
          simp only [s225, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hreg224 .x29 (by decide) (by decide), h29]
        have hst225 := step_ordinary oracle s225 225 (.BEQ .x29 .x6 12#13) (by decide) hpc225 rfl (by intro h; cases h) rfl
        let s226 := execInstrBr s225 (.BEQ .x29 .x6 12#13)
        have heq3 : (s225.getReg .x29 == s225.getReg .x6) = decide (step = 3) := by
          rw [hx29_225, hx6_225, bv64_beq_eq _ _ (by omega) (by omega)]
          exact decide_eq_decide.mpr (by omega)
        have hmem226 : s226.mem = s224.mem := by
          simp only [s226, execInstrBr]; split <;> simp [s225, execInstrBr, mem_setPC, mem_setReg]
        have hreg226 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s226.getReg r = s221.getReg r := fun r h6 h10 h12 => by
          have : s226.getReg r = s225.getReg r := by simp only [s226, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
          rw [this]; simp only [s225, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
          exact hreg224 r h10 h12
        have hpre226 := (((hst200.trans hst201).trans (hst202.trans hst203)).trans hmidA).trans
          (((hst221.trans hst222).trans hec).trans (hst224.trans hst225))
        by_cases hs3 : step = 3
        · -- step = 3 (l = 8 -> L9): mask238 at pc[228..230] -> pc[231]
          have hpc226 : s226.pc = pcWord 228 := by
            simp only [s226, execInstrBr, heq3, hs3, decide_true, ite_true, MachineState.setPC, hpc225]
            exact pc_225_branch
          obtain ⟨s231, hs231, hpc231, hreg231, hdig231, hout231⟩ :=
            step_mask238 oracle 228 .x21 s226 256 (by decide) (by decide) rfl rfl rfl hpc226
              ((hreg226 .x21 (by decide) (by decide) (by decide)).trans hfix221.x21)
              ((hreg226 .x9 (by decide) (by decide) (by decide)).trans hfix221.x9)
              (by decide) (by unfold MEMORY_BYTES; omega)
          have hdig_eq : readBuffer s231 256 32 = pw.evalLevel c96 (5 + (step + 1)) := by
            rw [heval_next, hdig231, (MemEqOutside.of_mem_eq hmem226 0 0).readBuffer_eq (by decide) (by omega),
              writeBits_readBuffer_digest]
            unfold maskLevel
            rw [if_neg (by omega), if_neg (by omega)]
          have hgap231 : readBuffer s231 320 32 = 0 := by
            rw [hout231.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem226 0 0).readBuffer_eq (by decide) (by omega),
              (MemEqOutside_writeBits_digest s223 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem223 0 0).readBuffer_eq (by decide) (by omega), hgap221]
          have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s231.getReg r = s221.getReg r :=
            fun r h6 h10 h12 => (hreg231 r h6).trans (hreg226 r h6 h10 h12)
          have hout_all : MemEqOutside s s231 256 320 :=
            hout221.trans ((MemEqOutside.of_mem_eq hmem223 256 320).trans
              (((MemEqOutside_writeBits_digest s223 256 _ (by decide)).mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem226 256 320).trans (hout231.mono (by omega) (by omega)))))
          refine hfooter s231 (4 + kA + 5 + 3) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
            ((hpre226.trans hs231).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
            hpc231
            (hfix221.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
            (by rw [hsb]; exact hcur221.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
            hout_all
            ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
            ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
            ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
            ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
            ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
            ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
            hdig_eq hgap231 ?_
          intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
          exact InTrace.singleton h768 oracle inpL
        · -- step < 3 (l ∈ 5..7 -> L6..L8): SH x21, x0, 30 (mask240) + JAL pc[231]
          have hpc226 : s226.pc = pcWord 226 := by
            simp only [s226, execInstrBr, heq3, hs3, decide_false, Bool.false_eq_true, ite_false,
              MachineState.setPC, hpc225, pcWord_add_four]
          have ha226 : s226.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
            rw [hreg226 .x21 (by decide) (by decide) (by decide), hfix221.x21]; decide
          have hv226 : memoryArgumentsValid s226 (.SH .x21 .x0 30#12) = true := by
            simp only [memoryArgumentsValid, memAccess, ha226]
            exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; omega) (by decide)
          have hst226 := step_ordinary oracle s226 226 (.SH .x21 .x0 30#12) (by decide) hpc226 rfl (by intro h; cases h)
            (by simp [ordinaryStep, hv226])
          let s227 := execInstrBr s226 (.SH .x21 .x0 30#12)
          have hpc227 : s227.pc = pcWord 227 := by simp only [s227, execInstrBr, MachineState.setPC, hpc226, pcWord_add_four]
          have hst227 := step_ordinary oracle s227 227 (.JAL .x0 16#21) (by decide) hpc227 rfl (by intro h; cases h) rfl
          let s231 := execInstrBr s227 (.JAL .x0 16#21)
          have hpc231 : s231.pc = pcWord 231 := by
            simp only [s231, execInstrBr, MachineState.setPC, hpc227]; exact pc_227_jal
          have hmem231 : s231.mem = s227.mem := by simp [s231, execInstrBr, mem_setPC, mem_setReg]
          have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s231.getReg r = s221.getReg r := fun r h6 h10 h12 => by
            have h1 : s231.getReg r = s227.getReg r := by simp [s231, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            have h2 : s227.getReg r = s226.getReg r := by
              simp [s227, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
            exact h1.trans (h2.trans (hreg226 r h6 h10 h12))
          have hout_sh : MemEqOutside s226 s227 286 288 := by
            intro a ha hout
            simp only [s227, execInstrBr, ha226, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
            exact MemEqOutside_setHalfword s226 286 _ (by decide) (by decide) a ha hout
          have hout_all : MemEqOutside s s231 256 320 :=
            hout221.trans ((MemEqOutside.of_mem_eq hmem223 256 320).trans
              (((MemEqOutside_writeBits_digest s223 256 _ (by decide)).mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem226 256 320).trans
                  ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem231 256 320)))))
          have hdig_eq : readBuffer s231 256 32 = pw.evalLevel c96 (5 + (step + 1)) := by
            rw [heval_next, (MemEqOutside.of_mem_eq hmem231 0 0).readBuffer_eq (by decide) (by omega)]
            have hsh : readBuffer s227 256 32 =
                readBuffer (s224.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s227, execInstrBr, ha226, MachineState.getByte, MachineState.setHalfword,
                MachineState.getMem, MachineState.setMem, mem_setPC, hmem226, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh, sh_zero_mask240 s224 256 (by decide) (by decide), writeBits_readBuffer_digest]
            unfold maskLevel
            rw [if_neg (by omega), if_pos (by omega)]
          have hgap231 : readBuffer s231 320 32 = 0 := by
            rw [(MemEqOutside.of_mem_eq hmem231 0 0).readBuffer_eq (by decide) (by omega),
              hout_sh.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem226 0 0).readBuffer_eq (by decide) (by omega),
              (MemEqOutside_writeBits_digest s223 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem223 0 0).readBuffer_eq (by decide) (by omega), hgap221]
          refine hfooter s231 (4 + kA + 5 + 2) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
            ((hpre226.trans (hst226.trans hst227)).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
            hpc231
            (hfix221.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
            (by rw [hsb]; exact hcur221.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
            hout_all
            ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
            ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
            ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
            ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
            ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
            ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
            hdig_eq hgap231 ?_
          intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
          exact InTrace.singleton h768 oracle inpL
      by_cases heven : (g1 >>> (3 + step)) % 2 = 0
      · -- Even: jump to pc[217..220] -> pc[221]
        have hx7z : s6.getReg .x7 = 0#64 := by rw [hx7_6, heven]
        have hpc7 : s7.pc = pcWord 217 := by
          simp only [s7, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
            MachineState.setPC, hpc6]; exact pc_203_branch
        have hmem7 : s7.mem = s.mem := by
          simpa [s7, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem6
        have hreg76 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
          simp only [s7, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → s7.getReg r = s.getReg r := fun r h6 h7 h28 => by
          rw [hreg76]
          simp only [s6, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
          exact hreg5 r h6 h7 h28
        have hst217 := step_ordinary oracle s7 217 (.ADDI .x12 .x21 32#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
        let s8 := execInstrBr s7 (.ADDI .x12 .x21 32#12)
        have hpc8 : s8.pc = pcWord 218 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
        obtain ⟨s9, hs9, hpc9, hx25_9, hreg9, hcopy9, hout9⟩ :=
          step_call_read_n oracle 218 30 s8 (11162446080 + pCur) 288 (by decide) (by decide) (by decide)
            rfl rfl hpc8
            (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                  hreg7 .x25 (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide),
                  hreg7 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
        -- pc[220]: SH x21, x0, 62
        have hx21_9 : s9.getReg .x21 = 256#64 := by
          rw [hreg9 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp only [s8, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21),
            hreg7 .x21 (by decide) (by decide) (by decide), hfix.x21]
        have ha220 : s9.getReg .x21 + signExtend12 62#12 = BitVec.ofNat 64 318 := by
          rw [hx21_9]; decide
        have hv220 : memoryArgumentsValid s9 (.SH .x21 .x0 62#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha220]
          exact accessValid_ofNat 318 2 (by unfold MEMORY_BYTES; omega) (by decide)
        have hst220 := step_ordinary oracle s9 220 (.SH .x21 .x0 62#12) (by decide) hpc9 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv220])
        let s10 := execInstrBr s9 (.SH .x21 .x0 62#12)
        have hpc10 : s10.pc = pcWord 221 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
        have hmem8 : s8.mem = s.mem := by simpa [s8, execInstrBr, mem_setPC, mem_setReg] using hmem7
        have hout_sh : MemEqOutside s9 s10 318 320 := by
          intro a ha hout
          simp only [s10, execInstrBr, ha220, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s9 318 _ (by decide) (by decide) a ha hout
        have hout_all : MemEqOutside s s10 288 320 :=
          (MemEqOutside.of_mem_eq hmem8 288 320).trans
            ((hout9.mono (by omega) (by omega)).trans (hout_sh.mono (by omega) (by omega)))
        have hreg10_9 : ∀ r, s10.getReg r = s9.getReg r := fun r => by
          simp [s10, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        have hreg10 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x28 →
            s10.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 h28 => by
          rw [hreg10_9, hreg9 r h1 h6 h10 h12 h25]
          simp only [s8, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
          exact hreg7 r h6 h7 h28
        have hcur10 : ProofCursor s0 input.proof.length (pCur + 30) tOff s10 := by
          refine ⟨hge30, ?_, ?_, ?_, ?_⟩
          · rw [hreg10_9, hx25_9]; congr 1
          · rw [hreg10 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg10 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg10 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
        have hgap10 : readBuffer s10 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp10 : readBuffer s10 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s10 256 hgap10]
          have hL : readBuffer s10 256 32 = curD :=
            (hout_all.readBuffer_eq (by decide) (by omega)).trans hcurDig
          have hR : readBuffer s10 288 32 = sibD := by
            rw [hsibD_eq]
            have hsh_eq : readBuffer s10 288 32 =
                readBuffer (s9.setHalfword (BitVec.ofNat 64 (288 + 30)) 0#16) 288 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s10, execInstrBr, ha220, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh_eq]
            apply sh_zero_readBuffer30 s9 s0 288 (11162446080 + pCur) (by decide) (by decide)
            intro j hj
            have hc := hcopy9 j hj
            simp only [MachineState.getByte, MachineState.getMem, hmem8] at hc ⊢
            exact hc.trans (hhigh (11162446080 + pCur + j) (by omega) (by omega))
          rw [hL, hR]; simp only [inpL, heven, ite_true]
        refine hcall221 s10 185 (by decide)
          (by simpa using (hst217.trans hs9).trans hst220) hpc10
          (hfix.of_agree (fun r hr => hreg10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur10 (hout_all.mono (by omega) (by omega))
          ((hreg10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
          ((hreg10 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg10 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg10 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg10 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp10 hgap10
      · -- Odd: fall through to pc[204..216] -> pc[221]
        have hodd : (g1 >>> (3 + step)) % 2 = 1 := by omega
        have hx7o : s6.getReg .x7 = 1#64 := by rw [hx7_6, hodd]
        have hpc7 : s7.pc = pcWord 204 := by
          simp only [s7, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc6, pcWord_add_four]
        have hmem7 : s7.mem = s.mem := by
          simpa [s7, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            MachineState.setPC] using hmem6
        have hreg76 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
          simp only [s7, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → s7.getReg r = s.getReg r := fun r h6 h7 h28 => by
          rw [hreg76]
          simp only [s6, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
          exact hreg5 r h6 h7 h28
        have hcp : ∀ j < 4,
            checkInstr (204 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (204 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s8, hs8, hpc8, hreg8, hcopy8, hout8⟩ :=
          step_copy_dwords oracle 204 4 .x21 .x21 0 32 s7 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp hpc7
            ((hreg7 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
            ((hreg7 .x21 (by decide) (by decide) (by decide)).trans hfix.x21)
            (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by decide)
        have hst212 := step_ordinary oracle s8 212 (.ADDI .x12 .x21 0#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 0#12)
        have hpc9 : s9.pc = pcWord 213 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hx25_10, hreg10, hcopy10, hout10⟩ :=
          step_call_read_n oracle 213 30 s9 (11162446080 + pCur) 256 (by decide) (by decide) (by decide)
            rfl rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg8 .x25 (by decide),
                  hreg7 .x25 (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg8 .x21 (by decide),
                  hreg7 .x21 (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
        have hx21_10 : s10.getReg .x21 = 256#64 := by
          rw [hreg10 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg8 .x21 (by decide),
            hreg7 .x21 (by decide) (by decide) (by decide), hfix.x21]
        have ha215 : s10.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
          rw [hx21_10]; decide
        have hv215 : memoryArgumentsValid s10 (.SH .x21 .x0 30#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha215]
          exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; omega) (by decide)
        have hst215 := step_ordinary oracle s10 215 (.SH .x21 .x0 30#12) (by decide) hpc10 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv215])
        let s11 := execInstrBr s10 (.SH .x21 .x0 30#12)
        have hpc11 : s11.pc = pcWord 216 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
        have hst216 := step_ordinary oracle s11 216 (.JAL .x0 20#21) (by decide) hpc11 rfl (by intro h; cases h) rfl
        let s12 := execInstrBr s11 (.JAL .x0 20#21)
        have hpc12 : s12.pc = pcWord 221 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11]; exact pc_216_jal
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hmem12 : s12.mem = s11.mem := by simp [s12, execInstrBr, mem_setPC, mem_setReg]
        have hout_sh : MemEqOutside s10 s11 286 288 := by
          intro a ha hout
          simp only [s11, execInstrBr, ha215, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s10 286 _ (by decide) (by decide) a ha hout
        have hout_all : MemEqOutside s s12 256 320 :=
          (MemEqOutside.of_mem_eq hmem7 256 320).trans
            ((hout8.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem9 256 320).trans
                ((hout10.mono (by omega) (by omega)).trans
                  ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem12 256 320)))))
        have hreg12_10 : ∀ r, s12.getReg r = s10.getReg r := fun r => by
          have h1 : s12.getReg r = s11.getReg r := by simp [s12, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          have h2 : s11.getReg r = s10.getReg r := by
            simp [s11, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
          exact h1.trans h2
        have hreg12 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x28 →
            s12.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 h28 => by
          rw [hreg12_10, hreg10 r h1 h6 h10 h12 h25]
          simp only [s9, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg8 r h6]
          exact hreg7 r h6 h7 h28
        have hcur12 : ProofCursor s0 input.proof.length (pCur + 30) tOff s12 := by
          refine ⟨hge30, ?_, ?_, ?_, ?_⟩
          · rw [hreg12_10, hx25_10]; congr 1
          · rw [hreg12 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg12 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg12 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
        have hgap12 : readBuffer s12 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp12 : readBuffer s12 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s12 256 hgap12]
          have hL : readBuffer s12 256 32 = sibD := by
            rw [hsibD_eq, (MemEqOutside.of_mem_eq hmem12 0 0).readBuffer_eq (by decide) (by omega)]
            have hsh_eq : readBuffer s11 256 32 =
                readBuffer (s10.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
              apply readBuffer_congr2; intro j hj
              simp [s11, execInstrBr, ha215, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
                show (0#64 : Word).truncate 16 = 0#16 by decide]
            rw [hsh_eq]
            apply sh_zero_readBuffer30 s10 s0 256 (11162446080 + pCur) (by decide) (by decide)
            intro j hj
            have h9s : MemEqOutside s s9 288 320 :=
              (MemEqOutside.of_mem_eq hmem7 288 320).trans (hout8.trans (MemEqOutside.of_mem_eq hmem9 288 320))
            exact (hcopy10 j hj).trans
              ((h9s (11162446080 + pCur + j) (by omega) (by omega)).trans
                (hhigh (11162446080 + pCur + j) (by omega) (by omega)))
          have hcur' : readBuffer s 256 32 = curD := hcurDig
          have hR : readBuffer s12 288 32 = curD := by
            rw [(MemEqOutside.of_mem_eq hmem12 0 0).readBuffer_eq (by decide) (by omega),
              hout_sh.readBuffer_eq (by decide) (by omega),
              hout10.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hcur']
            apply readBuffer_congr2; intro j hj
            have hc := hcopy8 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem7] at hc ⊢
            exact hc
          rw [hL, hR]; simp only [inpL, heven, ite_false]
        refine hcall221 s12 194 (by decide)
          (by simpa using ((hs8.trans hst212).trans hs10).trans (hst215.trans hst216)) hpc12
          (hfix.of_agree (fun r hr => hreg12 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          hcur12 hout_all
          ((hreg12 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
          ((hreg12 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg12 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg12 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg12 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg12 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp12 hgap12
  · -- Promoted (unpaired): binStepBytes g1 (3 + step) = 0, jump directly to pc[231]
    have hsb : binStepBytes g1 (3 + step) = 0 := by
      unfold binStepBytes; rw [show 2 + (3 + step) = 5 + step by omega]; simp [hpair]
    have hpc3 : s3.pc = pcWord 231 := by
      simp only [s3, execInstrBr, hult199, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc2]; exact pc_199_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hult199, hpair, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h28 => by
      simpa [s3, execInstrBr, hult199, hpair, MachineState.getReg_setPC] using hreg2 r h7 h28
    have hidx_pw : ((pw.index.val / 3) / 3) >>> (5 + step - 2) = g1 >>> (3 + step) := by
      change g1 >>> (5 + step - 2) = g1 >>> (3 + step)
      exact congrArg (fun k => g1 >>> k) (by omega)
    have heval_same : pw.evalLevel c96 (5 + (step + 1)) = pw.evalLevel c96 (5 + step) := by
      rw [show 5 + (step + 1) = (5 + step) + 1 by omega,
        evalLevel_succ_of_ge2 c96 pw (5 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_neg hpair]
    have hlinp_nil : pw.levelInput c96 (5 + step) = [] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_neg hpair]
    refine hfooter s3 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s3) hpc3
      (hfix.of_agree (fun r hr => hreg3 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (by rw [hsb, Nat.add_zero]
          exact hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (MemEqOutside.of_mem_eq hmem3 256 320)
      ((hreg3 .x22 (by decide) (by decide)).trans hx22)
      ((hreg3 .x24 (by decide) (by decide)).trans hx24)
      ((hreg3 .x8  (by decide) (by decide)).trans hx8)
      ((hreg3 .x27 (by decide) (by decide)).trans hx27)
      ((hreg3 .x29 (by decide) (by decide)).trans hx29)
      ((hreg3 .x30 (by decide) (by decide)).trans hx30)
      (by rw [heval_same]; exact ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hcurDig)
      (((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
      (by rw [hlinp_nil]; simp)

/-- Phase 1D-1: L5..L8 240b binary loop (`pc[196..233]` -> `pc[234]`), `≤ 865` steps, `≤ 4` calls. -/
theorem step_pos_bin240_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 196)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord) +
        binPathOff (((posAt input.positions ord).val / 3) / 3) 3) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((posAt input.positions ord).val / 3) / 3) >>> 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 5))
    (hl5 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 5)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g1 := (i.val / 3) / 3
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 865 4
      (input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 7 + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 4 ∧
        s'.pc = pcWord 234 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 7) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> 7) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 9 ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ prev, 5 ≤ prev → prev < 9 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g1 pw
  -- pc[196]: ADDI x30, x2, 288
  have hst196 := step_ordinary oracle s 196 (.ADDI .x30 .x2 288#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x30 .x2 288#12)
  have hpc1 : s1.pc = pcWord 197 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x30 → s1.getReg r = s.getReg r := fun r h30 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h30.symm
  have hx30_1 : s1.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hfix.x2, se12_288, bv64_add]
  have hloop : ∀ m ≤ 4,
      PhaseOutcome oracle s1 (215 * m) m
        (input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (3 + m) + tailBytes tOff)
        (fun s' q tr =>
          q ≤ m ∧
          s'.pc = (if m = 4 then pcWord 234 else pcWord 197) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (3 + m)) tOff s' ∧
          MemEqOutside s1 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + m)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + m)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (5 + m) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev, 5 ≤ prev → prev < 5 + m → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
    intro m hm
    induction m with
    | zero =>
      exact .continued s1 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s1)
        ⟨by decide, by simpa using hpc1,
         hfix.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl)),
         hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl)),
         MemEqOutside.refl s1 256 320,
         (hreg1 .x22 (by decide)).trans hx22,
         (hreg1 .x24 (by decide)).trans hx24,
         (hreg1 .x8  (by decide)).trans hx8,
         (hreg1 .x27 (by decide)).trans hx27,
         (hreg1 .x29 (by decide)).trans hx29, hx30_1,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by decide) (by omega)).trans hl5,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by decide) (by omega)).trans hgap,
         fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have hbin_mon : binPathOff g1 (3 + k) ≤ binPathOff g1 (3 + (k + 1)) := by
        rw [show 3 + (k + 1) = (3 + k) + 1 by omega]; simp only [binPathOff]; omega
      rw [show 215 * (k + 1) = 215 * k + 215 by omega]
      refine (ih (by omega)).bind_dep
        (fun hlt => by omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne4 : k ≠ 4 := by omega
          simp only [hne4, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem1 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
          have hstep_k := step_pos_bin240_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega)
            (fun hlt => by
              change input.proof.length <
                pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (3 + k) + binStepBytes g1 (3 + k) + tailBytes tOff at hlt
              rw [show 3 + (k + 1) = (3 + k) + 1 by omega]
              simp only [binPathOff] at hlt ⊢; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', ?_, hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          · rw [show 3 + (k + 1) = (3 + k) + 1 by omega]
            simpa [binPathOff, Nat.add_assoc] using hcur'
          · intro prev hp1 hp2 x hx
            by_cases hprev : prev < 5 + k
            · exact (htr_k prev hp1 hprev x hx).append_left
            · have : prev = 5 + k := by omega
              subst this; exact (htr' x hx).append_right)
  have h4 := hloop 4 (by decide)
  cases h4 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (1 + k) q tr hr (by omega) hq (by simpa using hst196.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', _, hdig', hgap', htr'⟩ := hp
    refine .continued s' (1 + k) q tr (by omega) hq (by simpa using hst196.trans hs)
      ⟨hq', by simpa using hpc', hfix', hcur',
       (MemEqOutside.of_mem_eq hmem1 256 320).trans hout',
       hx22', hx24', hx8', hx27', hx29', hdig', hgap',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-! #### Phase 1D-2: L9..L13 238b Binary Loop (`pc[234..261]` -> `pc[262]`) -/

/-- One iteration (`step < 5`, level `l = 9 + step ∈ 9..13`) of the 238b binary loop (`pc[235..261]`). -/
theorem step_pos_bin238_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 5)
    (s : MachineState) (hpc : s.pc = pcWord 235)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord) +
        binPathOff (((posAt input.positions ord).val / 3) / 3) (7 + step))
      (tOff + binTailOff (((posAt input.positions ord).val / 3) / 3) step) s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((posAt input.positions ord).val / 3) / 3) >>> (7 + step)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (9 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g1 := (i.val / 3) / 3
    let pCur := pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (7 + step)
    let tCur := tOff + binTailOff g1 step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 220 1
      (input.proof.length < pCur + binStepBytes g1 (7 + step) + tailBytes (tCur + binStepTails g1 step))
      (fun s' q tr =>
        q ≤ 1 ∧
        s'.pc = (if step + 1 = 5 then pcWord 262 else pcWord 235) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (7 + step)) (tCur + binStepTails g1 step) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (9 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 (9 + step), InTrace h768 oracle tr x) := by
  intro s0 c96 i g1 pCur tCur pw
  have hplen_bd : input.proof.length ≤ 8669633152 := hvalid
  have hi_lt : i.val < 16777216 := i.isLt
  have hg1_lt : g1 < 1864136 := by change (i.val / 3) / 3 < _; omega
  have hidx_lt : g1 >>> (7 + step) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hshr_step : (g1 >>> (7 + step)) / 2 = g1 >>> (7 + (step + 1)) := by
    simp only [Nat.shiftRight_eq_div_pow, show 7 + (step + 1) = (7 + step) + 1 by omega,
      Nat.pow_succ, Nat.div_div_eq_div_mul]
  -- pc[235]: XORI x28, x22, 1; pc[236]: LD x7, 8(x29); pc[237]: BGEU x28, x7, pc[259]
  have hst235 := step_ordinary oracle s 235 (.XORI .x28 .x22 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.XORI .x28 .x22 1#12)
  have hpc1 : s1.pc = pcWord 236 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 ((g1 >>> (7 + step)) ^^^ 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, se12_1]
    exact bv64_xor_one _ hidx_lt
  have hreg1 : ∀ r, r ≠ .x28 → s1.getReg r = s.getReg r := fun r h28 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h28.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha236 : s1.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475968 + (32 * (9 + step) + 8)) := by
    rw [hreg1 .x29 (by decide), hx29, se12_8]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv236 : memoryArgumentsValid s1 (.LD .x7 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha236]
    exact accessValid_ofNat (68719475968 + (32 * (9 + step) + 8)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst236 := step_ordinary oracle s1 236 (.LD .x7 .x29 8#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv236])
  let s2 := execInstrBr s1 (.LD .x7 .x29 8#12)
  have hpc2 : s2.pc = pcWord 237 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hsz_val : s1.getMem (BitVec.ofNat 64 (68719475968 + (32 * (9 + step) + 8))) =
      BitVec.ofNat 64 (levelSize (9 + step)) := by
    have hm1 : s1.getMem (BitVec.ofNat 64 (68719475968 + (32 * (9 + step) + 8))) =
        s.getMem (BitVec.ofNat 64 (68719475968 + (32 * (9 + step) + 8))) := by
      simp [MachineState.getMem, hmem1]
    rw [hm1, hhigh.getMem_eq (by omega) (by omega) (by omega),
      check_initial_data_dword input hvalid (32 * (9 + step) + 8) (by omega)]
    exact openingData_dword_1 ⟨9 + step, by omega⟩
  have hx7_2 : s2.getReg .x7 = BitVec.ofNat 64 (levelSize (9 + step)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha236]
    rw [MachineState.getReg_setReg_eq (by decide), hsz_val]
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 ((g1 >>> (7 + step)) ^^^ 1) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
  have hsib_lt64 : (g1 >>> (7 + step)) ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' (g1 >>> (7 + step)) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega
  have hsz_lt64 : levelSize (9 + step) < 2 ^ 64 := by
    interval_cases step <;> decide
  have hst237 := step_ordinary oracle s2 237 (.BGEU .x28 .x7 88#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BGEU .x28 .x7 88#13)
  have hult237 : BitVec.ult (s2.getReg .x28) (s2.getReg .x7) =
      decide (((g1 >>> (7 + step)) ^^^ 1) < levelSize (9 + step)) := by
    rw [hx28_2, hx7_2, bv64_ult_eq _ _ hsib_lt64 hsz_lt64]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1
  have hreg2 : ∀ r, r ≠ .x7 → r ≠ .x28 → s2.getReg r = s.getReg r := fun r h7 h28 => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg1 r h28]
  have hpre3 : StepsTo oracle s s3 3 0 [] := by
    simpa using (hst235.trans hst236).trans hst237
  -- Common loop footer at pc[259..261]: SRLI x22, x22, 1; ADDI x29, x29, 32; BNE x29, x30, pc[235]
  have hfooter : ∀ (s259 : MachineState) (kMid qMid : Nat) (trMid : CompressionReplies),
      kMid ≤ 214 → qMid ≤ 1 →
      StepsTo oracle s3 s259 kMid qMid trMid →
      s259.pc = pcWord 259 →
      CheckFixedRegs s259 →
      ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (7 + step)) (tCur + binStepTails g1 step) s259 →
      MemEqOutside s s259 256 320 →
      s259.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + step)) →
      s259.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) →
      s259.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) →
      s259.getReg .x27 = BitVec.ofNat 64 rem →
      s259.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + step)) →
      s259.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) →
      readBuffer s259 256 32 = pw.evalLevel c96 (9 + (step + 1)) →
      readBuffer s259 320 32 = 0 →
      (∀ x ∈ pw.levelInput c96 (9 + step), InTrace h768 oracle trMid x) →
      PhaseOutcome oracle s 220 1
        (input.proof.length < pCur + binStepBytes g1 (7 + step) + tailBytes (tCur + binStepTails g1 step))
        (fun s' q tr =>
          q ≤ 1 ∧
          s'.pc = (if step + 1 = 5 then pcWord 262 else pcWord 235) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (7 + step)) (tCur + binStepTails g1 step) s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (9 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ x ∈ pw.levelInput c96 (9 + step), InTrace h768 oracle tr x) := by
    intro s259 kMid qMid trMid hkMid hqMid hmid hpc259 hfix259 hcur259 hout259 h22 h24 h8 h27 h29 h30 hdig259 hgap259 htr259
    have hst259 := step_ordinary oracle s259 259 (.SRLI .x22 .x22 1#6) (by decide) hpc259 rfl (by intro h; cases h) rfl
    let s260 := execInstrBr s259 (.SRLI .x22 .x22 1#6)
    have hpc260 : s260.pc = pcWord 260 := by simp only [s260, execInstrBr, MachineState.setPC, hpc259, pcWord_add_four]
    have hx22_260 : s260.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) := by
      simp only [s260, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h22, show (1#6 : BitVec 6).toNat = 1 by decide,
        bv64_shr _ 1 (by omega), Nat.pow_one, hshr_step]
    have hst260 := step_ordinary oracle s260 260 (.ADDI .x29 .x29 32#12) (by decide) hpc260 rfl (by intro h; cases h) rfl
    let s261 := execInstrBr s260 (.ADDI .x29 .x29 32#12)
    have hpc261 : s261.pc = pcWord 261 := by simp only [s261, execInstrBr, MachineState.setPC, hpc260, pcWord_add_four]
    have hx29_261 : s261.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) := by
      simp only [s261, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide)]
      simp only [s260, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x29), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_261 : s261.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) := by
      simp only [s261, s260, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x30), h30]
    obtain ⟨sFin, hst261, hpcFin_raw, hregFin261, hmemFin261⟩ :=
      step_bne_reg oracle 261 235 .x29 .x30 8088#13 (by decide) rfl pc_261_branch
        s261 (68719475968 + 32 * (9 + (step + 1))) (68719475968 + 32 * 14) (by omega) (by omega)
        hpc261 hx29_261 hx30_261
    have hmemFin : sFin.mem = s259.mem :=
      hmemFin261.trans (by simp [s261, s260, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x22 → r ≠ .x29 → sFin.getReg r = s259.getReg r := fun r h22r h29r => by
      rw [hregFin261 r]
      simp only [s261, s260, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h29r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h22r.symm]
    have hx22Fin : sFin.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) := by
      rw [hregFin261 .x22]
      simp only [s261, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x22), hx22_260]
    have hx29Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) :=
      (hregFin261 .x29).trans hx29_261
    have hpcFin : sFin.pc = if step + 1 = 5 then pcWord 262 else pcWord 235 := by
      rw [hpcFin_raw]
      by_cases hdone : step + 1 = 5
      · simp [hdone]
      · have hne : 68719475968 + 32 * (9 + (step + 1)) ≠ 68719475968 + 32 * 14 := by omega
        simp [hdone, hne]
    have htot := (hpre3.trans hmid).trans ((hst259.trans hst260).trans hst261)
    refine .continued sFin (3 + kMid + 3) qMid trMid (by omega) hqMid (by simpa [Nat.add_assoc] using htot)
      ⟨hqMid, hpcFin,
       hfix259.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       hcur259.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
       hout259.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       hx22Fin,
       (hregFin .x24 (by decide) (by decide)).trans h24,
       (hregFin .x8  (by decide) (by decide)).trans h8,
       (hregFin .x27 (by decide) (by decide)).trans h27,
       hx29Fin, (hregFin .x30 (by decide) (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hdig259,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by decide) (by omega)).trans hgap259,
       htr259⟩
  -- Branch on whether sibling exists at level `9 + step`
  by_cases hpair : ((g1 >>> (7 + step)) ^^^ 1) < levelSize (9 + step)
  · -- Paired: binStepBytes g1 (7 + step) = 29, binStepTails g1 step = 1
    have hsb : binStepBytes g1 (7 + step) = 29 := by
      unfold binStepBytes
      rw [show 2 + (7 + step) = 9 + step by omega]
      simp [hpair, show ¬ (9 + step < 5) by omega, show ¬ (9 + step < 9) by omega]
    have hst_t : binStepTails g1 step = 1 := by
      unfold binStepTails; rw [show step + 7 = 7 + step by omega]; simp [hpair]
    have hpc3 : s3.pc = pcWord 238 := by
      simp only [s3, execInstrBr, hult237, hpair, decide_true, not_true_eq_false, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hult237, hpair, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h28 => by
      simpa [s3, execInstrBr, hult237, hpair, MachineState.getReg_setPC] using hreg2 r h7 h28
    -- pc[238]: ANDI x7, x22, 1; pc[239]: BEQ x7, x0, pc[251]
    have hst238 := step_ordinary oracle s3 238 (.ANDI .x7 .x22 1#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ANDI .x7 .x22 1#12)
    have hpc4 : s4.pc = pcWord 239 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hx7_4 : s4.getReg .x7 = BitVec.ofNat 64 ((g1 >>> (7 + step)) % 2) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x22 (by decide) (by decide), hx22, se12_1]
      exact bv64_and_one (g1 >>> (7 + step)) (by omega)
    have hst239 := step_ordinary oracle s4 239 (.BEQ .x7 .x0 48#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.BEQ .x7 .x0 48#13)
    have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
    have hst35 : StepsTo oracle s3 s5 2 0 [] := by simpa using hst238.trans hst239
    let sibD := pw.binSib (9 + step)
    have hsibD_eq : sibD = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur := by
      simp only [sibD, pw, parsePartialWitness,
        show ¬ (2 ≤ 9 + step ∧ 9 + step ≤ 4) by omega,
        show ¬ (5 ≤ 9 + step ∧ 9 + step ≤ 8) by omega, ite_false,
        show 9 ≤ 9 + step ∧ 9 + step ≤ 13 by omega, and_self, ite_true,
        show 9 + step - 2 = 7 + step by omega, show 9 + step - 9 = step by omega,
        pCur, tCur, Nat.add_assoc]
      dsimp only [g1]
    let curD := pw.evalLevel c96 (9 + step)
    let inpL : BitVec 768 :=
      if (g1 >>> (7 + step)) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
    have hidx_pw : ((pw.index.val / 3) / 3) >>> (9 + step - 2) = g1 >>> (7 + step) := by
      change g1 >>> (9 + step - 2) = g1 >>> (7 + step)
      exact congrArg (fun k => g1 >>> k) (by omega)
    have heval_next : pw.evalLevel c96 (9 + (step + 1)) = mask238 (c96 inpL) := by
      rw [show 9 + (step + 1) = (9 + step) + 1 by omega,
        evalLevel_succ_of_ge2 c96 pw (9 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_pos hpair]
      unfold maskLevel
      rw [if_neg (by omega), if_neg (by omega)]
    have hlinp : pw.levelInput c96 (9 + step) = [inpL] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_pos hpair]
    -- Common compression + mask238 at pc[253..258] -> pc[259]
    have hcall253 : ∀ (s253 : MachineState) (kA : Nat),
        kA ≤ 203 →
        StepsTo oracle s5 s253 kA 0 [] →
        s253.pc = pcWord 253 →
        CheckFixedRegs s253 →
        ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s253 →
        MemEqOutside s s253 256 320 →
        s253.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + step)) →
        s253.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) →
        s253.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) →
        s253.getReg .x27 = BitVec.ofNat 64 rem →
        s253.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + step)) →
        s253.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) →
        readBuffer s253 256 96 = inpL →
        readBuffer s253 320 32 = 0 →
        PhaseOutcome oracle s 220 1
          (input.proof.length < pCur + binStepBytes g1 (7 + step) + tailBytes (tCur + binStepTails g1 step))
          (fun s' q tr =>
            q ≤ 1 ∧ s'.pc = (if step + 1 = 5 then pcWord 262 else pcWord 235) ∧
            CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length (pCur + binStepBytes g1 (7 + step)) (tCur + binStepTails g1 step) s' ∧
            MemEqOutside s s' 256 320 ∧
            s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) ∧
            s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
            readBuffer s' 256 32 = pw.evalLevel c96 (9 + (step + 1)) ∧
            readBuffer s' 320 32 = 0 ∧
            ∀ x ∈ pw.levelInput c96 (9 + step), InTrace h768 oracle tr x) := by
      intro s253 kA hkA hmidA hpc253 hfix253 hcur253 hout253 h22 h24 h8 h27 h29 h30 hinp253 hgap253
      have hst253 := step_ordinary oracle s253 253 (.ADDI .x10 .x21 0#12) (by decide) hpc253 rfl (by intro h; cases h) rfl
      let s254 := execInstrBr s253 (.ADDI .x10 .x21 0#12)
      have hpc254 : s254.pc = pcWord 254 := by simp only [s254, execInstrBr, MachineState.setPC, hpc253, pcWord_add_four]
      have hst254 := step_ordinary oracle s254 254 (.ADDI .x12 .x21 0#12) (by decide) hpc254 rfl (by intro h; cases h) rfl
      let s255 := execInstrBr s254 (.ADDI .x12 .x21 0#12)
      have hpc255 : s255.pc = pcWord 255 := by simp only [s255, execInstrBr, MachineState.setPC, hpc254, pcWord_add_four]
      have hmem255 : s255.mem = s253.mem := by simp [s255, s254, execInstrBr, mem_setPC, mem_setReg]
      have hreg255 : ∀ r, r ≠ .x10 → r ≠ .x12 → s255.getReg r = s253.getReg r := fun r h10 h12 => by
        simp only [s255, s254, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_255 : s255.getReg .x10 = 256#64 := by
        simp only [s255, s254, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix253.x21, se12_0, BitVec.add_zero]
      have hx12_255 : s255.getReg .x12 = 256#64 := by
        simp only [s255, s254, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hfix253.x21, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h768 oracle s255 255 256 256 (by decide) hpc255 rfl
        ((hreg255 .x5 (by decide) (by decide)).trans hfix253.x5)
        ((hreg255 .x11 (by decide) (by decide)).trans hfix253.x11)
        ((hreg255 .x13 (by decide) (by decide)).trans hfix253.x13)
        hx10_255 hx12_255 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
      rw [(MemEqOutside.of_mem_eq hmem255 0 0).readBuffer_eq (by decide) (by omega), hinp253] at hec
      let s256 := writeBits s255 (BitVec.ofNat 64 256) (c96 inpL)
      have hpc256 : s256.pc = pcWord 256 := by simp only [s256, writeBits, MachineState.setPC, hpc255, pcWord_add_four]
      have hreg256 : ∀ r, r ≠ .x10 → r ≠ .x12 → s256.getReg r = s253.getReg r := fun r h10 h12 =>
        (writeBits_register s255 _ _ r).trans (hreg255 r h10 h12)
      obtain ⟨s259, hs259, hpc259, hreg259, hdig259, hout259⟩ :=
        step_mask238 oracle 256 .x21 s256 256 (by decide) (by decide) rfl rfl rfl hpc256
          ((hreg256 .x21 (by decide) (by decide)).trans hfix253.x21)
          ((hreg256 .x9 (by decide) (by decide)).trans hfix253.x9)
          (by decide) (by unfold MEMORY_BYTES; omega)
      have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s259.getReg r = s253.getReg r :=
        fun r h6 h10 h12 => (hreg259 r h6).trans (hreg256 r h10 h12)
      have hout_all : MemEqOutside s s259 256 320 :=
        hout253.trans ((MemEqOutside.of_mem_eq hmem255 256 320).trans
          (((MemEqOutside_writeBits_digest s255 256 _ (by decide)).mono (by omega) (by omega)).trans
            (hout259.mono (by omega) (by omega))))
      have hdig_eq : readBuffer s259 256 32 = pw.evalLevel c96 (9 + (step + 1)) := by
        rw [heval_next, hdig259, writeBits_readBuffer_digest]
      have hgap259 : readBuffer s259 320 32 = 0 := by
        rw [hout259.readBuffer_eq (by decide) (by omega),
          (MemEqOutside_writeBits_digest s255 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
          (MemEqOutside.of_mem_eq hmem255 0 0).readBuffer_eq (by decide) (by omega), hgap253]
      have htot := (hst35.trans hmidA).trans (((hst253.trans hst254).trans hec).trans hs259)
      refine hfooter s259 (2 + kA + 6) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
        (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
        hpc259
        (hfix253.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (by rw [hsb, hst_t]; exact hcur253.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        hout_all
        ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
        ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
        ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
        ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
        ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
        ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
        hdig_eq hgap259 ?_
      intro x hx; rw [hlinp, List.mem_singleton] at hx; subst hx
      exact InTrace.singleton h768 oracle inpL
    by_cases heven : (g1 >>> (7 + step)) % 2 = 0
    · -- Even: jump to pc[251..252] -> pc[253]
      have hx7z : s4.getReg .x7 = 0#64 := by rw [hx7_4, heven]
      have hpc5 : s5.pc = pcWord 251 := by
        simp only [s5, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
          MachineState.setPC, hpc4]; exact pc_239_branch
      have hmem5 : s5.mem = s.mem := by
        simpa [s5, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem4
      have hreg54 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
        simp only [s5, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
      have hreg5 : ∀ r, r ≠ .x7 → r ≠ .x28 → s5.getReg r = s.getReg r := fun r h7 h28 => by
        rw [hreg54]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg3 r h7 h28
      have hst251 := step_ordinary oracle s5 251 (.ADDI .x12 .x21 32#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ADDI .x12 .x21 32#12)
      have hpc6 : s6.pc = pcWord 252 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s.mem := by simpa [s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
      have hreg6 : ∀ r, r ≠ .x12 → s6.getReg r = s5.getReg r := fun r hr => by
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
      have hcur6 : ProofCursor s0 input.proof.length pCur tCur s6 :=
        hcur.of_agree (fun r hr => (hreg6 r (isCursorReg_ne_of_false hr rfl)).trans
          (hreg5 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 252 s6 pCur tCur 288
        (by decide) rfl hpc6 hcur6 (hhigh.trans (MemEqOutside.of_mem_eq hmem6 0 4294971392))
        (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide),
              hreg5 .x21 (by decide) (by decide), hfix.x21, se12_32]; decide)
        (by decide)
      cases hread with
      | rejected kR qR trR hrR hkR hqR hhR =>
        have htot := ((hpre3.trans hst35).trans hst251).halt hhR
        exact .rejected (3 + 2 + 1 + kR) qR trR (by rw [hsb, hst_t]; exact hrR) (by omega) (by omega)
          (by simpa only [Nat.zero_add, List.nil_append] using htot)
      | continued s7 kR qR trR hkR hqR hs7 hp7 =>
        obtain ⟨rfl, rfl, hpc7, hcur7, hreg7, hdig7, hout7⟩ := hp7
        have hout_all : MemEqOutside s s7 288 320 :=
          (MemEqOutside.of_mem_eq hmem6 288 320).trans hout7
        have hreg7_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 →
            r ≠ .x25 → r ≠ .x28 → r ≠ .x31 → s7.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h12 h25 h28 h31 =>
            (hreg7 r h1 h3 h4 h6 h7 h12 h25 h31).trans ((hreg6 r h12).trans (hreg5 r h7 h28))
        have hgap7 : readBuffer s7 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp7 : readBuffer s7 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s7 256 hgap7]
          have hL : readBuffer s7 256 32 = curD :=
            (hout_all.readBuffer_eq (by decide) (by omega)).trans hcurDig
          have hR : readBuffer s7 288 32 = sibD := hdig7.trans hsibD_eq.symm
          rw [hL, hR]; simp only [inpL, heven, ite_true]
        refine hcall253 s7 (1 + kR) (by omega)
          ((hst251.trans hs7).eq_of rfl (by omega) rfl (by simp)) hpc7
          (hfix.of_agree (fun r hr => hreg7_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl)))
          hcur7 (hout_all.mono (by omega) (by omega))
          ((hreg7_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
          ((hreg7_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg7_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg7_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg7_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg7_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp7 hgap7
    · -- Odd: fall through to pc[240..250] -> pc[253]
      have hodd : (g1 >>> (7 + step)) % 2 = 1 := by omega
      have hx7o : s4.getReg .x7 = 1#64 := by rw [hx7_4, hodd]
      have hpc5 : s5.pc = pcWord 240 := by
        simp only [s5, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc4, pcWord_add_four]
      have hmem5 : s5.mem = s.mem := by
        simpa [s5, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          MachineState.setPC] using hmem4
      have hreg54 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
        simp only [s5, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
      have hreg5 : ∀ r, r ≠ .x7 → r ≠ .x28 → s5.getReg r = s.getReg r := fun r h7 h28 => by
        rw [hreg54]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg3 r h7 h28
      have hcp : ∀ j < 4,
          checkInstr (240 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
          checkInstr (240 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
      obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
        step_copy_dwords oracle 240 4 .x21 .x21 0 32 s5 256 256 (by decide) (by decide)
          (by decide) (by decide) (by decide) hcp hpc5
          ((hreg5 .x21 (by decide) (by decide)).trans hfix.x21)
          ((hreg5 .x21 (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by decide)
      have hst248 := step_ordinary oracle s6 248 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
      have hpc7 : s7.pc = pcWord 249 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
      have hreg7 : ∀ r, r ≠ .x12 → s7.getReg r = s6.getReg r := fun r hr => by
        simp only [s7, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
      have hcur7 : ProofCursor s0 input.proof.length pCur tCur s7 :=
        hcur.of_agree (fun r hr => (hreg7 r (isCursorReg_ne_of_false hr rfl)).trans
          ((hreg6 r (isCursorReg_ne_of_false hr rfl)).trans
            (hreg5 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))))
      have hout_s7 : MemEqOutside s s7 288 320 :=
        (MemEqOutside.of_mem_eq hmem5 288 320).trans (hout6.trans (MemEqOutside.of_mem_eq hmem7 288 320))
      have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 249 s7 pCur tCur 256
        (by decide) rfl hpc7 hcur7 (hhigh.trans (hout_s7.mono (by omega) (by omega)))
        (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide),
              hreg5 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
        (by decide)
      cases hread with
      | rejected kR qR trR hrR hkR hqR hhR =>
        have htot := (((hpre3.trans hst35).trans hs6).trans hst248).halt hhR
        exact .rejected (3 + 2 + 8 + 1 + kR) qR trR (by rw [hsb, hst_t]; exact hrR) (by omega) (by omega)
          (by simpa only [Nat.zero_add, List.nil_append] using htot)
      | continued s8 kR qR trR hkR hqR hs8 hp8 =>
        obtain ⟨rfl, rfl, hpc8, hcur8, hreg8, hdig8, hout8⟩ := hp8
        have hst250 := step_ordinary oracle s8 250 (.JAL .x0 12#21) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.JAL .x0 12#21)
        have hpc9 : s9.pc = pcWord 253 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8]; exact pc_250_jal
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hreg9_8 : ∀ r, s9.getReg r = s8.getReg r := fun r => by
          simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have hout_all : MemEqOutside s s9 256 320 :=
          (hout_s7.mono (by omega) (by omega)).trans
            ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 320))
        have hreg9_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 →
            r ≠ .x25 → r ≠ .x28 → r ≠ .x31 → s9.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h12 h25 h28 h31 =>
            (hreg9_8 r).trans ((hreg8 r h1 h3 h4 h6 h7 h12 h25 h31).trans
              ((hreg7 r h12).trans ((hreg6 r h6).trans (hreg5 r h7 h28))))
        have hgap9 : readBuffer s9 320 32 = 0 :=
          (hout_all.readBuffer_eq (by decide) (by omega)).trans hgap
        have hinp9 : readBuffer s9 256 96 = inpL := by
          rw [readBuffer_binary_of_zero_gap s9 256 hgap9]
          have hL : readBuffer s9 256 32 = sibD :=
            ((MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega)).trans
              (hdig8.trans hsibD_eq.symm)
          have hcur' : readBuffer s 256 32 = curD := hcurDig
          have hR : readBuffer s9 288 32 = curD := by
            rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega),
              hout8.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by decide) (by omega), ← hcur']
            apply readBuffer_congr2; intro j hj
            have hc := hcopy6 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem5] at hc ⊢
            exact hc
          rw [hL, hR]; simp only [inpL, heven, ite_false]
        refine hcall253 s9 (8 + 1 + kR + 1) (by omega)
          ((((hs6.trans hst248).trans hs8).trans hst250).eq_of rfl (by omega) rfl (by simp)) hpc9
          (hfix.of_agree (fun r hr => hreg9_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl)))
          (hcur8.of_agree (fun r _ => hreg9_8 r))
          hout_all
          ((hreg9_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
          ((hreg9_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg9_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg9_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hreg9_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
          ((hreg9_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
          hinp9 hgap9
  · -- Promoted (unpaired): binStepBytes = 0, binStepTails = 0, jump directly to pc[259]
    have hsb : binStepBytes g1 (7 + step) = 0 := by
      unfold binStepBytes; rw [show 2 + (7 + step) = 9 + step by omega]; simp [hpair]
    have hst_t : binStepTails g1 step = 0 := by
      unfold binStepTails; rw [show step + 7 = 7 + step by omega]; simp [hpair]
    have hpc3 : s3.pc = pcWord 259 := by
      simp only [s3, execInstrBr, hult237, hpair, decide_false, Bool.false_eq_true, not_false_eq_true,
        ite_true, MachineState.setPC, hpc2]; exact pc_237_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hult237, hpair, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x28 → s3.getReg r = s.getReg r := fun r h7 h28 => by
      simpa [s3, execInstrBr, hult237, hpair, MachineState.getReg_setPC] using hreg2 r h7 h28
    have hidx_pw : ((pw.index.val / 3) / 3) >>> (9 + step - 2) = g1 >>> (7 + step) := by
      change g1 >>> (9 + step - 2) = g1 >>> (7 + step)
      exact congrArg (fun k => g1 >>> k) (by omega)
    have heval_same : pw.evalLevel c96 (9 + (step + 1)) = pw.evalLevel c96 (9 + step) := by
      rw [show 9 + (step + 1) = (9 + step) + 1 by omega,
        evalLevel_succ_of_ge2 c96 pw (9 + step) (by omega)]
      dsimp only
      rw [hidx_pw, if_neg hpair]
    have hlinp_nil : pw.levelInput c96 (9 + step) = [] := by
      unfold WitnessPath.levelInput
      dsimp only
      rw [hidx_pw, if_neg hpair]
    refine hfooter s3 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s3) hpc3
      (hfix.of_agree (fun r hr => hreg3 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (by rw [hsb, hst_t, Nat.add_zero, Nat.add_zero]
          exact hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (MemEqOutside.of_mem_eq hmem3 256 320)
      ((hreg3 .x22 (by decide) (by decide)).trans hx22)
      ((hreg3 .x24 (by decide) (by decide)).trans hx24)
      ((hreg3 .x8  (by decide) (by decide)).trans hx8)
      ((hreg3 .x27 (by decide) (by decide)).trans hx27)
      ((hreg3 .x29 (by decide) (by decide)).trans hx29)
      ((hreg3 .x30 (by decide) (by decide)).trans hx30)
      (by rw [heval_same]; exact ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hcurDig)
      (((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hgap)
      (by rw [hlinp_nil]; simp)

/-- Phase 1D-2: L9..L13 238b binary loop (`pc[234..261]` -> `pc[262]`), `≤ 1105` steps, `≤ 5` calls. -/
theorem step_pos_bin238_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 234)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord) +
        binPathOff (((posAt input.positions ord).val / 3) / 3) 7) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((posAt input.positions ord).val / 3) / 3) >>> 7))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 9))
    (hl9 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 9)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let g1 := (i.val / 3) / 3
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 1105 5
      (input.proof.length < pOff + recordLen i + tailBytes (tOff + recordTailCount i))
      (fun s' q tr =>
        q ≤ 5 ∧
        s'.pc = pcWord 262 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + recordLen i) (tOff + recordTailCount i) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> 12) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 14 ∧
        ∀ prev, 9 ≤ prev → prev ≤ 13 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i g1 pw
  -- pc[234]: ADDI x30, x2, 448
  have hst234 := step_ordinary oracle s 234 (.ADDI .x30 .x2 448#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x30 .x2 448#12)
  have hpc1 : s1.pc = pcWord 235 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x30 → s1.getReg r = s.getReg r := fun r h30 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h30.symm
  have hx30_1 : s1.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hfix.x2, se12_448, bv64_add]
  have hloop : ∀ m ≤ 5,
      PhaseOutcome oracle s1 (220 * m) m
        (input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (7 + m) + tailBytes (tOff + binTailOff g1 m))
        (fun s' q tr =>
          q ≤ m ∧
          s'.pc = (if m = 5 then pcWord 262 else pcWord 235) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (7 + m)) (tOff + binTailOff g1 m) s' ∧
          MemEqOutside s1 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + m)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + m)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (9 + m) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev, 9 ≤ prev → prev < 9 + m → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
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
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by decide) (by omega)).trans hl9,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by decide) (by omega)).trans hgap,
         fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have hbin_mon : binPathOff g1 (7 + k) ≤ binPathOff g1 (7 + (k + 1)) := by
        rw [show 7 + (k + 1) = (7 + k) + 1 by omega]; simp only [binPathOff]; omega
      have ht_mon : tailBytes (tOff + binTailOff g1 k) ≤ tailBytes (tOff + binTailOff g1 (k + 1)) :=
        tailBytes_mono (by simp only [binTailOff]; omega)
      rw [show 220 * (k + 1) = 220 * k + 220 by omega]
      refine (ih (by omega)).bind_dep
        (fun hlt => by omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne5 : k ≠ 5 := by omega
          simp only [hne5, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem1 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
          have hstep_k := step_pos_bin238_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega)
            (fun hlt => by
              change input.proof.length <
                pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 (7 + k) + binStepBytes g1 (7 + k) +
                  tailBytes (tOff + binTailOff g1 k + binStepTails g1 k) at hlt
              rw [show 7 + (k + 1) = (7 + k) + 1 by omega]
              simp only [binPathOff, binTailOff, Nat.add_assoc] at hlt ⊢; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', ?_, hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          · rw [show 7 + (k + 1) = (7 + k) + 1 by omega]
            simpa [binPathOff, binTailOff, Nat.add_assoc] using hcur'
          · intro prev hp1 hp2 x hx
            by_cases hprev : prev < 9 + k
            · exact (htr_k prev hp1 hprev x hx).append_left
            · have : prev = 9 + k := by omega
              subst this; exact (htr' x hx).append_right)
  have h5 := hloop 5 (by decide)
  cases h5 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (1 + k) q tr (by simpa [recordLen, recordTailCount, Nat.add_assoc] using hr) (by omega) hq
      (by simpa using hst234.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', _, _, hdig', _, htr'⟩ := hp
    refine .continued s' (1 + k) q tr (by omega) hq (by simpa using hst234.trans hs)
      ⟨hq', by simpa using hpc', hfix',
       by simpa [recordLen, recordTailCount, Nat.add_assoc] using hcur',
       (MemEqOutside.of_mem_eq hmem1 256 320).trans hout',
       hx22', hx24', hx8', hx27', hdig',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-! #### Phase 1E and Full Per-Position Loop (`pc[262..295]`, `pc[22] -> pc[296]`) -/

theorem gapOffset_disjoint {a b : Nat} (hne : a ≠ b) :
    gapOffset a + 32 ≤ gapOffset b ∨ gapOffset b + 32 ≤ gapOffset a := by
  unfold gapOffset; omega

theorem gapOffset_disjoint_gap (c q : Nat) :
    gapOffset c + 32 ≤ 96 * q + 64 ∨ 96 * q + 96 ≤ gapOffset c := by
  unfold gapOffset; omega

private def capAddrInstrs : List Instr :=
  [.SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6,
   .SLLI .x6 .x6 5#6, .ADD .x28 .x19 .x6, .ADD .x29 .x18 .x22]

private theorem pc_295_branch : pcWord 295 + signExtend13 7100#13 = pcWord 22 := by decide
private theorem pc_279_jal : pcWord 279 + signExtend21 52#21 = pcWord 292 := by decide
private theorem pc_268_branch : pcWord 268 + signExtend13 48#13 = pcWord 280 := by decide
private theorem checkInstr_267 : checkInstr 267 = .base (.LBU .x7 .x29 0#12) := rfl
private theorem checkInstr_268 : checkInstr 268 = .base (.BNE .x7 .x0 48#13) := rfl
private theorem checkInstr_269 : checkInstr 269 = .base (.ADDI .x7 .x0 1#12) := rfl
private theorem checkInstr_270 : checkInstr 270 = .base (.SB .x29 .x7 0#12) := rfl
private theorem checkInstr_279 : checkInstr 279 = .base (.JAL .x0 52#21) := rfl
private theorem checkInstr_292 : checkInstr 292 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_293 : checkInstr 293 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_294 : checkInstr 294 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_295 : checkInstr 295 = .base (.BNE .x27 .x0 7100#13) := rfl

private theorem ordinaryStep_ADDI (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    ordinaryStep st (.base (.ADDI rd rs imm)) = some (execInstrBr st (.ADDI rd rs imm)) := rfl

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
    checkInstr (262 + j) = .base (capAddrInstrs[j]'hj) := by
  intro j hj; have hj' : j < 5 := hj; interval_cases j <;> rfl

private theorem hpure_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    Instruction.base (capAddrInstrs[j]'hj) ≠ .base .ECALL ∧
    ∀ st, ordinaryStep st (.base (capAddrInstrs[j]'hj)) = some (execInstrBr st (capAddrInstrs[j]'hj)) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).mem = st.mem := by
  intro j hj; have hj' : j < 5 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩

private theorem hcode_capCopy : ∀ j < 4,
    checkInstr (271 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
    checkInstr (271 + 2 * j + 1) = .base (.SD .x28 .x6 (BitVec.ofNat 12 (0 + 8 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem hcode_capCmp : ∀ j < 4,
    checkInstr (280 + 3 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (280 + 3 * j + 1) = .base (.LD .x7 .x28 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (280 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (383 - (280 + 3 * j + 2))))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

private theorem step_tail_292 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 292)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 293 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 292 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_292
     (by intro h; cases h) (ordinaryStep_ADDI s .x24 .x24 8#12),
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 292)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (6733261056 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 6733261056 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_293 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 293)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (6867478784 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 294 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (6867478784 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 293 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_293
     (by intro h; cases h) (ordinaryStep_ADDI s .x8 .x8 256#12),
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 293)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (6867478784 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 6867478784 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_294 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 294)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 295 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 294 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_294
     (by intro h; cases h) (ordinaryStep_ADDI s .x27 .x27 4095#12),
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 294)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_tail_295 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 295)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 296 else pcWord 22) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  obtain ⟨s', hst, hpc', hreg', hmem'⟩ :=
    step_bne_reg oracle 295 22 .x27 .x0 7100#13 (by decide) checkInstr_295 pc_295_branch
      s rem1 0 hrem_lt (by omega) hpc h27 (getReg_x0 s)
  exact ⟨s', hst, hpc', hmem', hreg'⟩

private theorem step_pos_cap_store_tail (oracle : Oracle) (s0 : MachineState)
    (proofLen ord pOffNext tOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s292 : MachineState) (hpc292 : s292.pc = pcWord 292)
    (hfix292 : CheckFixedRegs s292)
    (hcur292 : ProofCursor s0 proofLen pOffNext tOffNext s292)
    (h24 : s292.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (h8  : s292.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (h27 : s292.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s292 sFin 4 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 296 else pcWord 22) ∧
      CheckFixedRegs sFin ∧
      ProofCursor s0 proofLen pOffNext tOffNext sFin ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * (ord + 1)) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s292.mem := by
  obtain ⟨s293, hs1, hpc293, hmem1, hx24_1, hreg1⟩ := step_tail_292 oracle ord s292 hpc292 h24
  obtain ⟨s294, hs2, hpc294, hmem2, hx8_2, hreg2⟩ :=
    step_tail_293 oracle ord s293 hpc293 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s295, hs3, hpc295, hmem3, hx27_3, hreg3⟩ :=
    step_tail_294 oracle rem1 s294 hpc294 ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27))
  obtain ⟨sFin, hs4, hpcFin, hmem4, hreg4⟩ :=
    step_tail_295 oracle rem1 (Nat.lt_of_succ_lt hrem_lt) s295 hpc295 hx27_3
  have hsteps : StepsTo oracle s292 sFin 4 0 [] :=
    (((hs1.trans hs2).trans hs3).trans hs4).eq_of rfl rfl rfl rfl
  have hmemFin : sFin.mem = s292.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x27 → sFin.getReg r = s292.getReg r :=
    fun r h24r h8r h27r => (hreg4 r).trans ((hreg3 r h27r).trans ((hreg2 r h8r).trans (hreg1 r h24r)))
  exact ⟨sFin, hsteps, hpcFin,
    hfix292.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hcur292.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    (hreg4 .x24).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1)),
    (hreg4 .x8).trans ((hreg3 .x8 (by decide)).trans hx8_2),
    (hreg4 .x27).trans hx27_3, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 456)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 269) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 256#64)
    (hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c))
    (hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c))
    (d14 : Digest) (hd14 : readBuffer s 256 32 = d14) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 292 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
      readBuffer s7 (8192 + gapOffset c) 32 = d14 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
        (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst269 := step_ordinary oracle s3 269 (.ADDI .x7 .x0 1#12) (by decide) hpc3 checkInstr_269 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 270 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx29_4 : s4.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha270 : s4.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_4, se12_0, BitVec.add_zero]
  have hv270 : memoryArgumentsValid s4 (.SB .x29 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha270]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst270 := step_ordinary oracle s4 270 (.SB .x29 .x7 0#12) (by decide) hpc4 checkInstr_270 (by intro h; cases h)
    (by simp [ordinaryStep, hv270])
  let s5 := execInstrBr s4 (.SB .x29 .x7 0#12)
  have hpc5 : s5.pc = pcWord 271 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (4096 + c)) 1#8).getByte q := by
    intro q
    simp only [s5, execInstrBr, ha270, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
      MachineState.getByte, MachineState.setByte, MachineState.getMem,
      MachineState.setMem, mem_setPC, hmem4]
  have hout5 : MemEqOutside s s5 (4096 + c) (4096 + c + 1) := by
    intro a ha hout
    rw [hbyte5]
    exact MemEqOutside_setByte s (4096 + c) 1#8 (by omega) a ha hout
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s5.getReg r = s.getReg r :=
    fun r h6 h7 h28 h29 => by
      have : s5.getReg r = s4.getReg r := by
        simp [s5, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [this]
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg3 r h6 h7 h28 h29
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
    step_copy_dwords oracle 271 4 .x21 .x28 0 0 s5 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCopy hpc5
      ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide)).trans hx21)
      hx28_5 (by decide) (by omega) (by unfold MEMORY_BYTES; omega) (by omega) (by omega)
  have hst279 := step_ordinary oracle s6 279 (.JAL .x0 52#21) (by decide) hpc6 checkInstr_279 (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 292 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_279_jal
  have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
  have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r :=
    fun r h6 h7 h28 h29 => by
      have : s7.getReg r = s6.getReg r := by simp [s7, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
      exact this.trans ((hreg6 r h6).trans (hreg5 r h6 h7 h28 h29))
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
  refine ⟨s7, by simpa using ((hst269.trans hst270).trans hs6).trans hst279, hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1E: store or duplicate-check cap leaf at L14 and advance loop counters (`pc[262..295]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext tOffNext rem1 : Nat) (hord : ord < input.positions.card)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 262)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOffNext tOffNext s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((posAt input.positions ord).val / 3) / 3) >>> 12))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
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
        s'.pc = (if rem1 = 0 then pcWord 296 else pcWord 22) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pOffNext tOffNext s' ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * (ord + 1)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
        readBuffer s' (8192 + gapOffset c) 32 = d14 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
          (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro s0 c
  have hc_lt : c < 456 := capLeafOf_lt (posAt input.positions ord)
  have hx22_c : s.getReg .x22 = BitVec.ofNat 64 c := hx22
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 262 capAddrInstrs s (by decide) hcode_capAddr hpure_capAddr hpc
  let s1 := runInstrs s capAddrInstrs
  have hs1 : StepsTo oracle s s1 5 0 [] := hs1
  have hpc1 : s1.pc = pcWord 267 := hpc1
  have hmem1' : s1.mem = s.mem := hmem1
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
    have hcomp : (8192#64 : Word) + ((BitVec.ofNat 64 c + (BitVec.ofNat 64 c >>> 1)) <<< 5) =
        BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [bv64_shr c 1 (by omega), Nat.pow_one, bv64_add, bv64_shl _ 5 (by omega)]
      change BitVec.ofNat 64 8192 + BitVec.ofNat 64 ((c + c / 2) * 32) = _
      rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by unfold gapOffset; omega)
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22_c, hfix.x19,
      show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide] using hcomp
  have hx29_1 : s1.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    have hcomp : (4096#64 : Word) + BitVec.ofNat 64 c = BitVec.ofNat 64 (4096 + c) := by
      change BitVec.ofNat 64 4096 + BitVec.ofNat 64 c = _; exact bv64_add 4096 c
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22_c, hfix.x18] using hcomp
  have hreg1 : ∀ r, r ≠ .x6 → r ≠ .x28 → r ≠ .x29 → s1.getReg r = s.getReg r :=
    fun r h6 h28 h29 => by
      simp only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h29.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  -- pc[267]: LBU x7, 0(x29)
  have ha267 : s1.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_1, se12_0, BitVec.add_zero]
  have hv267 : memoryArgumentsValid s1 (.LBU .x7 .x29 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha267]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst267 := step_ordinary oracle s1 267 (.LBU .x7 .x29 0#12) (by decide) hpc1 checkInstr_267 (by intro h; cases h)
    (by simp [ordinaryStep, hv267])
  let s2 := execInstrBr s1 (.LBU .x7 .x29 0#12)
  have hpc2 : s2.pc = pcWord 268 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1'
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha267]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s1.getByte (BitVec.ofNat 64 (4096 + c)) = if marked then 1#8 else 0#8 := by
      simpa only [c, MachineState.getByte, MachineState.getMem, hmem1'] using hmark
    rw [hb, bool_byte_zeroExtend]
  have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s2.getReg r = s.getReg r :=
    fun r h6 h7 h28 h29 => by
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg1 r h6 h28 h29
  -- pc[268]: BNE x7, x0, pc[280]
  have hst268 := step_ordinary oracle s2 268 (.BNE .x7 .x0 48#13) (by decide) hpc2 checkInstr_268 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 7 0 [] := by simpa using hs1.trans (hst267.trans hst268)
  cases marked with
  | false =>
    have hpc3 : s3.pc = pcWord 269 := by
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
        (fun r h6 h7 h28 h29 => (hreg3s r).trans (hreg2 r h6 h7 h28 h29))
        hfix.x21 hx28_3 hx29_3 d14 hd14
    have hfix7 : CheckFixedRegs s7 :=
      hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    have hcur7 : ProofCursor s0 input.proof.length pOffNext tOffNext s7 :=
      hcur.of_agree (fun r hr => hreg7 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
    obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
      step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s7 hpc7 hfix7 hcur7
        ((hreg7 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
    exact .continued sFin 22 0 [] (by decide) (by decide)
      (by simpa using (hs03.trans hs7).trans hsFin)
      ⟨rfl, rfl, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hm7,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)).trans hv7,
       fun a ha hne hout => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout7 a ha hne hout,
       fun h => by cases h⟩
  | true =>
    have hpc3 : s3.pc = pcWord 280 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_268_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.setPC] using hmem2
    have hreg3 : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.getReg_setPC]
    have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [hreg3]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
    have hcmp := step_compare4 oracle 280 .x21 .x28 s3 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCmp hpc3
      ((hreg3 .x21).trans ((hreg2 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
      hx28_3 (by decide) (by unfold gapOffset; omega)
      (by unfold MEMORY_BYTES; omega) (by unfold gapOffset MEMORY_BYTES; omega)
    have hrb_s3_a : readBuffer s3 256 32 = d14 :=
      ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)).trans hd14
    have hrb_s3_b : readBuffer s3 (8192 + gapOffset c) 32 = readBuffer s (8192 + gapOffset c) 32 :=
      (MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)
    cases hcmp with
    | rejected k q tr hr hk hq hh =>
      rw [hrb_s3_a, hrb_s3_b] at hr
      exact .rejected (7 + k) q tr ⟨rfl, hr⟩ (by omega) hq
        (by simpa using hs03.halt hh)
    | continued s4 k q tr hk hq hs4 hp4 =>
      obtain ⟨rfl, rfl, heq_dig, hpc4, hmem4, hreg4⟩ := hp4
      rw [hrb_s3_a, hrb_s3_b] at heq_dig
      have hmem4s : s4.mem = s.mem := hmem4.trans hmem3
      have hreg4s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s4.getReg r = s.getReg r :=
        fun r h6 h7 h28 h29 => (hreg4 r h6 h7).trans ((hreg3 r).trans (hreg2 r h6 h7 h28 h29))
      have hfix4 : CheckFixedRegs s4 :=
        hfix.of_agree (fun r hr => hreg4s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
      have hcur4 : ProofCursor s0 input.proof.length pOffNext tOffNext s4 :=
        hcur.of_agree (fun r hr => hreg4s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
        step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s4 hpc4 hfix4 hcur4
          ((hreg4s .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg4s .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg4s .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
      have hmemFins : sFin.mem = s.mem := hmemFin.trans hmem4s
      exact .continued sFin (7 + k + 4) 0 [] (by omega) (by decide)
        (by simpa [Nat.add_assoc] using (hs03.trans hs4).trans hsFin)
        ⟨rfl, rfl, hpcFin, hfixFin, hcurFin, hx24Fin, hx8Fin, hx27Fin,
         by simpa [MachineState.getByte, MachineState.getMem, hmemFins] using hmark,
         by rw [(MemEqOutside.of_mem_eq hmemFins 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← heq_dig],
         fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmemFins],
         fun _ => hmemFins⟩

/-! #### Per-Position Loop Invariant and Induction (`pc[22] -> pc[296]`) -/

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
  posRecordOff input.positions n + tailBytes (posTailOff input.positions n) ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions j1) (posTailOff input.positions j1)
      (posAt input.positions j1) (valAt input j1)).evalLevel c96 14 =
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions j2) (posTailOff input.positions j2)
      (posAt input.positions j2) (valAt input j2)).evalLevel c96 14

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff input.positions n) (posTailOff input.positions n) s
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if n = input.positions.card then pcWord 296 else pcWord 22
  x24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * n)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (input.positions.card - n)
  mark14 : ∀ c < 456, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if posMarked14 input.positions n c then 1#8 else 0#8
  mark_hi_zero : ∀ a, 4096 + 456 ≤ a → a < 5120 → s.getByte (BitVec.ofNat 64 a) = 0#8
  val14_gap_zero : ∀ q < 228, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + 96 * q + 64 + b)) = 0#8
  val_hi_zero : ∀ a, 8192 + capValOff 15 ≤ a → a < 8192 + 44000 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  witnesses : ∀ j < n,
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness (submission.initialState .check input) input.proof.length
      (posRecordOff input.positions j) (posTailOff input.positions j) (posAt input.positions j) (valAt input j)
    pw.evalLevel c96 14 = readBuffer s (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) ∧
    ((posAt input.positions j).val / 3 ≠ FULL_TRIPLETS_0 → InTrace h768 oracle tr (pw.l0Input c96)) ∧
    (((posAt input.positions j).val / 3) / 3 ≠ FULL_TRIPLETS_1 → InTrace h768 oracle tr (pw.l1Input c96)) ∧
    (∀ prev, 2 ≤ prev → prev ≤ 13 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x)

private theorem binPathOff_mono (g1 : Nat) {a b : Nat} (hab : a ≤ b) :
    binPathOff g1 a ≤ binPathOff g1 b := by
  induction hab with
  | refl => exact le_refl _
  | step _ ih => simp only [binPathOff]; omega

/-- Combined binary climb across all three digest bands (`L2..L4` 256b, `L5..L8` 240b, `L9..L13` 238b),
`pc[159] -> pc[262]`, `≤ 2655` steps, `≤ 12` calls. -/
private theorem step_pos_bin_all (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 159)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord) + l1Bytes (posAt input.positions ord)) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((posAt input.positions ord).val / 3) / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl2 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 2) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 2655 12
      (input.proof.length < pOff + recordLen i + tailBytes (tOff + recordTailCount i))
      (fun s' q tr =>
        q ≤ 12 ∧
        s'.pc = pcWord 262 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + recordLen i) (tOff + recordTailCount i) s' ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6867478784 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 14 ∧
        ∀ prev, 2 ≤ prev → prev ≤ 13 → ∀ x ∈ pw.levelInput c96 prev, InTrace h768 oracle tr x) := by
  intro s0 c96 i pw
  let g1 := (i.val / 3) / 3
  have htb_step : tailBytes tOff ≤ tailBytes (tOff + recordTailCount i) := tailBytes_mono (by omega)
  have hbp3_le : binPathOff g1 3 ≤ binPathOff g1 12 := binPathOff_mono g1 (by decide)
  have hbp7_le : binPathOff g1 7 ≤ binPathOff g1 12 := binPathOff_mono g1 (by decide)
  have hrec_eq : recordLen i = 24 + l0Bytes i + l1Bytes i + binPathOff g1 12 := rfl
  have h1d0 := step_pos_bin256_loop h768 oracle input hvalid ord pOff tOff rem hord
    s hpc hfix hcur hhigh hx22 hx24 hx8 hx27 hl2
  refine PhaseOutcome.weaken (K1 := 685 + (865 + 1105)) (Q1 := 3 + (4 + 5)) ?_ (by decide) (by decide) id (fun _ _ _ h => h)
  refine h1d0.bind_dep (fun hlt => by
      change input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 3 + tailBytes tOff at hlt
      rw [hrec_eq]; omega)
    (fun s3a qD0 trD0 ⟨hqD0, hpcD0, hfixD0, hcurD0, houtD0, hx22D0, hx24D0, hx8D0, hx27D0, hx29D0, hl5D0, hgapD0, htrD0⟩ => by
      have hhighD0 : HighMemPreserved s0 s3a := hhigh.trans (houtD0.mono (by omega) (by omega))
      have h1d1 := step_pos_bin240_loop h768 oracle input hvalid ord pOff tOff rem hord
        s3a hpcD0 hfixD0 hcurD0 hhighD0 hx22D0 hx24D0 hx8D0 hx27D0 hx29D0 hl5D0 hgapD0
      refine h1d1.bind_dep (fun hlt => by
          change input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 7 + tailBytes tOff at hlt
          rw [hrec_eq]; omega)
        (fun s3b qD1 trD1 ⟨hqD1, hpcD1, hfixD1, hcurD1, houtD1, hx22D1, hx24D1, hx8D1, hx27D1, hx29D1, hl9D1, hgapD1, htrD1⟩ => by
          have hhighD1 : HighMemPreserved s0 s3b := hhighD0.trans (houtD1.mono (by omega) (by omega))
          have h1d2 := step_pos_bin238_loop h768 oracle input hvalid ord pOff tOff rem hord
            s3b hpcD1 hfixD1 hcurD1 hhighD1 hx22D1 hx24D1 hx8D1 hx27D1 hx29D1 hl9D1 hgapD1
          refine h1d2.weaken (by decide) (by decide) id ?_
          rintro s4 qD2 trD2 ⟨hqD2, hpcD2, hfixD2, hcurD2, houtD2, hx22D2, hx24D2, hx8D2, hx27D2, hd14D, htrD2⟩
          refine ⟨by omega, hpcD2, hfixD2, hcurD2,
            houtD0.trans ((houtD1.mono (by omega) (by omega)).trans (houtD2.mono (by omega) (by omega))),
            hx22D2, hx24D2, hx8D2, hx27D2, hd14D, ?_⟩
          intro prev hp1 hp2 x hx
          by_cases hp_lt5 : prev < 5
          · exact (htrD0 prev hp1 hp_lt5 x hx).append_left
          · by_cases hp_lt9 : prev < 9
            · exact ((htrD1 prev (by omega) hp_lt9 x hx).append_left).append_right
            · exact ((htrD2 prev (by omega) hp2 x hx).append_right).append_right))

/-- One full position iteration (`k < input.positions.card`), `PosLoopInv k -> PosLoopInv (k + 1)`. -/
private theorem step_pos_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (k : Nat) (hlt_k : k < input.positions.card)
    (sk : MachineState) (tr1 : CompressionReplies)
    (hinv_k : PosLoopInv h768 oracle input k sk tr1) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sk 3715 18
      (¬ PosConsistent c96 s0 input (k + 1))
      (fun s' q tr => q ≤ 18 ∧ PosLoopInv h768 oracle input (k + 1) s' (tr1 ++ tr)) := by
  intro s0 c96
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hpc_k : sk.pc = pcWord 22 := by
    have hne : k ≠ input.positions.card := by omega
    simpa only [hne, ite_false] using hinv_k.pc
  let pOff := posRecordOff input.positions k
  let tOff := posTailOff input.positions k
  let i := posAt input.positions k
  let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input k)
  let rem1 := input.positions.card - (k + 1)
  have hrem_eq : input.positions.card - k = rem1 + 1 := by omega
  have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
    rw [hinv_k.x27, hrem_eq]
  have htb_step : tailBytes tOff ≤ tailBytes (tOff + recordTailCount i) := tailBytes_mono (by omega)
  have h1a := step_pos_leaf h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
    sk hpc_k hinv_k.fixed hinv_k.cursor hinv_k.high hinv_k.x24 hinv_k.x8 hx27_k
  have hcan_leaf : input.proof.length < pOff + 24 + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
    intro hlt hcons
    have h1 := hcons.1
    rw [posRecordOff_succ, posTailOff_succ] at h1
    change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
    unfold recordLen at h1; omega
  refine PhaseOutcome.weaken
    (K1 := 190 + (420 + (420 + (2655 + 30)))) (Q1 := 4 + (1 + (1 + (12 + 0))))
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
      have hcan_l1 : input.proof.length < pOff + 24 + l0Bytes i + l1Bytes i + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
        intro hlt hcons
        have h1 := hcons.1
        rw [posRecordOff_succ, posTailOff_succ] at h1
        change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1
        unfold recordLen at h1; omega
      refine h1c.bind_dep hcan_l1 (fun s3 qC trC ⟨hqC, hpcC, hfixC, hcurC, houtC, hx22C, hx24C, hx8C, hx27C, hl2C, htrC⟩ => by
        have hhighC : HighMemPreserved s0 s3 := hhighB.trans (houtC.mono (by omega) (by omega))
        have h1d := step_pos_bin_all h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
          s3 hpcC hfixC hcurC hhighC hx22C hx24C hx8C hx27C hl2C
        have hcan_bin : input.proof.length < pOff + recordLen i + tailBytes (tOff + recordTailCount i) →
            ¬ PosConsistent c96 s0 input (k + 1) := by
          intro hlt hcons
          have h1 := hcons.1
          rw [posRecordOff_succ, posTailOff_succ] at h1
          change pOff + recordLen i + tailBytes (tOff + recordTailCount i) ≤ input.proof.length at h1; omega
        refine h1d.bind_dep hcan_bin (fun s4 qD trD ⟨hqD, hpcD, hfixD, hcurD, houtD, hx22D, hx24D, hx8D, hx27D, hd14D, htrD⟩ => by
          have hout_sk4 : MemEqOutside sk s4 256 448 :=
            houtA.trans ((houtB.mono (by omega) (by omega)).trans
              ((houtC.mono (by omega) (by omega)).trans (houtD.mono (by omega) (by omega))))
          have hc_lt : capLeafOf i < 456 := capLeafOf_lt i
          have hmark4 : s4.getByte (BitVec.ofNat 64 (4096 + capLeafOf i)) =
              if posMarked14 input.positions k (capLeafOf i) then 1#8 else 0#8 :=
            (hout_sk4 (4096 + capLeafOf i) (by omega) (by omega)).trans (hinv_k.mark14 (capLeafOf i) hc_lt)
          have h1e := step_pos_cap_store oracle input k (pOff + recordLen i) (tOff + recordTailCount i) rem1 hlt_k (by omega)
            s4 hpcD hfixD hcurD hx22D hx24D hx8D hx27D (posMarked14 input.positions k (capLeafOf i))
            hmark4 (pw.evalLevel c96 14) hd14D
          have hcan_dup : (posMarked14 input.positions k (capLeafOf i) = true ∧
              pw.evalLevel c96 14 ≠ readBuffer s4 (8192 + gapOffset (capLeafOf i)) 32) →
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
            · have hz : rem1 = 0 := Nat.sub_eq_zero_of_le (le_of_eq hdone.symm)
              simp only [hdone, hz, ite_true] at hpcE ⊢; exact hpcE
            · have hnz : rem1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hlt_k) hdone)
              simp only [hdone, hnz, ite_false] at hpcE ⊢; exact hpcE
          · intro c hc
            rw [posMarked14_succ]
            change s5.getByte (BitVec.ofNat 64 (4096 + c)) =
              if (posMarked14 input.positions k c || decide (capLeafOf i = c)) = true then 1#8 else 0#8
            by_cases heq : capLeafOf i = c
            · subst heq; simp only [decide_true, Bool.or_true, ite_true]; exact hmark5
            · simp only [heq, decide_false, Bool.or_false]
              have hpres := hmem_pres (4096 + c) (by omega) (by omega) (by omega) (by unfold gapOffset; omega)
              exact hpres.trans (hinv_k.mark14 c hc)
          · intro a ha1 ha2
            exact (hmem_pres a (by omega) (by omega) (by omega) (by unfold gapOffset; omega)).trans
              (hinv_k.mark_hi_zero a ha1 ha2)
          · intro q hq b hb
            have hdisj := gapOffset_disjoint_gap (capLeafOf i) q
            exact (hmem_pres (8192 + 96 * q + 64 + b) (by omega) (by omega) (by omega) (by omega)).trans
              (hinv_k.val14_gap_zero q hq b hb)
          · intro a ha1 ha2
            have h15 : capValOff 15 = 21888 := by decide
            have hgo : gapOffset (capLeafOf i) + 32 ≤ 21888 := by unfold gapOffset; omega
            exact (hmem_pres a (by omega) (by omega) (by omega) (by omega)).trans
              (hinv_k.val_hi_zero a ha1 ha2)
          · intro j hj
            by_cases hjk : j < k
            · obtain ⟨hw_val, hw_leaf, hw_l0, hw_l1, hw_bin⟩ := hinv_k.witnesses j hjk
              have hval_pres : readBuffer s5 (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 =
                  readBuffer sk (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 := by
                by_cases hsame : capLeafOf (posAt input.positions j) = capLeafOf i
                · have hm_true : posMarked14 input.positions k (capLeafOf i) = true := by
                    unfold posMarked14; rw [decide_eq_true_eq]; exact ⟨j, hjk, hsame⟩
                  have hm5 := hmeq5 hm_true
                  exact ((MemEqOutside.of_mem_eq hm5 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)).trans
                    (hout_sk4.readBuffer_eq (by unfold gapOffset; omega) (by unfold gapOffset; omega))
                · have hdisj := gapOffset_disjoint hsame
                  have hcj_lt : capLeafOf (posAt input.positions j) < 456 := capLeafOf_lt _
                  apply readBuffer_congr2; intro b hb
                  exact hmem_pres (8192 + gapOffset (capLeafOf (posAt input.positions j)) + b)
                    (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                    (by unfold gapOffset; omega) (by omega)
              refine ⟨hw_val.trans hval_pres.symm,
                fun x hx => (hw_leaf x hx).append_left,
                fun hf => (hw_l0 hf).append_left,
                fun hf => (hw_l1 hf).append_left,
                fun prev hp1 hp2 x hx => (hw_bin prev hp1 hp2 x hx).append_left⟩
            · have hjeq : j = k := by omega
              subst hjeq
              refine ⟨hval5.symm, ?_, ?_, ?_, ?_⟩
              · intro x hx
                exact (((htrA x hx).append_left).append_right)
              · intro hf
                exact ((((htrB hf).append_left).append_right).append_right)
              · intro hf
                exact (((((htrC hf).append_left).append_right).append_right).append_right)
              · intro prev hp1 hp2 x hx
                exact ((((((htrD prev hp1 hp2 x hx).append_left).append_right).append_right).append_right).append_right)))))

/-- Complete per-position verification loop (`pc[22]` -> `pc[296]`), `≤ 3715 * k` steps, `≤ 18 * k` calls. -/
theorem step_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (_hne : input.positions.card ≠ 0)
    (sInit : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sInit (3715 * input.positions.card) (18 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' q tr => q ≤ 18 * input.positions.card ∧ PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (3715 * n) (18 * n)
        (¬ PosConsistent c96 s0 input n)
        (fun s' q tr => q ≤ 18 * n ∧ PosLoopInv h768 oracle input n s' tr) := by
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
      rw [show 3715 * (k + 1) = 3715 * k + 3715 by omega,
        show 18 * (k + 1) = 18 * k + 18 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hstep := step_pos_iter h768 oracle input hvalid k (by omega) sk tr1 hinv_k
        exact hstep.weaken (le_refl _) (le_refl _) id (fun s' q2 tr2 ⟨hq2, hinv'⟩ => ⟨by omega, hinv'⟩))
  exact hind input.positions.card (le_refl _)

end CommitGolfCandidate
