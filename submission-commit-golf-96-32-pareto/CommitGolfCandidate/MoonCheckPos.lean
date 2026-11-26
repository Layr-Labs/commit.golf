import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the unified L0..L15 (238b) pure-binary loop, L16 cap-store,
and full per-position loop (`pc[139..197]`, `pc[34] -> pc[198]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_140_branch : pcWord 140 + signExtend13 48#13 = pcWord 152 := by decide
private theorem pc_151_jal : pcWord 151 + signExtend21 12#21 = pcWord 154 := by decide
private theorem pc_162_branch : pcWord 162 + signExtend13 8100#13 = pcWord 139 := by decide

private theorem shiftRight_div2 (a k : Nat) : (a >>> k) / 2 = a >>> (k + 1) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- One iteration (`step < 16`, level `l = step ∈ 0..15`) of the uniform 238b binary loop (`pc[139..162]`). -/
theorem step_pos_bin238_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (_hord : ord < input.positions.card) (hstep : step < 16)
    (s : MachineState) (hpc : s.pc = pcWord 139)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 15 + 29 * step) (tOff + step) s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 10603204576)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 ord)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff ord
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) step)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pCur := pOff + 15 + 29 * step
    let tCur := tOff + step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff ord i (valAt input ord)
    PhaseOutcome oracle s 216 1 (input.proof.length < pCur + 29 + tailBytes (tCur + 1))
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = (if step + 1 = 16 then pcWord 163 else pcWord 139) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
        s'.getReg .x15 = BitVec.ofNat 64 ord ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (step + 1) ∧
        readBuffer s' 320 32 = 0 ∧
        InTrace h768 oracle tr (pw.levelInput c96 step)) := by
  intro s0 c96 i pCur tCur pw
  have hplen_bd : input.proof.length ≤ 8239714016 := hvalid
  have hi_lt : i.val < 16777216 := i.isLt
  have hidx_lt : i.val >>> step < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  -- pc[139]: ANDI x7, x22, 1; pc[140]: BEQ x7, x0, pc[152]
  have hst139 := step_ordinary oracle s 139 (.ANDI .x7 .x22 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ANDI .x7 .x22 1#12)
  have hpc1 : s1.pc = pcWord 140 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx7_1 : s1.getReg .x7 = BitVec.ofNat 64 ((i.val >>> step) % 2) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, se12_1]
    exact bv64_and_one (i.val >>> step) (by omega)
  have hst140 := step_ordinary oracle s1 140 (.BEQ .x7 .x0 48#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BEQ .x7 .x0 48#13)
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  let sibD := pw.binSib step
  have hsibD_eq : sibD = proofDigest238 s0 input.proof.length (10603204576 + pCur) tCur := by
    simp only [sibD, pw, parsePartialWitness, hstep, ite_true, pCur, tCur, Nat.add_assoc]
  let curD := pw.evalLevel c96 step
  let inpL : BitVec 768 :=
    if (i.val >>> step) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
  have heval_next : pw.evalLevel c96 (step + 1) = mask238 (c96 inpL) := by
    change maskLevel (step + 1) (c96 inpL) = _
    unfold maskLevel
    rw [if_neg (by omega)]
  have hlinp : pw.levelInput c96 step = inpL := rfl
  -- Common compress + mask238 + footer at pc[154..162]
  have hcall154 : ∀ (s154 : MachineState) (kA : Nat),
      kA ≤ 205 →
      StepsTo oracle s2 s154 kA 0 [] →
      s154.pc = pcWord 154 →
      CheckFixedRegs s154 →
      ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s154 →
      MemEqOutside s s154 256 320 →
      s154.getReg .x14 = BitVec.ofNat 64 10603204576 →
      s154.getReg .x15 = BitVec.ofNat 64 ord →
      s154.getReg .x22 = BitVec.ofNat 64 (i.val >>> step) →
      s154.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) →
      s154.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) →
      s154.getReg .x27 = BitVec.ofNat 64 rem →
      s154.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) →
      s154.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) →
      readBuffer s154 256 96 = inpL →
      readBuffer s154 320 32 = 0 →
      PhaseOutcome oracle s 216 1 (input.proof.length < pCur + 29 + tailBytes (tCur + 1))
        (fun s' q tr =>
          q = 1 ∧
          s'.pc = (if step + 1 = 16 then pcWord 163 else pcWord 139) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
          s'.getReg .x15 = BitVec.ofNat 64 ord ∧
          s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (step + 1) ∧
          readBuffer s' 320 32 = 0 ∧
          InTrace h768 oracle tr (pw.levelInput c96 step)) := by
    intro s154 kA hkA hmidA hpc154 hfix154 hcur154 hout154 h14 h15 h22 h24 h8 h27 h29 h30 hinp154 hgap154
    have hst154 := step_ordinary oracle s154 154 (.ADDI .x10 .x21 0#12) (by decide) hpc154 rfl (by intro h; cases h) rfl
    let s155 := execInstrBr s154 (.ADDI .x10 .x21 0#12)
    have hpc155 : s155.pc = pcWord 155 := by simp only [s155, execInstrBr, MachineState.setPC, hpc154, pcWord_add_four]
    have hst155 := step_ordinary oracle s155 155 (.ADDI .x12 .x21 0#12) (by decide) hpc155 rfl (by intro h; cases h) rfl
    let s156 := execInstrBr s155 (.ADDI .x12 .x21 0#12)
    have hpc156 : s156.pc = pcWord 156 := by simp only [s156, execInstrBr, MachineState.setPC, hpc155, pcWord_add_four]
    have hmem156 : s156.mem = s154.mem := by simp [s156, s155, execInstrBr, mem_setPC, mem_setReg]
    have hreg156 : ∀ r, r ≠ .x10 → r ≠ .x12 → s156.getReg r = s154.getReg r := fun r h10 h12 => by
      simp only [s156, s155, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
    have hx10_156 : s156.getReg .x10 = 256#64 := by
      simp only [s156, s155, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hfix154.x21, se12_0, BitVec.add_zero]
    have hx12_156 : s156.getReg .x12 = 256#64 := by
      simp only [s156, s155, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
        hfix154.x21, se12_0, BitVec.add_zero]
    have hec := step_ecall_compress h768 oracle s156 156 256 256 (by decide) hpc156 rfl
      ((hreg156 .x5 (by decide) (by decide)).trans hfix154.x5)
      ((hreg156 .x11 (by decide) (by decide)).trans hfix154.x11)
      ((hreg156 .x13 (by decide) (by decide)).trans hfix154.x13)
      hx10_156 hx12_156 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
    rw [(MemEqOutside.of_mem_eq hmem156 0 0).readBuffer_eq (by omega) (by omega), hinp154] at hec
    let s157 := writeBits s156 (BitVec.ofNat 64 256) (c96 inpL)
    have hpc157 : s157.pc = pcWord 157 := by simp only [s157, writeBits, MachineState.setPC, hpc156, pcWord_add_four]
    have hreg157 : ∀ r, r ≠ .x10 → r ≠ .x12 → s157.getReg r = s154.getReg r := fun r h10 h12 =>
      (writeBits_register s156 _ _ r).trans (hreg156 r h10 h12)
    -- pc[157..159]: mask238
    obtain ⟨s160, hs160, hpc160, hreg160, hdig160, hout160⟩ :=
      step_mask238 oracle 157 .x21 s157 256 (by decide) (by decide) rfl rfl rfl hpc157
        ((hreg157 .x21 (by decide) (by decide)).trans hfix154.x21)
        ((hreg157 .x9 (by decide) (by decide)).trans hfix154.x9)
        (by decide) (by unfold MEMORY_BYTES; omega)
    have hreg160_s : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s160.getReg r = s154.getReg r := fun r h6 h10 h12 =>
      (hreg160 r h6).trans (hreg157 r h10 h12)
    have hdig_eq : readBuffer s160 256 32 = pw.evalLevel c96 (step + 1) := by
      rw [heval_next, hdig160, writeBits_readBuffer_digest]
    have hgap160 : readBuffer s160 320 32 = 0 := by
      rw [hout160.readBuffer_eq (by omega) (by omega),
        (MemEqOutside_writeBits_digest s156 256 _ (by omega)).readBuffer_eq (by omega) (by omega),
        (MemEqOutside.of_mem_eq hmem156 0 0).readBuffer_eq (by omega) (by omega), hgap154]
    -- pc[160..162]: SRLI x22, x22, 1; ADDI x29, x29, 32; BNE x29, x30, pc[139]
    have hst160 := step_ordinary oracle s160 160 (.SRLI .x22 .x22 1#6) (by decide) hpc160 rfl (by intro h; cases h) rfl
    let s161 := execInstrBr s160 (.SRLI .x22 .x22 1#6)
    have hpc161 : s161.pc = pcWord 161 := by simp only [s161, execInstrBr, MachineState.setPC, hpc160, pcWord_add_four]
    have hx22_161 : s161.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) := by
      simp only [s161, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg160_s .x22 (by decide) (by decide) (by decide), h22,
        show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr _ 1 (by omega), Nat.pow_one, shiftRight_div2]
    have hst161 := step_ordinary oracle s161 161 (.ADDI .x29 .x29 32#12) (by decide) hpc161 rfl (by intro h; cases h) rfl
    let s162 := execInstrBr s161 (.ADDI .x29 .x29 32#12)
    have hpc162 : s162.pc = pcWord 162 := by simp only [s162, execInstrBr, MachineState.setPC, hpc161, pcWord_add_four]
    have hmem162 : s162.mem = s160.mem := by simp [s162, s161, execInstrBr, mem_setPC, mem_setReg]
    have hx29_162 : s162.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) := by
      simp only [s162, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide)]
      simp only [s161, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x29),
        hreg160_s .x29 (by decide) (by decide) (by decide), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_162 : s162.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
      simp only [s162, s161, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x30),
        hreg160_s .x30 (by decide) (by decide) (by decide), h30]
    have hx22_162 : s162.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) := by
      simp only [s162, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x22), hx22_161]
    have hreg162 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x29 → s162.getReg r = s154.getReg r :=
      fun r h6 h10 h12 h22r h29r => by
        simp only [s162, s161, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h29r.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h22r.symm, hreg160_s r h6 h10 h12]
    obtain ⟨sFin, hst162, hpcFin_raw, hregFin_162, hmemFin_162⟩ :=
      step_bne_reg oracle 162 139 .x29 .x30 8100#13 (by decide) rfl pc_162_branch s162
        (68719475936 + 32 * (step + 1)) (68719475936 + 32 * 16) (by omega) (by omega) hpc162 hx29_162 hx30_162
    have hpcFin : sFin.pc = if step + 1 = 16 then pcWord 163 else pcWord 139 := by
      rw [hpcFin_raw]; congr 1; exact propext (by omega)
    have hmemFin : sFin.mem = s160.mem := hmemFin_162.trans hmem162
    have hregFin : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x29 → sFin.getReg r = s154.getReg r :=
      fun r h6 h10 h12 h22r h29r => (hregFin_162 r).trans (hreg162 r h6 h10 h12 h22r h29r)
    have hout_all : MemEqOutside s sFin 256 320 :=
      hout154.trans ((MemEqOutside.of_mem_eq hmem156 256 320).trans
        (((MemEqOutside_writeBits_digest s156 256 _ (by omega)).mono (by omega) (by omega)).trans
          ((hout160.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmemFin 256 320))))
    have htot := (((hst139.trans hst140).trans hmidA).trans (((hst154.trans hst155).trans hec).trans hs160)).trans
      ((hst160.trans hst161).trans hst162)
    refine .continued sFin (2 + kA + 9) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
      (htot.eq_of rfl (by omega) (by decide) (by simp only [List.nil_append, List.append_nil]; rfl))
      ⟨rfl, hpcFin,
       hfix154.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
         (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       hcur154.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
         (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
       hout_all,
       (hregFin .x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14,
       (hregFin .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15,
       (hregFin_162 .x22).trans hx22_162,
       (hregFin .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24,
       (hregFin .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8,
       (hregFin .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27,
       (hregFin_162 .x29).trans hx29_162,
       (hregFin .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hdig_eq,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hgap160,
       by rw [hlinp]; exact InTrace.singleton h768 oracle inpL⟩
  by_cases heven : (i.val >>> step) % 2 = 0
  · -- Even: pc[152..153] -> pc[154]
    have hx7z : s1.getReg .x7 = 0#64 := by rw [hx7_1, heven]
    have hpc2 : s2.pc = pcWord 152 := by
      simp only [s2, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc1]
      exact pc_140_branch
    have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x7 → s2.getReg r = s.getReg r := fun r h7 => by
      have : s2.getReg r = s1.getReg r := by
        simp only [s2, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
      rw [this]; simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
    have hst152 := step_ordinary oracle s2 152 (.ADDI .x12 .x21 32#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x12 .x21 32#12)
    have hpc3 : s3.pc = pcWord 153 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h7 h12 => by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg2 r h7]
    have hx12_3 : s3.getReg .x12 = BitVec.ofNat 64 288 := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x21 (by decide), hfix.x21, se12_32]; decide
    have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 153 s3 pCur tCur 288
      (by decide) rfl hpc3
      (hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (hhigh.trans (MemEqOutside.of_mem_eq hmem3 0 4294971392)) hx12_3 (by omega)
    cases hread with
    | rejected kR qR trR hrR hkR hqR hhR =>
      have htot := ((hst139.trans hst140).trans hst152).halt hhR
      exact .rejected (3 + kR) qR trR hrR (by omega) (by omega)
        (by simpa only [Nat.zero_add, List.nil_append] using htot)
    | continued s4 kR qR trR hkR hqR hs4 hp4 =>
      obtain ⟨rfl, rfl, hpc4, hcur4, hreg4, hdigR, hout4⟩ := hp4
      have hreg4_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s4.getReg r = s.getReg r := fun r h1 h3 h4 h6 h7 h12 h25 h31 =>
        (hreg4 r h1 h3 h4 h6 h7 h12 h25 h31).trans (hreg3 r h7 h12)
      have hout_all : MemEqOutside s s4 288 320 :=
        (MemEqOutside.of_mem_eq hmem3 288 320).trans hout4
      have hgap4 : readBuffer s4 320 32 = 0 :=
        (hout_all.readBuffer_eq (by omega) (by omega)).trans hgap
      have hinp4 : readBuffer s4 256 96 = inpL := by
        rw [readBuffer_binary_of_zero_gap s4 256 hgap4,
          (hout_all.readBuffer_eq (by omega) (by omega)).trans hcurDig, hdigR, ← hsibD_eq]
        simp only [inpL, heven, ite_true]; rfl
      exact hcall154 s4 (1 + kR) (by omega)
        ((hst152.trans hs4).eq_of rfl rfl rfl (by simp only [List.nil_append]))
        hpc4
        (hfix.of_agree (fun r hr => hreg4_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        hcur4 (hout_all.mono (by omega) (by omega))
        ((hreg4_s .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14)
        ((hreg4_s .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15)
        ((hreg4_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg4_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg4_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg4_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg4_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg4_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        hinp4 hgap4
  · -- Odd: pc[141..151] -> pc[154]
    have hodd : (i.val >>> step) % 2 = 1 := by omega
    have hx7o : s1.getReg .x7 = 1#64 := by rw [hx7_1, hodd]
    have hpc2 : s2.pc = pcWord 141 := by
      simp only [s2, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x7 → s2.getReg r = s.getReg r := fun r h7 => by
      have : s2.getReg r = s1.getReg r := by
        simp only [s2, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
      rw [this]; simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
    have hcC : ∀ j < 4,
        checkInstr (141 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
        checkInstr (141 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s3, hs3, hpc3, hreg3, hcopy3, hout3⟩ :=
      step_copy_dwords oracle 141 4 .x21 .x21 0 32 s2 256 256
        (by decide) (by decide) (by decide) (by decide) (by decide) hcC hpc2
        ((hreg2 .x21 (by decide)).trans hfix.x21)
        ((hreg2 .x21 (by decide)).trans hfix.x21)
        (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by decide)
    have hst149 := step_ordinary oracle s3 149 (.ADDI .x12 .x21 0#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x12 .x21 0#12)
    have hpc4 : s4.pc = pcWord 150 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s3.mem := by simp [s4, execInstrBr, mem_setPC, mem_setReg]
    have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → s4.getReg r = s.getReg r := fun r h6 h7 h12 => by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg3 r h6]
      exact hreg2 r h7
    have hx12_4 : s4.getReg .x12 = BitVec.ofNat 64 256 := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x21 (by decide),
        hreg2 .x21 (by decide), hfix.x21, se12_0, BitVec.add_zero]
    have hhigh4 : HighMemPreserved s0 s4 :=
      hhigh.trans ((MemEqOutside.of_mem_eq hmem2 0 4294971392).trans
        ((hout3.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem4 0 4294971392)))
    have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 150 s4 pCur tCur 256
      (by decide) rfl hpc4
      (hcur.of_agree (fun r hr => hreg4 r (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      hhigh4 hx12_4 (by omega)
    cases hread with
    | rejected kR qR trR hrR hkR hqR hhR =>
      have htot := ((hst139.trans hst140).trans (hs3.trans hst149)).halt hhR
      have hkeq : 1 + 1 + (2 * 4 + 1) + kR = 11 + kR := by omega
      exact .rejected (11 + kR) qR trR hrR (by omega) (by omega)
        (by simpa only [Nat.zero_add, List.nil_append, hkeq] using htot)
    | continued s5 kR qR trR hkR hqR hs5 hp5 =>
      obtain ⟨rfl, rfl, hpc5, hcur5, hreg5, hdigL, hout5⟩ := hp5
      have hst151 := step_ordinary oracle s5 151 (.JAL .x0 12#21) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.JAL .x0 12#21)
      have hpc6 : s6.pc = pcWord 154 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5]; exact pc_151_jal
      have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
      have hreg6_5 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
        simp [s6, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
      have hreg6_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s6.getReg r = s.getReg r := fun r h1 h3 h4 h6 h7 h12 h25 h31 =>
        (hreg6_5 r).trans ((hreg5 r h1 h3 h4 h6 h7 h12 h25 h31).trans (hreg4 r h6 h7 h12))
      have hout_46 : MemEqOutside s4 s6 256 288 := hout5.trans (MemEqOutside.of_mem_eq hmem6 256 288)
      have hout_all : MemEqOutside s s6 256 320 :=
        (MemEqOutside.of_mem_eq hmem2 256 320).trans
          ((hout3.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem4 256 320).trans (hout_46.mono (by omega) (by omega))))
      have hgap6 : readBuffer s6 320 32 = 0 :=
        (hout_all.readBuffer_eq (by omega) (by omega)).trans hgap
      have hinp6 : readBuffer s6 256 96 = inpL := by
        rw [readBuffer_binary_of_zero_gap s6 256 hgap6]
        have hL : readBuffer s6 256 32 = sibD := by
          rw [(MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega), hdigL, hsibD_eq]
        have hR : readBuffer s6 288 32 = curD := by
          have hcurD : readBuffer s 256 32 = curD := hcurDig
          rw [hout_46.readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega), ← hcurD]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy3 j hj
          simp only [Nat.add_zero] at hc
          rw [show 288 + j = 256 + 32 + j by omega, hc]
          simp [MachineState.getByte, MachineState.getMem, hmem2]
        rw [hL, hR]; simp only [inpL, heven, ite_false]
      exact hcall154 s6 (9 + kR + 1) (by omega)
        (((hs3.trans hst149).trans (hs5.trans hst151)).eq_of rfl (by omega) rfl (by simp only [List.append_nil]))
        hpc6
        (hfix.of_agree (fun r hr => hreg6_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (hcur5.of_agree (fun r _ => hreg6_5 r))
        hout_all
        ((hreg6_s .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14)
        ((hreg6_s .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15)
        ((hreg6_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg6_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg6_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg6_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg6_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg6_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        hinp6 hgap6

/-- Phase 1C: complete L0..L15 (uniform 238b) binary loop (`pc[139]` -> `pc[163]`), ≤ 3456 steps, 16 calls. -/
theorem step_pos_bin238_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 139)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 15) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 10603204576)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 ord)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> 0))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 0))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16))
    (hl0 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff ord
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 0)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff ord i (valAt input ord)
    PhaseOutcome oracle s 3456 16 (input.proof.length < pOff + 479 + tailBytes (tOff + 16))
      (fun s' q tr =>
        q = 16 ∧
        s'.pc = pcWord 163 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 479) (tOff + 16) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
        s'.getReg .x15 = BitVec.ofNat 64 ord ∧
        s'.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 16 ∧
        ∀ prev < 16, InTrace h768 oracle tr (pw.levelInput c96 prev)) := by
  intro s0 c96 i pw
  have hloop : ∀ n ≤ 16,
      PhaseOutcome oracle s (216 * n) n
        (input.proof.length < pOff + 15 + 29 * n + tailBytes (tOff + n))
        (fun s' q tr =>
          q = n ∧
          s'.pc = (if n = 16 then pcWord 163 else pcWord 139) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 15 + 29 * n) (tOff + n) s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
          s'.getReg .x15 = BitVec.ofNat 64 ord ∧
          s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> n) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * n) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 n ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev < n, InTrace h768 oracle tr (pw.levelInput c96 prev)) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued s 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s)
        ⟨rfl, by simpa using hpc, hfix, by simpa using hcur, MemEqOutside.refl s 256 320,
         hx14, hx15, hx22, hx24, hx8, hx27, hx29, hx30, hl0, hgap, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      have htb_m : tailBytes (tOff + k) ≤ tailBytes (tOff + (k + 1)) := tailBytes_mono (by omega)
      rw [show 216 * (k + 1) = 216 * k + 216 by omega]
      refine (ih (by omega)).bind_dep (by omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx14_k, hx15_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne16 : k ≠ 16 := by omega
          simp only [hne16, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk := hhigh.trans (hout_k.mono (by omega) (by omega))
          have hstep_k := step_pos_bin238_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx14_k hx15_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega) (by intro h; rw [Nat.add_assoc tOff k 1] at h; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx14', hx15', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', ?_, hout_k.trans hout', hx14', hx15', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          · simpa only [show pOff + 15 + 29 * (k + 1) = pOff + 15 + 29 * k + 29 by omega,
              show tOff + (k + 1) = tOff + k + 1 by omega] using hcur'
          · intro prev hp
            by_cases hprev : prev < k
            · exact (htr_k prev hprev).append_left
            · have : prev = k := by omega
              subst this; exact htr'.append_right)
  refine (hloop 16 (by decide)).weaken (by decide) (by decide) (by omega) ?_
  rintro s' q tr ⟨hq', hpc', hfix', hcur', hout', hx14', hx15', hx22', hx24', hx8', hx27', _, _, hdig', _, htr'⟩
  exact ⟨hq', by simpa using hpc', hfix',
    by simpa only [show pOff + 15 + 29 * 16 = pOff + 479 by omega] using hcur',
    hout', hx14', hx15', hx22', hx24', hx8', hx27', hdig', htr'⟩

/-! #### Phase 1D and Full Per-Position Loop (`pc[163..197]`, `pc[34] -> pc[198]`) -/

theorem gapOffset_disjoint {a b : Nat} (hne : a ≠ b) :
    gapOffset a + 32 ≤ gapOffset b ∨ gapOffset b + 32 ≤ gapOffset a := by
  unfold gapOffset; omega

theorem gapOffset_disjoint_gap (c q : Nat) :
    gapOffset c + 32 ≤ 96 * q + 64 ∨ 96 * q + 96 ≤ gapOffset c := by
  unfold gapOffset; omega

private def capAddrInstrs : List Instr :=
  [.SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6,
   .SLLI .x6 .x6 5#6, .ADD .x28 .x19 .x6, .ADD .x29 .x18 .x22]

private theorem pc_169_branch : pcWord 169 + signExtend13 48#13 = pcWord 181 := by decide
private theorem pc_180_jal : pcWord 180 + signExtend21 52#21 = pcWord 193 := by decide
private theorem pc_197_branch : pcWord 197 + signExtend13 7540#13 = pcWord 34 := by decide
private theorem checkInstr_168 : checkInstr 168 = .base (.LBU .x7 .x29 0#12) := rfl
private theorem checkInstr_169 : checkInstr 169 = .base (.BNE .x7 .x0 48#13) := rfl
private theorem checkInstr_170 : checkInstr 170 = .base (.ADDI .x7 .x0 1#12) := rfl
private theorem checkInstr_171 : checkInstr 171 = .base (.SB .x29 .x7 0#12) := rfl
private theorem checkInstr_180 : checkInstr 180 = .base (.JAL .x0 52#21) := rfl
private theorem checkInstr_193 : checkInstr 193 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_194 : checkInstr 194 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_195 : checkInstr 195 = .base (.ADDI .x15 .x15 1#12) := rfl
private theorem checkInstr_196 : checkInstr 196 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_197 : checkInstr 197 = .base (.BNE .x27 .x0 7540#13) := rfl

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

private theorem se12_1_ofNat : signExtend12 1#12 = BitVec.ofNat 64 1 :=
  signExtend12_ofNat_lt2048 1 (by decide)

private theorem hcode_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    checkInstr (163 + j) = .base (capAddrInstrs[j]'hj) := by
  intro j hj; have hj' : j < 5 := hj; interval_cases j <;> rfl

private theorem hpure_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    Instruction.base (capAddrInstrs[j]'hj) ≠ .base .ECALL ∧
    ∀ st, ordinaryStep st (.base (capAddrInstrs[j]'hj)) = some (execInstrBr st (capAddrInstrs[j]'hj)) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).mem = st.mem := by
  intro j hj; have hj' : j < 5 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩

private theorem hcode_capCopy : ∀ j < 4,
    checkInstr (172 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
    checkInstr (172 + 2 * j + 1) = .base (.SD .x28 .x6 (BitVec.ofNat 12 (0 + 8 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem hcode_capCmp : ∀ j < 4,
    checkInstr (181 + 3 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (181 + 3 * j + 1) = .base (.LD .x7 .x28 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (181 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (261 - (181 + 3 * j + 2))))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

private theorem step_tail_193 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 193)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 194 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 193 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_193
     (by intro h; cases h) (ordinaryStep_ADDI s .x24 .x24 8#12),
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 193)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (6174019552 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 6174019552 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_194 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 194)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (6308237280 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 195 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (6308237280 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 194 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_194
     (by intro h; cases h) (ordinaryStep_ADDI s .x8 .x8 256#12),
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 194)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (6308237280 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 6308237280 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_195 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 195)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 ord) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 196 ∧ s'.mem = s.mem ∧
      s'.getReg .x15 = BitVec.ofNat 64 (ord + 1) ∧
      ∀ r, r ≠ .x15 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x15 .x15 1#12),
   step_ordinary oracle s 195 (.ADDI .x15 .x15 1#12) (by decide) hpc checkInstr_195
     (by intro h; cases h) (ordinaryStep_ADDI s .x15 .x15 1#12),
   (execInstrBr_ADDI_pc s .x15 .x15 1#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 195)),
   execInstrBr_ADDI_mem s .x15 .x15 1#12,
   (execInstrBr_ADDI_getReg_eq s .x15 .x15 1#12 (by decide)).trans
     ((congrArg (· + signExtend12 1#12) h15).trans
       ((congrArg (BitVec.ofNat 64 ord + ·) se12_1_ofNat).trans (bv64_add ord 1))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x15 .x15 1#12 r hr.symm⟩

private theorem step_tail_196 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 196)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 197 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 196 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_196
     (by intro h; cases h) (ordinaryStep_ADDI s .x27 .x27 4095#12),
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 196)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_pos_cap_store_tail (oracle : Oracle) (s0 : MachineState)
    (proofLen ord pOffNext tOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s193 : MachineState) (hpc193 : s193.pc = pcWord 193)
    (hfix193 : CheckFixedRegs s193)
    (hcur193 : ProofCursor s0 proofLen pOffNext tOffNext s193)
    (h14 : s193.getReg .x14 = BitVec.ofNat 64 10603204576)
    (h15 : s193.getReg .x15 = BitVec.ofNat 64 ord)
    (h24 : s193.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord))
    (h8  : s193.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (h27 : s193.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s193 sFin 5 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 198 else pcWord 34) ∧
      CheckFixedRegs sFin ∧
      ProofCursor s0 proofLen pOffNext tOffNext sFin ∧
      sFin.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
      sFin.getReg .x15 = BitVec.ofNat 64 (ord + 1) ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * (ord + 1)) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s193.mem := by
  obtain ⟨s194, hs1, hpc194, hmem1, hx24_1, hreg1⟩ := step_tail_193 oracle ord s193 hpc193 h24
  obtain ⟨s195, hs2, hpc195, hmem2, hx8_2, hreg2⟩ :=
    step_tail_194 oracle ord s194 hpc194 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s196, hs3, hpc196, hmem3, hx15_3, hreg3⟩ :=
    step_tail_195 oracle ord s195 hpc195 ((hreg2 .x15 (by decide)).trans ((hreg1 .x15 (by decide)).trans h15))
  obtain ⟨s197, hs4, hpc197, hmem4, hx27_4, hreg4⟩ :=
    step_tail_196 oracle rem1 s196 hpc196
      ((hreg3 .x27 (by decide)).trans ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27)))
  obtain ⟨sFin, hs5, hpcFin, hreg5, hmem5⟩ :=
    step_bne_reg oracle 197 34 .x27 .x0 7540#13 (by decide) checkInstr_197 pc_197_branch s197
      rem1 0 (by omega) (by omega) hpc197 hx27_4 (getReg_x0 s197)
  have hsteps : StepsTo oracle s193 sFin 5 0 [] :=
    ((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).eq_of rfl rfl rfl rfl
  have hmemFin : sFin.mem = s193.mem := hmem5.trans (hmem4.trans (hmem3.trans (hmem2.trans hmem1)))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x15 → r ≠ .x27 → sFin.getReg r = s193.getReg r :=
    fun r h24r h8r h15r h27r =>
      (hreg5 r).trans ((hreg4 r h27r).trans ((hreg3 r h15r).trans ((hreg2 r h8r).trans (hreg1 r h24r))))
  exact ⟨sFin, hsteps, hpcFin,
    hfix193.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hcur193.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    (hregFin .x14 (by decide) (by decide) (by decide) (by decide)).trans h14,
    (hreg5 .x15).trans ((hreg4 .x15 (by decide)).trans hx15_3),
    (hreg5 .x24).trans ((hreg4 .x24 (by decide)).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1))),
    (hreg5 .x8).trans ((hreg4 .x8 (by decide)).trans ((hreg3 .x8 (by decide)).trans hx8_2)),
    (hreg5 .x27).trans hx27_4, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 256)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 170) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 256#64)
    (hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c))
    (hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c))
    (d16 : Digest) (hd16 : readBuffer s 256 32 = d16) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 193 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
      readBuffer s7 (8192 + gapOffset c) 32 = d16 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
        (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst170 := step_ordinary oracle s3 170 (.ADDI .x7 .x0 1#12) (by decide) hpc3 checkInstr_170 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 171 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx29_4 : s4.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha171 : s4.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_4, se12_0, BitVec.add_zero]
  have hv171 : memoryArgumentsValid s4 (.SB .x29 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha171]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst171 := step_ordinary oracle s4 171 (.SB .x29 .x7 0#12) (by decide) hpc4 checkInstr_171 (by intro h; cases h)
    (by simp [ordinaryStep, hv171])
  let s5 := execInstrBr s4 (.SB .x29 .x7 0#12)
  have hpc5 : s5.pc = pcWord 172 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (4096 + c)) 1#8).getByte q := by
    intro q
    simp only [s5, execInstrBr, ha171, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
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
    step_copy_dwords oracle 172 4 .x21 .x28 0 0 s5 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCopy hpc5
      ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide)).trans hx21)
      hx28_5 (by decide) (by omega) (by unfold MEMORY_BYTES; omega) (by omega) (by omega)
  have hst180 := step_ordinary oracle s6 180 (.JAL .x0 52#21) (by decide) hpc6 checkInstr_180 (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 193 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_180_jal
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
  have hv7 : readBuffer s7 (8192 + gapOffset c) 32 = d16 := by
    rw [(MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← hd16]
    apply readBuffer_congr2; intro j hj
    have hc := hcopy6 j hj
    simp only [Nat.add_zero] at hc
    rw [hc]
    exact hout5 (256 + j) (by omega) (by omega)
  refine ⟨s7, by simpa using ((hst170.trans hst171).trans hs6).trans hst180, hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1D: store or duplicate-check cap leaf at L16 and advance loop counters (`pc[163..197]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext tOffNext rem1 : Nat) (_hord : ord < input.positions.card)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 163)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOffNext tOffNext s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 10603204576)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 ord)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (capLeafOf (posAt input.positions ord)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1))
    (marked : Bool)
    (hmark : s.getByte (BitVec.ofNat 64 (4096 + capLeafOf (posAt input.positions ord))) =
      if marked then 1#8 else 0#8)
    (d16 : Digest) (hd16 : readBuffer s 256 32 = d16) :
    let s0 := submission.initialState .check input
    let c := capLeafOf (posAt input.positions ord)
    PhaseOutcome oracle s 31 0
      (marked = true ∧ d16 ≠ readBuffer s (8192 + gapOffset c) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = (if rem1 = 0 then pcWord 198 else pcWord 34) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pOffNext tOffNext s' ∧
        s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
        s'.getReg .x15 = BitVec.ofNat 64 (ord + 1) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * (ord + 1)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
        readBuffer s' (8192 + gapOffset c) 32 = d16 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
          (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro s0 c
  have hc_lt : c < 256 := capLeafOf_lt (posAt input.positions ord)
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 163 capAddrInstrs s (by decide) hcode_capAddr hpure_capAddr hpc
  let s1 := runInstrs s capAddrInstrs
  have hs1 : StepsTo oracle s s1 5 0 [] := hs1
  have hpc1 : s1.pc = pcWord 168 := hpc1
  have hmem1' : s1.mem = s.mem := hmem1
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
    have hcomp : (8192#64 : Word) + ((BitVec.ofNat 64 c + (BitVec.ofNat 64 c >>> 1)) <<< 5) =
        BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [bv64_shr c 1 (by omega), Nat.pow_one, bv64_add, bv64_shl _ 5 (by omega)]
      change BitVec.ofNat 64 8192 + BitVec.ofNat 64 ((c + c / 2) * 32) = _
      rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by unfold gapOffset; omega)
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22, hfix.x19,
      show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide] using hcomp
  have hx29_1 : s1.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    have hcomp : (4096#64 : Word) + BitVec.ofNat 64 c = BitVec.ofNat 64 (4096 + c) := bv64_add 4096 c
    simpa only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx22, hfix.x18] using hcomp
  have hreg1 : ∀ r, r ≠ .x6 → r ≠ .x28 → r ≠ .x29 → s1.getReg r = s.getReg r :=
    fun r h6 h28 h29 => by
      simp only [s1, runInstrs, capAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h29.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  -- pc[168]: LBU x7, 0(x29)
  have ha168 : s1.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_1, se12_0, BitVec.add_zero]
  have hv168 : memoryArgumentsValid s1 (.LBU .x7 .x29 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha168]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst168 := step_ordinary oracle s1 168 (.LBU .x7 .x29 0#12) (by decide) hpc1 checkInstr_168 (by intro h; cases h)
    (by simp [ordinaryStep, hv168])
  let s2 := execInstrBr s1 (.LBU .x7 .x29 0#12)
  have hpc2 : s2.pc = pcWord 169 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1'
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha168]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s1.getByte (BitVec.ofNat 64 (4096 + c)) = if marked then 1#8 else 0#8 := by
      simpa only [c, MachineState.getByte, MachineState.getMem, hmem1'] using hmark
    rw [hb, bool_byte_zeroExtend]
  have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s2.getReg r = s.getReg r :=
    fun r h6 h7 h28 h29 => by
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg1 r h6 h28 h29
  -- pc[169]: BNE x7, x0, pc[181]
  have hst169 := step_ordinary oracle s2 169 (.BNE .x7 .x0 48#13) (by decide) hpc2 checkInstr_169 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 7 0 [] := by simpa using hs1.trans (hst168.trans hst169)
  cases marked with
  | false =>
    have hpc3 : s3.pc = pcWord 170 := by
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
        hfix.x21 hx28_3 hx29_3 d16 hd16
    have hfix7 : CheckFixedRegs s7 :=
      hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    have hcur7 : ProofCursor s0 input.proof.length pOffNext tOffNext s7 :=
      hcur.of_agree (fun r hr => hreg7 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
    obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx14Fin, hx15Fin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
      step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s7 hpc7 hfix7 hcur7
        ((hreg7 .x14 (by decide) (by decide) (by decide) (by decide)).trans hx14)
        ((hreg7 .x15 (by decide) (by decide) (by decide) (by decide)).trans hx15)
        ((hreg7 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
    exact .continued sFin 23 0 [] (by decide) (by decide)
      (by simpa using (hs03.trans hs7).trans hsFin)
      ⟨rfl, rfl, hpcFin, hfixFin, hcurFin, hx14Fin, hx15Fin, hx24Fin, hx8Fin, hx27Fin,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hm7,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)).trans hv7,
       fun a ha hne hout => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout7 a ha hne hout,
       fun h => by cases h⟩
  | true =>
    have hpc3 : s3.pc = pcWord 181 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_169_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.setPC] using hmem2
    have hreg3 : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.getReg_setPC]
    have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [hreg3]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
    have hcmp := step_compare4 oracle 181 .x21 .x28 s3 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCmp hpc3
      ((hreg3 .x21).trans ((hreg2 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
      hx28_3 (by decide) (by unfold gapOffset; omega)
      (by unfold MEMORY_BYTES; omega) (by unfold gapOffset MEMORY_BYTES; omega)
    have hrb_s3_a : readBuffer s3 256 32 = d16 :=
      ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)).trans hd16
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
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, hcurFin, hx14Fin, hx15Fin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
        step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s4 hpc4 hfix4 hcur4
          ((hreg4s .x14 (by decide) (by decide) (by decide) (by decide)).trans hx14)
          ((hreg4s .x15 (by decide) (by decide) (by decide) (by decide)).trans hx15)
          ((hreg4s .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg4s .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg4s .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
      have hmemFins : sFin.mem = s.mem := hmemFin.trans hmem4s
      exact .continued sFin (7 + k + 5) 0 [] (by omega) (by decide)
        (by simpa [Nat.add_assoc] using (hs03.trans hs4).trans hsFin)
        ⟨rfl, rfl, hpcFin, hfixFin, hcurFin, hx14Fin, hx15Fin, hx24Fin, hx8Fin, hx27Fin,
         by simpa [MachineState.getByte, MachineState.getMem, hmemFins] using hmark,
         by rw [(MemEqOutside.of_mem_eq hmemFins 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega), ← heq_dig],
         fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmemFins],
         fun _ => hmemFins⟩

/-! #### Per-Position Loop Invariant and Induction (`pc[34] -> pc[198]`) -/

def posMarked16 (positions : Positions) (n c : Nat) : Bool :=
  decide (∃ j < n, capLeafOf (posAt positions j) = c)

theorem posMarked16_zero (positions : Positions) (c : Nat) :
    posMarked16 positions 0 c = false := by
  simp [posMarked16]

theorem posMarked16_succ (positions : Positions) (n c : Nat) :
    posMarked16 positions (n + 1) c =
      (posMarked16 positions n c || decide (capLeafOf (posAt positions n) = c)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [posMarked16, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hc⟩
    by_cases hjn : j < n
    · exact Or.inl ⟨j, hjn, hc⟩
    · have hjeq : j = n := by omega
      subst hjeq; exact Or.inr hc
  · rintro (⟨j, hj, hc⟩ | hc)
    · exact ⟨j, by omega, hc⟩
    · exact ⟨n, by omega, hc⟩

theorem posMarked16_card_eq_capMark (positions : Positions) (c : Nat) :
    posMarked16 positions positions.card c = capMark positions 16 c := by
  unfold posMarked16
  rw [capMark_16]
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
  posRecordOff input.positions.card n + tailBytes (posTailOff n) ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions.card j1) (posTailOff j1) j1
      (posAt input.positions j1) (valAt input j1)).evalLevel c96 16 =
    (parsePartialWitness s0 input.proof.length (posRecordOff input.positions.card j2) (posTailOff j2) j2
      (posAt input.positions j2) (valAt input j2)).evalLevel c96 16

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff input.positions.card n) (posTailOff n) s
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if n = input.positions.card then pcWord 198 else pcWord 34
  x14 : s.getReg .x14 = BitVec.ofNat 64 10603204576
  x15 : s.getReg .x15 = BitVec.ofNat 64 n
  x24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * n)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (input.positions.card - n)
  mark16 : ∀ c < 256, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if posMarked16 input.positions n c then 1#8 else 0#8
  mark_hi_zero : ∀ a, 4096 + 256 ≤ a → a < 4696 → s.getByte (BitVec.ofNat 64 a) = 0#8
  val16_gap_zero : ∀ q < 128, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + 96 * q + 64 + b)) = 0#8
  val_hi_zero : ∀ a, 8192 + capValOff 17 ≤ a → a < 8192 + 25000 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  witnesses : ∀ j < n,
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness (submission.initialState .check input) input.proof.length
      (posRecordOff input.positions.card j) (posTailOff j) j (posAt input.positions j) (valAt input j)
    pw.evalLevel c96 16 = readBuffer s (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) ∧
    (∀ prev < 16, InTrace h768 oracle tr (pw.levelInput c96 prev))

/-- Complete per-position verification loop (`pc[34]` -> `pc[198]`), `≤ 3687 * k` steps, `≤ 20 * k` calls. -/
theorem step_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (_hne : input.positions.card ≠ 0)
    (sInit : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sInit (3687 * input.positions.card) (20 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' q tr => q ≤ 20 * input.positions.card ∧ PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (3687 * n) (20 * n)
        (¬ PosConsistent c96 s0 input n)
        (fun s' q tr => q ≤ 20 * n ∧ PosLoopInv h768 oracle input n s' tr) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued sInit 0 0 [] (by decide) (by decide) (StepsTo.refl oracle sInit) ⟨by decide, hinit⟩
    | succ k ih =>
      have hcons_sub : ¬ PosConsistent c96 s0 input k → ¬ PosConsistent c96 s0 input (k + 1) := by
        intro hnot hcons
        apply hnot
        have hp_m := posRecordOff_mono input.positions.card (show k ≤ k + 1 by omega)
        have ht_m := tailBytes_mono (posTailOff_mono (show k ≤ k + 1 by omega))
        refine ⟨by have := hcons.1; omega, ?_⟩
        intro j1 j2 hj1 hj2 hc
        exact hcons.2 j1 j2 (by omega) (by omega) hc
      rw [show 3687 * (k + 1) = 3687 * k + 3687 by omega,
        show 20 * (k + 1) = 20 * k + 20 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hlt_k : k < input.positions.card := by omega
        have hpc_k : sk.pc = pcWord 34 := by
          have := hinv_k.pc
          rwa [if_neg (by omega : k ≠ input.positions.card)] at this
        let pOff := posRecordOff input.positions.card k
        let tOff := posTailOff k
        let i := posAt input.positions k
        let pw := parsePartialWitness s0 input.proof.length pOff tOff k i (valAt input k)
        let rem1 := input.positions.card - (k + 1)
        have hrem_eq : input.positions.card - k = rem1 + 1 := by omega
        have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
          rw [hinv_k.x27, hrem_eq]
        have htb_step : tailBytes tOff ≤ tailBytes (tOff + 16) := tailBytes_mono (by omega)
        -- 1A: leaf (190 steps, 4 calls)
        have h1a := step_pos_leaf h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
          sk hpc_k hinv_k.fixed hinv_k.cursor hinv_k.high hinv_k.x14 hinv_k.x15 hinv_k.x24 hinv_k.x8 hx27_k
        have hcan_leaf : input.proof.length < pOff + 15 + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
          intro hlt hcons
          have h1 := hcons.1
          rw [posRecordOff_succ, posTailOff_succ] at h1
          change pOff + 479 + tailBytes (tOff + 16) ≤ input.proof.length at h1
          omega
        -- Chain 1A (190,4) -> 1B (10,0) -> 1C (3456,16) -> 1D (31,0)
        refine PhaseOutcome.weaken
          (K1 := 190 + (10 + (3456 + 31))) (Q1 := 4 + (16 + 0))
          ?_ (by decide) (by decide) id (fun _ _ _ h => h)
        refine h1a.bind_dep hcan_leaf (fun s1 qA trA ⟨hqA, hpcA, hfixA, hcurA, houtA, hx14A, hx15A, hx20A, hx24A, hx8A, hx27A, hleafA, htrA⟩ => by
          obtain ⟨s2, hsB, hpcB, hfixB, hcurB, houtB, hx14B, hx15B, hx22B, hx24B, hx8B, hx27B, hx29B, hx30B, hl0B, hgapB⟩ :=
            step_pos_l0_setup h768 oracle input k pOff tOff (rem1 + 1)
              s1 hpcA hfixA hcurA hx14A hx15A hx20A hx24A hx8A hx27A hleafA
          refine hsB.prepend_pure ?_
          have hhighB : HighMemPreserved s0 s2 :=
            hinv_k.high.trans ((houtA.mono (by omega) (by omega)).trans (houtB.mono (by omega) (by omega)))
          have h1c := step_pos_bin238_loop h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
            s2 hpcB hfixB hcurB hhighB hx14B hx15B hx22B hx24B hx8B hx27B hx29B hx30B hl0B hgapB
          have hcan_238 : input.proof.length < pOff + 479 + tailBytes (tOff + 16) → ¬ PosConsistent c96 s0 input (k + 1) := by
            intro hlt hcons
            have h1 := hcons.1
            rw [posRecordOff_succ, posTailOff_succ] at h1
            change pOff + 479 + tailBytes (tOff + 16) ≤ input.proof.length at h1
            omega
          refine h1c.bind_dep hcan_238 (fun s3 qC trC ⟨hqC, hpcC, hfixC, hcurC, houtC, hx14C, hx15C, hx22C, hx24C, hx8C, hx27C, hl16C, htrC⟩ => by
            have hout_sk_s3 : MemEqOutside sk s3 256 352 :=
              houtA.trans (houtB.trans (houtC.mono (by omega) (by omega)))
            let c := capLeafOf i
            have hc_lt : c < 256 := capLeafOf_lt i
            have hmark3 : s3.getByte (BitVec.ofNat 64 (4096 + c)) =
                if posMarked16 input.positions k c then 1#8 else 0#8 := by
              rw [hout_sk_s3 (4096 + c) (by omega) (by omega)]
              exact hinv_k.mark16 c hc_lt
            have h1d := step_pos_cap_store oracle input k (pOff + 479) (tOff + 16) rem1 hlt_k (by omega)
              s3 hpcC hfixC hcurC hx14C hx15C hx22C hx24C hx8C hx27C
              (posMarked16 input.positions k c) hmark3 (pw.evalLevel c96 16) hl16C
            have hcan_dup : (posMarked16 input.positions k c = true ∧
                pw.evalLevel c96 16 ≠ readBuffer s3 (8192 + gapOffset c) 32) →
                ¬ PosConsistent c96 s0 input (k + 1) := by
              rintro ⟨hmk, hne_dig⟩ hcons
              unfold posMarked16 at hmk
              rw [decide_eq_true_eq] at hmk
              obtain ⟨j, hj, hcj⟩ := hmk
              have hwj := (hinv_k.witnesses j hj).1
              have heq_rb : readBuffer s3 (8192 + gapOffset c) 32 = readBuffer sk (8192 + gapOffset c) 32 :=
                hout_sk_s3.readBuffer_eq (by unfold gapOffset; omega) (by omega)
              have hcons_j := hcons.2 j k (by omega) (by omega) hcj
              rw [heq_rb, ← hcj, ← hwj] at hne_dig
              exact hne_dig hcons_j.symm
            refine h1d.weaken (le_refl _) (le_refl _) hcan_dup ?_
            rintro s4 qD trD ⟨rfl, rfl, hpc4, hfix4, hcur4, hx14_4, hx15_4, hx24_4, hx8_4, hx27_4, hmark4, hval4, hout4, hmem_dup⟩
            have hbyte_sk_s4 : ∀ a : Nat, a < 2 ^ 64 →
                (a < 256 ∨ 352 ≤ a) → a ≠ 4096 + c →
                (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
                s4.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a ha h1 h2 h3 =>
              (hout4 a ha h2 h3).trans (hout_sk_s3 a ha h1)
            have hcap17_eq : capValOff 17 = 12288 := by decide
            have hc_val_lt : gapOffset c + 32 ≤ capValOff 17 := by
              rw [hcap17_eq]; unfold gapOffset; omega
            refine ⟨by omega, ?_⟩
            refine ⟨hfix4,
              by simpa only [posRecordOff_succ, posTailOff_succ] using hcur4,
              ?_, ?_, hx14_4, hx15_4, hx24_4, hx8_4, hx27_4, ?_, ?_, ?_, ?_, ?_⟩
            · -- HighMemPreserved
              intro a ha hge
              exact (hbyte_sk_s4 a ha (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans (hinv_k.high a ha hge)
            · -- pc
              have hiff : rem1 = 0 ↔ k + 1 = input.positions.card := by omega
              simpa only [hiff] using hpc4
            · -- mark16
              intro c' hc'
              rw [posMarked16_succ]
              by_cases heq : c = c'
              · subst heq; simp only [c, i, decide_true, Bool.or_true, ite_true]; exact hmark4
              · simp only [show ¬ (capLeafOf (posAt input.positions k) = c') from heq,
                  decide_false, Bool.or_false]
                exact (hbyte_sk_s4 (4096 + c') (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))).trans
                  (hinv_k.mark16 c' hc')
            · -- mark_hi_zero
              intro a ha1 ha2
              exact (hbyte_sk_s4 a (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))).trans
                (hinv_k.mark_hi_zero a ha1 ha2)
            · -- val16_gap_zero
              intro q hq b hb
              have hdisj := gapOffset_disjoint_gap c q
              exact (hbyte_sk_s4 (8192 + 96 * q + 64 + b) (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans
                (hinv_k.val16_gap_zero q hq b hb)
            · -- val_hi_zero
              intro a ha1 ha2
              exact (hbyte_sk_s4 a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans
                (hinv_k.val_hi_zero a ha1 ha2)
            · -- witnesses
              intro j hj
              by_cases hjk : j < k
              · obtain ⟨hw_val, hw_leaf, hw_bin⟩ := hinv_k.witnesses j hjk
                let cj := capLeafOf (posAt input.positions j)
                have hcj_lt : cj < 256 := capLeafOf_lt (posAt input.positions j)
                have hrb_eq : readBuffer s4 (8192 + gapOffset cj) 32 = readBuffer sk (8192 + gapOffset cj) 32 := by
                  by_cases hceq : cj = c
                  · have hmk_t : posMarked16 input.positions k c = true := by
                      unfold posMarked16; rw [decide_eq_true_eq]; exact ⟨j, hjk, hceq⟩
                    have hmem43 : s4.mem = s3.mem := hmem_dup hmk_t
                    rw [(MemEqOutside.of_mem_eq hmem43 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)]
                    exact hout_sk_s3.readBuffer_eq (by unfold gapOffset; omega) (by omega)
                  · apply readBuffer_congr2; intro b hb
                    have hdisj := gapOffset_disjoint hceq
                    exact hbyte_sk_s4 (8192 + gapOffset cj + b) (by unfold gapOffset; omega)
                      (Or.inr (by omega)) (by omega) (by omega)
                refine ⟨hw_val.trans hrb_eq.symm,
                  fun x hx => (hw_leaf x hx).append_left,
                  fun prev hp => (hw_bin prev hp).append_left⟩
              · have hjeq : j = k := by omega
                subst hjeq
                refine ⟨hval4.symm, ?_, ?_⟩
                · intro x hx
                  have h1 := (htrA x hx).append_left (t2 := trC ++ [])
                  exact h1.append_right
                · intro prev hp
                  have h1 := (htrC prev hp).append_left (t2 := [])
                  have h2 := h1.append_right (t1 := trA)
                  exact h2.append_right)))
  exact hind input.positions.card (le_refl _)

end CommitGolfCandidate
