import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the L0..L1 (240b) and L2..L15 (238b) pure-binary loops, L16 cap-store,
and full per-position loop (`pc[75..167]`, `pc[22] -> pc[168]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_76_branch : pcWord 76 + signExtend13 620#13 = pcWord 231 := by decide
private theorem pc_78_branch : pcWord 78 + signExtend13 56#13 = pcWord 92 := by decide
private theorem pc_91_jal : pcWord 91 + signExtend21 20#21 = pcWord 96 := by decide
private theorem pc_100_branch : pcWord 100 + signExtend13 12#13 = pcWord 103 := by decide
private theorem pc_102_jal : pcWord 102 + signExtend21 16#21 = pcWord 106 := by decide
private theorem pc_108_branch : pcWord 108 + signExtend13 8060#13 = pcWord 75 := by decide
private theorem pc_111_branch : pcWord 111 + signExtend13 48#13 = pcWord 123 := by decide
private theorem pc_122_jal : pcWord 122 + signExtend21 12#21 = pcWord 125 := by decide
private theorem pc_133_branch : pcWord 133 + signExtend13 8100#13 = pcWord 110 := by decide

private theorem shiftRight_div2 (a k : Nat) : (a >>> k) / 2 = a >>> (k + 1) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- One iteration (`step < 2`, level `l = step ∈ 0..1`) of the 240b binary loop (`pc[75..108]`). -/
theorem step_pos_bin240_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 2)
    (s : MachineState) (hpc : s.pc = pcWord 75)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + 30 * step) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) step)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pCur := pOff + 24 + 30 * step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 212 1 (input.proof.length < pCur + 30 + tailBytes tOff)
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = (if step + 1 = 2 then pcWord 109 else pcWord 75) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + 30) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (step + 1) ∧
        readBuffer s' 320 32 = 0 ∧
        InTrace h768 oracle tr (pw.levelInput c96 step)) := by
  intro s0 c96 i pCur pw
  have hplen_bd : input.proof.length ≤ 8397000416 := hvalid
  have hle_cur : pCur + tailBytes tOff ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hidx_lt : i.val >>> step < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  -- pc[75]: ADDI x6, x25, 30; pc[76]: BLTU x31, x6, pc[231]
  have hst75 := step_ordinary oracle s 75 (.ADDI .x6 .x25 30#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x6 .x25 30#12)
  have hpc1 : s1.pc = pcWord 76 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 (11878272992 + pCur + 30) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hcur.x25, se12_30_ofNat]
    change BitVec.ofNat 64 (11878272992 + pCur) + BitVec.ofNat 64 30 = _
    exact bv64_add _ 30
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (11878272992 + (input.proof.length - tailBytes tOff)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hcur.x31]
  have hst76 := step_ordinary oracle s1 76 (.BLTU .x31 .x6 620#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BLTU .x31 .x6 620#13)
  have hult76 : BitVec.ult (s1.getReg .x31) (s1.getReg .x6) =
      decide (input.proof.length < pCur + 30 + tailBytes tOff) := by
    rw [hx31_1, hx6_1, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pCur + 30 + tailBytes tOff
  · have hpc2 : s2.pc = pcWord 231 := by
      simp only [s2, execInstrBr, hult76, hshort, decide_true, ite_true, MachineState.setPC, hpc1]
      exact pc_76_branch
    exact .rejected 5 0 [] hshort (by decide) (by decide)
      (by simpa using (hst75.trans hst76).halt (halt_reject oracle s2 hpc2))
  · have hge30 : pCur + 30 + tailBytes tOff ≤ input.proof.length := by omega
    have hpc2 : s2.pc = pcWord 77 := by
      simp only [s2, execInstrBr, hult76, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      have h21 : s2.mem = s1.mem := by
        simp only [s2, execInstrBr, hult76, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      exact h21.trans (by simp [s1, execInstrBr, mem_setPC, mem_setReg])
    have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r h6 => by
      have h21 : s2.getReg r = s1.getReg r := by
        simp only [s2, execInstrBr, hult76, hshort, decide_false, Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
      rw [h21]; simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
    -- pc[77]: ANDI x7, x22, 1; pc[78]: BEQ x7, x0, pc[92]
    have hst77 := step_ordinary oracle s2 77 (.ANDI .x7 .x22 1#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ANDI .x7 .x22 1#12)
    have hpc3 : s3.pc = pcWord 78 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 ((i.val >>> step) % 2) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x22 (by decide), hx22, se12_1]
      exact bv64_and_one (i.val >>> step) (by omega)
    have hst78 := step_ordinary oracle s3 78 (.BEQ .x7 .x0 56#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.BEQ .x7 .x0 56#13)
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    let sibD := pw.binSib step
    have hsibD_eq : sibD = proofDigest30 s0 (11878272992 + pCur) := by
      simp only [sibD, pw, parsePartialWitness, hstep, ite_true, pCur, Nat.add_assoc]
    let curD := pw.evalLevel c96 step
    let inpL : BitVec 768 :=
      if (i.val >>> step) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
    have heval_next : pw.evalLevel c96 (step + 1) = maskLevel (step + 1) (c96 inpL) := rfl
    have hlinp : pw.levelInput c96 step = inpL := rfl
    -- Common footer at pc[106..108]
    have hfooter : ∀ (s106 : MachineState) (kMid : Nat),
        kMid ≤ 209 →
        StepsTo oracle s s106 kMid 1 [(inpL.cast h768.symm, c96 inpL)] →
        s106.pc = pcWord 106 →
        CheckFixedRegs s106 →
        ProofCursor s0 input.proof.length (pCur + 30) tOff s106 →
        MemEqOutside s s106 256 320 →
        s106.getReg .x22 = BitVec.ofNat 64 (i.val >>> step) →
        s106.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) →
        s106.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) →
        s106.getReg .x27 = BitVec.ofNat 64 rem →
        s106.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) →
        s106.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) →
        readBuffer s106 256 32 = pw.evalLevel c96 (step + 1) →
        readBuffer s106 320 32 = 0 →
        PhaseOutcome oracle s 212 1 (input.proof.length < pCur + 30 + tailBytes tOff)
          (fun s' q tr =>
            q = 1 ∧
            s'.pc = (if step + 1 = 2 then pcWord 109 else pcWord 75) ∧
            CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length (pCur + 30) tOff s' ∧
            MemEqOutside s s' 256 320 ∧
            s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) ∧
            s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
            readBuffer s' 256 32 = pw.evalLevel c96 (step + 1) ∧
            readBuffer s' 320 32 = 0 ∧
            InTrace h768 oracle tr (pw.levelInput c96 step)) := by
      intro s106 kMid hkMid hmid hpc106 hfix106 hcur106 hout106 h22 h24 h8 h27 h29 h30 hdig106 hgap106
      have hst106 := step_ordinary oracle s106 106 (.SRLI .x22 .x22 1#6) (by decide) hpc106 rfl (by intro h; cases h) rfl
      let s107 := execInstrBr s106 (.SRLI .x22 .x22 1#6)
      have hpc107 : s107.pc = pcWord 107 := by simp only [s107, execInstrBr, MachineState.setPC, hpc106, pcWord_add_four]
      have hx22_107 : s107.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) := by
        simp only [s107, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), h22, show (1#6 : BitVec 6).toNat = 1 by decide,
          bv64_shr _ 1 (by omega), Nat.pow_one, shiftRight_div2]
      have hst107 := step_ordinary oracle s107 107 (.ADDI .x29 .x29 32#12) (by decide) hpc107 rfl (by intro h; cases h) rfl
      let s108 := execInstrBr s107 (.ADDI .x29 .x29 32#12)
      have hpc108 : s108.pc = pcWord 108 := by simp only [s108, execInstrBr, MachineState.setPC, hpc107, pcWord_add_four]
      have hmem108 : s108.mem = s106.mem := by simp [s108, s107, execInstrBr, mem_setPC, mem_setReg]
      have hx29_108 : s108.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) := by
        simp only [s108, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide)]
        simp only [s107, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x29), h29, se12_32]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hx30_108 : s108.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) := by
        simp only [s108, s107, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x30), h30]
      have hx22_108 : s108.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) := by
        simp only [s108, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x22), hx22_107]
      have hreg108 : ∀ r, r ≠ .x22 → r ≠ .x29 → s108.getReg r = s106.getReg r := fun r h22r h29r => by
        simp only [s108, s107, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h29r.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h22r.symm]
      obtain ⟨sFin, hst108, hpcFin_raw, hregFin_108, hmemFin_108⟩ :=
        step_bne_reg oracle 108 75 .x29 .x30 8060#13 (by decide) rfl pc_108_branch s108
          (68719475936 + 32 * (step + 1)) (68719475936 + 32 * 2) (by omega) (by omega) hpc108 hx29_108 hx30_108
      have hpcFin : sFin.pc = if step + 1 = 2 then pcWord 109 else pcWord 75 := by
        rw [hpcFin_raw]; congr 1; exact propext (by omega)
      have hmemFin : sFin.mem = s106.mem := hmemFin_108.trans hmem108
      have hregFin : ∀ r, r ≠ .x22 → r ≠ .x29 → sFin.getReg r = s106.getReg r := fun r h22r h29r =>
        (hregFin_108 r).trans (hreg108 r h22r h29r)
      have htot := (hmid.trans (hst106.trans hst107)).trans hst108
      refine .continued sFin (kMid + 3) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
        (htot.eq_of rfl (by omega) rfl (by simp only [List.append_nil]))
        ⟨rfl, hpcFin,
         hfix106.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         hcur106.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         hout106.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
         (hregFin_108 .x22).trans hx22_108,
         (hregFin .x24 (by decide) (by decide)).trans h24,
         (hregFin .x8  (by decide) (by decide)).trans h8,
         (hregFin .x27 (by decide) (by decide)).trans h27,
         (hregFin_108 .x29).trans hx29_108,
         (hregFin .x30 (by decide) (by decide)).trans h30,
         ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hdig106,
         ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hgap106,
         by rw [hlinp]; exact InTrace.singleton h768 oracle inpL⟩
    -- Common compression + mask (240b for step = 0 -> L1, 238b for step = 1 -> L2) at pc[96..105] -> pc[106]
    have hcall96 : ∀ (s96 : MachineState) (kA : Nat),
        kA ≤ 196 →
        StepsTo oracle s4 s96 kA 0 [] →
        s96.pc = pcWord 96 →
        CheckFixedRegs s96 →
        ProofCursor s0 input.proof.length (pCur + 30) tOff s96 →
        MemEqOutside s s96 256 320 →
        s96.getReg .x22 = BitVec.ofNat 64 (i.val >>> step) →
        s96.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) →
        s96.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) →
        s96.getReg .x27 = BitVec.ofNat 64 rem →
        s96.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) →
        s96.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) →
        readBuffer s96 256 96 = inpL →
        readBuffer s96 320 32 = 0 →
        PhaseOutcome oracle s 212 1 (input.proof.length < pCur + 30 + tailBytes tOff)
          (fun s' q tr =>
            q = 1 ∧ s'.pc = (if step + 1 = 2 then pcWord 109 else pcWord 75) ∧
            CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length (pCur + 30) tOff s' ∧
            MemEqOutside s s' 256 320 ∧
            s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) ∧
            s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
            readBuffer s' 256 32 = pw.evalLevel c96 (step + 1) ∧
            readBuffer s' 320 32 = 0 ∧
            InTrace h768 oracle tr (pw.levelInput c96 step)) := by
      intro s96 kA hkA hmidA hpc96 hfix96 hcur96 hout96 h22 h24 h8 h27 h29 h30 hinp96 hgap96
      have hst96 := step_ordinary oracle s96 96 (.ADDI .x10 .x21 0#12) (by decide) hpc96 rfl (by intro h; cases h) rfl
      let s97 := execInstrBr s96 (.ADDI .x10 .x21 0#12)
      have hpc97 : s97.pc = pcWord 97 := by simp only [s97, execInstrBr, MachineState.setPC, hpc96, pcWord_add_four]
      have hst97 := step_ordinary oracle s97 97 (.ADDI .x12 .x21 0#12) (by decide) hpc97 rfl (by intro h; cases h) rfl
      let s98 := execInstrBr s97 (.ADDI .x12 .x21 0#12)
      have hpc98 : s98.pc = pcWord 98 := by simp only [s98, execInstrBr, MachineState.setPC, hpc97, pcWord_add_four]
      have hmem98 : s98.mem = s96.mem := by simp [s98, s97, execInstrBr, mem_setPC, mem_setReg]
      have hreg98 : ∀ r, r ≠ .x10 → r ≠ .x12 → s98.getReg r = s96.getReg r := fun r h10 h12 => by
        simp only [s98, s97, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_98 : s98.getReg .x10 = 256#64 := by
        simp only [s98, s97, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix96.x21, se12_0, BitVec.add_zero]
      have hx12_98 : s98.getReg .x12 = 256#64 := by
        simp only [s98, s97, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hfix96.x21, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h768 oracle s98 98 256 256 (by decide) hpc98 rfl
        ((hreg98 .x5 (by decide) (by decide)).trans hfix96.x5)
        ((hreg98 .x11 (by decide) (by decide)).trans hfix96.x11)
        ((hreg98 .x13 (by decide) (by decide)).trans hfix96.x13)
        hx10_98 hx12_98 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
      rw [(MemEqOutside.of_mem_eq hmem98 0 0).readBuffer_eq (by omega) (by omega), hinp96] at hec
      let s99 := writeBits s98 (BitVec.ofNat 64 256) (c96 inpL)
      have hpc99 : s99.pc = pcWord 99 := by simp only [s99, writeBits, MachineState.setPC, hpc98, pcWord_add_four]
      have hreg99 : ∀ r, r ≠ .x10 → r ≠ .x12 → s99.getReg r = s96.getReg r := fun r h10 h12 =>
        (writeBits_register s98 _ _ r).trans (hreg98 r h10 h12)
      -- pc[99]: ADDI x6, x2, 32; pc[100]: BEQ x29, x6, pc[103]
      have hst99 := step_ordinary oracle s99 99 (.ADDI .x6 .x2 32#12) (by decide) hpc99 rfl (by intro h; cases h) rfl
      let s100 := execInstrBr s99 (.ADDI .x6 .x2 32#12)
      have hpc100 : s100.pc = pcWord 100 := by simp only [s100, execInstrBr, MachineState.setPC, hpc99, pcWord_add_four]
      have hx6_100 : s100.getReg .x6 = BitVec.ofNat 64 (68719475936 + 32) := by
        simp only [s100, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg99 .x2 (by decide) (by decide), hfix96.x2, se12_32]
        change BitVec.ofNat 64 68719475936 + BitVec.ofNat 64 32 = _; exact bv64_add _ _
      have hx29_100 : s100.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) := by
        simp only [s100, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hreg99 .x29 (by decide) (by decide), h29]
      have hst100 := step_ordinary oracle s100 100 (.BEQ .x29 .x6 12#13) (by decide) hpc100 rfl (by intro h; cases h) rfl
      let s101 := execInstrBr s100 (.BEQ .x29 .x6 12#13)
      have heq1 : (s100.getReg .x29 == s100.getReg .x6) = decide (step = 1) := by
        rw [hx29_100, hx6_100, bv64_beq_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      have hmem101 : s101.mem = s99.mem := by
        simp only [s101, execInstrBr]; split <;> simp [s100, execInstrBr, mem_setPC, mem_setReg]
      have hreg101 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s101.getReg r = s96.getReg r := fun r h6 h10 h12 => by
        have : s101.getReg r = s100.getReg r := by simp only [s101, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
        rw [this]; simp only [s100, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg99 r h10 h12
      have hpre101 := (((hst75.trans hst76).trans (hst77.trans hst78)).trans hmidA).trans
        (((hst96.trans hst97).trans hec).trans (hst99.trans hst100))
      by_cases hs1 : step = 1
      · -- step = 1 (L1 -> L2): mask238 at pc[103..105] -> pc[106]
        have hpc101 : s101.pc = pcWord 103 := by
          simp only [s101, execInstrBr, heq1, hs1, decide_true, ite_true, MachineState.setPC, hpc100]
          exact pc_100_branch
        obtain ⟨s106, hs106, hpc106, hreg106, hdig106, hout106⟩ :=
          step_mask238 oracle 103 .x21 s101 256 (by decide) (by decide) rfl rfl rfl hpc101
            ((hreg101 .x21 (by decide) (by decide) (by decide)).trans hfix96.x21)
            ((hreg101 .x9 (by decide) (by decide) (by decide)).trans hfix96.x9)
            (by decide) (by unfold MEMORY_BYTES; omega)
        have hdig_eq : readBuffer s106 256 32 = pw.evalLevel c96 (step + 1) := by
          rw [heval_next, hdig106, (MemEqOutside.of_mem_eq hmem101 0 0).readBuffer_eq (by omega) (by omega),
            writeBits_readBuffer_digest]
          unfold maskLevel FIRST_240_LVL FIRST_238_LVL
          rw [if_neg (by omega), if_neg (by omega)]
        have hgap106 : readBuffer s106 320 32 = 0 := by
          rw [hout106.readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem101 0 0).readBuffer_eq (by omega) (by omega),
            (MemEqOutside_writeBits_digest s98 256 _ (by omega)).readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem98 0 0).readBuffer_eq (by omega) (by omega), hgap96]
        have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s106.getReg r = s96.getReg r :=
          fun r h6 h10 h12 => (hreg106 r h6).trans (hreg101 r h6 h10 h12)
        have hout_all : MemEqOutside s s106 256 320 :=
          hout96.trans ((MemEqOutside.of_mem_eq hmem98 256 320).trans
            (((MemEqOutside_writeBits_digest s98 256 _ (by omega)).mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem101 256 320).trans (hout106.mono (by omega) (by omega)))))
        exact hfooter s106 (4 + kA + 5 + 3) (by omega)
          ((hpre101.trans hs106).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
          hpc106
          (hfix96.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          (hcur96.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
          hout_all
          ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
          ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
          ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
          ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
          ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
          ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
          hdig_eq hgap106
      · -- step = 0 (L0 -> L1): SH x21, x0, 30 (mask240) + JAL pc[106]
        have hpc101 : s101.pc = pcWord 101 := by
          simp only [s101, execInstrBr, heq1, hs1, decide_false, Bool.false_eq_true, ite_false,
            MachineState.setPC, hpc100, pcWord_add_four]
        have ha101 : s101.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
          rw [hreg101 .x21 (by decide) (by decide) (by decide), hfix96.x21]; decide
        have hv101 : memoryArgumentsValid s101 (.SH .x21 .x0 30#12) = true := by
          simp only [memoryArgumentsValid, memAccess, ha101]
          exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; omega) (by decide)
        have hst101 := step_ordinary oracle s101 101 (.SH .x21 .x0 30#12) (by decide) hpc101 rfl (by intro h; cases h)
          (by simp [ordinaryStep, hv101])
        let s102 := execInstrBr s101 (.SH .x21 .x0 30#12)
        have hpc102 : s102.pc = pcWord 102 := by simp only [s102, execInstrBr, MachineState.setPC, hpc101, pcWord_add_four]
        have hst102 := step_ordinary oracle s102 102 (.JAL .x0 16#21) (by decide) hpc102 rfl (by intro h; cases h) rfl
        let s106 := execInstrBr s102 (.JAL .x0 16#21)
        have hpc106 : s106.pc = pcWord 106 := by
          simp only [s106, execInstrBr, MachineState.setPC, hpc102]; exact pc_102_jal
        have hmem106 : s106.mem = s102.mem := by simp [s106, execInstrBr, mem_setPC, mem_setReg]
        have hreg_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s106.getReg r = s96.getReg r := fun r h6 h10 h12 => by
          have h1 : s106.getReg r = s102.getReg r := by simp [s106, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          have h2 : s102.getReg r = s101.getReg r := by
            simp [s102, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
          exact h1.trans (h2.trans (hreg101 r h6 h10 h12))
        have hout_sh : MemEqOutside s101 s102 286 288 := by
          intro a ha hout
          simp only [s102, execInstrBr, ha101, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
          exact MemEqOutside_setHalfword s101 286 _ (by decide) (by omega) a ha hout
        have hout_all : MemEqOutside s s106 256 320 :=
          hout96.trans ((MemEqOutside.of_mem_eq hmem98 256 320).trans
            (((MemEqOutside_writeBits_digest s98 256 _ (by omega)).mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem101 256 320).trans
                ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem106 256 320)))))
        have hdig_eq : readBuffer s106 256 32 = pw.evalLevel c96 (step + 1) := by
          rw [heval_next, (MemEqOutside.of_mem_eq hmem106 0 0).readBuffer_eq (by omega) (by omega)]
          have hsh : readBuffer s102 256 32 =
              readBuffer (s99.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
            apply readBuffer_congr2; intro j _
            simp [s102, execInstrBr, ha101, MachineState.getByte, MachineState.setHalfword,
              MachineState.getMem, MachineState.setMem, mem_setPC, hmem101, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [hsh, sh_zero_mask240 s99 256 (by decide) (by omega), writeBits_readBuffer_digest]
          unfold maskLevel FIRST_240_LVL FIRST_238_LVL
          rw [if_neg (by omega), if_pos (by omega)]
        have hgap106 : readBuffer s106 320 32 = 0 := by
          rw [(MemEqOutside.of_mem_eq hmem106 0 0).readBuffer_eq (by omega) (by omega),
            hout_sh.readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem101 0 0).readBuffer_eq (by omega) (by omega),
            (MemEqOutside_writeBits_digest s98 256 _ (by omega)).readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem98 0 0).readBuffer_eq (by omega) (by omega), hgap96]
        exact hfooter s106 (4 + kA + 5 + 2) (by omega)
          ((hpre101.trans (hst101.trans hst102)).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
          hpc106
          (hfix96.of_agree (fun r hr => hreg_all r (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
          (hcur96.of_agree (fun r hr => hreg_all r (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
          hout_all
          ((hreg_all .x22 (by decide) (by decide) (by decide)).trans h22)
          ((hreg_all .x24 (by decide) (by decide) (by decide)).trans h24)
          ((hreg_all .x8  (by decide) (by decide) (by decide)).trans h8)
          ((hreg_all .x27 (by decide) (by decide) (by decide)).trans h27)
          ((hreg_all .x29 (by decide) (by decide) (by decide)).trans h29)
          ((hreg_all .x30 (by decide) (by decide) (by decide)).trans h30)
          hdig_eq hgap106
    by_cases heven : (i.val >>> step) % 2 = 0
    · -- Even: jump to pc[92..95] -> pc[96]
      have hx7z : s3.getReg .x7 = 0#64 := by rw [hx7_3, heven]
      have hpc4 : s4.pc = pcWord 92 := by
        simp only [s4, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
          MachineState.setPC, hpc3]; exact pc_78_branch
      have hmem4 : s4.mem = s.mem := by
        simpa [s4, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem3
      have hreg43 : ∀ r, s4.getReg r = s3.getReg r := fun r => by
        simp only [s4, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → s4.getReg r = s.getReg r := fun r h6 h7 => by
        rw [hreg43]; simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg2 r h6
      have hst92 := step_ordinary oracle s4 92 (.ADDI .x12 .x21 32#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
      let s5 := execInstrBr s4 (.ADDI .x12 .x21 32#12)
      have hpc5 : s5.pc = pcWord 93 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
      obtain ⟨s6, hs6, hpc6, hx25_6, hreg6, hcopy6, hout6⟩ :=
        step_call_read_n oracle 93 30 s5 (11878272992 + pCur) 288 (by decide) (by decide) (by decide)
          rfl rfl hpc5
          (by simp only [s5, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg4 .x25 (by decide) (by decide), hcur.x25])
          (by simp only [s5, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide),
                hreg4 .x21 (by decide) (by decide), hfix.x21, se12_32]; decide)
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
      -- pc[95]: SH x21, x0, 62
      have hx21_6 : s6.getReg .x21 = 256#64 := by
        rw [hreg6 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21),
          hreg4 .x21 (by decide) (by decide), hfix.x21]
      have ha95 : s6.getReg .x21 + signExtend12 62#12 = BitVec.ofNat 64 318 := by
        rw [hx21_6]; decide
      have hv95 : memoryArgumentsValid s6 (.SH .x21 .x0 62#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha95]
        exact accessValid_ofNat 318 2 (by unfold MEMORY_BYTES; omega) (by decide)
      have hst95 := step_ordinary oracle s6 95 (.SH .x21 .x0 62#12) (by decide) hpc6 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv95])
      let s7 := execInstrBr s6 (.SH .x21 .x0 62#12)
      have hpc7 : s7.pc = pcWord 96 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
      have hout_sh : MemEqOutside s6 s7 318 320 := by
        intro a ha hout
        simp only [s7, execInstrBr, ha95, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact MemEqOutside_setHalfword s6 318 _ (by decide) (by omega) a ha hout
      have hout_all : MemEqOutside s s7 288 320 :=
        (MemEqOutside.of_mem_eq hmem5 288 320).trans
          ((hout6.mono (by omega) (by omega)).trans (hout_sh.mono (by omega) (by omega)))
      have hreg7_6 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
        simp [s7, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      have hreg7 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s7.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        rw [hreg7_6, hreg6 r h1 h6 h10 h12 h25]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
        exact hreg4 r h6 h7
      have hcur7 : ProofCursor s0 input.proof.length (pCur + 30) tOff s7 := by
        refine ⟨hge30, ?_, ?_, ?_, ?_⟩
        · rw [hreg7_6, hx25_6]; congr 1
        · rw [hreg7 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg7 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg7 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      have hgap7 : readBuffer s7 320 32 = 0 :=
        (hout_all.readBuffer_eq (by omega) (by omega)).trans hgap
      have hinp7 : readBuffer s7 256 96 = inpL := by
        rw [readBuffer_binary_of_zero_gap s7 256 hgap7]
        have hL : readBuffer s7 256 32 = curD :=
          (hout_all.readBuffer_eq (by omega) (by omega)).trans hcurDig
        have hR : readBuffer s7 288 32 = sibD := by
          rw [hsibD_eq]
          have hsh_eq : readBuffer s7 288 32 =
              readBuffer (s6.setHalfword (BitVec.ofNat 64 (288 + 30)) 0#16) 288 32 := by
            apply readBuffer_congr2; intro j _
            simp [s7, execInstrBr, ha95, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [hsh_eq]
          apply sh_zero_readBuffer30 s6 s0 288 (11878272992 + pCur) (by decide) (by omega)
          intro j hj
          rw [hcopy6 j hj]
          have h50 : HighMemPreserved s0 s5 := hhigh.trans (MemEqOutside.of_mem_eq hmem5 0 4294971392)
          exact h50 (11878272992 + pCur + j) (by omega) (by omega)
        rw [hL, hR]; simp only [inpL, heven, ite_true]
      exact hcall96 s7 185 (by decide)
        (((hst92.trans hs6).trans hst95).eq_of rfl (by decide) (by decide) (by simp))
        hpc7
        (hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        hcur7 (hout_all.mono (by omega) (by omega))
        ((hreg7 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg7 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg7 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg7 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        hinp7 hgap7
    · -- Odd: fall through to pc[79..91] -> pc[96]
      have hodd : (i.val >>> step) % 2 = 1 := by omega
      have hx7o : s3.getReg .x7 = 1#64 := by rw [hx7_3, hodd]
      have hpc4 : s4.pc = pcWord 79 := by
        simp only [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc3, pcWord_add_four]
      have hmem4 : s4.mem = s.mem := by
        simpa [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem3
      have hreg43 : ∀ r, s4.getReg r = s3.getReg r := fun r => by
        simp only [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → s4.getReg r = s.getReg r := fun r h6 h7 => by
        rw [hreg43]; simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg2 r h6
      -- pc[79..86]: copy 4 dwords S[0..32) -> S[32..64)
      have hcC : ∀ j < 4,
          checkInstr (79 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
          checkInstr (79 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
      obtain ⟨s5, hs5, hpc5, hreg5, hcopy5, hout5⟩ :=
        step_copy_dwords oracle 79 4 .x21 .x21 0 32 s4 256 256
          (by decide) (by decide) (by decide) (by decide) (by decide) hcC hpc4
          ((hreg4 .x21 (by decide) (by decide)).trans hfix.x21)
          ((hreg4 .x21 (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by decide)
      -- pc[87]: ADDI x12, x21, 0; pc[88..89]: call readN(30) -> S[0..30)
      have hst87 := step_ordinary oracle s5 87 (.ADDI .x12 .x21 0#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ADDI .x12 .x21 0#12)
      have hpc6 : s6.pc = pcWord 88 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
      obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
        step_call_read_n oracle 88 30 s6 (11878272992 + pCur) 256 (by decide) (by decide) (by decide)
          rfl rfl hpc6
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg5 .x25 (by decide), hreg4 .x25 (by decide) (by decide), hcur.x25])
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide),
                hreg5 .x21 (by decide), hreg4 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
      -- pc[90]: SH x21, x0, 30; pc[91]: JAL x0, pc[96]
      have hx21_7 : s7.getReg .x21 = 256#64 := by
        rw [hreg7 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21),
          hreg5 .x21 (by decide), hreg4 .x21 (by decide) (by decide), hfix.x21]
      have ha90 : s7.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
        rw [hx21_7]; decide
      have hv90 : memoryArgumentsValid s7 (.SH .x21 .x0 30#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha90]
        exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; omega) (by decide)
      have hst90 := step_ordinary oracle s7 90 (.SH .x21 .x0 30#12) (by decide) hpc7 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv90])
      let s8 := execInstrBr s7 (.SH .x21 .x0 30#12)
      have hpc8 : s8.pc = pcWord 91 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
      have hst91 := step_ordinary oracle s8 91 (.JAL .x0 20#21) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let s9 := execInstrBr s8 (.JAL .x0 20#21)
      have hpc9 : s9.pc = pcWord 96 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8]; exact pc_91_jal
      have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
      have hout_sh : MemEqOutside s7 s8 286 288 := by
        intro a ha hout
        simp only [s8, execInstrBr, ha90, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact MemEqOutside_setHalfword s7 286 _ (by decide) (by omega) a ha hout
      have hout_69 : MemEqOutside s6 s9 256 288 :=
        (hout7.mono (by omega) (by omega)).trans
          ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 288))
      have hout_all : MemEqOutside s s9 256 320 :=
        (MemEqOutside.of_mem_eq hmem4 256 320).trans
          ((hout5.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem6 256 320).trans (hout_69.mono (by omega) (by omega))))
      have hreg9_7 : ∀ r, s9.getReg r = s7.getReg r := fun r => by
        have h1 : s9.getReg r = s8.getReg r := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have h2 : s8.getReg r = s7.getReg r := by
          simp [s8, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        exact h1.trans h2
      have hreg9 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s9.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        rw [hreg9_7, hreg7 r h1 h6 h10 h12 h25]
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg5 r h6]
        exact hreg4 r h6 h7
      have hcur9 : ProofCursor s0 input.proof.length (pCur + 30) tOff s9 := by
        refine ⟨hge30, ?_, ?_, ?_, ?_⟩
        · rw [hreg9_7, hx25_7]; congr 1
        · rw [hreg9 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg9 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg9 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      have hgap9 : readBuffer s9 320 32 = 0 :=
        (hout_all.readBuffer_eq (by omega) (by omega)).trans hgap
      have hinp9 : readBuffer s9 256 96 = inpL := by
        rw [readBuffer_binary_of_zero_gap s9 256 hgap9]
        have hL : readBuffer s9 256 32 = sibD := by
          rw [hsibD_eq, (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by omega) (by omega)]
          have hsh_eq : readBuffer s8 256 32 =
              readBuffer (s7.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
            apply readBuffer_congr2; intro j _
            simp [s8, execInstrBr, ha90, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [hsh_eq]
          apply sh_zero_readBuffer30 s7 s0 256 (11878272992 + pCur) (by decide) (by omega)
          intro j hj
          rw [hcopy7 j hj]
          have h60 : HighMemPreserved s0 s6 :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem4 0 4294971392).trans
              ((hout5.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem6 0 4294971392)))
          exact h60 (11878272992 + pCur + j) (by omega) (by omega)
        have hR : readBuffer s9 288 32 = curD := by
          have hcurD : readBuffer s 256 32 = curD := hcurDig
          rw [hout_69.readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega), ← hcurD]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy5 j hj
          simp only [Nat.add_zero] at hc
          rw [show 288 + j = 256 + 32 + j by omega, hc]
          simp [MachineState.getByte, MachineState.getMem, hmem4]
        rw [hL, hR]; simp only [inpL, heven, ite_false]
      exact hcall96 s9 194 (by decide)
        ((((hs5.trans hst87).trans hs7).trans (hst90.trans hst91)).eq_of rfl (by decide) (by decide) (by simp))
        hpc9
        (hfix.of_agree (fun r hr => hreg9 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        hcur9 hout_all
        ((hreg9 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg9 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg9 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg9 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg9 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg9 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        hinp9 hgap9

/-- Phase 1C: complete L0..L1 (240b) binary loop (`pc[75]` -> `pc[109]`), ≤ 424 steps, 2 calls. -/
theorem step_pos_bin240_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 75)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 24) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> 0))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 0))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2))
    (hl0 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 0)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 424 2 (input.proof.length < pOff + 84 + tailBytes tOff)
      (fun s' q tr =>
        q = 2 ∧
        s'.pc = pcWord 109 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 84) tOff s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> 2) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 2 ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ prev < 2, InTrace h768 oracle tr (pw.levelInput c96 prev)) := by
  intro s0 c96 i pw
  have hloop : ∀ n ≤ 2,
      PhaseOutcome oracle s (212 * n) n
        (input.proof.length < pOff + 24 + 30 * n + tailBytes tOff)
        (fun s' q tr =>
          q = n ∧
          s'.pc = (if n = 2 then pcWord 109 else pcWord 75) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 24 + 30 * n) tOff s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> n) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * n) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 n ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev < n, InTrace h768 oracle tr (pw.levelInput c96 prev)) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued s 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s)
        ⟨rfl, by simpa using hpc, hfix, by simpa using hcur, MemEqOutside.refl s 256 320,
         hx22, hx24, hx8, hx27, hx29, hx30, hl0, hgap, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      rw [show 212 * (k + 1) = 212 * k + 212 by omega]
      refine (ih (by omega)).bind_dep (by omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne2 : k ≠ 2 := by omega
          simp only [hne2, ite_false] at hpc_k
          have hstep_k := step_pos_bin240_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k (hhigh.trans (hout_k.mono (by omega) (by omega)))
            hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega) (by omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', ?_, hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          · simpa only [show pOff + 24 + 30 * (k + 1) = pOff + 24 + 30 * k + 30 by omega] using hcur'
          · intro prev hprev
            by_cases hlt : prev < k
            · exact (htr_k prev hlt).append_left
            · have : prev = k := by omega
              subst this; exact htr'.append_right)
  refine (hloop 2 (by decide)).weaken (by decide) (by decide) (by omega) ?_
  rintro s' q tr ⟨hq, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', _, hdig', hgap', htr'⟩
  exact ⟨hq, by simpa using hpc', hfix',
    by simpa only [show pOff + 24 + 30 * 2 = pOff + 84 by omega] using hcur',
    hout', hx22', hx24', hx8', hx27', hx29', hdig', hgap', htr'⟩

/-- One iteration (`step < 14`, level `l = 2 + step ∈ 2..15`) of the 238b binary loop (`pc[110..133]`). -/
theorem step_pos_bin238_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hord : ord < input.positions.card) (hstep : step < 14)
    (s : MachineState) (hpc : s.pc = pcWord 110)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 84 + 29 * step) (tOff + step) s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> (2 + step)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16))
    (hcurDig : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) (2 + step))
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pCur := pOff + 84 + 29 * step
    let tCur := tOff + step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 216 1 (input.proof.length < pCur + 29 + tailBytes (tCur + 1))
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = (if step + 1 = 14 then pcWord 134 else pcWord 110) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
        readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
        readBuffer s' 320 32 = 0 ∧
        InTrace h768 oracle tr (pw.levelInput c96 (2 + step))) := by
  intro s0 c96 i pCur tCur pw
  have hplen_bd : input.proof.length ≤ 8397000416 := hvalid
  have hi_lt : i.val < 16777216 := i.isLt
  have hidx_lt : i.val >>> (2 + step) < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  -- pc[110]: ANDI x7, x22, 1; pc[111]: BEQ x7, x0, pc[123]
  have hst110 := step_ordinary oracle s 110 (.ANDI .x7 .x22 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ANDI .x7 .x22 1#12)
  have hpc1 : s1.pc = pcWord 111 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx7_1 : s1.getReg .x7 = BitVec.ofNat 64 ((i.val >>> (2 + step)) % 2) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, se12_1]
    exact bv64_and_one (i.val >>> (2 + step)) (by omega)
  have hst111 := step_ordinary oracle s1 111 (.BEQ .x7 .x0 48#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BEQ .x7 .x0 48#13)
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  let sibD := pw.binSib (2 + step)
  have hsibD_eq : sibD = proofDigest238 s0 input.proof.length (11878272992 + pCur) tCur := by
    simp only [sibD, pw, parsePartialWitness, show ¬ (2 + step < 2) by omega, ite_false,
      show 2 + step < 16 by omega, ite_true, show 2 + step - 2 = step by omega, pCur, tCur, Nat.add_assoc]
  let curD := pw.evalLevel c96 (2 + step)
  let inpL : BitVec 768 :=
    if (i.val >>> (2 + step)) % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
  have heval_next : pw.evalLevel c96 (2 + (step + 1)) = mask238 (c96 inpL) := by
    rw [show 2 + (step + 1) = (2 + step) + 1 by omega]
    change maskLevel (2 + step + 1) (c96 inpL) = _
    unfold maskLevel FIRST_240_LVL FIRST_238_LVL
    rw [if_neg (by omega), if_neg (by omega)]
  have hlinp : pw.levelInput c96 (2 + step) = inpL := rfl
  -- Common compress + mask238 + footer at pc[125..133]
  have hcall125 : ∀ (s125 : MachineState) (kA : Nat),
      kA ≤ 205 →
      StepsTo oracle s2 s125 kA 0 [] →
      s125.pc = pcWord 125 →
      CheckFixedRegs s125 →
      ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s125 →
      MemEqOutside s s125 256 320 →
      s125.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + step)) →
      s125.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) →
      s125.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) →
      s125.getReg .x27 = BitVec.ofNat 64 rem →
      s125.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)) →
      s125.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) →
      readBuffer s125 256 96 = inpL →
      readBuffer s125 320 32 = 0 →
      PhaseOutcome oracle s 216 1 (input.proof.length < pCur + 29 + tailBytes (tCur + 1))
        (fun s' q tr =>
          q = 1 ∧
          s'.pc = (if step + 1 = 14 then pcWord 134 else pcWord 110) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pCur + 29) (tCur + 1) s' ∧
          MemEqOutside s s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + (step + 1)) ∧
          readBuffer s' 320 32 = 0 ∧
          InTrace h768 oracle tr (pw.levelInput c96 (2 + step))) := by
    intro s125 kA hkA hmidA hpc125 hfix125 hcur125 hout125 h22 h24 h8 h27 h29 h30 hinp125 hgap125
    have hst125 := step_ordinary oracle s125 125 (.ADDI .x10 .x21 0#12) (by decide) hpc125 rfl (by intro h; cases h) rfl
    let s126 := execInstrBr s125 (.ADDI .x10 .x21 0#12)
    have hpc126 : s126.pc = pcWord 126 := by simp only [s126, execInstrBr, MachineState.setPC, hpc125, pcWord_add_four]
    have hst126 := step_ordinary oracle s126 126 (.ADDI .x12 .x21 0#12) (by decide) hpc126 rfl (by intro h; cases h) rfl
    let s127 := execInstrBr s126 (.ADDI .x12 .x21 0#12)
    have hpc127 : s127.pc = pcWord 127 := by simp only [s127, execInstrBr, MachineState.setPC, hpc126, pcWord_add_four]
    have hmem127 : s127.mem = s125.mem := by simp [s127, s126, execInstrBr, mem_setPC, mem_setReg]
    have hreg127 : ∀ r, r ≠ .x10 → r ≠ .x12 → s127.getReg r = s125.getReg r := fun r h10 h12 => by
      simp only [s127, s126, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
    have hx10_127 : s127.getReg .x10 = 256#64 := by
      simp only [s127, s126, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hfix125.x21, se12_0, BitVec.add_zero]
    have hx12_127 : s127.getReg .x12 = 256#64 := by
      simp only [s127, s126, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
        hfix125.x21, se12_0, BitVec.add_zero]
    have hec := step_ecall_compress h768 oracle s127 127 256 256 (by decide) hpc127 rfl
      ((hreg127 .x5 (by decide) (by decide)).trans hfix125.x5)
      ((hreg127 .x11 (by decide) (by decide)).trans hfix125.x11)
      ((hreg127 .x13 (by decide) (by decide)).trans hfix125.x13)
      hx10_127 hx12_127 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
    rw [(MemEqOutside.of_mem_eq hmem127 0 0).readBuffer_eq (by omega) (by omega), hinp125] at hec
    let s128 := writeBits s127 (BitVec.ofNat 64 256) (c96 inpL)
    have hpc128 : s128.pc = pcWord 128 := by simp only [s128, writeBits, MachineState.setPC, hpc127, pcWord_add_four]
    have hreg128 : ∀ r, r ≠ .x10 → r ≠ .x12 → s128.getReg r = s125.getReg r := fun r h10 h12 =>
      (writeBits_register s127 _ _ r).trans (hreg127 r h10 h12)
    obtain ⟨s131, hs131, hpc131, hreg131, hdig131, hout131⟩ :=
      step_mask238 oracle 128 .x21 s128 256 (by decide) (by decide) rfl rfl rfl hpc128
        ((hreg128 .x21 (by decide) (by decide)).trans hfix125.x21)
        ((hreg128 .x9 (by decide) (by decide)).trans hfix125.x9)
        (by decide) (by unfold MEMORY_BYTES; omega)
    have hdig_eq : readBuffer s131 256 32 = pw.evalLevel c96 (2 + (step + 1)) := by
      rw [heval_next, hdig131, writeBits_readBuffer_digest]
    have hgap131 : readBuffer s131 320 32 = 0 := by
      rw [hout131.readBuffer_eq (by omega) (by omega),
        (MemEqOutside_writeBits_digest s127 256 _ (by omega)).readBuffer_eq (by omega) (by omega),
        (MemEqOutside.of_mem_eq hmem127 0 0).readBuffer_eq (by omega) (by omega), hgap125]
    have hreg131_all : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s131.getReg r = s125.getReg r :=
      fun r h6 h10 h12 => (hreg131 r h6).trans (hreg128 r h10 h12)
    have hout131_all : MemEqOutside s s131 256 320 :=
      hout125.trans ((MemEqOutside.of_mem_eq hmem127 256 320).trans
        (((MemEqOutside_writeBits_digest s127 256 _ (by omega)).mono (by omega) (by omega)).trans
          (hout131.mono (by omega) (by omega))))
    -- pc[131..133]: SRLI x22, x22, 1; ADDI x29, x29, 32; BNE x29, x30, pc[110]
    have hst131 := step_ordinary oracle s131 131 (.SRLI .x22 .x22 1#6) (by decide) hpc131 rfl (by intro h; cases h) rfl
    let s132 := execInstrBr s131 (.SRLI .x22 .x22 1#6)
    have hpc132 : s132.pc = pcWord 132 := by simp only [s132, execInstrBr, MachineState.setPC, hpc131, pcWord_add_four]
    have hx22_132 : s132.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) := by
      simp only [s132, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg131_all .x22 (by decide) (by decide) (by decide), h22,
        show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr _ 1 (by omega), Nat.pow_one, shiftRight_div2]
      exact congrArg (fun k => BitVec.ofNat 64 (i.val >>> k)) (by omega)
    have hst132 := step_ordinary oracle s132 132 (.ADDI .x29 .x29 32#12) (by decide) hpc132 rfl (by intro h; cases h) rfl
    let s133 := execInstrBr s132 (.ADDI .x29 .x29 32#12)
    have hpc133 : s133.pc = pcWord 133 := by simp only [s133, execInstrBr, MachineState.setPC, hpc132, pcWord_add_four]
    have hmem133 : s133.mem = s131.mem := by simp [s133, s132, execInstrBr, mem_setPC, mem_setReg]
    have hx29_133 : s133.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      simp only [s133, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide)]
      simp only [s132, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x29),
        hreg131_all .x29 (by decide) (by decide) (by decide), h29, se12_32]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx30_133 : s133.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
      simp only [s133, s132, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x30),
        hreg131_all .x30 (by decide) (by decide) (by decide), h30]
    have hx22_133 : s133.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) := by
      simp only [s133, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x22), hx22_132]
    have hreg133 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x29 → s133.getReg r = s125.getReg r :=
      fun r h6 h10 h12 h22r h29r => by
        simp only [s133, s132, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h29r.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h22r.symm]
        exact hreg131_all r h6 h10 h12
    obtain ⟨sFin, hst133, hpcFin_raw, hregFin_133, hmemFin_133⟩ :=
      step_bne_reg oracle 133 110 .x29 .x30 8100#13 (by decide) rfl pc_133_branch s133
        (68719475936 + 32 * (2 + (step + 1))) (68719475936 + 32 * 16) (by omega) (by omega) hpc133 hx29_133 hx30_133
    have hpcFin : sFin.pc = if step + 1 = 14 then pcWord 134 else pcWord 110 := by
      rw [hpcFin_raw]; congr 1; exact propext (by omega)
    have hmemFin : sFin.mem = s131.mem := hmemFin_133.trans hmem133
    have hregFin : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x29 → sFin.getReg r = s125.getReg r :=
      fun r h6 h10 h12 h22r h29r => (hregFin_133 r).trans (hreg133 r h6 h10 h12 h22r h29r)
    have htot := (((hst110.trans hst111).trans hmidA).trans (((hst125.trans hst126).trans hec).trans hs131)).trans
      ((hst131.trans hst132).trans hst133)
    refine .continued sFin (2 + kA + 6 + 3) 1 [(inpL.cast h768.symm, c96 inpL)] (by omega) (by decide)
      (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
      ⟨rfl, hpcFin,
       hfix125.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
         (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       hcur125.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
         (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
       hout131_all.trans (MemEqOutside.of_mem_eq hmemFin 256 320),
       (hregFin_133 .x22).trans hx22_133,
       (hregFin .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24,
       (hregFin .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8,
       (hregFin .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27,
       (hregFin_133 .x29).trans hx29_133,
       (hregFin .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hdig_eq,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hgap131,
       by rw [hlinp]; exact InTrace.singleton h768 oracle inpL⟩
  by_cases heven : (i.val >>> (2 + step)) % 2 = 0
  · -- Even: pc[123..124] -> pc[125]
    have hx7z : s1.getReg .x7 = 0#64 := by rw [hx7_1, heven]
    have hpc2 : s2.pc = pcWord 123 := by
      simp only [s2, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
        MachineState.setPC, hpc1]; exact pc_111_branch
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x7 → s2.getReg r = s.getReg r := fun r h7 => by
      have : s2.getReg r = s1.getReg r := by
        simp only [s2, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
      rw [this]; simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
    have hst123 := step_ordinary oracle s2 123 (.ADDI .x12 .x21 32#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x12 .x21 32#12)
    have hpc3 : s3.pc = pcWord 124 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h7 h12 => by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
      exact hreg2 r h7
    have hx12_3 : s3.getReg .x12 = BitVec.ofNat 64 288 := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x21 (by decide), hfix.x21, se12_32]; decide
    have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 124 s3 pCur tCur 288
      (by decide) rfl hpc3
      (hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (hhigh.trans (MemEqOutside.of_mem_eq hmem3 0 4294971392)) hx12_3 (by omega)
    cases hread with
    | rejected kR qR trR hrR hkR hqR hhR =>
      have htot := ((hst110.trans hst111).trans hst123).halt hhR
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
      exact hcall125 s4 (1 + kR) (by omega)
        ((hst123.trans hs4).eq_of rfl rfl rfl (by simp only [List.nil_append]))
        hpc4
        (hfix.of_agree (fun r hr => hreg4_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        hcur4 (hout_all.mono (by omega) (by omega))
        ((hreg4_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg4_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg4_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg4_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg4_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg4_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        hinp4 hgap4
  · -- Odd: pc[112..122] -> pc[125]
    have hodd : (i.val >>> (2 + step)) % 2 = 1 := by omega
    have hx7o : s1.getReg .x7 = 1#64 := by rw [hx7_1, hodd]
    have hpc2 : s2.pc = pcWord 112 := by
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
        checkInstr (112 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
        checkInstr (112 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s3, hs3, hpc3, hreg3, hcopy3, hout3⟩ :=
      step_copy_dwords oracle 112 4 .x21 .x21 0 32 s2 256 256
        (by decide) (by decide) (by decide) (by decide) (by decide) hcC hpc2
        ((hreg2 .x21 (by decide)).trans hfix.x21)
        ((hreg2 .x21 (by decide)).trans hfix.x21)
        (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by decide)
    have hst120 := step_ordinary oracle s3 120 (.ADDI .x12 .x21 0#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x12 .x21 0#12)
    have hpc4 : s4.pc = pcWord 121 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
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
    have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 121 s4 pCur tCur 256
      (by decide) rfl hpc4
      (hcur.of_agree (fun r hr => hreg4 r (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      hhigh4 hx12_4 (by omega)
    cases hread with
    | rejected kR qR trR hrR hkR hqR hhR =>
      have htot := ((hst110.trans hst111).trans (hs3.trans hst120)).halt hhR
      have hkeq : 1 + 1 + (2 * 4 + 1) + kR = 11 + kR := by omega
      exact .rejected (11 + kR) qR trR hrR (by omega) (by omega)
        (by simpa only [Nat.zero_add, List.nil_append, hkeq] using htot)
    | continued s5 kR qR trR hkR hqR hs5 hp5 =>
      obtain ⟨rfl, rfl, hpc5, hcur5, hreg5, hdigL, hout5⟩ := hp5
      have hst122 := step_ordinary oracle s5 122 (.JAL .x0 12#21) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.JAL .x0 12#21)
      have hpc6 : s6.pc = pcWord 125 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5]; exact pc_122_jal
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
      exact hcall125 s6 (9 + kR + 1) (by omega)
        (((hs3.trans hst120).trans (hs5.trans hst122)).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]))
        hpc6
        (hfix.of_agree (fun r hr => hreg6_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (hcur5.of_agree (fun r _ => hreg6_5 r))
        hout_all
        ((hreg6_s .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg6_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg6_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg6_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        ((hreg6_s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg6_s .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        hinp6 hgap6

/-- Phase 1D: complete L2..L15 (238b) binary loop (`pc[109]` -> `pc[134]`), ≤ 3025 steps, 14 calls. -/
theorem step_pos_bin238_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 109)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 84) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> 2))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 2))
    (hl2 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h768.symm)) 2)
    (hgap : readBuffer s 320 32 = 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 3025 14 (input.proof.length < pOff + 490 + tailBytes (tOff + 14))
      (fun s' q tr =>
        q = 14 ∧
        s'.pc = pcWord 134 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 490) (tOff + 14) s' ∧
        MemEqOutside s s' 256 320 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 16 ∧
        ∀ prev, 2 ≤ prev → prev < 16 → InTrace h768 oracle tr (pw.levelInput c96 prev)) := by
  intro s0 c96 i pw
  -- pc[109]: ADDI x30, x2, 512
  have hst109 := step_ordinary oracle s 109 (.ADDI .x30 .x2 512#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x30 .x2 512#12)
  have hpc1 : s1.pc = pcWord 110 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x30 → s1.getReg r = s.getReg r := fun r h30 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h30.symm
  have hx30_1 : s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hfix.x2, se12_512, bv64_add]
  have hloop : ∀ n ≤ 14,
      PhaseOutcome oracle s1 (216 * n) n
        (input.proof.length < pOff + 84 + 29 * n + tailBytes (tOff + n))
        (fun s' q tr =>
          q = n ∧
          s'.pc = (if n = 14 then pcWord 134 else pcWord 110) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length (pOff + 84 + 29 * n) (tOff + n) s' ∧
          MemEqOutside s1 s' 256 320 ∧
          s'.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + n)) ∧
          s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord) ∧
          s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord) ∧
          s'.getReg .x27 = BitVec.ofNat 64 rem ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + n)) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
          readBuffer s' 256 32 = pw.evalLevel c96 (2 + n) ∧
          readBuffer s' 320 32 = 0 ∧
          ∀ prev, 2 ≤ prev → prev < 2 + n → InTrace h768 oracle tr (pw.levelInput c96 prev)) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued s1 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s1)
        ⟨rfl, by simpa using hpc1,
         hfix.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl)),
         by simpa using hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl)),
         MemEqOutside.refl s1 256 320,
         (hreg1 .x22 (by decide)).trans hx22, (hreg1 .x24 (by decide)).trans hx24,
         (hreg1 .x8  (by decide)).trans hx8,  (hreg1 .x27 (by decide)).trans hx27,
         (hreg1 .x29 (by decide)).trans hx29, hx30_1,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)).trans hl2,
         ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)).trans hgap,
         fun _ h1 h2 => by omega⟩
    | succ k ih =>
      have htb_m : tailBytes (tOff + k) ≤ tailBytes (tOff + (k + 1)) := tailBytes_mono (by omega)
      rw [show 216 * (k + 1) = 216 * k + 216 by omega]
      refine (ih (by omega)).bind_dep (by omega)
        (fun sk q1 tr1 hk => by
          obtain ⟨hq1, hpc_k, hfix_k, hcur_k, hout_k, hx22_k, hx24_k, hx8_k, hx27_k,
            hx29_k, hx30_k, hdig_k, hgap_k, htr_k⟩ := hk
          have hne14 : k ≠ 14 := by omega
          simp only [hne14, ite_false] at hpc_k
          have hhigh_k : HighMemPreserved s0 sk :=
            hhigh.trans ((MemEqOutside.of_mem_eq hmem1 0 4294971392).trans (hout_k.mono (by omega) (by omega)))
          have hstep_k := step_pos_bin238_iter h768 oracle input hvalid ord pOff tOff rem k hord (by omega)
            sk hpc_k hfix_k hcur_k hhigh_k hx22_k hx24_k hx8_k hx27_k hx29_k hx30_k hdig_k hgap_k
          refine hstep_k.weaken (by omega) (by omega) (by intro h; rw [Nat.add_assoc tOff k 1] at h; omega) ?_
          rintro s' q2 tr2 ⟨hq2, hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', htr'⟩
          refine ⟨by omega, hpc', hfix', ?_, hout_k.trans hout', hx22', hx24', hx8', hx27', hx29', hx30', hdig', hgap', ?_⟩
          · simpa only [show pOff + 84 + 29 * (k + 1) = pOff + 84 + 29 * k + 29 by omega,
              show tOff + (k + 1) = tOff + k + 1 by omega] using hcur'
          · intro prev hp1 hp2
            by_cases hprev : prev < 2 + k
            · exact (htr_k prev hp1 hprev).append_left
            · have : prev = 2 + k := by omega
              subst this; exact htr'.append_right)
  have h14 := hloop 14 (by decide)
  cases h14 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected (1 + k) q tr (by simpa only [show pOff + 84 + 29 * 14 = pOff + 490 by omega] using hr)
      (by omega) hq (by simpa using hst109.halt hh)
  | continued s' k q tr hk hq hs hp =>
    obtain ⟨hq', hpc', hfix', hcur', hout', hx22', hx24', hx8', hx27', _, _, hdig', _, htr'⟩ := hp
    refine .continued s' (1 + k) q tr (by omega) hq (by simpa using hst109.trans hs)
      ⟨hq', by simpa using hpc', hfix',
       by simpa only [show pOff + 84 + 29 * 14 = pOff + 490 by omega] using hcur',
       (MemEqOutside.of_mem_eq hmem1 256 320).trans hout',
       hx22', hx24', hx8', hx27', hdig',
       fun prev hp1 hp2 => htr' prev hp1 (by omega)⟩

/-! #### Phase 1E and Full Per-Position Loop (`pc[134..167]`, `pc[22] -> pc[168]`) -/

theorem gapOffset_disjoint {a b : Nat} (hne : a ≠ b) :
    gapOffset a + 32 ≤ gapOffset b ∨ gapOffset b + 32 ≤ gapOffset a := by
  unfold gapOffset; omega

theorem gapOffset_disjoint_gap (c q : Nat) :
    gapOffset c + 32 ≤ 96 * q + 64 ∨ 96 * q + 96 ≤ gapOffset c := by
  unfold gapOffset; omega

private def capAddrInstrs : List Instr :=
  [.SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6,
   .SLLI .x6 .x6 5#6, .ADD .x28 .x19 .x6, .ADD .x29 .x18 .x22]

private theorem pc_140_branch : pcWord 140 + signExtend13 48#13 = pcWord 152 := by decide
private theorem pc_151_jal : pcWord 151 + signExtend21 52#21 = pcWord 164 := by decide
private theorem pc_167_branch : pcWord 167 + signExtend13 7612#13 = pcWord 22 := by decide
private theorem checkInstr_139 : checkInstr 139 = .base (.LBU .x7 .x29 0#12) := rfl
private theorem checkInstr_140 : checkInstr 140 = .base (.BNE .x7 .x0 48#13) := rfl
private theorem checkInstr_141 : checkInstr 141 = .base (.ADDI .x7 .x0 1#12) := rfl
private theorem checkInstr_142 : checkInstr 142 = .base (.SB .x29 .x7 0#12) := rfl
private theorem checkInstr_151 : checkInstr 151 = .base (.JAL .x0 52#21) := rfl
private theorem checkInstr_164 : checkInstr 164 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_165 : checkInstr 165 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_166 : checkInstr 166 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_167 : checkInstr 167 = .base (.BNE .x27 .x0 7612#13) := rfl

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
    checkInstr (134 + j) = .base (capAddrInstrs[j]'hj) := by
  intro j hj; have hj' : j < 5 := hj; interval_cases j <;> rfl

private theorem hpure_capAddr : ∀ j (hj : j < capAddrInstrs.length),
    Instruction.base (capAddrInstrs[j]'hj) ≠ .base .ECALL ∧
    ∀ st, ordinaryStep st (.base (capAddrInstrs[j]'hj)) = some (execInstrBr st (capAddrInstrs[j]'hj)) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
          (execInstrBr st (capAddrInstrs[j]'hj)).mem = st.mem := by
  intro j hj; have hj' : j < 5 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩

private theorem hcode_capCopy : ∀ j < 4,
    checkInstr (143 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
    checkInstr (143 + 2 * j + 1) = .base (.SD .x28 .x6 (BitVec.ofNat 12 (0 + 8 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem hcode_capCmp : ∀ j < 4,
    checkInstr (152 + 3 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (152 + 3 * j + 1) = .base (.LD .x7 .x28 (BitVec.ofNat 12 (8 * j))) ∧
    checkInstr (152 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (231 - (152 + 3 * j + 2))))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

private theorem step_tail_164 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 164)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 165 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 164 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_164
     (by intro h; cases h) (ordinaryStep_ADDI s .x24 .x24 8#12),
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 164)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (7449087968 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 7449087968 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_165 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 165)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (7583305696 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 166 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (7583305696 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 165 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_165
     (by intro h; cases h) (ordinaryStep_ADDI s .x8 .x8 256#12),
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 165)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (7583305696 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 7583305696 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_166 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 166)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 167 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 166 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_166
     (by intro h; cases h) (ordinaryStep_ADDI s .x27 .x27 4095#12),
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 166)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_pos_cap_store_tail (oracle : Oracle) (s0 : MachineState)
    (proofLen ord pOffNext tOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s164 : MachineState) (hpc164 : s164.pc = pcWord 164)
    (hfix164 : CheckFixedRegs s164)
    (hcur164 : ProofCursor s0 proofLen pOffNext tOffNext s164)
    (h24 : s164.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord))
    (h8  : s164.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord))
    (h27 : s164.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s164 sFin 4 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 168 else pcWord 22) ∧
      CheckFixedRegs sFin ∧
      ProofCursor s0 proofLen pOffNext tOffNext sFin ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * (ord + 1)) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s164.mem := by
  obtain ⟨s165, hs1, hpc165, hmem1, hx24_1, hreg1⟩ := step_tail_164 oracle ord s164 hpc164 h24
  obtain ⟨s166, hs2, hpc166, hmem2, hx8_2, hreg2⟩ :=
    step_tail_165 oracle ord s165 hpc165 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s167, hs3, hpc167, hmem3, hx27_3, hreg3⟩ :=
    step_tail_166 oracle rem1 s166 hpc166 ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27))
  obtain ⟨sFin, hs4, hpcFin, hreg4, hmem4⟩ :=
    step_bne_reg oracle 167 22 .x27 .x0 7612#13 (by decide) checkInstr_167 pc_167_branch s167
      rem1 0 (by omega) (by omega) hpc167 hx27_3 (getReg_x0 s167)
  have hsteps : StepsTo oracle s164 sFin 4 0 [] :=
    (((hs1.trans hs2).trans hs3).trans hs4).eq_of rfl rfl rfl rfl
  have hmemFin : sFin.mem = s164.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x27 → sFin.getReg r = s164.getReg r :=
    fun r h24r h8r h27r => (hreg4 r).trans ((hreg3 r h27r).trans ((hreg2 r h8r).trans (hreg1 r h24r)))
  exact ⟨sFin, hsteps, hpcFin,
    hfix164.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hcur164.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    (hreg4 .x24).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1)),
    (hreg4 .x8).trans ((hreg3 .x8 (by decide)).trans hx8_2),
    (hreg4 .x27).trans hx27_3, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 256)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 141) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 256#64)
    (hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c))
    (hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (4096 + c))
    (d16 : Digest) (hd16 : readBuffer s 256 32 = d16) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 164 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
      readBuffer s7 (8192 + gapOffset c) 32 = d16 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
        (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst141 := step_ordinary oracle s3 141 (.ADDI .x7 .x0 1#12) (by decide) hpc3 checkInstr_141 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 142 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx29_4 : s4.getReg .x29 = BitVec.ofNat 64 (4096 + c) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29), hx29_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha142 : s4.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_4, se12_0, BitVec.add_zero]
  have hv142 : memoryArgumentsValid s4 (.SB .x29 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha142]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst142 := step_ordinary oracle s4 142 (.SB .x29 .x7 0#12) (by decide) hpc4 checkInstr_142 (by intro h; cases h)
    (by simp [ordinaryStep, hv142])
  let s5 := execInstrBr s4 (.SB .x29 .x7 0#12)
  have hpc5 : s5.pc = pcWord 143 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (4096 + c)) 1#8).getByte q := by
    intro q
    simp only [s5, execInstrBr, ha142, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
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
    step_copy_dwords oracle 143 4 .x21 .x28 0 0 s5 256 (8192 + gapOffset c)
      (by decide) (by decide) (by decide) (by decide) (by decide) hcode_capCopy hpc5
      ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide)).trans hx21)
      hx28_5 (by decide) (by omega) (by unfold MEMORY_BYTES; omega) (by omega) (by omega)
  have hst151 := step_ordinary oracle s6 151 (.JAL .x0 52#21) (by decide) hpc6 checkInstr_151 (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 164 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_151_jal
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
  refine ⟨s7, by simpa using ((hst141.trans hst142).trans hs6).trans hst151, hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1E: store or duplicate-check cap leaf at L16 and advance loop counters (`pc[134..167]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext tOffNext rem1 : Nat) (hord : ord < input.positions.card)
    (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 134)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOffNext tOffNext s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (capLeafOf (posAt input.positions ord)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1))
    (marked : Bool)
    (hmark : s.getByte (BitVec.ofNat 64 (4096 + capLeafOf (posAt input.positions ord))) =
      if marked then 1#8 else 0#8)
    (d16 : Digest) (hd16 : readBuffer s 256 32 = d16) :
    let s0 := submission.initialState .check input
    let c := capLeafOf (posAt input.positions ord)
    PhaseOutcome oracle s 30 0
      (marked = true ∧ d16 ≠ readBuffer s (8192 + gapOffset c) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = (if rem1 = 0 then pcWord 168 else pcWord 22) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pOffNext tOffNext s' ∧
        s'.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * (ord + 1)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
        readBuffer s' (8192 + gapOffset c) 32 = d16 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 4096 + c →
          (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro s0 c
  have hc_lt : c < 256 := capLeafOf_lt (posAt input.positions ord)
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 134 capAddrInstrs s (by decide) hcode_capAddr hpure_capAddr hpc
  let s1 := runInstrs s capAddrInstrs
  have hs1 : StepsTo oracle s s1 5 0 [] := hs1
  have hpc1 : s1.pc = pcWord 139 := hpc1
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
    have hcomp : (4096#64 : Word) + BitVec.ofNat 64 c = BitVec.ofNat 64 (4096 + c) := by
      change BitVec.ofNat 64 4096 + BitVec.ofNat 64 c = _; exact bv64_add 4096 c
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
  -- pc[139]: LBU x7, 0(x29)
  have ha139 : s1.getReg .x29 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx29_1, se12_0, BitVec.add_zero]
  have hv139 : memoryArgumentsValid s1 (.LBU .x7 .x29 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha139]
    exact accessValid_ofNat (4096 + c) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst139 := step_ordinary oracle s1 139 (.LBU .x7 .x29 0#12) (by decide) hpc1 checkInstr_139 (by intro h; cases h)
    (by simp [ordinaryStep, hv139])
  let s2 := execInstrBr s1 (.LBU .x7 .x29 0#12)
  have hpc2 : s2.pc = pcWord 140 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1'
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha139]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s1.getByte (BitVec.ofNat 64 (4096 + c)) = if marked then 1#8 else 0#8 := by
      simpa only [c, MachineState.getByte, MachineState.getMem, hmem1'] using hmark
    rw [hb, bool_byte_zeroExtend]
  have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → s2.getReg r = s.getReg r :=
    fun r h6 h7 h28 h29 => by
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg1 r h6 h28 h29
  -- pc[140]: BNE x7, x0, pc[152]
  have hst140 := step_ordinary oracle s2 140 (.BNE .x7 .x0 48#13) (by decide) hpc2 checkInstr_140 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 7 0 [] := by simpa using hs1.trans (hst139.trans hst140)
  cases marked with
  | false =>
    have hpc3 : s3.pc = pcWord 141 := by
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
    have hpc3 : s3.pc = pcWord 152 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_140_branch
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.setPC] using hmem2
    have hreg3 : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        MachineState.getReg_setPC]
    have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (8192 + gapOffset c) := by
      rw [hreg3]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx28_1]
    have hcmp := step_compare4 oracle 152 .x21 .x28 s3 256 (8192 + gapOffset c)
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

/-! #### Per-Position Loop Invariant and Induction (`pc[22] -> pc[168]`) -/

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
  posRecordOff n + tailBytes (posTailOff n) ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 input.proof.length (posRecordOff j1) (posTailOff j1)
      (posAt input.positions j1) (valAt input j1)).evalLevel c96 16 =
    (parsePartialWitness s0 input.proof.length (posRecordOff j2) (posTailOff j2)
      (posAt input.positions j2) (valAt input j2)).evalLevel c96 16

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff n) (posTailOff n) s
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if n = input.positions.card then pcWord 168 else pcWord 22
  x24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (7583305696 + 256 * n)
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
      (posRecordOff j) (posTailOff j) (posAt input.positions j) (valAt input j)
    pw.evalLevel c96 16 = readBuffer s (8192 + gapOffset (capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) ∧
    (∀ prev < 16, InTrace h768 oracle tr (pw.levelInput c96 prev))

/-- Complete per-position verification loop (`pc[22]` -> `pc[168]`), `≤ 3677 * k` steps, `≤ 20 * k` calls. -/
theorem step_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0)
    (sInit : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle sInit (3677 * input.positions.card) (20 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' q tr => q ≤ 20 * input.positions.card ∧ PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (3677 * n) (20 * n)
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
        have hp_m := posRecordOff_mono (show k ≤ k + 1 by omega)
        have ht_m := tailBytes_mono (posTailOff_mono (show k ≤ k + 1 by omega))
        refine ⟨by have := hcons.1; omega, ?_⟩
        intro j1 j2 hj1 hj2 hc
        exact hcons.2 j1 j2 (by omega) (by omega) hc
      rw [show 3677 * (k + 1) = 3677 * k + 3677 by omega,
        show 20 * (k + 1) = 20 * k + 20 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hlt_k : k < input.positions.card := by omega
        have hpc_k : sk.pc = pcWord 22 := by
          have := hinv_k.pc
          rwa [if_neg (by omega : k ≠ input.positions.card)] at this
        let pOff := posRecordOff k
        let tOff := posTailOff k
        let i := posAt input.positions k
        let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input k)
        let rem1 := input.positions.card - (k + 1)
        have hrem_eq : input.positions.card - k = rem1 + 1 := by omega
        have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
          rw [hinv_k.x27, hrem_eq]
        have htb_step : tailBytes tOff ≤ tailBytes (tOff + 14) := tailBytes_mono (by omega)
        -- 1A: leaf (190 steps, 4 calls)
        have h1a := step_pos_leaf h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
          sk hpc_k hinv_k.fixed hinv_k.cursor hinv_k.high hinv_k.x24 hinv_k.x8 hx27_k
        have hcan_leaf : input.proof.length < pOff + 24 + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
          intro hlt hcons
          have h1 := hcons.1
          rw [posRecordOff_succ, posTailOff_succ] at h1
          change pOff + 490 + tailBytes (tOff + 14) ≤ input.proof.length at h1
          omega
        -- Chain 1A (190,4) -> 1B (8,0) -> 1C (424,2) -> 1D (3025,14) -> 1E (30,0)
        refine PhaseOutcome.weaken
          (K1 := 190 + (8 + (424 + (3025 + 30)))) (Q1 := 4 + (2 + (14 + 0)))
          ?_ (by decide) (by decide) id (fun _ _ _ h => h)
        refine h1a.bind_dep hcan_leaf (fun s1 qA trA ⟨hqA, hpcA, hfixA, hcurA, houtA, hx20A, hx24A, hx8A, hx27A, hleafA, htrA⟩ => by
          obtain ⟨s2, hsB, hpcB, hfixB, hcurB, houtB, hx22B, hx24B, hx8B, hx27B, hx29B, hx30B, hl0B, hgapB⟩ :=
            step_pos_l0_setup h768 oracle input k pOff tOff (rem1 + 1)
              s1 hpcA hfixA hcurA hx20A hx24A hx8A hx27A hleafA
          refine hsB.prepend_pure ?_
          have hhighB : HighMemPreserved s0 s2 :=
            hinv_k.high.trans ((houtA.mono (by omega) (by omega)).trans (houtB.mono (by omega) (by omega)))
          have h1c := step_pos_bin240_loop h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
            s2 hpcB hfixB hcurB hhighB hx22B hx24B hx8B hx27B hx29B hx30B hl0B hgapB
          have hcan_240 : input.proof.length < pOff + 84 + tailBytes tOff → ¬ PosConsistent c96 s0 input (k + 1) := by
            intro hlt hcons
            have h1 := hcons.1
            rw [posRecordOff_succ, posTailOff_succ] at h1
            change pOff + 490 + tailBytes (tOff + 14) ≤ input.proof.length at h1
            omega
          refine h1c.bind_dep hcan_240 (fun s3 qC trC ⟨hqC, hpcC, hfixC, hcurC, houtC, hx22C, hx24C, hx8C, hx27C, hx29C, hl2C, hgapC, htrC⟩ => by
            have hhighC : HighMemPreserved s0 s3 := hhighB.trans (houtC.mono (by omega) (by omega))
            have h1d := step_pos_bin238_loop h768 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
              s3 hpcC hfixC hcurC hhighC hx22C hx24C hx8C hx27C hx29C hl2C hgapC
            have hcan_238 : input.proof.length < pOff + 490 + tailBytes (tOff + 14) → ¬ PosConsistent c96 s0 input (k + 1) := by
              intro hlt hcons
              have h1 := hcons.1
              rw [posRecordOff_succ, posTailOff_succ] at h1
              change pOff + 490 + tailBytes (tOff + 14) ≤ input.proof.length at h1
              omega
            refine h1d.bind_dep hcan_238 (fun s4 qD trD ⟨hqD, hpcD, hfixD, hcurD, houtD, hx22D, hx24D, hx8D, hx27D, hl16D, htrD⟩ => by
              have hout_sk_s4 : MemEqOutside sk s4 256 448 :=
                houtA.trans ((houtB.mono (by omega) (by omega)).trans
                  ((houtC.mono (by omega) (by omega)).trans (houtD.mono (by omega) (by omega))))
              have hhighD : HighMemPreserved s0 s4 := hinv_k.high.trans (hout_sk_s4.mono (by omega) (by omega))
              let c := capLeafOf i
              have hc_lt : c < 256 := capLeafOf_lt i
              have hmark4 : s4.getByte (BitVec.ofNat 64 (4096 + c)) =
                  if posMarked16 input.positions k c then 1#8 else 0#8 := by
                rw [hout_sk_s4 (4096 + c) (by omega) (by omega)]
                exact hinv_k.mark16 c hc_lt
              have h1e := step_pos_cap_store oracle input k (pOff + 490) (tOff + 14) rem1 hlt_k (by omega)
                s4 hpcD hfixD hcurD hx22D hx24D hx8D hx27D
                (posMarked16 input.positions k c) hmark4 (pw.evalLevel c96 16) hl16D
              have hcan_dup : (posMarked16 input.positions k c = true ∧
                  pw.evalLevel c96 16 ≠ readBuffer s4 (8192 + gapOffset c) 32) →
                  ¬ PosConsistent c96 s0 input (k + 1) := by
                rintro ⟨hmk, hne_dig⟩ hcons
                unfold posMarked16 at hmk
                rw [decide_eq_true_eq] at hmk
                obtain ⟨j, hj, hcj⟩ := hmk
                have hwj := (hinv_k.witnesses j hj).1
                have heq_rb : readBuffer s4 (8192 + gapOffset c) 32 = readBuffer sk (8192 + gapOffset c) 32 :=
                  hout_sk_s4.readBuffer_eq (by unfold gapOffset; omega) (by omega)
                have hcons_j := hcons.2 j k (by omega) (by omega) hcj
                rw [heq_rb, ← hcj, ← hwj] at hne_dig
                exact hne_dig hcons_j.symm
              refine h1e.weaken (le_refl _) (le_refl _) hcan_dup ?_
              rintro s5 qE trE ⟨rfl, rfl, hpc5, hfix5, hcur5, hx24_5, hx8_5, hx27_5, hmark5, hval5, hout5, hmem_dup⟩
              have hbyte_sk_s5 : ∀ a : Nat, a < 2 ^ 64 →
                  (a < 256 ∨ 448 ≤ a) → a ≠ 4096 + c →
                  (a < 8192 + gapOffset c ∨ 8192 + gapOffset c + 32 ≤ a) →
                  s5.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a ha h1 h2 h3 =>
                (hout5 a ha h2 h3).trans (hout_sk_s4 a ha h1)
              have hcap17_eq : capValOff 17 = 12288 := by decide
              have hc_val_lt : gapOffset c + 32 ≤ capValOff 17 := by
                rw [hcap17_eq]; unfold gapOffset; omega
              refine ⟨by omega, ?_⟩
              refine ⟨hfix5,
                by simpa only [posRecordOff_succ, posTailOff_succ] using hcur5,
                ?_, ?_, hx24_5, hx8_5, hx27_5, ?_, ?_, ?_, ?_, ?_⟩
              · -- HighMemPreserved
                intro a ha hge
                exact (hbyte_sk_s5 a ha (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans (hinv_k.high a ha hge)
              · -- pc
                have hiff : rem1 = 0 ↔ k + 1 = input.positions.card := by omega
                simpa only [hiff] using hpc5
              · -- mark16
                intro c' hc'
                rw [posMarked16_succ]
                by_cases heq : c = c'
                · subst heq; simp only [c, i, decide_true, Bool.or_true, ite_true]; exact hmark5
                · simp only [show ¬ (capLeafOf (posAt input.positions k) = c') from heq,
                    decide_false, Bool.or_false]
                  exact (hbyte_sk_s5 (4096 + c') (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))).trans
                    (hinv_k.mark16 c' hc')
              · -- mark_hi_zero
                intro a ha1 ha2
                exact (hbyte_sk_s5 a (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))).trans
                  (hinv_k.mark_hi_zero a ha1 ha2)
              · -- val16_gap_zero
                intro q hq b hb
                have hdisj := gapOffset_disjoint_gap c q
                exact (hbyte_sk_s5 (8192 + 96 * q + 64 + b) (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans
                  (hinv_k.val16_gap_zero q hq b hb)
              · -- val_hi_zero
                intro a ha1 ha2
                exact (hbyte_sk_s5 a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans
                  (hinv_k.val_hi_zero a ha1 ha2)
              · -- witnesses
                intro j hj
                by_cases hjk : j < k
                · obtain ⟨hw_val, hw_leaf, hw_bin⟩ := hinv_k.witnesses j hjk
                  let cj := capLeafOf (posAt input.positions j)
                  have hcj_lt : cj < 256 := capLeafOf_lt (posAt input.positions j)
                  have hrb_eq : readBuffer s5 (8192 + gapOffset cj) 32 = readBuffer sk (8192 + gapOffset cj) 32 := by
                    by_cases hceq : cj = c
                    · have hmk_t : posMarked16 input.positions k c = true := by
                        unfold posMarked16; rw [decide_eq_true_eq]; exact ⟨j, hjk, hceq⟩
                      have hmem54 : s5.mem = s4.mem := hmem_dup hmk_t
                      rw [(MemEqOutside.of_mem_eq hmem54 0 0).readBuffer_eq (by unfold gapOffset; omega) (by omega)]
                      exact hout_sk_s4.readBuffer_eq (by unfold gapOffset; omega) (by omega)
                    · apply readBuffer_congr2; intro b hb
                      have hdisj := gapOffset_disjoint hceq
                      exact hbyte_sk_s5 (8192 + gapOffset cj + b) (by unfold gapOffset; omega)
                        (Or.inr (by omega)) (by omega) (by omega)
                  refine ⟨hw_val.trans hrb_eq.symm,
                    fun x hx => (hw_leaf x hx).append_left,
                    fun prev hp => (hw_bin prev hp).append_left⟩
                · have hjeq : j = k := by omega
                  subst hjeq
                  refine ⟨hval5.symm, ?_, ?_⟩
                  · intro x hx
                    have h1 := (htrA x hx).append_left (t2 := trC ++ (trD ++ []))
                    exact h1.append_right
                  · intro prev hp
                    by_cases hlt2 : prev < 2
                    · have h1 := (htrC prev hlt2).append_left (t2 := trD ++ [])
                      have h2 := h1.append_right (t1 := trA)
                      exact h2.append_right
                    · have h1 := (htrD prev (by omega) hp).append_left (t2 := [])
                      have h2 := h1.append_right (t1 := trC)
                      have h3 := h2.append_right (t1 := trA)
                      exact h3.append_right))))
  exact hind input.positions.card (le_refl _)

end CommitGolfCandidate
