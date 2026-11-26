import CommitGolfCandidate.MoonCheckPosA

/-! Symbolic execution of the L2..L5 (240b) and L6..L15 (238b) binary loops, L16 cap-store,
and full per-position verification loop (`pc[105..196]`, `pc[23] -> pc[197]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_107_reject : pcWord 107 + signExtend13 544#13 = pcWord 243 := by decide
private theorem pc_109_even : pcWord 109 + signExtend13 56#13 = pcWord 123 := by decide
private theorem pc_122_join : pcWord 122 + signExtend21 20#21 = pcWord 127 := by decide
private theorem pc_131_m238 : pcWord 131 + signExtend13 12#13 = pcWord 134 := by decide
private theorem pc_133_skip : pcWord 133 + signExtend21 16#21 = pcWord 137 := by decide
private theorem pc_139_loop : pcWord 139 + signExtend13 8060#13 = pcWord 106 := by decide
private theorem pc_142_even : pcWord 142 + signExtend13 48#13 = pcWord 154 := by decide
private theorem pc_153_join : pcWord 153 + signExtend21 12#21 = pcWord 156 := by decide
private theorem pc_164_loop : pcWord 164 + signExtend13 8100#13 = pcWord 141 := by decide
private theorem pc_169_dup : pcWord 169 + signExtend13 48#13 = pcWord 181 := by decide
private theorem pc_180_tail : pcWord 180 + signExtend21 52#21 = pcWord 193 := by decide
private theorem pc_196_loop : pcWord 196 + signExtend13 7500#13 = pcWord 23 := by decide

private theorem checkInstr_139 : checkInstr 139 = .base (.BNE .x23 .x0 8060#13) := rfl
private theorem checkInstr_164 : checkInstr 164 = .base (.BNE .x23 .x0 8100#13) := rfl
private theorem checkInstr_193 : checkInstr 193 = .base (.ADDI .x24 .x24 8#12) := rfl
private theorem checkInstr_194 : checkInstr 194 = .base (.ADDI .x8 .x8 256#12) := rfl
private theorem checkInstr_195 : checkInstr 195 = .base (.ADDI .x27 .x27 4095#12) := rfl
private theorem checkInstr_196 : checkInstr 196 = .base (.BNE .x27 .x0 7500#13) := rfl

private theorem execInstrBr_ADDI_pc (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr st (.ADDI rd rs imm)).pc = st.pc + (4 : Word) := rfl
private theorem execInstrBr_ADDI_mem (st : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr st (.ADDI rd rs imm)).mem = st.mem := by
  simp only [execInstrBr, mem_setPC, mem_setReg]
private theorem execInstrBr_ADDI_getReg_eq (st : MachineState) (rd rs : Reg) (imm : BitVec 12) (hne : rd ≠ .x0) :
    (execInstrBr st (.ADDI rd rs imm)).getReg rd = st.getReg rs + signExtend12 imm := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hne]
private theorem execInstrBr_ADDI_getReg_ne (st : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (r : Reg) (hne : rd ≠ r) :
    (execInstrBr st (.ADDI rd rs imm)).getReg r = st.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
private theorem bv64_add_mul_step (base stride ord : Nat) :
    BitVec.ofNat 64 (base + stride * ord) + BitVec.ofNat 64 stride =
      BitVec.ofNat 64 (base + stride * (ord + 1)) := by
  rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by ring)
private theorem se12_8_ofNat : signExtend12 8#12 = BitVec.ofNat 64 8 := se12_8

/-! #### Isolated Backward-Branch 1-Step Lemmas -/

private theorem step_bne_139 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 139) (h23 : s.getReg .x23 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 140 else pcWord 106) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x23 .x0 8060#13),
    step_ordinary oracle s 139 (.BNE .x23 .x0 8060#13) (by decide) hpc checkInstr_139
      (by intro h; cases h) (ordinaryStep_BNE_base s .x23 .x0 8060#13),
    ?_, execInstrBr_BNE_mem_base s .x23 .x0 8060#13, execInstrBr_BNE_getReg_base s .x23 .x0 8060#13⟩
  have hne_iff : (s.getReg .x23 != s.getReg .x0) = decide (rem1 ≠ 0) := by
    rw [getReg_x0 s, h23]
    exact bv64_bne_eq rem1 0 hrem_lt (by omega)
  by_cases hz : rem1 = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x23 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false_base s .x23 .x0 8060#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 139))
  · rw [if_neg hz]
    have ht : (s.getReg .x23 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true_base s .x23 .x0 8060#13 ht).trans
      ((congrArg (· + signExtend13 8060#13) hpc).trans pc_139_loop)

private theorem step_bne_164 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 164) (h23 : s.getReg .x23 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 165 else pcWord 141) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x23 .x0 8100#13),
    step_ordinary oracle s 164 (.BNE .x23 .x0 8100#13) (by decide) hpc checkInstr_164
      (by intro h; cases h) (ordinaryStep_BNE_base s .x23 .x0 8100#13),
    ?_, execInstrBr_BNE_mem_base s .x23 .x0 8100#13, execInstrBr_BNE_getReg_base s .x23 .x0 8100#13⟩
  have hne_iff : (s.getReg .x23 != s.getReg .x0) = decide (rem1 ≠ 0) := by
    rw [getReg_x0 s, h23]
    exact bv64_bne_eq rem1 0 hrem_lt (by omega)
  by_cases hz : rem1 = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x23 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false_base s .x23 .x0 8100#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 164))
  · rw [if_neg hz]
    have ht : (s.getReg .x23 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true_base s .x23 .x0 8100#13 ht).trans
      ((congrArg (· + signExtend13 8100#13) hpc).trans pc_164_loop)

private theorem step_bne_196 (oracle : Oracle) (rem1 : Nat) (hrem_lt : rem1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 196) (h27 : s.getReg .x27 = BitVec.ofNat 64 rem1) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if rem1 = 0 then pcWord 197 else pcWord 23) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x27 .x0 7500#13),
    step_ordinary oracle s 196 (.BNE .x27 .x0 7500#13) (by decide) hpc checkInstr_196
      (by intro h; cases h) (ordinaryStep_BNE_base s .x27 .x0 7500#13),
    ?_, execInstrBr_BNE_mem_base s .x27 .x0 7500#13, execInstrBr_BNE_getReg_base s .x27 .x0 7500#13⟩
  have hne_iff : (s.getReg .x27 != s.getReg .x0) = decide (rem1 ≠ 0) := by
    rw [getReg_x0 s, h27]
    exact bv64_bne_eq rem1 0 hrem_lt (by omega)
  by_cases hz : rem1 = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x27 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false_base s .x27 .x0 7500#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 196))
  · rw [if_neg hz]
    have ht : (s.getReg .x27 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true_base s .x27 .x0 7500#13 ht).trans
      ((congrArg (· + signExtend13 7500#13) hpc).trans pc_196_loop)

/-! #### Phase 1D-1: L2..L5 (240-bit) Binary Loop (`pc[105..139]` -> `pc[140]`) -/

/-- One iteration (`step < 4`, level `l = 2 + step ∈ 2..5`, `x23 = 4 - step`) of the 240b loop (`pc[106..139]`). -/
theorem step_pos_bin240_iter (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hstep : step < 4)
    (s : MachineState) (hpc : s.pc = pcWord 106)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 88 + 30 * step) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx (2 + step) ((posAt input.positions ord).val >>> (2 + step))))
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (4 - step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hcurD : readBuffer s 4096 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation (2 + step)) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pCur := pOff + 88 + 30 * step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 215 1 (input.proof.length < pCur + 30 + tailBytes tOff)
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = (if step + 1 = 4 then pcWord 140 else pcWord 106) ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 88 + 30 * (step + 1)) tOff s' ∧
        MemEqOutside s s' 4096 4160 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (heapIdx (2 + (step + 1)) (i.val >>> (2 + (step + 1)))) ∧
        s'.getReg .x23 = BitVec.ofNat 64 (4 - (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation (2 + (step + 1)) ∧
        InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation (2 + step))) := by
  intro s0 c64 i pCur pw
  have hplen_bd : input.proof.length ≤ 8480886496 := hvalid
  have hle_cur : pCur + tailBytes tOff ≤ input.proof.length := hcur.le
  let hIdx := heapIdx (2 + step) (i.val >>> (2 + step))
  have hhIdx_lt : hIdx < 2 ^ 64 := Nat.lt_trans (heapIdx_shiftRight_lt i (2 + step) (by omega)) (by omega)
  have hmod : hIdx % 2 = (i.val >>> (2 + step)) % 2 := heapIdx_mod_two (2 + step) _ (by omega)
  -- pc[106..107]: bounds check 30B
  have hst106 := step_ordinary oracle s 106 (.ADDI .x6 .x25 30#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x6 .x25 30#12)
  have hpc1 : s1.pc = pcWord 107 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 (10804531232 + pCur + 30) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hcur.x25, se12_30_ofNat]
    exact bv64_add _ 30
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (10804531232 + (input.proof.length - tailBytes tOff)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hcur.x31]
  have hst107 := step_ordinary oracle s1 107 (.BLTU .x31 .x6 544#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BLTU .x31 .x6 544#13)
  have hult : BitVec.ult (s1.getReg .x31) (s1.getReg .x6) = decide (input.proof.length < pCur + 30 + tailBytes tOff) := by
    rw [hx31_1, hx6_1, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pCur + 30 + tailBytes tOff
  · have hpc2 : s2.pc = pcWord 243 := by
      simp only [s2, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc1]
      exact pc_107_reject
    exact .rejected 5 0 [] hshort (by decide) (by decide)
      (by simpa using (hst106.trans hst107).halt (halt_reject oracle s2 hpc2))
  · have hge30 : pCur + 30 + tailBytes tOff ≤ input.proof.length := by omega
    have hpc2 : s2.pc = pcWord 108 := by
      simp only [s2, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      have h21 : s2.mem = s1.mem := by
        simp only [s2, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      exact h21.trans (by simp [s1, execInstrBr, mem_setPC, mem_setReg])
    have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r h6 => by
      simp only [s2, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.getReg_setPC]
      simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
    -- pc[108..109]: parity test
    have hst108 := step_ordinary oracle s2 108 (.ANDI .x7 .x22 1#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ANDI .x7 .x22 1#12)
    have hpc3 : s3.pc = pcWord 109 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 ((i.val >>> (2 + step)) % 2) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x22 (by decide), hx22, se12_1,
        bv64_and_one hIdx hhIdx_lt, hmod]
    have hst109 := step_ordinary oracle s3 109 (.BEQ .x7 .x0 56#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.BEQ .x7 .x0 56#13)
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hpre4 : StepsTo oracle s s4 4 0 [] :=
      ((hst106.trans hst107).trans (hst108.trans hst109)).eq_of rfl (by decide) (by decide) (by simp)
    let sibD := pw.binSib (2 + step)
    have hsibD_eq : sibD = proofDigest30 s0 (10804531232 + pCur) := by
      simp only [sibD, pw, parsePartialWitness, show 2 + step ≠ 0 by omega, show 2 + step ≠ 1 by omega,
        ite_false, show 2 ≤ 2 + step ∧ 2 + step ≤ 5 by omega, and_self, ite_true,
        show 2 + step - 2 = step by omega, pCur, Nat.add_assoc]
    let curD := pw.evalLevel c64 oracle.permutation (2 + step)
    let inpL := pw.levelInput c64 oracle.permutation (2 + step)
    have hpCur_next : pCur + 30 = pOff + 88 + 30 * (step + 1) := by dsimp only [pCur]; omega
    -- Common finish pc[127..139]
    have hfinish : ∀ (s127 : MachineState) (kMid : Nat),
        kMid ≤ 195 →
        StepsTo oracle s4 s127 kMid 0 [] →
        s127.pc = pcWord 127 →
        ProofCursor s0 input.proof.length (pOff + 88 + 30 * (step + 1)) tOff s127 →
        MemEqOutside s s127 4096 4160 →
        (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s127.getReg r = s.getReg r) →
        readBuffer s127 4096 64 = inpL →
        PhaseOutcome oracle s 215 1 (input.proof.length < pCur + 30 + tailBytes tOff)
          (fun s' q tr =>
            q = 1 ∧ s'.pc = (if step + 1 = 4 then pcWord 140 else pcWord 106) ∧
            CheckFixedRegs s' ∧ s'.getReg .x11 = 64#64 ∧ s'.getReg .x13 = 0#64 ∧
            ProofCursor s0 input.proof.length (pOff + 88 + 30 * (step + 1)) tOff s' ∧
            MemEqOutside s s' 4096 4160 ∧
            s'.getReg .x22 = BitVec.ofNat 64 (heapIdx (2 + (step + 1)) (i.val >>> (2 + (step + 1)))) ∧
            s'.getReg .x23 = BitVec.ofNat 64 (4 - (step + 1)) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation (2 + (step + 1)) ∧
            InCompRows h512 oracle tr inpL) := by
      intro s127 kMid hkMid hmid hpc127 hcur127 hout127 hreg127 hinp127
      have hst127 := step_ordinary oracle s127 127 (.ADDI .x10 .x21 0#12) (by decide) hpc127 rfl (by intro h; cases h) rfl
      let s128 := execInstrBr s127 (.ADDI .x10 .x21 0#12)
      have hpc128 : s128.pc = pcWord 128 := by simp only [s128, execInstrBr, MachineState.setPC, hpc127, pcWord_add_four]
      have hst128 := step_ordinary oracle s128 128 (.ADDI .x12 .x21 0#12) (by decide) hpc128 rfl (by intro h; cases h) rfl
      let s129 := execInstrBr s128 (.ADDI .x12 .x21 0#12)
      have hpc129 : s129.pc = pcWord 129 := by simp only [s129, execInstrBr, MachineState.setPC, hpc128, pcWord_add_four]
      have hmem129 : s129.mem = s127.mem := by simp [s129, s128, execInstrBr, mem_setPC, mem_setReg]
      have hreg129 : ∀ r, r ≠ .x10 → r ≠ .x12 → s129.getReg r = s127.getReg r := fun r h10 h12 => by
        simp only [s129, s128, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx21_127 : s127.getReg .x21 = 4096#64 :=
        (hreg127 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21
      have hx10_129 : s129.getReg .x10 = 4096#64 := by
        simp only [s129, s128, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hx21_127, se12_0, BitVec.add_zero]
      have hx12_129 : s129.getReg .x12 = 4096#64 := by
        simp only [s129, s128, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21), hx21_127, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h512 oracle s129 129 4096 4096 (by decide) hpc129 rfl
        ((hreg129 .x5 (by decide) (by decide)).trans ((hreg127 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5))
        ((hreg129 .x11 (by decide) (by decide)).trans ((hreg127 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
        ((hreg129 .x13 (by decide) (by decide)).trans ((hreg127 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
        hx10_129 hx12_129 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem129 0 0).readBuffer_eq (by omega) (by omega), hinp127] at hec
      let s130 := writeBits s129 (BitVec.ofNat 64 4096) (c64 inpL)
      have hpc130 : s130.pc = pcWord 130 := by simp only [s130, writeBits, MachineState.setPC, hpc129, pcWord_add_four]
      have hreg130 : ∀ r, r ≠ .x10 → r ≠ .x12 → s130.getReg r = s127.getReg r := fun r h10 h12 =>
        (writeBits_register s129 _ _ r).trans (hreg129 r h10 h12)
      -- pc[130..136] -> pc[137]: mask240 (step < 3) or mask238 (step = 3)
      have hst130 := step_ordinary oracle s130 130 (.ADDI .x6 .x0 1#12) (by decide) hpc130 rfl (by intro h; cases h) rfl
      let s131 := execInstrBr s130 (.ADDI .x6 .x0 1#12)
      have hpc131 : s131.pc = pcWord 131 := by simp only [s131, execInstrBr, MachineState.setPC, hpc130, pcWord_add_four]
      have hx6_131 : s131.getReg .x6 = 1#64 := by
        simp only [s131, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
          ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
      have hx23_131 : s131.getReg .x23 = BitVec.ofNat 64 (4 - step) := by
        simp only [s131, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x23),
          hreg130 .x23 (by decide) (by decide),
          hreg127 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx23]
      have hst131 := step_ordinary oracle s131 131 (.BEQ .x23 .x6 12#13) (by decide) hpc131 rfl (by intro h; cases h) rfl
      let s132 := execInstrBr s131 (.BEQ .x23 .x6 12#13)
      have heq3 : (s131.getReg .x23 == s131.getReg .x6) = decide (step = 3) := by
        rw [hx23_131, hx6_131]
        change (BitVec.ofNat 64 (4 - step) == BitVec.ofNat 64 1) = _
        rw [bv64_beq_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      have hmem132 : s132.mem = s130.mem := by
        simp only [s132, execInstrBr]; split <;> simp [s131, execInstrBr, mem_setPC, mem_setReg]
      have hreg132 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s132.getReg r = s127.getReg r := fun r h6 h10 h12 => by
        have : s132.getReg r = s131.getReg r := by simp only [s132, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
        rw [this]; simp only [s131, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg130 r h10 h12
      -- Step to pc[137] in ≤ 3 steps with exact masked digest
      have hmask : ∃ s137 kM, kM ≤ 3 ∧ StepsTo oracle s132 s137 kM 0 [] ∧
          s137.pc = pcWord 137 ∧
          (∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s137.getReg r = s127.getReg r) ∧
          MemEqOutside s130 s137 4096 4128 ∧
          readBuffer s137 4096 32 = pw.evalLevel c64 oracle.permutation (2 + (step + 1)) := by
        by_cases hs3 : step = 3
        · have hpc132 : s132.pc = pcWord 134 := by
            simp only [s132, execInstrBr, heq3, hs3, decide_true, ite_true, MachineState.setPC, hpc131]
            exact pc_131_m238
          obtain ⟨s137, hs137, hpc137, hreg137, hdig137, hout137⟩ :=
            step_mask238 oracle 134 .x21 s132 4096 (by decide) (by decide) rfl rfl rfl hpc132
              ((hreg132 .x21 (by decide) (by decide) (by decide)).trans hx21_127)
              ((hreg132 .x9 (by decide) (by decide) (by decide)).trans
                ((hreg127 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x9))
              (by decide) (by unfold MEMORY_BYTES; decide)
          refine ⟨s137, 3, by decide, hs137, hpc137, fun r h6 h10 h12 => (hreg137 r h6).trans (hreg132 r h6 h10 h12),
            (MemEqOutside.of_mem_eq hmem132 4096 4128).trans hout137, ?_⟩
          rw [hdig137, (MemEqOutside.of_mem_eq hmem132 0 0).readBuffer_eq (by omega) (by omega),
            writeBits_readBuffer_digest]
          change mask238 (c64 inpL) = pw.evalLevel c64 oracle.permutation ((2 + step) + 1)
          simp only [WitnessPath.evalLevel, maskLevel, show ¬ ((2 + step) + 1 < 2 ∨ (2 + step) + 1 = 24) by omega,
            show ¬ ((2 + step) + 1 < 6) by omega, ite_false]; rfl
        · have hpc132 : s132.pc = pcWord 132 := by
            simp only [s132, execInstrBr, heq3, hs3, decide_false, Bool.false_eq_true, ite_false,
              MachineState.setPC, hpc131, pcWord_add_four]
          have ha132 : s132.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 4126 := by
            rw [hreg132 .x21 (by decide) (by decide) (by decide), hx21_127, se12_30]; decide
          have hv132 : memoryArgumentsValid s132 (.SH .x21 .x0 30#12) = true := by
            simp only [memoryArgumentsValid, memAccess, ha132]
            exact accessValid_ofNat 4126 2 (by unfold MEMORY_BYTES; decide) (by decide)
          have hst132 := step_ordinary oracle s132 132 (.SH .x21 .x0 30#12) (by decide) hpc132 rfl (by intro h; cases h)
            (by simp [ordinaryStep, hv132])
          let s133 := execInstrBr s132 (.SH .x21 .x0 30#12)
          have hpc133 : s133.pc = pcWord 133 := by simp only [s133, execInstrBr, MachineState.setPC, hpc132, pcWord_add_four]
          have hst133 := step_ordinary oracle s133 133 (.JAL .x0 16#21) (by decide) hpc133 rfl (by intro h; cases h) rfl
          let s137 := execInstrBr s133 (.JAL .x0 16#21)
          have hpc137 : s137.pc = pcWord 137 := by
            simp only [s137, execInstrBr, MachineState.setPC, hpc133]; exact pc_133_skip
          have hmem137 : s137.mem = s133.mem := by simp [s137, execInstrBr, mem_setPC, mem_setReg]
          have hout_sh : MemEqOutside s132 s133 4126 4128 := by
            intro q hq hout
            simp only [s133, execInstrBr, ha132, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
            exact MemEqOutside_setHalfword s132 4126 _ (by decide) (by omega) q hq hout
          refine ⟨s137, 2, by decide, (hst132.trans hst133).eq_of rfl (by decide) (by decide) (by simp), hpc137,
            fun r h6 h10 h12 => by
              have h1 : s137.getReg r = s133.getReg r := by simp [s137, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
              have h2 : s133.getReg r = s132.getReg r := by
                simp [s133, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
              exact h1.trans (h2.trans (hreg132 r h6 h10 h12)),
            (MemEqOutside.of_mem_eq hmem132 4096 4128).trans
              ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem137 4096 4128)), ?_⟩
          have hsh : readBuffer s133 4096 32 =
              readBuffer (s130.setHalfword (BitVec.ofNat 64 (4096 + 30)) 0#16) 4096 32 := by
            apply readBuffer_congr2; intro j hj
            simp [s133, execInstrBr, ha132, MachineState.getByte, MachineState.setHalfword,
              MachineState.getMem, MachineState.setMem, mem_setPC, hmem132, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [(MemEqOutside.of_mem_eq hmem137 0 0).readBuffer_eq (by omega) (by omega),
            hsh, sh_zero_mask240 s130 4096 (by decide) (by omega), writeBits_readBuffer_digest]
          change mask240 (c64 inpL) = pw.evalLevel c64 oracle.permutation ((2 + step) + 1)
          simp only [WitnessPath.evalLevel, maskLevel, show ¬ ((2 + step) + 1 < 2 ∨ (2 + step) + 1 = 24) by omega,
            show (2 + step) + 1 < 6 by omega, ite_false, ite_true]; rfl
      obtain ⟨s137, kM, hkM, hsM, hpc137, hreg137, hout137, hdig137⟩ := hmask
      -- pc[137..139]: SRLI x22, 1; ADDI x23, -1; BNE x23, x0, pc[106]
      have hst137 := step_ordinary oracle s137 137 (.SRLI .x22 .x22 1#6) (by decide) hpc137 rfl (by intro h; cases h) rfl
      let s138 := execInstrBr s137 (.SRLI .x22 .x22 1#6)
      have hpc138 : s138.pc = pcWord 138 := by simp only [s138, execInstrBr, MachineState.setPC, hpc137, pcWord_add_four]
      have hx22_138 : s138.getReg .x22 = BitVec.ofNat 64 (heapIdx (2 + (step + 1)) (i.val >>> (2 + (step + 1)))) := by
        simp only [s138, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg137 .x22 (by decide) (by decide) (by decide),
          hreg127 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx22,
          show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr hIdx 1 hhIdx_lt, Nat.pow_one]
        simpa only [show 2 + step + 1 = 2 + (step + 1) by omega] using
          congrArg (BitVec.ofNat 64) (heapIdx_shiftRight_div2 i (2 + step) (by omega))
      have hst138 := step_ordinary oracle s138 138 (.ADDI .x23 .x23 4095#12) (by decide) hpc138 rfl (by intro h; cases h) rfl
      let s139 := execInstrBr s138 (.ADDI .x23 .x23 4095#12)
      have hpc139 : s139.pc = pcWord 139 := by simp only [s139, execInstrBr, MachineState.setPC, hpc138, pcWord_add_four]
      have hx23_139 : s139.getReg .x23 = BitVec.ofNat 64 (4 - (step + 1)) := by
        simp only [s139, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide)]
        simp only [s138, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x23),
          hreg137 .x23 (by decide) (by decide) (by decide),
          hreg127 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx23,
          show 4 - step = (4 - (step + 1)) + 1 by omega]
        exact bv64_add_neg1 _
      obtain ⟨sFin, hst139, hpcFin_if, hmem139, hreg139⟩ :=
        step_bne_139 oracle (4 - (step + 1)) (by omega) s139 hpc139 hx23_139
      have hmemFin : sFin.mem = s137.mem := hmem139.trans (by simp [s139, s138, execInstrBr, mem_setPC, mem_setReg])
      have hregFin : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → sFin.getReg r = s127.getReg r :=
        fun r h6 h10 h12 h22 h23 => by
          rw [hreg139 r]
          simp only [s139, s138, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h23.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
          exact hreg137 r h6 h10 h12
      have hpcFin : sFin.pc = if step + 1 = 4 then pcWord 140 else pcWord 106 := by
        rw [hpcFin_if]
        split_ifs <;> first | rfl | omega
      have hout_all : MemEqOutside s sFin 4096 4160 :=
        hout127.trans ((MemEqOutside.of_mem_eq hmem129 4096 4160).trans
          (((MemEqOutside_writeBits_digest s129 4096 _ (by omega)).mono (by omega) (by omega)).trans
            ((hout137.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmemFin 4096 4160))))
      have htot := ((hpre4.trans hmid).trans (((hst127.trans hst128).trans hec).trans (hst130.trans hst131))).trans
        (hsM.trans ((hst137.trans hst138).trans hst139))
      refine .continued sFin (4 + kMid + 5 + kM + 3) 1 [PublicRow.compression (inpL.cast h512.symm) (c64 inpL)]
        (by omega) (by decide)
        (htot.eq_of rfl (by omega) (by decide) (by simp [c64]))
        ⟨rfl, hpcFin,
         hfix.of_agree (fun r hr => (hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
           (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
           (hreg127 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
             (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))),
         (hregFin .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg127 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11),
         (hregFin .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg127 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13),
         hcur127.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
           (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         hout_all,
         (hreg139 .x22).trans (by
           simp only [s139, execInstrBr, MachineState.getReg_setPC]
           rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x22), hx22_138]),
         (hreg139 .x23).trans hx23_139,
         (hregFin .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg127 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24),
         (hregFin .x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg127 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8),
         (hregFin .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg127 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
         ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hdig137,
         InCompRows.singleton h512 oracle inpL⟩
    by_cases heven : (i.val >>> (2 + step)) % 2 = 0
    · -- Even: pc[123..126] -> pc[127]
      have hx7z : s3.getReg .x7 = 0#64 := by rw [hx7_3, heven]
      have hpc4 : s4.pc = pcWord 123 := by
        simp only [s4, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc3]
        exact pc_109_even
      have hmem4 : s4.mem = s.mem := by
        simpa [s4, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem3
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → s4.getReg r = s.getReg r := fun r h6 h7 => by
        simp only [s4, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg2 r h6
      have hst123 := step_ordinary oracle s4 123 (.ADDI .x12 .x21 32#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
      let s5 := execInstrBr s4 (.ADDI .x12 .x21 32#12)
      have hpc5 : s5.pc = pcWord 124 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
      have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
      obtain ⟨s6, hs6, hpc6, hx25_6, hreg6, hcopy6, hout6⟩ :=
        step_call_read_n oracle 124 30 s5 (10804531232 + pCur) 4128 (by decide) (by decide) (by decide)
          rfl rfl hpc5
          (by simp only [s5, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg4 .x25 (by decide) (by decide), hcur.x25])
          (by simp only [s5, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide), hreg4 .x21 (by decide) (by decide), hfix.x21, se12_32]; decide)
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      -- pc[126]: SH x21, x0, 62
      have hx21_6 : s6.getReg .x21 = 4096#64 := by
        rw [hreg6 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg4 .x21 (by decide) (by decide), hfix.x21]
      have ha126 : s6.getReg .x21 + signExtend12 62#12 = BitVec.ofNat 64 4158 := by
        rw [hx21_6, se12_62]; decide
      have hv126 : memoryArgumentsValid s6 (.SH .x21 .x0 62#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha126]
        exact accessValid_ofNat 4158 2 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst126 := step_ordinary oracle s6 126 (.SH .x21 .x0 62#12) (by decide) hpc6 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv126])
      let s7 := execInstrBr s6 (.SH .x21 .x0 62#12)
      have hpc7 : s7.pc = pcWord 127 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hout_sh : MemEqOutside s6 s7 4158 4160 := by
        intro q hq hout
        simp only [s7, execInstrBr, ha126, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact MemEqOutside_setHalfword s6 4158 _ (by decide) (by omega) q hq hout
      have hout_all : MemEqOutside s s7 4128 4160 :=
        (MemEqOutside.of_mem_eq hmem5 4128 4160).trans
          ((hout6.mono (by omega) (by omega)).trans (hout_sh.mono (by omega) (by omega)))
      have hreg7_6 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
        simp [s7, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      have hreg7_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s7.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        rw [hreg7_6, hreg6 r h1 h6 h10 h12 h25]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
        exact hreg4 r h6 h7
      have hinp7 : readBuffer s7 4096 64 = inpL := by
        rw [readBuffer_binary s7 4096]
        have hL : readBuffer s7 4096 32 = curD :=
          (hout_all.readBuffer_eq (by omega) (by omega)).trans hcurD
        have hR : readBuffer s7 (4096 + 32) 32 = sibD := by
          rw [show 4096 + 32 = 4128 by omega, hsibD_eq]
          have hsh : readBuffer s7 4128 32 = readBuffer (s6.setHalfword (BitVec.ofNat 64 (4128 + 30)) 0#16) 4128 32 := by
            apply readBuffer_congr2; intro j hj
            simp [s7, execInstrBr, ha126, MachineState.getByte, MachineState.setHalfword,
              MachineState.getMem, MachineState.setMem, mem_setPC, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [hsh]
          apply sh_zero_readBuffer30 s6 s0 4128 (10804531232 + pCur) (by decide) (by omega)
          intro j hj
          rw [hcopy6 j hj]
          exact (hhigh.trans_mem_eq hmem5) (10804531232 + pCur + j) (by omega) (Or.inr (by omega))
        rw [hL, hR]; simp only [inpL, WitnessPath.levelInput, curD, sibD, show pw.index = i from rfl, heven, ite_true]
      have hcur7 : ProofCursor s0 input.proof.length (pOff + 88 + 30 * (step + 1)) tOff s7 := by
        refine ⟨by rw [← hpCur_next]; exact hge30, by rw [hreg7_6, hx25_6, ← hpCur_next]; congr 1,
          (hreg7_s .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x31,
          (hreg7_s .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x3,
          (hreg7_s .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x4⟩
      exact hfinish s7 185 (by decide)
        (((hst123.trans hs6).trans hst126).eq_of rfl (by decide) (by decide) (by simp))
        hpc7 hcur7 (hout_all.mono (by omega) (by omega)) hreg7_s hinp7
    · -- Odd: pc[110..122] -> pc[127]
      have hodd : (i.val >>> (2 + step)) % 2 = 1 := by omega
      have hx7o : s3.getReg .x7 = 1#64 := by rw [hx7_3, hodd]
      have hpc4 : s4.pc = pcWord 110 := by
        simp only [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc3, pcWord_add_four]
      have hmem4 : s4.mem = s.mem := by
        simpa [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem3
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → s4.getReg r = s.getReg r := fun r h6 h7 => by
        simp only [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg2 r h6
      obtain ⟨s5, hs5, hpc5, hreg5, hcopy5, hout5⟩ :=
        step_copy_dwords oracle 110 4 .x21 .x21 0 32 s4 4096 4096
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩) hpc4
          ((hreg4 .x21 (by decide) (by decide)).trans hfix.x21)
          ((hreg4 .x21 (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by omega)
      have hst118 := step_ordinary oracle s5 118 (.ADDI .x12 .x21 0#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ADDI .x12 .x21 0#12)
      have hpc6 : s6.pc = pcWord 119 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
      obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
        step_call_read_n oracle 119 30 s6 (10804531232 + pCur) 4096 (by decide) (by decide) (by decide)
          rfl rfl hpc6
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg5 .x25 (by decide), hreg4 .x25 (by decide) (by decide), hcur.x25])
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide), hreg5 .x21 (by decide),
                hreg4 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      -- pc[121]: SH x21, x0, 30; pc[122]: JAL x0, 20 -> pc[127]
      have hx21_7 : s7.getReg .x21 = 4096#64 := by
        rw [hreg7 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg5 .x21 (by decide),
          hreg4 .x21 (by decide) (by decide), hfix.x21]
      have ha121 : s7.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 4126 := by
        rw [hx21_7, se12_30]; decide
      have hv121 : memoryArgumentsValid s7 (.SH .x21 .x0 30#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha121]
        exact accessValid_ofNat 4126 2 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst121 := step_ordinary oracle s7 121 (.SH .x21 .x0 30#12) (by decide) hpc7 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv121])
      let s8 := execInstrBr s7 (.SH .x21 .x0 30#12)
      have hpc8 : s8.pc = pcWord 122 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
      have hst122 := step_ordinary oracle s8 122 (.JAL .x0 20#21) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let s9 := execInstrBr s8 (.JAL .x0 20#21)
      have hpc9 : s9.pc = pcWord 127 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8]; exact pc_122_join
      have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
      have hout_sh : MemEqOutside s7 s8 4126 4128 := by
        intro q hq hout
        simp only [s8, execInstrBr, ha121, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact MemEqOutside_setHalfword s7 4126 _ (by decide) (by omega) q hq hout
      have hout_all : MemEqOutside s s9 4096 4160 :=
        (MemEqOutside.of_mem_eq hmem4 4096 4160).trans
          ((hout5.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem6 4096 4160).trans
              ((hout7.mono (by omega) (by omega)).trans
                ((hout_sh.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 4096 4160)))))
      have hreg9_7 : ∀ r, s9.getReg r = s7.getReg r := fun r => by
        have h98 : s9.getReg r = s8.getReg r := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have h87 : s8.getReg r = s7.getReg r := by
          simp [s8, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        exact h98.trans h87
      have hreg9_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s9.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        rw [hreg9_7, hreg7 r h1 h6 h10 h12 h25]
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg5 r h6]
        exact hreg4 r h6 h7
      have hinp9 : readBuffer s9 4096 64 = inpL := by
        rw [readBuffer_binary s9 4096]
        have hL : readBuffer s9 4096 32 = sibD := by
          rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by omega) (by omega), hsibD_eq]
          have hsh : readBuffer s8 4096 32 = readBuffer (s7.setHalfword (BitVec.ofNat 64 (4096 + 30)) 0#16) 4096 32 := by
            apply readBuffer_congr2; intro j hj
            simp [s8, execInstrBr, ha121, MachineState.getByte, MachineState.setHalfword,
              MachineState.getMem, MachineState.setMem, mem_setPC, getReg_x0,
              show (0#64 : Word).truncate 16 = 0#16 by decide]
          rw [hsh]
          apply sh_zero_readBuffer30 s7 s0 4096 (10804531232 + pCur) (by decide) (by omega)
          intro j hj
          rw [hcopy7 j hj]
          have h6_0 : HighMemPreserved s0 s6 :=
            hhigh.trans_low ((MemEqOutside.of_mem_eq hmem4 4128 4160).trans
              (hout5.trans (MemEqOutside.of_mem_eq hmem6 4128 4160))) (by omega)
          exact h6_0 (10804531232 + pCur + j) (by omega) (Or.inr (by omega))
        have hR : readBuffer s9 (4096 + 32) 32 = curD := by
          rw [show 4096 + 32 = 4128 by omega,
            (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by omega) (by omega),
            hout_sh.readBuffer_eq (by omega) (by omega),
            hout7.readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega),
            show curD = readBuffer s 4096 32 from hcurD.symm]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy5 j hj
          simp only [Nat.add_zero, show 4096 + 32 = 4128 by omega] at hc
          rw [hc]; simp only [MachineState.getByte, MachineState.getMem, hmem4]
        rw [hL, hR]; simp only [inpL, WitnessPath.levelInput, curD, sibD, show pw.index = i from rfl, heven, ite_false]
      have hcur9 : ProofCursor s0 input.proof.length (pOff + 88 + 30 * (step + 1)) tOff s9 := by
        refine ⟨by rw [← hpCur_next]; exact hge30, by rw [hreg9_7, hx25_7, ← hpCur_next]; congr 1,
          (hreg9_s .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x31,
          (hreg9_s .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x3,
          (hreg9_s .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x4⟩
      exact hfinish s9 194 (by decide)
        ((((hs5.trans hst118).trans hs7).trans (hst121.trans hst122)).eq_of rfl (by decide) (by decide) (by simp))
        hpc9 hcur9 hout_all hreg9_s hinp9

/-- Full L2..L5 loop (`pc[105..139]` -> `pc[140]`), `≤ 870` steps, `4` oracle calls. -/
theorem step_pos_bin240_loop (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 105)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 88) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx 2 ((posAt input.positions ord).val >>> 2)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hcurD : readBuffer s 4096 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation 2) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 870 4 (input.proof.length < pOff + 208 + tailBytes tOff)
      (fun s' q tr =>
        q = 4 ∧
        s'.pc = pcWord 140 ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 208) tOff s' ∧
        MemEqOutside s s' 4096 4160 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (heapIdx 6 (i.val >>> 6)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation 6 ∧
        ∀ l, 2 ≤ l → l ≤ 5 → InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation l)) := by
  intro s0 c64 i pw
  have hst105 := step_ordinary oracle s 105 (.ADDI .x23 .x0 4#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x23 .x0 4#12)
  have hpc1 : s1.pc = pcWord 106 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x23 → s1.getReg r = s.getReg r := fun r h23 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h23.symm
  have hx23_1 : s1.getReg .x23 = BitVec.ofNat 64 4 := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hind : ∀ n ≤ 4,
      PhaseOutcome oracle s1 (215 * n) n (input.proof.length < pOff + 88 + 30 * n + tailBytes tOff)
        (fun sn q tr =>
          q = n ∧
          sn.pc = (if n = 4 then pcWord 140 else pcWord 106) ∧
          CheckFixedRegs sn ∧
          sn.getReg .x11 = 64#64 ∧
          sn.getReg .x13 = 0#64 ∧
          ProofCursor s0 input.proof.length (pOff + 88 + 30 * n) tOff sn ∧
          MemEqOutside s1 sn 4096 4160 ∧
          sn.getReg .x22 = BitVec.ofNat 64 (heapIdx (2 + n) (i.val >>> (2 + n))) ∧
          sn.getReg .x23 = BitVec.ofNat 64 (4 - n) ∧
          sn.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
          sn.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
          sn.getReg .x27 = BitVec.ofNat 64 rem ∧
          readBuffer sn 4096 32 = pw.evalLevel c64 oracle.permutation (2 + n) ∧
          ∀ step < n, InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation (2 + step))) := by
    intro n hn
    induction n with
    | zero =>
      refine .continued s1 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s1) ?_
      exact ⟨rfl, by simp [hpc1],
        hfix.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl)),
        (hreg1 .x11 (by decide)).trans hx11, (hreg1 .x13 (by decide)).trans hx13,
        by simpa using hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl)),
        MemEqOutside.refl s1 4096 4160, (hreg1 .x22 (by decide)).trans hx22, hx23_1,
        (hreg1 .x24 (by decide)).trans hx24, (hreg1 .x8 (by decide)).trans hx8, (hreg1 .x27 (by decide)).trans hx27,
        ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)).trans hcurD,
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      rw [show 215 * (k + 1) = 215 * k + 215 by omega]
      refine (ih (by omega)).bind_dep (by omega) (fun sk q1 tr1 ⟨hq1, hpck, hfixk, h11k, h13k,
          hcurk, houtk, hx22k, hx23k, hx24k, hx8k, hx27k, hdigk, htrk⟩ => by
        have hpck' : sk.pc = pcWord 106 := by rwa [if_neg (by omega : k ≠ 4)] at hpck
        have hhighk : HighMemPreserved s0 sk := (hhigh.trans_mem_eq hmem1).trans_low houtk (by omega)
        have hstep_k := step_pos_bin240_iter h512 oracle input hvalid ord pOff tOff rem k (by omega)
          sk hpck' hfixk h11k h13k hcurk hhighk hx22k hx23k hx24k hx8k hx27k hdigk
        refine hstep_k.weaken (le_refl _) (le_refl _) (by omega) ?_
        rintro sk1 q2 tr2 ⟨rfl, hpc2, hfix2, h11_2, h13_2, hcur2, hout2, hx22_2, hx23_2, hx24_2, hx8_2, hx27_2, hdig2, htr2⟩
        refine ⟨by omega, hpc2, hfix2, h11_2, h13_2, hcur2, houtk.trans hout2,
          hx22_2, hx23_2, hx24_2, hx8_2, hx27_2, hdig2, ?_⟩
        intro step hst
        by_cases hlt : step < k
        · exact (htrk step hlt).append_left
        · have : step = k := by omega
          subst this; exact htr2.append_right)
  refine (hst105.prepend_pure (hind 4 (le_refl 4))).weaken (by decide) (by decide) (by omega) ?_
  rintro s' q tr ⟨rfl, hpc', hfix', h11', h13', hcur', hout', hx22', _, hx24', hx8', hx27', hdig', htr'⟩
  refine ⟨rfl, by simpa using hpc', hfix', h11', h13',
    by simpa only [show pOff + 88 + 30 * 4 = pOff + 208 by omega] using hcur',
    (MemEqOutside.of_mem_eq hmem1 4096 4160).trans hout',
    hx22', hx24', hx8', hx27', hdig', fun l hl1 hl2 => ?_⟩
  have h := htr' (l - 2) (by omega)
  rwa [show 2 + (l - 2) = l by omega] at h

/-! #### Phase 1D-2: L6..L15 (238-bit) Binary Loop (`pc[140..164]` -> `pc[165]`) -/

/-- One iteration (`step < 10`, level `l = 6 + step ∈ 6..15`, `x23 = 10 - step`) of the 238b loop (`pc[141..164]`). -/
theorem step_pos_bin238_iter (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem step : Nat) (hstep : step < 10)
    (s : MachineState) (hpc : s.pc = pcWord 141)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 208 + 29 * step) (tOff + step) s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx (6 + step) ((posAt input.positions ord).val >>> (6 + step))))
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (10 - step))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hcurD : readBuffer s 4096 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation (6 + step)) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pCur := pOff + 208 + 29 * step
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 220 1 (input.proof.length < pCur + 29 + tailBytes (tOff + step + 1))
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = (if step + 1 = 10 then pcWord 165 else pcWord 141) ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 208 + 29 * (step + 1)) (tOff + (step + 1)) s' ∧
        MemEqOutside s s' 4096 4160 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (heapIdx (6 + (step + 1)) (i.val >>> (6 + (step + 1)))) ∧
        s'.getReg .x23 = BitVec.ofNat 64 (10 - (step + 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation (6 + (step + 1)) ∧
        InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation (6 + step))) := by
  intro s0 c64 i pCur pw
  let hIdx := heapIdx (6 + step) (i.val >>> (6 + step))
  have hhIdx_lt : hIdx < 2 ^ 64 := Nat.lt_trans (heapIdx_shiftRight_lt i (6 + step) (by omega)) (by omega)
  have hmod : hIdx % 2 = (i.val >>> (6 + step)) % 2 := heapIdx_mod_two (6 + step) _ (by omega)
  -- pc[141..142]: parity test
  have hst141 := step_ordinary oracle s 141 (.ANDI .x7 .x22 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ANDI .x7 .x22 1#12)
  have hpc1 : s1.pc = pcWord 142 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx7_1 : s1.getReg .x7 = BitVec.ofNat 64 ((i.val >>> (6 + step)) % 2) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx22, se12_1, bv64_and_one hIdx hhIdx_lt, hmod]
  have hst142 := step_ordinary oracle s1 142 (.BEQ .x7 .x0 48#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BEQ .x7 .x0 48#13)
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hpre2 : StepsTo oracle s s2 2 0 [] := (hst141.trans hst142).eq_of rfl (by decide) (by decide) (by simp)
  let sibD := pw.binSib (6 + step)
  have hsibD_eq : sibD = proofDigest238 s0 input.proof.length (10804531232 + pCur) (tOff + step) := by
    simp only [sibD, pw, parsePartialWitness, show 6 + step ≠ 0 by omega, show 6 + step ≠ 1 by omega,
      show ¬ (2 ≤ 6 + step ∧ 6 + step ≤ 5) by omega, ite_false,
      show 6 ≤ 6 + step ∧ 6 + step ≤ 15 by omega, and_self, ite_true,
      show 6 + step - 6 = step by omega, pCur, Nat.add_assoc]
  let curD := pw.evalLevel c64 oracle.permutation (6 + step)
  let inpL := pw.levelInput c64 oracle.permutation (6 + step)
  have hpCur_next : pCur + 29 = pOff + 208 + 29 * (step + 1) := by dsimp only [pCur]; omega
  -- Common finish from pc[156..164] (exact 9 steps, 1 call)
  have hfinish : ∀ (s156 : MachineState),
      s156.pc = pcWord 156 →
      ProofCursor s0 input.proof.length (pOff + 208 + 29 * (step + 1)) (tOff + (step + 1)) s156 →
      MemEqOutside s s156 4096 4160 →
      (∀ r : Reg, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
        s156.getReg r = s.getReg r) →
      readBuffer s156 4096 64 = inpL →
      ∃ sFin, StepsTo oracle s156 sFin 9 1 [PublicRow.compression (inpL.cast h512.symm) (c64 inpL)] ∧
        sFin.pc = (if step + 1 = 10 then pcWord 165 else pcWord 141) ∧
        CheckFixedRegs sFin ∧
        sFin.getReg .x11 = 64#64 ∧
        sFin.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 208 + 29 * (step + 1)) (tOff + (step + 1)) sFin ∧
        MemEqOutside s sFin 4096 4160 ∧
        sFin.getReg .x22 = BitVec.ofNat 64 (heapIdx (6 + (step + 1)) (i.val >>> (6 + (step + 1)))) ∧
        sFin.getReg .x23 = BitVec.ofNat 64 (10 - (step + 1)) ∧
        sFin.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        sFin.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        sFin.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer sFin 4096 32 = pw.evalLevel c64 oracle.permutation (6 + (step + 1)) := by
    intro s156 hpc156 hcur156 hout156 hreg156 hinp156
    have hst156 := step_ordinary oracle s156 156 (.ADDI .x10 .x21 0#12) (by decide) hpc156 rfl (by intro h; cases h) rfl
    let s157 := execInstrBr s156 (.ADDI .x10 .x21 0#12)
    have hpc157 : s157.pc = pcWord 157 := by simp only [s157, execInstrBr, MachineState.setPC, hpc156, pcWord_add_four]
    have hst157 := step_ordinary oracle s157 157 (.ADDI .x12 .x21 0#12) (by decide) hpc157 rfl (by intro h; cases h) rfl
    let s158 := execInstrBr s157 (.ADDI .x12 .x21 0#12)
    have hpc158 : s158.pc = pcWord 158 := by simp only [s158, execInstrBr, MachineState.setPC, hpc157, pcWord_add_four]
    have hmem158 : s158.mem = s156.mem := by simp [s158, s157, execInstrBr, mem_setPC, mem_setReg]
    have hreg158 : ∀ r, r ≠ .x10 → r ≠ .x12 → s158.getReg r = s156.getReg r := fun r h10 h12 => by
      simp only [s158, s157, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
    have hx21_156 : s156.getReg .x21 = 4096#64 :=
      (hreg156 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21
    have hx10_158 : s158.getReg .x10 = 4096#64 := by
      simp only [s158, s157, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hx21_156, se12_0, BitVec.add_zero]
    have hx12_158 : s158.getReg .x12 = 4096#64 := by
      simp only [s158, s157, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21), hx21_156, se12_0, BitVec.add_zero]
    have hec := step_ecall_compress h512 oracle s158 158 4096 4096 (by decide) hpc158 rfl
      ((hreg158 .x5 (by decide) (by decide)).trans
        ((hreg156 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5))
      ((hreg158 .x11 (by decide) (by decide)).trans
        ((hreg156 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
      ((hreg158 .x13 (by decide) (by decide)).trans
        ((hreg156 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
      hx10_158 hx12_158 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
    rw [(MemEqOutside.of_mem_eq hmem158 0 0).readBuffer_eq (by omega) (by omega), hinp156] at hec
    let s159 := writeBits s158 (BitVec.ofNat 64 4096) (c64 inpL)
    have hpc159 : s159.pc = pcWord 159 := by simp only [s159, writeBits, MachineState.setPC, hpc158, pcWord_add_four]
    have hreg159 : ∀ r, r ≠ .x10 → r ≠ .x12 → s159.getReg r = s156.getReg r := fun r h10 h12 =>
      (writeBits_register s158 _ _ r).trans (hreg158 r h10 h12)
    obtain ⟨s162, hs162, hpc162, hreg162, hdig162, hout162⟩ :=
      step_mask238 oracle 159 .x21 s159 4096 (by decide) (by decide) rfl rfl rfl hpc159
        ((hreg159 .x21 (by decide) (by decide)).trans hx21_156)
        ((hreg159 .x9 (by decide) (by decide)).trans
          ((hreg156 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x9))
        (by decide) (by unfold MEMORY_BYTES; decide)
    have hst162 := step_ordinary oracle s162 162 (.SRLI .x22 .x22 1#6) (by decide) hpc162 rfl (by intro h; cases h) rfl
    let s163 := execInstrBr s162 (.SRLI .x22 .x22 1#6)
    have hpc163 : s163.pc = pcWord 163 := by simp only [s163, execInstrBr, MachineState.setPC, hpc162, pcWord_add_four]
    have hx22_163 : s163.getReg .x22 = BitVec.ofNat 64 (heapIdx (6 + (step + 1)) (i.val >>> (6 + (step + 1)))) := by
      simp only [s163, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg162 .x22 (by decide), hreg159 .x22 (by decide) (by decide),
        hreg156 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hx22, show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr hIdx 1 hhIdx_lt, Nat.pow_one]
      simpa only [show 6 + step + 1 = 6 + (step + 1) by omega] using
        congrArg (BitVec.ofNat 64) (heapIdx_shiftRight_div2 i (6 + step) (by omega))
    have hst163 := step_ordinary oracle s163 163 (.ADDI .x23 .x23 4095#12) (by decide) hpc163 rfl (by intro h; cases h) rfl
    let s164 := execInstrBr s163 (.ADDI .x23 .x23 4095#12)
    have hpc164 : s164.pc = pcWord 164 := by simp only [s164, execInstrBr, MachineState.setPC, hpc163, pcWord_add_four]
    have hx23_164 : s164.getReg .x23 = BitVec.ofNat 64 (10 - (step + 1)) := by
      simp only [s164, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide)]
      simp only [s163, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x22 ≠ .x23),
        hreg162 .x23 (by decide), hreg159 .x23 (by decide) (by decide),
        hreg156 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hx23, show 10 - step = (10 - (step + 1)) + 1 by omega]
      exact bv64_add_neg1 _
    obtain ⟨sFin, hst164, hpcFin_if, hmem164, hreg164⟩ :=
      step_bne_164 oracle (10 - (step + 1)) (by omega) s164 hpc164 hx23_164
    have hmemFin : sFin.mem = s162.mem := hmem164.trans (by simp [s164, s163, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → sFin.getReg r = s156.getReg r :=
      fun r h6 h10 h12 h22 h23 => by
        rw [hreg164 r]
        simp only [s164, s163, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h23.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
        exact (hreg162 r h6).trans (hreg159 r h10 h12)
    have hpcFin : sFin.pc = if step + 1 = 10 then pcWord 165 else pcWord 141 := by
      rw [hpcFin_if]
      split_ifs <;> first | rfl | omega
    have hout_all : MemEqOutside s sFin 4096 4160 :=
      hout156.trans ((MemEqOutside.of_mem_eq hmem158 4096 4160).trans
        (((MemEqOutside_writeBits_digest s158 4096 _ (by omega)).mono (by omega) (by omega)).trans
          ((hout162.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmemFin 4096 4160))))
    have htot := (((hst156.trans hst157).trans hec).trans hs162).trans ((hst162.trans hst163).trans hst164)
    refine ⟨sFin, htot.eq_of rfl (by decide) (by decide) (by simp [c64]), hpcFin,
      hfix.of_agree (fun r hr => (hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
        (hreg156 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))),
      (hregFin .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg156 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11),
      (hregFin .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg156 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13),
      hcur156.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
      hout_all,
      (hreg164 .x22).trans (by
        simp only [s164, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x22), hx22_163]),
      (hreg164 .x23).trans hx23_164,
      (hregFin .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg156 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24),
      (hregFin .x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg156 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8),
      (hregFin .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg156 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
      ?_⟩
    rw [(MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega), hdig162, writeBits_readBuffer_digest]
    change mask238 (c64 inpL) = pw.evalLevel c64 oracle.permutation ((6 + step) + 1)
    simp only [WitnessPath.evalLevel, maskLevel, show ¬ ((6 + step) + 1 < 2 ∨ (6 + step) + 1 = 24) by omega,
      show ¬ ((6 + step) + 1 < 6) by omega, ite_false]; rfl
  by_cases heven : (i.val >>> (6 + step)) % 2 = 0
  · -- Even: pc[154..155] -> pc[156]
    have hx7z : s1.getReg .x7 = 0#64 := by rw [hx7_1, heven]
    have hpc2 : s2.pc = pcWord 154 := by
      simp only [s2, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc1]
      exact pc_142_even
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x7 → s2.getReg r = s.getReg r := fun r h7 => by
      simp only [s2, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
      simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
    have hst154 := step_ordinary oracle s2 154 (.ADDI .x12 .x21 32#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x12 .x21 32#12)
    have hpc3 : s3.pc = pcWord 155 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h7 h12 => by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
      exact hreg2 r h7
    have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 155 s3 pCur (tOff + step) 4128
      (by decide) rfl hpc3
      (hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (hhigh.trans_mem_eq hmem3)
      (by simp only [s3, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x21 (by decide), hfix.x21, se12_32]; decide)
      (by omega)
    refine (((hpre2.trans hst154).prepend_pure hread).bind_dep (K2 := 9) (Q2 := 1) id (fun s4 q4 tr4 ⟨hq4, htr4, hpc4, hcur4, hreg4, hdig4, hout4⟩ => by
      have hout_all : MemEqOutside s s4 4128 4160 := (MemEqOutside.of_mem_eq hmem3 4128 4160).trans hout4
      have hreg4_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s4.getReg r = s.getReg r := fun r h1 h3 h4 h6 h7 _ h12 h25 h31 =>
        (hreg4 r h1 h3 h4 h6 h7 h12 h25 h31).trans (hreg3 r h7 h12)
      have hinp4 : readBuffer s4 4096 64 = inpL := by
        rw [readBuffer_binary s4 4096]
        have hL : readBuffer s4 4096 32 = curD := (hout_all.readBuffer_eq (by omega) (by omega)).trans hcurD
        have hR : readBuffer s4 (4096 + 32) 32 = sibD := by rw [show 4096 + 32 = 4128 by omega, hsibD_eq]; exact hdig4
        rw [hL, hR]; simp only [inpL, WitnessPath.levelInput, curD, sibD, show pw.index = i from rfl, heven, ite_true]
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, houtFin, hx22Fin, hx23Fin, hx24Fin, hx8Fin, hx27Fin, hdigFin⟩ :=
        hfinish s4 hpc4 (by simpa only [hpCur_next, Nat.add_assoc] using hcur4) (hout_all.mono (by omega) (by omega)) hreg4_s hinp4
      refine .continued sFin 9 1 [PublicRow.compression (inpL.cast h512.symm) (c64 inpL)] (by decide) (by decide) hsFin ?_
      rw [hq4, htr4, Nat.zero_add, List.nil_append]
      exact ⟨rfl, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, houtFin, hx22Fin, hx23Fin, hx24Fin, hx8Fin, hx27Fin, hdigFin,
        InCompRows.singleton h512 oracle inpL⟩)).weaken (by omega) (by omega) id (fun _ _ _ h => h)
  · -- Odd: pc[143..153] -> pc[156]
    have hodd : (i.val >>> (6 + step)) % 2 = 1 := by omega
    have hx7o : s1.getReg .x7 = 1#64 := by rw [hx7_1, hodd]
    have hpc2 : s2.pc = pcWord 143 := by
      simp only [s2, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x7 → s2.getReg r = s.getReg r := fun r h7 => by
      simp only [s2, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
        Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
      simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
    obtain ⟨s3, hs3, hpc3, hreg3, hcopy3, hout3⟩ :=
      step_copy_dwords oracle 143 4 .x21 .x21 0 32 s2 4096 4096
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩) hpc2
        ((hreg2 .x21 (by decide)).trans hfix.x21)
        ((hreg2 .x21 (by decide)).trans hfix.x21)
        (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by omega)
    have hst151 := step_ordinary oracle s3 151 (.ADDI .x12 .x21 0#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x12 .x21 0#12)
    have hpc4 : s4.pc = pcWord 152 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s3.mem := by simp [s4, execInstrBr, mem_setPC, mem_setReg]
    have hreg4_s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → s4.getReg r = s.getReg r := fun r h6 h7 h12 => by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg3 r h6]
      exact hreg2 r h7
    have hout_s4 : MemEqOutside s s4 4128 4160 :=
      (MemEqOutside.of_mem_eq hmem2 4128 4160).trans (hout3.trans (MemEqOutside.of_mem_eq hmem4 4128 4160))
    have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 152 s4 pCur (tOff + step) 4096
      (by decide) rfl hpc4
      (hcur.of_agree (fun r hr => hreg4_s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (hhigh.trans_low hout_s4 (by omega))
      (by simp only [s4, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x21 (by decide), hreg2 .x21 (by decide), hfix.x21, se12_0, BitVec.add_zero])
      (by omega)
    refine ((((hpre2.trans hs3).trans hst151).prepend_pure hread).bind_dep (K2 := 10) (Q2 := 1) id
      (fun s5 q5 tr5 ⟨hq5, htr5, hpc5, hcur5, hreg5, hdig5, hout5⟩ => by
        have hst153 := step_ordinary oracle s5 153 (.JAL .x0 12#21) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s6 := execInstrBr s5 (.JAL .x0 12#21)
        have hpc6 : s6.pc = pcWord 156 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5]; exact pc_153_join
        have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
        have hreg6_5 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
          simp [s6, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        have hreg6_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
            s6.getReg r = s.getReg r := fun r h1 h3 h4 h6 h7 _ h12 h25 h31 =>
          (hreg6_5 r).trans ((hreg5 r h1 h3 h4 h6 h7 h12 h25 h31).trans (hreg4_s r h6 h7 h12))
        have hout_all : MemEqOutside s s6 4096 4160 :=
          (hout_s4.mono (by omega) (by omega)).trans
            ((hout5.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem6 4096 4160))
        have hinp6 : readBuffer s6 4096 64 = inpL := by
          rw [readBuffer_binary s6 4096]
          have hL : readBuffer s6 4096 32 = sibD := by
            rw [(MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega), hsibD_eq]; exact hdig5
          have hR : readBuffer s6 (4096 + 32) 32 = curD := by
            rw [show 4096 + 32 = 4128 by omega,
              (MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega),
              hout5.readBuffer_eq (by omega) (by omega),
              (MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega),
              show curD = readBuffer s 4096 32 from hcurD.symm]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy3 j hj
            simp only [Nat.add_zero, show 4096 + 32 = 4128 by omega] at hc
            rw [hc]; simp only [MachineState.getByte, MachineState.getMem, hmem2]
          rw [hL, hR]; simp only [inpL, WitnessPath.levelInput, curD, sibD, show pw.index = i from rfl, heven, ite_false]
        obtain ⟨sFin, hsFin, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, houtFin, hx22Fin, hx23Fin, hx24Fin, hx8Fin, hx27Fin, hdigFin⟩ :=
          hfinish s6 hpc6 (by simpa only [hpCur_next, Nat.add_assoc] using hcur5.of_agree (fun r _ => hreg6_5 r))
            hout_all hreg6_s hinp6
        refine .continued sFin 10 1 [PublicRow.compression (inpL.cast h512.symm) (c64 inpL)] (by decide) (by decide)
          ((hst153.trans hsFin).eq_of rfl (by decide) (by decide) (by simp)) ?_
        rw [hq5, htr5, Nat.zero_add, List.nil_append]
        exact ⟨rfl, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, houtFin, hx22Fin, hx23Fin, hx24Fin, hx8Fin, hx27Fin, hdigFin,
          InCompRows.singleton h512 oracle inpL⟩)).weaken (by omega) (by omega) id (fun _ _ _ h => h)

/-- Full L6..L15 loop (`pc[140..164]` -> `pc[165]`), `≤ 2210` steps, `10` oracle calls. -/
theorem step_pos_bin238_loop (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 140)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 208) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx 6 ((posAt input.positions ord).val >>> 6)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hcurD : readBuffer s 4096 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation 6) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 2210 10 (input.proof.length < pOff + 498 + tailBytes (tOff + 10))
      (fun s' q tr =>
        q = 10 ∧
        s'.pc = pcWord 165 ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 498) (tOff + 10) s' ∧
        MemEqOutside s s' 4096 4160 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (256 + capLeafOf i) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation 16 ∧
        ∀ l, 6 ≤ l → l ≤ 15 → InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation l)) := by
  intro s0 c64 i pw
  have hst140 := step_ordinary oracle s 140 (.ADDI .x23 .x0 10#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x23 .x0 10#12)
  have hpc1 : s1.pc = pcWord 141 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x23 → s1.getReg r = s.getReg r := fun r h23 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ h23.symm
  have hx23_1 : s1.getReg .x23 = BitVec.ofNat 64 10 := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hind : ∀ n ≤ 10,
      PhaseOutcome oracle s1 (220 * n) n (input.proof.length < pOff + 208 + 29 * n + tailBytes (tOff + n))
        (fun sn q tr =>
          q = n ∧
          sn.pc = (if n = 10 then pcWord 165 else pcWord 141) ∧
          CheckFixedRegs sn ∧
          sn.getReg .x11 = 64#64 ∧
          sn.getReg .x13 = 0#64 ∧
          ProofCursor s0 input.proof.length (pOff + 208 + 29 * n) (tOff + n) sn ∧
          MemEqOutside s1 sn 4096 4160 ∧
          sn.getReg .x22 = BitVec.ofNat 64 (heapIdx (6 + n) (i.val >>> (6 + n))) ∧
          sn.getReg .x23 = BitVec.ofNat 64 (10 - n) ∧
          sn.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
          sn.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
          sn.getReg .x27 = BitVec.ofNat 64 rem ∧
          readBuffer sn 4096 32 = pw.evalLevel c64 oracle.permutation (6 + n) ∧
          ∀ step < n, InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation (6 + step))) := by
    intro n hn
    induction n with
    | zero =>
      refine .continued s1 0 0 [] (by decide) (by decide) (StepsTo.refl oracle s1) ?_
      exact ⟨rfl, by simp [hpc1],
        hfix.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl)),
        (hreg1 .x11 (by decide)).trans hx11, (hreg1 .x13 (by decide)).trans hx13,
        by simpa using hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl)),
        MemEqOutside.refl s1 4096 4160, (hreg1 .x22 (by decide)).trans hx22, hx23_1,
        (hreg1 .x24 (by decide)).trans hx24, (hreg1 .x8 (by decide)).trans hx8, (hreg1 .x27 (by decide)).trans hx27,
        ((MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)).trans hcurD,
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      rw [show 220 * (k + 1) = 220 * k + 220 by omega]
      have htb_m := tailBytes_mono (show tOff + k ≤ tOff + (k + 1) by omega)
      refine (ih (by omega)).bind_dep (by omega) (fun sk q1 tr1 ⟨hq1, hpck, hfixk, h11k, h13k,
          hcurk, houtk, hx22k, hx23k, hx24k, hx8k, hx27k, hdigk, htrk⟩ => by
        have hpck' : sk.pc = pcWord 141 := by rwa [if_neg (by omega : k ≠ 10)] at hpck
        have hhighk : HighMemPreserved s0 sk := (hhigh.trans_mem_eq hmem1).trans_low houtk (by omega)
        have hstep_k := step_pos_bin238_iter h512 oracle input hvalid ord pOff tOff rem k (by omega)
          sk hpck' hfixk h11k h13k hcurk hhighk hx22k hx23k hx24k hx8k hx27k hdigk
        refine hstep_k.weaken (le_refl _) (le_refl _) (by rw [show tOff + k + 1 = tOff + (k + 1) by omega]; omega) ?_
        rintro sk1 q2 tr2 ⟨rfl, hpc2, hfix2, h11_2, h13_2, hcur2, hout2, hx22_2, hx23_2, hx24_2, hx8_2, hx27_2, hdig2, htr2⟩
        refine ⟨by omega, hpc2, hfix2, h11_2, h13_2, hcur2, houtk.trans hout2,
          hx22_2, hx23_2, hx24_2, hx8_2, hx27_2, hdig2, ?_⟩
        intro step hst
        by_cases hlt : step < k
        · exact (htrk step hlt).append_left
        · have : step = k := by omega
          subst this; exact htr2.append_right)
  refine (hst140.prepend_pure (hind 10 (le_refl 10))).weaken (by decide) (by decide) (by omega) ?_
  rintro s' q tr ⟨rfl, hpc', hfix', h11', h13', hcur', hout', hx22', _, hx24', hx8', hx27', hdig', htr'⟩
  refine ⟨rfl, by simpa using hpc', hfix', h11', h13',
    by simpa only [show pOff + 208 + 29 * 10 = pOff + 498 by omega] using hcur',
    (MemEqOutside.of_mem_eq hmem1 4096 4160).trans hout',
    by simpa only [show (6 + 10 : Nat) = 16 from rfl, heapIdx_16, capLeafOf] using hx22',
    hx24', hx8', hx27', hdig', fun l hl1 hl2 => ?_⟩
  have h := htr' (l - 6) (by omega)
  rwa [show 6 + (l - 6) = l by omega] at h

/-! #### Phase 1E: L16 Cap Store / Duplicate Check and Loop Footer (`pc[165..196]`) -/

private theorem step_tail_193 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 193) (h24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 194 ∧ s'.mem = s.mem ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * (ord + 1)) ∧
      ∀ r, r ≠ .x24 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x24 .x24 8#12),
   step_ordinary oracle s 193 (.ADDI .x24 .x24 8#12) (by decide) hpc checkInstr_193 (by intro h; cases h) rfl,
   (execInstrBr_ADDI_pc s .x24 .x24 8#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 193)),
   execInstrBr_ADDI_mem s .x24 .x24 8#12,
   (execInstrBr_ADDI_getReg_eq s .x24 .x24 8#12 (by decide)).trans
     ((congrArg (· + signExtend12 8#12) h24).trans
       ((congrArg (BitVec.ofNat 64 (6375346208 + 8 * ord) + ·) se12_8_ofNat).trans
         (bv64_add_mul_step 6375346208 8 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x24 .x24 8#12 r hr.symm⟩

private theorem step_tail_194 (oracle : Oracle) (ord : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 194) (h8 : s.getReg .x8 = BitVec.ofNat 64 (6509563936 + 256 * ord)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 195 ∧ s'.mem = s.mem ∧
      s'.getReg .x8 = BitVec.ofNat 64 (6509563936 + 256 * (ord + 1)) ∧
      ∀ r, r ≠ .x8 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x8 .x8 256#12),
   step_ordinary oracle s 194 (.ADDI .x8 .x8 256#12) (by decide) hpc checkInstr_194 (by intro h; cases h) rfl,
   (execInstrBr_ADDI_pc s .x8 .x8 256#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 194)),
   execInstrBr_ADDI_mem s .x8 .x8 256#12,
   (execInstrBr_ADDI_getReg_eq s .x8 .x8 256#12 (by decide)).trans
     ((congrArg (· + signExtend12 256#12) h8).trans
       ((congrArg (BitVec.ofNat 64 (6509563936 + 256 * ord) + ·) se12_256).trans
         (bv64_add_mul_step 6509563936 256 ord))),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x8 .x8 256#12 r hr.symm⟩

private theorem step_tail_195 (oracle : Oracle) (rem1 : Nat) (s : MachineState)
    (hpc : s.pc = pcWord 195) (h27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord 196 ∧ s'.mem = s.mem ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      ∀ r, r ≠ .x27 → s'.getReg r = s.getReg r :=
  ⟨execInstrBr s (.ADDI .x27 .x27 4095#12),
   step_ordinary oracle s 195 (.ADDI .x27 .x27 4095#12) (by decide) hpc checkInstr_195 (by intro h; cases h) rfl,
   (execInstrBr_ADDI_pc s .x27 .x27 4095#12).trans ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 195)),
   execInstrBr_ADDI_mem s .x27 .x27 4095#12,
   (execInstrBr_ADDI_getReg_eq s .x27 .x27 4095#12 (by decide)).trans
     ((congrArg (· + signExtend12 4095#12) h27).trans (bv64_add_neg1 rem1)),
   fun r hr => execInstrBr_ADDI_getReg_ne s .x27 .x27 4095#12 r hr.symm⟩

private theorem step_pos_cap_store_tail (oracle : Oracle) (s0 : MachineState)
    (proofLen ord pOffNext tOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s193 : MachineState) (hpc193 : s193.pc = pcWord 193)
    (hfix193 : CheckFixedRegs s193)
    (hx11_193 : s193.getReg .x11 = 64#64) (hx13_193 : s193.getReg .x13 = 0#64)
    (hcur193 : ProofCursor s0 proofLen pOffNext tOffNext s193)
    (h24 : s193.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (h8  : s193.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (h27 : s193.getReg .x27 = BitVec.ofNat 64 (rem1 + 1)) :
    ∃ sFin, StepsTo oracle s193 sFin 4 0 [] ∧
      sFin.pc = (if rem1 = 0 then pcWord 197 else pcWord 23) ∧
      CheckFixedRegs sFin ∧
      sFin.getReg .x11 = 64#64 ∧
      sFin.getReg .x13 = 0#64 ∧
      ProofCursor s0 proofLen pOffNext tOffNext sFin ∧
      sFin.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * (ord + 1)) ∧
      sFin.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * (ord + 1)) ∧
      sFin.getReg .x27 = BitVec.ofNat 64 rem1 ∧
      sFin.mem = s193.mem := by
  obtain ⟨s194, hs1, hpc194, hmem1, hx24_1, hreg1⟩ := step_tail_193 oracle ord s193 hpc193 h24
  obtain ⟨s195, hs2, hpc195, hmem2, hx8_2, hreg2⟩ :=
    step_tail_194 oracle ord s194 hpc194 ((hreg1 .x8 (by decide)).trans h8)
  obtain ⟨s196, hs3, hpc196, hmem3, hx27_3, hreg3⟩ :=
    step_tail_195 oracle rem1 s195 hpc195 ((hreg2 .x27 (by decide)).trans ((hreg1 .x27 (by decide)).trans h27))
  obtain ⟨sFin, hs4, hpcFin, hmem4, hreg4⟩ :=
    step_bne_196 oracle rem1 (Nat.lt_of_succ_lt hrem_lt) s196 hpc196 hx27_3
  have hsteps : StepsTo oracle s193 sFin 4 0 [] :=
    (((hs1.trans hs2).trans hs3).trans hs4).eq_of rfl (by decide) (by decide) (by simp)
  have hmemFin : sFin.mem = s193.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
  have hregFin : ∀ r, r ≠ .x24 → r ≠ .x8 → r ≠ .x27 → sFin.getReg r = s193.getReg r :=
    fun r h24r h8r h27r => (hreg4 r).trans ((hreg3 r h27r).trans ((hreg2 r h8r).trans (hreg1 r h24r)))
  exact ⟨sFin, hsteps, hpcFin,
    hfix193.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    (hregFin .x11 (by decide) (by decide) (by decide)).trans hx11_193,
    (hregFin .x13 (by decide) (by decide) (by decide)).trans hx13_193,
    hcur193.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    (hreg4 .x24).trans ((hreg3 .x24 (by decide)).trans ((hreg2 .x24 (by decide)).trans hx24_1)),
    (hreg4 .x8).trans ((hreg3 .x8 (by decide)).trans hx8_2),
    (hreg4 .x27).trans hx27_3, hmemFin⟩

private theorem step_pos_cap_store_first (oracle : Oracle) (c : Nat) (hc_lt : c < 256)
    (s s3 : MachineState) (hpc3 : s3.pc = pcWord 170) (hmem3 : s3.mem = s.mem)
    (hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → r ≠ .x15 → s3.getReg r = s.getReg r)
    (hx21 : s.getReg .x21 = 4096#64)
    (hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 (16384 + 32 * (256 + c)))
    (hx15_3 : s3.getReg .x15 = BitVec.ofNat 64 (8192 + (256 + c)))
    (d16 : Digest) (hd16 : readBuffer s 4096 32 = d16) :
    ∃ s7, StepsTo oracle s3 s7 11 0 [] ∧
      s7.pc = pcWord 193 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → r ≠ .x15 → s7.getReg r = s.getReg r) ∧
      s7.getByte (BitVec.ofNat 64 (8192 + (256 + c))) = 1#8 ∧
      readBuffer s7 (16384 + 32 * (256 + c)) 32 = d16 ∧
      (∀ a : Nat, a < 2 ^ 64 → a ≠ 8192 + (256 + c) →
        (a < 16384 + 32 * (256 + c) ∨ 16384 + 32 * (256 + c) + 32 ≤ a) →
        s7.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have hst170 := step_ordinary oracle s3 170 (.ADDI .x7 .x0 1#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 1#12)
  have hpc4 : s4.pc = pcWord 171 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hx15_4 : s4.getReg .x15 = BitVec.ofNat 64 (8192 + (256 + c)) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x15), hx15_3]
  have hx7_4 : s4.getReg .x7 = 1#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have ha171 : s4.getReg .x15 + signExtend12 0#12 = BitVec.ofNat 64 (8192 + (256 + c)) := by
    rw [hx15_4, se12_0, BitVec.add_zero]
  have hv171 : memoryArgumentsValid s4 (.SB .x15 .x7 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha171]
    exact accessValid_ofNat (8192 + (256 + c)) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst171 := step_ordinary oracle s4 171 (.SB .x15 .x7 0#12) (by decide) hpc4 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv171])
  let s5 := execInstrBr s4 (.SB .x15 .x7 0#12)
  have hpc5 : s5.pc = pcWord 172 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hbyte5 : ∀ q, s5.getByte q = (s.setByte (BitVec.ofNat 64 (8192 + (256 + c))) 1#8).getByte q := fun q => by
    simp only [s5, execInstrBr, ha171, hx7_4, show (1#64 : Word).truncate 8 = 1#8 by decide,
      MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, mem_setPC, hmem4]
  have hout5 : MemEqOutside s s5 (8192 + (256 + c)) (8192 + (256 + c) + 1) := by
    intro a ha hout
    rw [hbyte5]
    exact MemEqOutside_setByte s (8192 + (256 + c)) 1#8 (by omega) a ha hout
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → r ≠ .x15 → s5.getReg r = s.getReg r :=
    fun r h6 h7 h14 h15 => by
      have : s5.getReg r = s4.getReg r := by
        simp [s5, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [this]; simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg3 r h6 h7 h14 h15
  have hx14_5 : s5.getReg .x14 = BitVec.ofNat 64 (16384 + 32 * (256 + c)) := by
    have : s5.getReg .x14 = s4.getReg .x14 := by
      simp [s5, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    rw [this]; simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x14), hx14_3]
  obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
    step_copy_dwords oracle 172 4 .x21 .x14 0 0 s5 4096 (16384 + 32 * (256 + c))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩) hpc5
      ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide)).trans hx21)
      hx14_5 (by decide) (by omega) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; omega) (by omega)
  have hst180 := step_ordinary oracle s6 180 (.JAL .x0 52#21) (by decide) hpc6 rfl (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JAL .x0 52#21)
  have hpc7 : s7.pc = pcWord 193 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; exact pc_180_tail
  have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
  have hreg7 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → r ≠ .x15 → s7.getReg r = s.getReg r :=
    fun r h6 h7 h14 h15 => by
      have : s7.getReg r = s6.getReg r := by simp [s7, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
      exact this.trans ((hreg6 r h6).trans (hreg5 r h6 h7 h14 h15))
  have hm7 : s7.getByte (BitVec.ofNat 64 (8192 + (256 + c))) = 1#8 := by
    have : s7.getByte (BitVec.ofNat 64 (8192 + (256 + c))) = s6.getByte (BitVec.ofNat 64 (8192 + (256 + c))) := by
      simp [MachineState.getByte, MachineState.getMem, hmem7]
    rw [this, hout6 (8192 + (256 + c)) (by omega) (by omega), hbyte5, set_byte_read]; simp
  have hv7 : readBuffer s7 (16384 + 32 * (256 + c)) 32 = d16 := by
    rw [(MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by omega) (by omega), ← hd16]
    apply readBuffer_congr2; intro j hj
    have hc := hcopy6 j hj
    simp only [Nat.add_zero] at hc
    rw [hc]; exact hout5 (4096 + j) (by omega) (by omega)
  refine ⟨s7, (((hst170.trans hst171).trans hs6).trans hst180).eq_of rfl (by decide) (by decide) (by simp),
    hpc7, hreg7, hm7, hv7, ?_⟩
  intro a ha hne hout
  have h76 : s7.getByte (BitVec.ofNat 64 a) = s6.getByte (BitVec.ofNat 64 a) := by
    simp [MachineState.getByte, MachineState.getMem, hmem7]
  rw [h76, hout6 a ha (by simpa only [Nat.add_zero] using hout), hout5 a ha (by omega)]

/-- Phase 1E: store or duplicate-check cap leaf at L16 and advance loop counters (`pc[165..196]`). -/
theorem step_pos_cap_store (oracle : Oracle) (input : CheckInput)
    (ord pOffNext tOffNext rem1 : Nat) (hrem_lt : rem1 + 1 < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 165)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOffNext tOffNext s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (256 + capLeafOf (posAt input.positions ord)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (rem1 + 1))
    (marked : Bool)
    (hmark : s.getByte (BitVec.ofNat 64 (8192 + (256 + capLeafOf (posAt input.positions ord)))) =
      if marked then 1#8 else 0#8)
    (d16 : Digest) (hd16 : readBuffer s 4096 32 = d16) :
    let s0 := submission.initialState .check input
    let c := capLeafOf (posAt input.positions ord)
    PhaseOutcome oracle s 30 0
      (marked = true ∧ d16 ≠ readBuffer s (16384 + 32 * (256 + c)) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = (if rem1 = 0 then pcWord 197 else pcWord 23) ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length pOffNext tOffNext s' ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * (ord + 1)) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * (ord + 1)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem1 ∧
        s'.getByte (BitVec.ofNat 64 (8192 + (256 + c))) = 1#8 ∧
        readBuffer s' (16384 + 32 * (256 + c)) 32 = d16 ∧
        (∀ a : Nat, a < 2 ^ 64 → a ≠ 8192 + (256 + c) →
          (a < 16384 + 32 * (256 + c) ∨ 16384 + 32 * (256 + c) + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        (marked = true → s'.mem = s.mem)) := by
  intro s0 c
  have hc_lt : c < 256 := capLeafOf_lt (posAt input.positions ord)
  -- pc[165..167]: compute x14 = 16384 + 32*(256+c), x15 = 8192 + (256+c)
  have hst165 := step_ordinary oracle s 165 (.SLLI .x6 .x22 5#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1a := execInstrBr s (.SLLI .x6 .x22 5#6)
  have hpc1a : s1a.pc = pcWord 166 := by simp only [s1a, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst166 := step_ordinary oracle s1a 166 (.ADD .x14 .x19 .x6) (by decide) hpc1a rfl (by intro h; cases h) rfl
  let s1b := execInstrBr s1a (.ADD .x14 .x19 .x6)
  have hpc1b : s1b.pc = pcWord 167 := by simp only [s1b, execInstrBr, MachineState.setPC, hpc1a, pcWord_add_four]
  have hst167 := step_ordinary oracle s1b 167 (.ADD .x15 .x18 .x22) (by decide) hpc1b rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s1b (.ADD .x15 .x18 .x22)
  have hpc1 : s1.pc = pcWord 168 := by simp only [s1, execInstrBr, MachineState.setPC, hpc1b, pcWord_add_four]
  have hmem1 : s1.mem = s.mem := by simp [s1, s1b, s1a, execInstrBr, mem_setPC, mem_setReg]
  have hreg1 : ∀ r, r ≠ .x6 → r ≠ .x14 → r ≠ .x15 → s1.getReg r = s.getReg r := fun r h6 h14 h15 => by
    simp only [s1, s1b, s1a, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h15.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h14.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  have hx14_1 : s1.getReg .x14 = BitVec.ofNat 64 (16384 + 32 * (256 + c)) := by
    simp only [s1, s1b, s1a, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq,
      hx22, hfix.x19, show (5#6 : BitVec 6).toNat = 5 by decide]
    rw [bv64_shl (256 + c) 5 (by omega)]
    change BitVec.ofNat 64 16384 + BitVec.ofNat 64 ((256 + c) * 32) = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hx15_1 : s1.getReg .x15 = BitVec.ofNat 64 (8192 + (256 + c)) := by
    simp only [s1, s1b, s1a, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq,
      hx22, hfix.x18]
    change BitVec.ofNat 64 8192 + BitVec.ofNat 64 (256 + c) = _
    exact bv64_add 8192 (256 + c)
  -- pc[168..169]: LBU x7, 0(x15); BNE x7, x0, pc[181]
  have ha168 : s1.getReg .x15 + signExtend12 0#12 = BitVec.ofNat 64 (8192 + (256 + c)) := by
    rw [hx15_1, se12_0, BitVec.add_zero]
  have hv168 : memoryArgumentsValid s1 (.LBU .x7 .x15 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha168]
    exact accessValid_ofNat (8192 + (256 + c)) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst168 := step_ordinary oracle s1 168 (.LBU .x7 .x15 0#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv168])
  let s2 := execInstrBr s1 (.LBU .x7 .x15 0#12)
  have hpc2 : s2.pc = pcWord 169 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simpa [s2, execInstrBr, mem_setPC, mem_setReg] using hmem1
  have hx7_2 : s2.getReg .x7 = if marked then 1#64 else 0#64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha168]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s1.getByte (BitVec.ofNat 64 (8192 + (256 + c))) = if marked then 1#8 else 0#8 := by
      simpa only [c, MachineState.getByte, MachineState.getMem, hmem1] using hmark
    rw [hb, bool_byte_zeroExtend]
  have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → r ≠ .x15 → s2.getReg r = s.getReg r :=
    fun r h6 h7 h14 h15 => by
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
      exact hreg1 r h6 h14 h15
  have hst169 := step_ordinary oracle s2 169 (.BNE .x7 .x0 48#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x7 .x0 48#13)
  have hs03 : StepsTo oracle s s3 5 0 [] :=
    (((hst165.trans hst166).trans hst167).trans (hst168.trans hst169)).eq_of rfl (by decide) (by decide) (by simp)
  cases marked with
  | false =>
    have hpc3 : s3.pc = pcWord 170 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
        ite_false, MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, MachineState.setPC] using hmem2
    have hreg3s : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, MachineState.getReg_setPC]
    have hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 (16384 + 32 * (256 + c)) := by
      rw [hreg3s]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x14), hx14_1]
    have hx15_3 : s3.getReg .x15 = BitVec.ofNat 64 (8192 + (256 + c)) := by
      rw [hreg3s]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x15), hx15_1]
    obtain ⟨s7, hs7, hpc7, hreg7, hm7, hv7, hout7⟩ :=
      step_pos_cap_store_first oracle c hc_lt s s3 hpc3 hmem3
        (fun r h6 h7 h14 h15 => (hreg3s r).trans (hreg2 r h6 h7 h14 h15))
        hfix.x21 hx14_3 hx15_3 d16 hd16
    have hfix7 : CheckFixedRegs s7 :=
      hfix.of_agree (fun r hr => hreg7 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
    have hcur7 : ProofCursor s0 input.proof.length pOffNext tOffNext s7 :=
      hcur.of_agree (fun r hr => hreg7 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
        (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
    obtain ⟨sFin, hsFin, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
      step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s7 hpc7 hfix7
        ((hreg7 .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11)
        ((hreg7 .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13)
        hcur7
        ((hreg7 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
    exact .continued sFin 20 0 [] (by decide) (by decide)
      (((hs03.trans hs7).trans hsFin).eq_of rfl (by decide) (by decide) (by simp))
      ⟨rfl, rfl, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, hx24Fin, hx8Fin, hx27Fin,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hm7,
       ((MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega)).trans hv7,
       fun a ha hne hout => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout7 a ha hne hout,
       fun h => by cases h⟩
  | true =>
    have hpc3 : s3.pc = pcWord 181 := by
      simp only [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide,
        ite_true, MachineState.setPC, hpc2]
      exact pc_169_dup
    have hmem3 : s3.mem = s.mem := by
      simpa [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide, MachineState.setPC] using hmem2
    have hreg3 : ∀ r, s3.getReg r = s2.getReg r := fun r => by
      simp [s3, execInstrBr, hx7_2, getReg_x0, show (1#64 != 0#64) = true by decide, MachineState.getReg_setPC]
    have hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 (16384 + 32 * (256 + c)) := by
      rw [hreg3]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x14), hx14_1]
    have hcmp := step_compare4 oracle 181 .x21 .x14 s3 4096 (16384 + 32 * (256 + c))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl, rfl⟩) hpc3
      ((hreg3 .x21).trans ((hreg2 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
      hx14_3 (by decide) (by omega) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; omega)
    have hrb_s3_a : readBuffer s3 4096 32 = d16 :=
      ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)).trans hd16
    have hrb_s3_b : readBuffer s3 (16384 + 32 * (256 + c)) 32 = readBuffer s (16384 + 32 * (256 + c)) 32 :=
      (MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)
    cases hcmp with
    | rejected k q tr hr hk hq hh =>
      rw [hrb_s3_a, hrb_s3_b] at hr
      exact .rejected (5 + k) q tr ⟨rfl, hr⟩ (by omega) hq (by simpa using hs03.halt hh)
    | continued s4 k q tr hk hq hs4 hp4 =>
      obtain ⟨rfl, rfl, heq_dig, hpc4, hmem4, hreg4⟩ := hp4
      rw [hrb_s3_a, hrb_s3_b] at heq_dig
      have hmem4s : s4.mem = s.mem := hmem4.trans hmem3
      have hreg4s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x14 → r ≠ .x15 → s4.getReg r = s.getReg r :=
        fun r h6 h7 h14 h15 => (hreg4 r h6 h7).trans ((hreg3 r).trans (hreg2 r h6 h7 h14 h15))
      have hfix4 : CheckFixedRegs s4 :=
        hfix.of_agree (fun r hr => hreg4s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
      have hcur4 : ProofCursor s0 input.proof.length pOffNext tOffNext s4 :=
        hcur.of_agree (fun r hr => hreg4s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))
      obtain ⟨sFin, hsFin, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, hx24Fin, hx8Fin, hx27Fin, hmemFin⟩ :=
        step_pos_cap_store_tail oracle s0 input.proof.length ord pOffNext tOffNext rem1 hrem_lt s4 hpc4 hfix4
          ((hreg4s .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11)
          ((hreg4s .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13)
          hcur4
          ((hreg4s .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24)
          ((hreg4s .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8)
          ((hreg4s .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
      have hmemFins : sFin.mem = s.mem := hmemFin.trans hmem4s
      exact .continued sFin (5 + k + 4) 0 [] (by omega) (by decide)
        (by simpa [Nat.add_assoc] using (hs03.trans hs4).trans hsFin)
        ⟨rfl, rfl, hpcFin, hfixFin, h11Fin, h13Fin, hcurFin, hx24Fin, hx8Fin, hx27Fin,
         by simpa [MachineState.getByte, MachineState.getMem, hmemFins] using hmark,
         by rw [(MemEqOutside.of_mem_eq hmemFins 0 0).readBuffer_eq (by omega) (by omega), ← heq_dig],
         fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmemFins],
         fun _ => hmemFins⟩

/-! #### Per-Position Loop Invariant and Full Induction (`pc[23]` -> `pc[197]`) -/

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
def PosConsistent (c64 : Comp64) (p : Perm200) (s0 : MachineState) (input : CheckInput) (n : Nat) : Prop :=
  498 * n + tailBytes (10 * n) ≤ input.proof.length ∧
  ∀ j1 j2, j1 < n → j2 < n →
    capLeafOf (posAt input.positions j1) = capLeafOf (posAt input.positions j2) →
    (parsePartialWitness s0 input.proof.length (498 * j1) (10 * j1)
      (posAt input.positions j1) (valAt input j1)).evalLevel c64 p 16 =
    (parsePartialWitness s0 input.proof.length (498 * j2) (10 * j2)
      (posAt input.positions j2) (valAt input j2)).evalLevel c64 p 16

/-- Invariant maintained after processing `n` positions (`n ≤ input.positions.card`). -/
structure PosLoopInv (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : List PublicRow) : Prop where
  fixed : CheckFixedRegs s
  x11 : 0 < n → s.getReg .x11 = 64#64
  x13 : 0 < n → s.getReg .x13 = 0#64
  cursor : ProofCursor (submission.initialState .check input) input.proof.length (498 * n) (10 * n) s
  inp : InputMemPreserved (submission.initialState .check input) n s
  pc : s.pc = if n = input.positions.card then pcWord 197 else pcWord 23
  x24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * n)
  x8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * n)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (input.positions.card - n)
  mark16 : ∀ c < 256, s.getByte (BitVec.ofNat 64 (8192 + (256 + c))) =
    if posMarked16 input.positions n c then 1#8 else 0#8
  mark_lo_zero : ∀ h < 256, s.getByte (BitVec.ofNat 64 (8192 + h)) = 0#8
  witnesses : ∀ j < n,
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let pw := parsePartialWitness (submission.initialState .check input) input.proof.length
      (498 * j) (10 * j) (posAt input.positions j) (valAt input j)
    pw.evalLevel c64 oracle.permutation 16 =
      readBuffer s (16384 + 32 * (256 + capLeafOf (posAt input.positions j))) 32 ∧
    (∀ x ∈ pw.leafCompInputs c64 oracle.permutation, InCompRows h512 oracle tr x) ∧
    InPermRows oracle tr (pw.leafPermInput c64) ∧
    (∀ l < 16, InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation l))

/-- Complete per-position verification loop (`pc[23]` -> `pc[197]`), `≤ 3750 * k` steps, `≤ 20 * k` calls. -/
theorem step_pos_loop (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (sInit : MachineState) (hinit : PosLoopInv h512 oracle input 0 sInit []) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    PhaseOutcome oracle sInit (3750 * input.positions.card) (20 * input.positions.card)
      (¬ PosConsistent c64 oracle.permutation s0 input input.positions.card)
      (fun s' q tr => q ≤ 20 * input.positions.card ∧ PosLoopInv h512 oracle input input.positions.card s' tr) := by
  intro s0 c64
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hind : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle sInit (3750 * n) (20 * n)
        (¬ PosConsistent c64 oracle.permutation s0 input n)
        (fun s' q tr => q ≤ 20 * n ∧ PosLoopInv h512 oracle input n s' tr) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued sInit 0 0 [] (by decide) (by decide) (StepsTo.refl oracle sInit) ⟨by decide, hinit⟩
    | succ k ih =>
      have hcons_sub : ¬ PosConsistent c64 oracle.permutation s0 input k →
          ¬ PosConsistent c64 oracle.permutation s0 input (k + 1) := by
        intro hnot hcons
        apply hnot
        have ht_m := tailBytes_mono (show 10 * k ≤ 10 * (k + 1) by omega)
        exact ⟨by have := hcons.1; omega, fun j1 j2 hj1 hj2 hc => hcons.2 j1 j2 (by omega) (by omega) hc⟩
      rw [show 3750 * (k + 1) = 3750 * k + 3750 by omega,
        show 20 * (k + 1) = 20 * k + 20 by omega]
      refine (ih (by omega)).bind_dep hcons_sub (fun sk q1 tr1 ⟨hq1, hinv_k⟩ => by
        have hlt_k : k < input.positions.card := by omega
        have hpc_k : sk.pc = pcWord 23 := by
          have := hinv_k.pc; rwa [if_neg (by omega : k ≠ input.positions.card)] at this
        let pOff := 498 * k
        let tOff := 10 * k
        let i := posAt input.positions k
        let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input k)
        let rem1 := input.positions.card - (k + 1)
        have hx27_k : sk.getReg .x27 = BitVec.ofNat 64 (rem1 + 1) := by
          rw [hinv_k.x27, show input.positions.card - k = rem1 + 1 by omega]
        have htb_step : tailBytes tOff ≤ tailBytes (tOff + 10) := tailBytes_mono (by omega)
        have h1a := step_pos_leaf h512 oracle input hvalid k pOff tOff (rem1 + 1) hlt_k
          sk hpc_k hinv_k.fixed hinv_k.cursor hinv_k.inp hinv_k.x24 hinv_k.x8 hx27_k
        have hcan_sub : ∀ d ≤ 498, input.proof.length < pOff + d + tailBytes tOff →
            ¬ PosConsistent c64 oracle.permutation s0 input (k + 1) := by
          intro d hd hlt hcons
          have h1 := hcons.1
          change 498 * (k + 1) + tailBytes (10 * (k + 1)) ≤ input.proof.length at h1
          have : pOff + d ≤ 498 * (k + 1) := by dsimp only [pOff]; omega
          have : tailBytes tOff ≤ tailBytes (10 * (k + 1)) := by dsimp only [tOff]; exact tailBytes_mono (by omega)
          omega
        refine PhaseOutcome.weaken
          (K1 := 180 + (220 + (220 + (870 + (2210 + 30))))) (Q1 := 4 + (1 + (1 + (4 + (10 + 0)))))
          ?_ (by decide) (by decide) id (fun _ _ _ h => h)
        refine h1a.bind_dep (hcan_sub 24 (by decide)) (fun s1 qA trA ⟨hqA, hpcA, hfixA, h11A, h13A,
            hcurA, hinpA, hlowA, hx22A, hx24A, hx8A, hx27A, hleafA, htrAC, htrAP⟩ => by
          have h1b := step_pos_l0 h512 oracle input hvalid k pOff tOff (rem1 + 1)
            s1 hpcA hfixA h11A h13A hcurA (hinpA.toHigh (by omega)) hx22A hx24A hx8A hx27A hleafA
          refine h1b.bind_dep (hcan_sub 56 (by decide)) (fun s2 qB trB ⟨hqB, hpcB, hfixB, h11B, h13B,
              hcurB, houtB, hx22B, hx24B, hx8B, hx27B, hl1B, htrB⟩ => by
            have hinpB : InputMemPreserved s0 (k + 1) s2 := hinpA.trans_low houtB (by omega)
            have h1c := step_pos_l1 h512 oracle input hvalid k pOff tOff (rem1 + 1)
              s2 hpcB hfixB h11B h13B hcurB (hinpB.toHigh (by omega)) hx22B hx24B hx8B hx27B hl1B
            refine h1c.bind_dep (hcan_sub 88 (by decide)) (fun s3 qC trC ⟨hqC, hpcC, hfixC, h11C, h13C,
                hcurC, houtC, hx22C, hx24C, hx8C, hx27C, hl2C, htrC⟩ => by
              have hinpC : InputMemPreserved s0 (k + 1) s3 := hinpB.trans_low houtC (by omega)
              have h1d1 := step_pos_bin240_loop h512 oracle input hvalid k pOff tOff (rem1 + 1)
                s3 hpcC hfixC h11C h13C hcurC (hinpC.toHigh (by omega)) hx22C hx24C hx8C hx27C hl2C
              refine h1d1.bind_dep (hcan_sub 208 (by decide)) (fun s3b qD1 trD1 ⟨hqD1, hpcD1, hfixD1, h11D1, h13D1,
                  hcurD1, houtD1, hx22D1, hx24D1, hx8D1, hx27D1, hl6D1, htrD1⟩ => by
                have hinpD1 : InputMemPreserved s0 (k + 1) s3b := hinpC.trans_low houtD1 (by omega)
                have h1d2 := step_pos_bin238_loop h512 oracle input hvalid k pOff tOff (rem1 + 1)
                  s3b hpcD1 hfixD1 h11D1 h13D1 hcurD1 (hinpD1.toHigh (by omega)) hx22D1 hx24D1 hx8D1 hx27D1 hl6D1
                have hcan_d2 : input.proof.length < pOff + 498 + tailBytes (tOff + 10) →
                    ¬ PosConsistent c64 oracle.permutation s0 input (k + 1) := by
                  intro hlt hcons
                  have h1 := hcons.1
                  change 498 * (k + 1) + tailBytes (10 * (k + 1)) ≤ input.proof.length at h1
                  have hp : pOff + 498 = 498 * (k + 1) := by dsimp only [pOff]; omega
                  have ht : tOff + 10 = 10 * (k + 1) := by dsimp only [tOff]; omega
                  rw [hp, ht] at hlt
                  omega
                refine h1d2.bind_dep hcan_d2 (fun s4 qD2 trD2 ⟨hqD2, hpcD2, hfixD2, h11D2, h13D2,
                    hcurD2, houtD2, hx22D2, hx24D2, hx8D2, hx27D2, hd16D, htrD2⟩ => by
                  have hinpD2 : InputMemPreserved s0 (k + 1) s4 := hinpD1.trans_low houtD2 (by omega)
                  have hout_14 : MemEqOutside s1 s4 4096 4160 :=
                    houtB.trans (houtC.trans (houtD1.trans houtD2))
                  have hlow_sk4 : ∀ a : Nat, 4160 ≤ a → a < 4294971392 →
                      s4.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a hlo hhi =>
                    (hout_14 a (by omega) (by omega)).trans (hlowA a hlo hhi)
                  have hc_lt : capLeafOf i < 256 := capLeafOf_lt i
                  have hmark4 : s4.getByte (BitVec.ofNat 64 (8192 + (256 + capLeafOf i))) =
                      if posMarked16 input.positions k (capLeafOf i) then 1#8 else 0#8 :=
                    (hlow_sk4 (8192 + (256 + capLeafOf i)) (by omega) (by omega)).trans (hinv_k.mark16 (capLeafOf i) hc_lt)
                  have h1e := step_pos_cap_store oracle input k (pOff + 498) (tOff + 10) rem1 (by omega)
                    s4 hpcD2 hfixD2 h11D2 h13D2 hcurD2 hx22D2 hx24D2 hx8D2 hx27D2
                    (posMarked16 input.positions k (capLeafOf i)) hmark4
                    (pw.evalLevel c64 oracle.permutation 16) hd16D
                  have hcan_dup : (posMarked16 input.positions k (capLeafOf i) = true ∧
                      pw.evalLevel c64 oracle.permutation 16 ≠ readBuffer s4 (16384 + 32 * (256 + capLeafOf i)) 32) →
                      ¬ PosConsistent c64 oracle.permutation s0 input (k + 1) := by
                    rintro ⟨hm, hne_d⟩ hcons
                    obtain ⟨j, hj, hcj⟩ := of_decide_eq_true hm
                    have hwj := (hinv_k.witnesses j hj).1
                    have hval_eq : readBuffer s4 (16384 + 32 * (256 + capLeafOf i)) 32 =
                        readBuffer sk (16384 + 32 * (256 + capLeafOf i)) 32 :=
                      readBuffer_congr2 _ _ _ _ _ (fun b hb => hlow_sk4 _ (by omega) (by omega))
                    rw [hval_eq, ← hcj, ← hwj] at hne_d
                    exact hne_d (hcons.2 k j (by omega) (by omega) hcj.symm)
                  refine h1e.weaken (by decide) (by decide) hcan_dup ?_
                  rintro s5 qE trE ⟨rfl, rfl, hpcE, hfixE, h11E, h13E, hcurE, hx24E, hx8E, hx27E, hmark5, hval5, hout5, hmeq5⟩
                  have hc_k : capLeafOf (posAt input.positions k) < 256 := hc_lt
                  have hinp5 : InputMemPreserved s0 (k + 1) s5 := fun a ha hreg =>
                    (hout5 a ha (by omega) (by omega)).trans (hinpD2 a ha hreg)
                  have hlow_sk5 : ∀ a : Nat, 4160 ≤ a → a < 4294971392 →
                      a ≠ 8192 + (256 + capLeafOf i) →
                      (a < 16384 + 32 * (256 + capLeafOf i) ∨ 16384 + 32 * (256 + capLeafOf i) + 32 ≤ a) →
                      s5.getByte (BitVec.ofNat 64 a) = sk.getByte (BitVec.ofNat 64 a) := fun a hlo hhi hne hout =>
                    (hout5 a (by omega) hne hout).trans (hlow_sk4 a hlo hhi)
                  refine ⟨by omega, ?_⟩
                  refine ⟨hfixE, fun _ => h11E, fun _ => h13E,
                    by simpa only [show pOff + 498 = 498 * (k + 1) by dsimp only [pOff]; omega,
                                   show tOff + 10 = 10 * (k + 1) by dsimp only [tOff]; omega] using hcurE,
                    hinp5, ?_, hx24E, hx8E, hx27E, ?_, ?_, ?_⟩
                  · by_cases hdone : k + 1 = input.positions.card
                    · have hz : rem1 = 0 := by omega
                      simp [hdone, hz, hpcE]
                    · have hnz : rem1 ≠ 0 := by omega
                      simp [hdone, hnz, hpcE]
                  · intro c hc
                    rw [posMarked16_succ]
                    change s5.getByte (BitVec.ofNat 64 (8192 + (256 + c))) =
                      if (posMarked16 input.positions k c || decide (capLeafOf i = c)) = true then 1#8 else 0#8
                    by_cases heq : capLeafOf i = c
                    · subst heq; simp only [decide_true, Bool.or_true, ite_true]; exact hmark5
                    · simp only [heq, decide_false, Bool.or_false]
                      exact (hlow_sk5 (8192 + (256 + c)) (by omega) (by omega) (by omega) (by omega)).trans
                        (hinv_k.mark16 c hc)
                  · intro h hh
                    exact (hlow_sk5 (8192 + h) (by omega) (by omega) (by omega) (by omega)).trans
                      (hinv_k.mark_lo_zero h hh)
                  · intro j hj
                    by_cases hjk : j < k
                    · obtain ⟨hw16, hwLC, hwLP, hwBin⟩ := hinv_k.witnesses j hjk
                      refine ⟨?_, fun x hx => (hwLC x hx).append_left, hwLP.append_left,
                        fun l hl => (hwBin l hl).append_left⟩
                      rw [hw16]
                      by_cases hsame : capLeafOf (posAt input.positions j) = capLeafOf i
                      · have hm : posMarked16 input.positions k (capLeafOf i) = true :=
                          decide_eq_true ⟨j, hjk, hsame⟩
                        rw [hsame]
                        have hm54 : s5.mem = s4.mem := hmeq5 hm
                        refine (readBuffer_congr2 _ _ _ _ _ (fun b hb => (hlow_sk4 _ (by omega) (by omega)).symm)).trans ?_
                        exact readBuffer_congr2 s4 s5 _ _ _ (fun b _ => by simp only [MachineState.getByte, MachineState.getMem, hm54])
                      · have hc_j : capLeafOf (posAt input.positions j) < 256 := capLeafOf_lt _
                        exact readBuffer_congr2 _ _ _ _ _ (fun b hb =>
                          (hlow_sk5 _ (by omega) (by omega) (by omega) (by omega)).symm)
                    · have hjeq : j = k := by omega
                      subst hjeq
                      refine ⟨hval5.symm,
                        fun x hx => (htrAC x hx).append_left.append_right,
                        htrAP.append_left.append_right,
                        fun l hl => ?_⟩
                      by_cases hl0 : l = 0
                      · subst hl0; exact htrB.append_left.append_right.append_right
                      · by_cases hl1 : l = 1
                        · subst hl1; exact htrC.append_left.append_right.append_right.append_right
                        · by_cases hl5 : l ≤ 5
                          · exact (htrD1 l (by omega) hl5).append_left.append_right.append_right.append_right.append_right
                          · exact (htrD2 l (by omega) (by omega)).append_left.append_right.append_right.append_right.append_right.append_right))))))
  exact hind input.positions.card (le_refl _)

end CommitGolfCandidate
