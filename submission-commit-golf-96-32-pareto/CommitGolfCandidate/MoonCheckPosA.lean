import CommitGolfCandidate.MoonCheckBase

/-! Symbolic execution of the checker prologue (including salt-top header validation) and
per-position early-salt leaf / L0-setup phases (`pc[0..138]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private def prologuePrefix : List Instr :=
  [.ADDI .x26 .x11 0#12, .ADDI .x24 .x13 0#12, .ADDI .x8 .x14 0#12,
   .ADDI .x25 .x15 0#12, .ADD .x31 .x15 .x17, .ADDI .x27 .x16 0#12]

private def prologueHeaderPrefix : List Instr :=
  [.ADDI .x14 .x25 0#12, .ADDI .x15 .x0 0#12, .ADDI .x6 .x27 7#12,
   .SRLI .x6 .x6 3#6, .ADD .x6 .x25 .x6]

private def prologueNonemptySetup : List Instr :=
  [.ADDI .x25 .x6 0#12, .ADDI .x3 .x0 0#12, .ADDI .x4 .x0 0#12,
   .ADDI .x9 .x0 1#12, .SLLI .x9 .x9 46#6, .ADDI .x9 .x9 4095#12,
   .ADDI .x21 .x0 256#12, .ADDI .x18 .x0 2#12, .SLLI .x18 .x18 11#6,
   .ADDI .x19 .x0 4#12, .SLLI .x19 .x19 11#6, .ADDI .x5 .x0 0#12,
   .ADDI .x11 .x0 96#12, .ADDI .x13 .x0 0#12]

/-- Number of packed top-salt-bit header bytes for `k` opened positions. -/
def saltTopLen (k : Nat) : Nat := (k + 7) / 8

/-- Reject condition for the packed top-salt-bit header (`pc[14]` or `pc[19]`). -/
def SaltTopBad (s0 : MachineState) (input : CheckInput) : Prop :=
  input.proof.length < saltTopLen input.positions.card ∨
  (input.positions.card % 8 ≠ 0 ∧
    (s0.getByte (BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card - 1))).toNat /
      2 ^ (input.positions.card % 8) ≠ 0)

theorem initialState_check_regs (input : CheckInput) :
    let s0 := submission.initialState .check input
    s0.pc = pcWord 0 ∧
    s0.getReg .x2  = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x11 = BitVec.ofNat 64 4294971392 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6174019552 ∧
    s0.getReg .x14 = BitVec.ofNat 64 6308237280 ∧
    s0.getReg .x15 = BitVec.ofNat 64 10603204576 ∧
    s0.getReg .x16 = BitVec.ofNat 64 input.positions.card ∧
    s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := by
  intro s0
  have hdb : dataBase (submission.image .check) = 68719475936 := check_dataBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (
    simp only [s0, Submission.initialState, submission_layout, hdb, inputCount, inputProofLength,
      MachineState.pc_setReg, initialMachine, pcWord,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, decide_not,
      not_false_eq_true, reduceCtorEq]
    try rfl)

/-- When `positions.card = 0`, the checker halts in at most 12 steps with 0 oracle calls,
accepting iff `proof.length = 0`. -/
theorem step_prologue_empty (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hempty : input.positions.card = 0) :
    HaltsWith oracle (submission.initialState .check input) 12 0
      (if input.proof.length = 0 then .success else .failure) [] := by
  let s0 := submission.initialState .check input
  obtain ⟨hpc0, _, _, _, _, _, hx16, hx17⟩ := initialState_check_regs input
  have hcode : ∀ i (hi : i < prologuePrefix.length),
      checkInstr (0 + i) = .base (prologuePrefix[i]'hi) := by
    intro i hi; have hi' : i < 6 := hi; interval_cases i <;> rfl
  have hpure : ∀ i (hi : i < prologuePrefix.length),
      Instruction.base (prologuePrefix[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologuePrefix[i]'hi)) = some (execInstrBr st (prologuePrefix[i]'hi)) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).mem = st.mem := by
    intro i hi; have hi' : i < 6 := hi
    interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs1, hpc1, _⟩ := step_pure_list oracle 0 prologuePrefix s0 (by decide) hcode hpure hpc0
  let s1 := runInstrs s0 prologuePrefix
  have hs1 : StepsTo oracle s0 s1 6 0 [] := hs1
  have hpc1 : s1.pc = pcWord 6 := hpc1
  have hx27 : s1.getReg .x27 = 0#64 := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx16.trans (by rw [hempty])
  have hx17_1 : s1.getReg .x17 = BitVec.ofNat 64 input.proof.length := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, decide_not,
      not_false_eq_true, reduceCtorEq]
    exact hx17
  have hst6 := step_ordinary oracle s1 6 (.BNE .x27 .x0 12#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BNE .x27 .x0 12#13)
  have hpc2 : s2.pc = pcWord 7 := by
    simp only [s2, execInstrBr, hx27, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
      ite_false, MachineState.setPC, hpc1, pcWord_add_four]
  have hx17_2 : s2.getReg .x17 = BitVec.ofNat 64 input.proof.length := by
    simpa [s2, execInstrBr, hx27, getReg_x0, MachineState.getReg_setPC] using hx17_1
  have hst7 := step_ordinary oracle s2 7 (.BNE .x17 .x0 1016#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x17 .x0 1016#13)
  have hplen_lt : input.proof.length < 2 ^ 64 := by
    change input.proof.length ≤ 8239714016 at hvalid; omega
  by_cases hpz : input.proof.length = 0
  · simp only [hpz, ite_true]
    have hx17_z : s2.getReg .x17 = 0#64 := by rw [hx17_2, hpz]
    have hpc3 : s3.pc = pcWord 8 := by
      simp only [s3, execInstrBr, hx17_z, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
        ite_false, MachineState.setPC, hpc2, pcWord_add_four]
    have hst8 := step_ordinary oracle s3 8 (.JAL .x0 1000#21) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.JAL .x0 1000#21)
    have hpc4 : s4.pc = pcWord 258 := by
      simp only [s4, execInstrBr, MachineState.setPC, hpc3]; decide
    have htot := ((hs1.trans hst6).trans (hst7.trans hst8)).halt (halt_accept oracle s4 hpc4)
    simpa using htot
  · simp only [hpz, ite_false]
    have hne : s2.getReg .x17 ≠ 0#64 := by
      rw [hx17_2]
      change BitVec.ofNat 64 input.proof.length ≠ BitVec.ofNat 64 0
      rw [ne_eq, bv64_eq_iff _ 0 hplen_lt (by omega)]
      exact hpz
    have hneb : (s2.getReg .x17 != s2.getReg .x0) = true := by
      change (s2.getReg .x17 != 0#64) = true
      rw [bne_iff_ne]; exact hne
    have hpc3 : s3.pc = pcWord 261 := by
      simp only [s3, execInstrBr, hneb, ite_true, MachineState.setPC, hpc2]; decide
    have htot := ((hs1.trans hst6).trans hst7).halt (halt_reject oracle s3 hpc3)
    exact (by simpa using htot : HaltsWith oracle s0 11 0 .failure []).mono (by decide)

private theorem pc_14_reject : pcWord 14 + signExtend13 988#13 = pcWord 261 := by decide
private theorem pc_16_ok : pcWord 16 + signExtend13 16#13 = pcWord 20 := by decide
private theorem pc_19_reject : pcWord 19 + signExtend13 968#13 = pcWord 261 := by decide

/-- When `positions.card ≥ 1`, the prologue validates `saltTopBytes` and either rejects
(when `SaltTopBad`) or reaches `pc[34]` in at most 36 steps with 0 oracle calls. -/
theorem step_prologue_nonempty (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0) :
    let s0 := submission.initialState .check input
    PhaseOutcome oracle s0 36 0 (SaltTopBad s0 input)
      (fun s1 q tr =>
        q = 0 ∧ tr = [] ∧
        s1.pc = pcWord 34 ∧
        s1.mem = s0.mem ∧
        CheckFixedRegs s1 ∧
        ProofCursor s0 input.proof.length (saltTopLen input.positions.card) 0 s1 ∧
        s1.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
        s1.getReg .x15 = BitVec.ofNat 64 0 ∧
        s1.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
        s1.getReg .x8  = BitVec.ofNat 64 6308237280 ∧
        s1.getReg .x27 = BitVec.ofNat 64 input.positions.card) := by
  intro s0
  have hplen_bd : input.proof.length ≤ 8239714016 := hvalid
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at this; omega
  have hntop_pos : 1 ≤ saltTopLen input.positions.card := by unfold saltTopLen; omega
  have hntop_bd : saltTopLen input.positions.card ≤ 2097152 := by unfold saltTopLen; omega
  obtain ⟨hpc0, hx2, hx11, hx13, hx14, hx15, hx16, hx17⟩ := initialState_check_regs input
  -- pc[0..5]: prologuePrefix
  have hcode1 : ∀ i (hi : i < prologuePrefix.length), checkInstr (0 + i) = .base (prologuePrefix[i]'hi) := by
    intro i hi; have hi' : i < 6 := hi; interval_cases i <;> rfl
  have hpure1 : ∀ i (hi : i < prologuePrefix.length),
      Instruction.base (prologuePrefix[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologuePrefix[i]'hi)) = some (execInstrBr st (prologuePrefix[i]'hi)) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).mem = st.mem := by
    intro i hi; have hi' : i < 6 := hi
    interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 0 prologuePrefix s0 (by decide) hcode1 hpure1 hpc0
  let s1 := runInstrs s0 prologuePrefix
  have hs1 : StepsTo oracle s0 s1 6 0 [] := hs1
  have hpc1 : s1.pc = pcWord 6 := hpc1
  have hx27_1 : s1.getReg .x27 = BitVec.ofNat 64 input.positions.card := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx16
  have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 10603204576 := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx15
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (10603204576 + input.proof.length) := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq]
    have h15 : s0.getReg .x15 = BitVec.ofNat 64 10603204576 := hx15
    have h17 : s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := hx17
    rw [h15, h17, bv64_add]
  have hx24_1 : s1.getReg .x24 = BitVec.ofNat 64 6174019552 := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx13
  have hx8_1 : s1.getReg .x8 = BitVec.ofNat 64 6308237280 := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx14
  have hx26_1 : s1.getReg .x26 = BitVec.ofNat 64 4294971392 := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx11
  have hx2_1 : s1.getReg .x2 = BitVec.ofNat 64 68719475936 := by
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq]
    exact hx2
  -- pc[6]: BNE x27, x0, pc[9]
  have hneb6 : (s1.getReg .x27 != s1.getReg .x0) = true := by
    change (s1.getReg .x27 != 0#64) = true
    rw [bne_iff_ne, hx27_1]
    change BitVec.ofNat 64 input.positions.card ≠ BitVec.ofNat 64 0
    rw [ne_eq, bv64_eq_iff _ 0 (by omega) (by omega)]
    exact hne
  have hst6 := step_ordinary oracle s1 6 (.BNE .x27 .x0 12#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BNE .x27 .x0 12#13)
  have hpc2 : s2.pc = pcWord 9 := by
    simp only [s2, execInstrBr, hneb6, ite_true, MachineState.setPC, hpc1]; decide
  have hmem2 : s2.mem = s0.mem := by simpa [s2, execInstrBr, hneb6, MachineState.setPC] using hmem1
  have hreg2 : ∀ r, s2.getReg r = s1.getReg r := fun r => by
    simp [s2, execInstrBr, hneb6, MachineState.getReg_setPC]
  -- pc[9..13]: prologueHeaderPrefix
  have hcodeH : ∀ i (hi : i < prologueHeaderPrefix.length), checkInstr (9 + i) = .base (prologueHeaderPrefix[i]'hi) := by
    intro i hi; have hi' : i < 5 := hi; interval_cases i <;> rfl
  have hpureH : ∀ i (hi : i < prologueHeaderPrefix.length),
      Instruction.base (prologueHeaderPrefix[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologueHeaderPrefix[i]'hi)) = some (execInstrBr st (prologueHeaderPrefix[i]'hi)) ∧
            (execInstrBr st (prologueHeaderPrefix[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologueHeaderPrefix[i]'hi)).mem = st.mem := by
    intro i hi; have hi' : i < 5 := hi
    interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs3, hpc3, hmem3⟩ := step_pure_list oracle 9 prologueHeaderPrefix s2 (by decide) hcodeH hpureH hpc2
  let s3 := runInstrs s2 prologueHeaderPrefix
  have hs3 : StepsTo oracle s2 s3 5 0 [] := hs3
  have hpc3 : s3.pc = pcWord 14 := hpc3
  have hmem3' : s3.mem = s0.mem := hmem3.trans hmem2
  have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x14 → r ≠ .x15 → s3.getReg r = s1.getReg r := fun r h6 h14 h15 => by
    simp only [s3, runInstrs, prologueHeaderPrefix, List.foldl, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h15.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h14.symm, hreg2 r]
  have hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 10603204576 := by
    simp only [s3, runInstrs, prologueHeaderPrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero, hreg2, hx25_1]
  have hx15_3 : s3.getReg .x15 = BitVec.ofNat 64 0 := by
    simp only [s3, runInstrs, prologueHeaderPrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0, se12_0, BitVec.add_zero]
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card) := by
    have harith : BitVec.ofNat 64 10603204576 +
        ((BitVec.ofNat 64 input.positions.card + signExtend12 7#12) >>> (3#6 : BitVec 6).toNat) =
        BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card) := by
      rw [chk_se12_7]
      change BitVec.ofNat 64 10603204576 + ((BitVec.ofNat 64 input.positions.card + BitVec.ofNat 64 7) >>> 3) = _
      rw [bv64_add, bv64_shr _ 3 (by omega), bv64_add]
      rfl
    simpa only [s3, runInstrs, prologueHeaderPrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, hreg2, hx25_1, hx27_1] using harith
  -- pc[14]: BLTU x31, x6, pc[261]
  have hst14 := step_ordinary oracle s3 14 (.BLTU .x31 .x6 988#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.BLTU .x31 .x6 988#13)
  have hult14 : BitVec.ult (s3.getReg .x31) (s3.getReg .x6) =
      decide (input.proof.length < saltTopLen input.positions.card) := by
    rw [hreg3 .x31 (by decide) (by decide) (by decide), hx31_1, hx6_3, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have hpre14 : StepsTo oracle s0 s4 13 0 [] := by
    simpa using ((hs1.trans hst6).trans hs3).trans hst14
  by_cases hshort : input.proof.length < saltTopLen input.positions.card
  · have hpc4 : s4.pc = pcWord 261 := by
      simp only [s4, execInstrBr, hult14, hshort, decide_true, ite_true, MachineState.setPC, hpc3]
      exact pc_14_reject
    exact .rejected 16 0 [] (Or.inl hshort) (by decide) (by decide)
      (by simpa using hpre14.halt (halt_reject oracle s4 hpc4))
  · have hge_top : saltTopLen input.positions.card ≤ input.proof.length := by omega
    -- Common continuation from pc[20..33] -> pc[34]
    have hfinish20 : ∀ (s20 : MachineState) (kPre : Nat),
        kPre ≤ 22 →
        StepsTo oracle s0 s20 kPre 0 [] →
        s20.pc = pcWord 20 →
        s20.mem = s0.mem →
        s20.getReg .x2  = BitVec.ofNat 64 68719475936 →
        s20.getReg .x6  = BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card) →
        s20.getReg .x8  = BitVec.ofNat 64 6308237280 →
        s20.getReg .x14 = BitVec.ofNat 64 10603204576 →
        s20.getReg .x15 = BitVec.ofNat 64 0 →
        s20.getReg .x24 = BitVec.ofNat 64 6174019552 →
        s20.getReg .x26 = BitVec.ofNat 64 4294971392 →
        s20.getReg .x27 = BitVec.ofNat 64 input.positions.card →
        s20.getReg .x31 = BitVec.ofNat 64 (10603204576 + input.proof.length) →
        PhaseOutcome oracle s0 36 0 (SaltTopBad s0 input)
          (fun sFin q tr =>
            q = 0 ∧ tr = [] ∧
            sFin.pc = pcWord 34 ∧
            sFin.mem = s0.mem ∧
            CheckFixedRegs sFin ∧
            ProofCursor s0 input.proof.length (saltTopLen input.positions.card) 0 sFin ∧
            sFin.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
            sFin.getReg .x15 = BitVec.ofNat 64 0 ∧
            sFin.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
            sFin.getReg .x8  = BitVec.ofNat 64 6308237280 ∧
            sFin.getReg .x27 = BitVec.ofNat 64 input.positions.card) := by
      intro s20 kPre hkPre hpre20 hpc20 hmem20 h2 h6 h8 h14 h15 h24 h26 h27 h31
      have hcode2 : ∀ i (hi : i < prologueNonemptySetup.length),
          checkInstr (20 + i) = .base (prologueNonemptySetup[i]'hi) := by
        intro i hi; have hi' : i < 14 := hi; interval_cases i <;> rfl
      have hpure2 : ∀ i (hi : i < prologueNonemptySetup.length),
          Instruction.base (prologueNonemptySetup[i]'hi) ≠ .base .ECALL ∧
          ∀ st, ordinaryStep st (.base (prologueNonemptySetup[i]'hi)) = some (execInstrBr st (prologueNonemptySetup[i]'hi)) ∧
                (execInstrBr st (prologueNonemptySetup[i]'hi)).pc = st.pc + (4 : Word) ∧
                (execInstrBr st (prologueNonemptySetup[i]'hi)).mem = st.mem := by
        intro i hi; have hi' : i < 14 := hi
        interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
      obtain ⟨hsFin, hpcFin, hmemFin⟩ := step_pure_list oracle 20 prologueNonemptySetup s20 (by decide) hcode2 hpure2 hpc20
      let sFin := runInstrs s20 prologueNonemptySetup
      have hsFin : StepsTo oracle s20 sFin 14 0 [] := hsFin
      have hpcFin : sFin.pc = pcWord 34 := hpcFin
      have hregFin : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x9 → r ≠ .x11 → r ≠ .x13 →
          r ≠ .x18 → r ≠ .x19 → r ≠ .x21 → r ≠ .x25 → sFin.getReg r = s20.getReg r :=
        fun r h3r h4r h5r h9r h11r h13r h18r h19r h21r h25r => by
          simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h13r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h11r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h5r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h19r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h19r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h18r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h18r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h21r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h9r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h9r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h9r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h4r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h3r.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h25r.symm]
      have hfixed : CheckFixedRegs sFin := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact (hregFin .x2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · exact (hregFin .x26 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
      have hcur : ProofCursor s0 input.proof.length (saltTopLen input.positions.card) 0 sFin := by
        refine ⟨by simpa only [tailBytes_zero, Nat.add_zero] using hge_top, ?_, ?_, ?_, ?_⟩
        · simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, h6, se12_0, BitVec.add_zero]
        · rw [hregFin .x31 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), h31, tailBytes_zero, Nat.sub_zero]
        · rw [tailBuf_zero]
          simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        · rw [tailCnt_zero]
          simp only [sFin, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
            MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
      exact .continued sFin (kPre + 14) 0 [] (by omega) (by decide)
        (by simpa using hpre20.trans hsFin)
        ⟨rfl, rfl, hpcFin, hmemFin.trans hmem20, hfixed, hcur,
         (hregFin .x14 (by decide) (by decide) (by decide) (by decide) (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14,
         (hregFin .x15 (by decide) (by decide) (by decide) (by decide) (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15,
         (hregFin .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24,
         (hregFin .x8  (by decide) (by decide) (by decide) (by decide) (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8,
         (hregFin .x27 (by decide) (by decide) (by decide) (by decide) (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27⟩
    have hpc4 : s4.pc = pcWord 15 := by
      simp only [s4, execInstrBr, hult14, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s0.mem := by
      simpa [s4, execInstrBr, hult14, hshort, MachineState.setPC] using hmem3'
    have hreg4 : ∀ r, s4.getReg r = s3.getReg r := fun r => by
      simp [s4, execInstrBr, hult14, hshort, MachineState.getReg_setPC]
    -- pc[15]: ANDI x7, x27, 7; pc[16]: BEQ x7, x0, pc[20]
    have hst15 := step_ordinary oracle s4 15 (.ANDI .x7 .x27 7#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ANDI .x7 .x27 7#12)
    have hpc5 : s5.pc = pcWord 16 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hmem5 : s5.mem = s0.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
    have hreg5 : ∀ r, r ≠ .x7 → s5.getReg r = s3.getReg r := fun r h7 => by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg4 r]
    have hx7_5 : s5.getReg .x7 = BitVec.ofNat 64 (input.positions.card % 8) := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg4 .x27, hreg3 .x27 (by decide) (by decide) (by decide),
        hx27_1, chk_se12_7]
      exact chk_bv64_and_7 input.positions.card (by omega)
    have hst16 := step_ordinary oracle s5 16 (.BEQ .x7 .x0 16#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BEQ .x7 .x0 16#13)
    have heq16 : (s5.getReg .x7 == s5.getReg .x0) = decide (input.positions.card % 8 = 0) := by
      rw [hx7_5, getReg_x0]
      exact bv64_beq_eq _ 0 (by omega) (by omega)
    by_cases hmod0 : input.positions.card % 8 = 0
    · have hpc6 : s6.pc = pcWord 20 := by
        simp only [s6, execInstrBr, heq16, hmod0, decide_true, ite_true, MachineState.setPC, hpc5]
        exact pc_16_ok
      have hmem6 : s6.mem = s0.mem := by simpa [s6, execInstrBr, heq16, hmod0, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x7 → s6.getReg r = s3.getReg r := fun r h7 => by
        simpa [s6, execInstrBr, heq16, hmod0, MachineState.getReg_setPC] using hreg5 r h7
      exact hfinish20 s6 15 (by decide) (by simpa using (hpre14.trans hst15).trans hst16) hpc6 hmem6
        ((hreg6 .x2 (by decide)).trans ((hreg3 .x2 (by decide) (by decide) (by decide)).trans hx2_1))
        ((hreg6 .x6 (by decide)).trans hx6_3)
        ((hreg6 .x8 (by decide)).trans ((hreg3 .x8 (by decide) (by decide) (by decide)).trans hx8_1))
        ((hreg6 .x14 (by decide)).trans hx14_3)
        ((hreg6 .x15 (by decide)).trans hx15_3)
        ((hreg6 .x24 (by decide)).trans ((hreg3 .x24 (by decide) (by decide) (by decide)).trans hx24_1))
        ((hreg6 .x26 (by decide)).trans ((hreg3 .x26 (by decide) (by decide) (by decide)).trans hx26_1))
        ((hreg6 .x27 (by decide)).trans ((hreg3 .x27 (by decide) (by decide) (by decide)).trans hx27_1))
        ((hreg6 .x31 (by decide)).trans ((hreg3 .x31 (by decide) (by decide) (by decide)).trans hx31_1))
    · -- pc[17..19]: check high unused bits of last saltTop byte are 0
      have hpc6 : s6.pc = pcWord 17 := by
        simp only [s6, execInstrBr, heq16, hmod0, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s0.mem := by simpa [s6, execInstrBr, heq16, hmod0, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
        simp [s6, execInstrBr, heq16, hmod0, MachineState.getReg_setPC]
      have hx6_6 : s6.getReg .x6 = BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card) :=
        (hreg6 .x6).trans ((hreg5 .x6 (by decide)).trans hx6_3)
      have ha17 : s6.getReg .x6 + signExtend12 4095#12 =
          BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card - 1) := by
        rw [hx6_6, show 10603204576 + saltTopLen input.positions.card =
          (10603204576 + saltTopLen input.positions.card - 1) + 1 by omega]
        exact bv64_add_neg1 _
      have hv17 : memoryArgumentsValid s6 (.LBU .x5 .x6 4095#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha17]
        exact accessValid_ofNat _ 1 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst17 := step_ordinary oracle s6 17 (.LBU .x5 .x6 4095#12) (by decide) hpc6 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv17])
      let s7 := execInstrBr s6 (.LBU .x5 .x6 4095#12)
      have hpc7 : s7.pc = pcWord 18 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      have hmem7 : s7.mem = s0.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
      let lastB := s0.getByte (BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card - 1))
      have hlastB_lt : lastB.toNat < 256 := lastB.isLt
      have hx5_7 : s7.getReg .x5 = BitVec.ofNat 64 lastB.toNat := by
        simp only [s7, execInstrBr, MachineState.getReg_setPC, ha17]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have hb : s6.getByte (BitVec.ofNat 64 (10603204576 + saltTopLen input.positions.card - 1)) = lastB := by
          simp [lastB, MachineState.getByte, MachineState.getMem, hmem6]
        rw [hb]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.zeroExtend, BitVec.toNat_setWidth]
      have hx7_7 : s7.getReg .x7 = BitVec.ofNat 64 (input.positions.card % 8) := by
        simp only [s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), hreg6 .x7, hx7_5]
      have hst18 := step_ordinary oracle s7 18 (.SRL .x5 .x5 .x7) (by decide) hpc7 rfl (by intro h; cases h) rfl
      let s8 := execInstrBr s7 (.SRL .x5 .x5 .x7)
      have hpc8 : s8.pc = pcWord 19 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
      have hmem8 : s8.mem = s0.mem := by simpa [s8, execInstrBr, mem_setPC, mem_setReg] using hmem7
      have hx5_8 : s8.getReg .x5 = BitVec.ofNat 64 (lastB.toNat / 2 ^ (input.positions.card % 8)) := by
        simp only [s8, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hx5_7, hx7_7,
          toNat_ofNat64 (input.positions.card % 8) (by omega),
          Nat.mod_eq_of_lt (by omega : input.positions.card % 8 < 64)]
        exact bv64_shr lastB.toNat (input.positions.card % 8) (by omega)
      have hreg8 : ∀ r, r ≠ .x5 → r ≠ .x7 → s8.getReg r = s3.getReg r := fun r h5r h7r => by
        simp only [s8, s7, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h5r.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h5r.symm, hreg6 r, hreg5 r h7r]
      have hst19 := step_ordinary oracle s8 19 (.BNE .x5 .x0 968#13) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let s9 := execInstrBr s8 (.BNE .x5 .x0 968#13)
      have hdiv_lt : lastB.toNat / 2 ^ (input.positions.card % 8) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      have hne19 : (s8.getReg .x5 != s8.getReg .x0) =
          decide (lastB.toNat / 2 ^ (input.positions.card % 8) ≠ 0) := by
        rw [hx5_8, getReg_x0]
        exact bv64_bne_eq _ 0 hdiv_lt (by omega)
      have hpre19 : StepsTo oracle s0 s9 18 0 [] := by
        simpa using (((hpre14.trans (hst15.trans hst16)).trans (hst17.trans hst18)).trans hst19)
      by_cases hnz : lastB.toNat / 2 ^ (input.positions.card % 8) ≠ 0
      · have hdec19 : (s8.getReg .x5 != s8.getReg .x0) = true := hne19.trans (decide_eq_true hnz)
        have hpc9 : s9.pc = pcWord 261 := by
          simp only [s9, execInstrBr, hdec19, ite_true, MachineState.setPC, hpc8]
          exact pc_19_reject
        exact .rejected 21 0 [] (Or.inr ⟨hmod0, hnz⟩) (by decide) (by decide)
          (by simpa using hpre19.halt (halt_reject oracle s9 hpc9))
      · have hdec19 : (s8.getReg .x5 != s8.getReg .x0) = false := hne19.trans (decide_eq_false hnz)
        have hpc9 : s9.pc = pcWord 20 := by
          simp only [s9, execInstrBr, hdec19, Bool.false_eq_true, ite_false,
            MachineState.setPC, hpc8, pcWord_add_four]
        have hmem9 : s9.mem = s0.mem := by simpa [s9, execInstrBr, hdec19, MachineState.setPC] using hmem8
        have hreg9 : ∀ r, r ≠ .x5 → r ≠ .x7 → s9.getReg r = s3.getReg r := fun r h5r h7r => by
          simpa [s9, execInstrBr, hdec19, MachineState.getReg_setPC] using hreg8 r h5r h7r
        exact hfinish20 s9 18 (by decide) hpre19 hpc9 hmem9
          ((hreg9 .x2 (by decide) (by decide)).trans ((hreg3 .x2 (by decide) (by decide) (by decide)).trans hx2_1))
          ((hreg9 .x6 (by decide) (by decide)).trans hx6_3)
          ((hreg9 .x8 (by decide) (by decide)).trans ((hreg3 .x8 (by decide) (by decide) (by decide)).trans hx8_1))
          ((hreg9 .x14 (by decide) (by decide)).trans hx14_3)
          ((hreg9 .x15 (by decide) (by decide)).trans hx15_3)
          ((hreg9 .x24 (by decide) (by decide)).trans ((hreg3 .x24 (by decide) (by decide) (by decide)).trans hx24_1))
          ((hreg9 .x26 (by decide) (by decide)).trans ((hreg3 .x26 (by decide) (by decide) (by decide)).trans hx26_1))
          ((hreg9 .x27 (by decide) (by decide)).trans ((hreg3 .x27 (by decide) (by decide) (by decide)).trans hx27_1))
          ((hreg9 .x31 (by decide) (by decide)).trans ((hreg3 .x31 (by decide) (by decide) (by decide)).trans hx31_1))

/-! #### Deterministic Two-End Proof-Offset Schedule and Witness Parser -/

def posAt (positions : Positions) (ord : Nat) : Index :=
  if h : ord < positions.card then
    (positions.sort (· ≤ ·))[ord]'(by simpa using h)
  else ⟨0, by unfold LENGTH LOG_LENGTH; decide⟩

def valAt (input : CheckInput) (ord : Nat) : Entry :=
  if h : ord < input.positions.card then
    input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ord]'(by simpa using h))
  else 0

theorem posAt_val (positions : Positions) (ord : Nat) (h : ord < positions.card) :
    (posAt positions ord).val = openingIndex positions ord := by
  simp only [posAt, openingIndex, dif_pos h]

theorem posAt_mem (positions : Positions) (ord : Nat) (h : ord < positions.card) :
    posAt positions ord ∈ positions := by
  simp only [posAt, dif_pos h]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _)

theorem valAt_eq_values (input : CheckInput) (ord : Nat) (h : ord < input.positions.card) :
    valAt input ord = input.values ⟨posAt input.positions ord, posAt_mem input.positions ord h⟩ := by
  simp only [valAt, dif_pos h]
  congr 1
  apply Subtype.ext
  apply Fin.ext
  rw [sorted_value_index input.positions ord h, posAt_val input.positions ord h]

/-- Constant per-position forward byte record length (`15 + 16 * 29 = 479`). -/
def recordLen : Nat := 479

/-- Constant per-position 6-bit tail count (`16`, for `L0..L15`). -/
def recordTailCount : Nat := 16

def posRecordOff (k n : Nat) : Nat := saltTopLen k + 479 * n

def posTailOff (n : Nat) : Nat := 16 * n

theorem posRecordOff_zero (k : Nat) : posRecordOff k 0 = saltTopLen k := by
  unfold posRecordOff; omega
theorem posRecordOff_succ (k n : Nat) : posRecordOff k (n + 1) = posRecordOff k n + 479 := by
  unfold posRecordOff; omega
theorem posRecordOff_mono (k : Nat) {a b : Nat} (hab : a ≤ b) : posRecordOff k a ≤ posRecordOff k b := by
  unfold posRecordOff; omega

theorem posTailOff_zero : posTailOff 0 = 0 := rfl
theorem posTailOff_succ (n : Nat) : posTailOff (n + 1) = posTailOff n + 16 := by
  unfold posTailOff; omega
theorem posTailOff_mono {a b : Nat} (hab : a ≤ b) : posTailOff a ≤ posTailOff b := by
  unfold posTailOff; omega

/-- Top bit (bit 120) of the `ord`-th opened salt read from the `saltTopBytes` header. -/
def saltTopBitFromMem (s0 : MachineState) (ord : Nat) : Bool :=
  (s0.getByte (BitVec.ofNat 64 (10603204576 + ord / 8))).getLsbD (ord % 8)

/-- 121-bit leaf salt reconstructed from 15 forward bytes at `pOff` plus bit 120 in `saltTopBytes`. -/
def parseSalt121 (s0 : MachineState) (pOff ord : Nat) : Salt121 :=
  (if saltTopBitFromMem s0 ord then 1#1 else 0#1) ++ readBuffer s0 (10603204576 + pOff) 15

theorem parseSalt121_getLsbD_120 (s0 : MachineState) (pOff ord : Nat) :
    (parseSalt121 s0 pOff ord).getLsbD 120 = saltTopBitFromMem s0 ord := by
  unfold parseSalt121
  rw [BitVec.getLsbD_append]
  simp only [show ¬ (120 < 120) by decide, decide_false, Bool.false_eq_true, ite_false, Nat.sub_self]
  cases saltTopBitFromMem s0 ord <;> decide

theorem parseSalt121_word16_bytes (s s0 : MachineState) (dst pOff ord : Nat)
    (hlo : ∀ j < 15, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (10603204576 + pOff + j)))
    (h15 : s.getByte (BitVec.ofNat 64 (dst + 15)) =
      BitVec.ofNat 8 (if saltTopBitFromMem s0 ord then 1 else 0)) :
    readBuffer s dst 16 = salt121Word16 (parseSalt121 s0 pOff ord) := by
  have hr := read_serialized_slice s (salt121Word16 (parseSalt121 s0 pOff ord)) dst 0 16 (by
    intro j hj
    simp only [Nat.zero_add]
    by_cases hlt : j < 15
    · rw [hlo j hlt]
      have hrb := read_buffer_byte s0 (10603204576 + pOff) 15 j hlt
      rw [← hrb]
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
        salt121Word16_getLsbD, show 8 * j + b < 121 by omega, parseSalt121,
        BitVec.getLsbD_append, show 8 * j + b < 120 by omega, ite_true]
    · have hj15 : j = 15 := by omega
      subst hj15
      rw [h15, salt121Word16_byte_15, parseSalt121_getLsbD_120])
  simpa using hr

/-- Pure-binary partial witness path parsed deterministically from `(pOff, tOff, ord)`. -/
def parsePartialWitness (s0 : MachineState) (proofLen pOff tOff ord : Nat)
    (i : Index) (val : Entry) : WitnessPath where
  index := i
  value := val
  salt := parseSalt121 s0 pOff ord
  binSib := fun l =>
    if l < 16 then
      proofDigest238 s0 proofLen
        (10603204576 + pOff + 15 + 29 * l)
        (tOff + l)
    else 0

/-- Membership of a 768-bit compression input and its reply in a checker trace. -/
def InTrace (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (tr : CompressionReplies) (x : BitVec 768) : Prop :=
  (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ tr

theorem InTrace.append_left {h768 : COMPRESSION_INPUT_LENGTH = 768} {oracle : Oracle}
    {t1 t2 : CompressionReplies} {x : BitVec 768} (h : InTrace h768 oracle t1 x) :
    InTrace h768 oracle (t1 ++ t2) x :=
  List.mem_append_left t2 h

theorem InTrace.append_right {h768 : COMPRESSION_INPUT_LENGTH = 768} {oracle : Oracle}
    {t1 t2 : CompressionReplies} {x : BitVec 768} (h : InTrace h768 oracle t2 x) :
    InTrace h768 oracle (t1 ++ t2) x :=
  List.mem_append_right t1 h

theorem InTrace.singleton (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) (x : BitVec 768) :
    InTrace h768 oracle [(x.cast h768.symm, oracle.compression (x.cast h768.symm))] x :=
  List.mem_singleton_self _

/-! #### Per-Position Sub-Phases (`pc[34..138]`) -/

private theorem pc_36_reject : pcWord 36 + signExtend13 900#13 = pcWord 261 := by decide

private theorem chk_byte_getLsbD_eq_div_mod (b : Byte) (r : Nat) (hr : r < 8) :
    (b.toNat / 2 ^ r) % 2 = if b.getLsbD r then 1 else 0 := by
  have htb : b.getLsbD r = b.toNat.testBit r := by
    simp [BitVec.getLsbD_eq_getElem, BitVec.getElem_eq_testBit_toNat, hr]
  rw [htb, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h1 : b.toNat / 2 ^ r % 2 = 1
  · simp [h1]
  · have h0 : b.toNat / 2 ^ r % 2 = 0 := by omega
    simp [h0]

private def leafTagInstrs : List Instr :=
  [.SLLI .x6 .x20 8#6, .ADDI .x6 .x6 2036#12, .ADDI .x6 .x6 2036#12]

/-- Helper for one 8-dword value copy + compression chain step (Calls 1, 2, 3 at `pc[72]`, `pc[91]`, `pc[110]`). -/
private theorem step_leaf_chain_call (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (ord base valOff : Nat) (hord : ord < input.positions.card)
    (hval_bd : valOff + 64 ≤ 256) (hval_al : valOff % 8 = 0)
    (hhi : base + 19 ≤ 295)
    (hcodeC : ∀ j < 8,
      checkInstr (base + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (valOff + 8 * j))) ∧
      checkInstr (base + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))))
    (hc16 : checkInstr (base + 16) = .base (.ADDI .x10 .x21 0#12))
    (hc17 : checkInstr (base + 17) = .base (.ADDI .x12 .x21 0#12))
    (hc18 : checkInstr (base + 18) = .base .ECALL)
    (s : MachineState) (hpc : s.pc = pcWord base)
    (hfix : CheckFixedRegs s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (cv : Digest) (hcv : readBuffer s 256 32 = cv) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let inp : BitVec 768 := (valAt input ord).extractLsb' (8 * valOff) 512 ++ cv
    ∃ s', StepsTo oracle s s' 19 1 [(inp.cast h768.symm, c96 inp)] ∧
      s'.pc = pcWord (base + 19) ∧
      CheckFixedRegs s' ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      MemEqOutside s s' 256 352 ∧
      readBuffer s' 256 32 = c96 inp := by
  intro c96 inp
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  obtain ⟨s1, hs1, hpc1, hreg1, hcopy1, hout1⟩ :=
    step_copy_dwords oracle base 8 .x8 .x21 valOff 32 s (6308237280 + 256 * ord) 256
      (by decide) (by decide) (by omega) (by omega) (by omega) hcodeC hpc hx8 hfix.x21
      (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
  have hpc1' : s1.pc = pcWord (base + 16) := hpc1
  have hst16 := step_ordinary oracle s1 (base + 16) (.ADDI .x10 .x21 0#12) (by omega) hpc1' hc16 (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x10 .x21 0#12)
  have hpc2 : s2.pc = pcWord (base + 17) := by
    simp only [s2, execInstrBr, MachineState.setPC, hpc1', pcWord_add_four]
  have hst17 := step_ordinary oracle s2 (base + 17) (.ADDI .x12 .x21 0#12) (by omega) hpc2 hc17 (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADDI .x12 .x21 0#12)
  have hpc3 : s3.pc = pcWord (base + 18) := by
    simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem3 : s3.mem = s1.mem := by simp [s3, s2, execInstrBr, mem_setPC, mem_setReg]
  have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h6 h10 h12 => by
    simp only [s3, s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h10.symm, hreg1 r h6]
  have hx10_3 : s3.getReg .x10 = 256#64 := by
    simp only [s3, s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hreg1 .x21 (by decide), hfix.x21, se12_0, BitVec.add_zero]
  have hx12_3 : s3.getReg .x12 = 256#64 := by
    simp only [s3, s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
      hreg1 .x21 (by decide), hfix.x21, se12_0, BitVec.add_zero]
  have hinp3 : readBuffer s3 256 96 = inp := by
    rw [readBuffer_chain96 s3 256]
    have hlo : readBuffer s3 256 32 = cv := by
      rw [(MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega),
        hout1.readBuffer_eq (by omega) (by omega), hcv]
    have hhi64 : readBuffer s3 288 64 = (valAt input ord).extractLsb' (8 * valOff) 512 := by
      have hval : readBuffer (submission.initialState .check input) (6308237280 + 256 * ord + valOff) 64 =
          (valAt input ord).extractLsb' (8 * valOff) 512 := by
        simpa only [valAt, dif_pos hord] using check_initial_value_slice input ord valOff 64 hord hval_bd
      rw [(MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega), ← hval]
      apply readBuffer_congr2; intro j hj
      rw [show 288 + j = 256 + 32 + j by omega, hcopy1 j hj]
      exact hhigh (6308237280 + 256 * ord + valOff + j) (by omega) (by omega)
    rw [hlo, hhi64]
  have hec := step_ecall_compress h768 oracle s3 (base + 18) 256 256 (by omega) hpc3 hc18
    ((hreg3 .x5 (by decide) (by decide) (by decide)).trans hfix.x5)
    ((hreg3 .x11 (by decide) (by decide) (by decide)).trans hfix.x11)
    ((hreg3 .x13 (by decide) (by decide) (by decide)).trans hfix.x13)
    hx10_3 hx12_3 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
  rw [hinp3] at hec
  let s4 := writeBits s3 (BitVec.ofNat 64 256) (c96 inp)
  have hpc4 : s4.pc = pcWord (base + 19) := by
    simp only [s4, writeBits, MachineState.setPC, hpc3, pcWord_add_four]
  have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s4.getReg r = s.getReg r := fun r h6 h10 h12 =>
    (writeBits_register s3 _ _ r).trans (hreg3 r h6 h10 h12)
  have hout4 : MemEqOutside s s4 256 352 :=
    (hout1.mono (by omega) (by omega)).trans
      ((MemEqOutside.of_mem_eq hmem3 256 352).trans
        ((MemEqOutside_writeBits_digest s3 256 _ (by omega)).mono (by omega) (by omega)))
  exact ⟨s4, (((hs1.trans (hst16.trans hst17)).trans hec).eq_of rfl (by omega) rfl (by simp; rfl)),
    hpc4,
    hfix.of_agree (fun r hr => hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hreg4, hout4, writeBits_readBuffer_digest s3 256 (c96 inp)⟩

/-- Phase 1A: check 15B low-salt availability and execute the branchless 4-call early-salt leaf chain
(`pc[34..128]` -> `pc[129]`, ≤ 190 steps, 4 calls). -/
theorem step_pos_leaf (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 34)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOff tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 10603204576)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 ord)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness s0 input.proof.length pOff tOff ord (posAt input.positions ord) (valAt input ord)
    PhaseOutcome oracle s 190 4 (input.proof.length < pOff + 15 + tailBytes tOff)
      (fun s' q tr =>
        q = 4 ∧
        s'.pc = pcWord 129 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 15) tOff s' ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
        s'.getReg .x15 = BitVec.ofNat 64 ord ∧
        s'.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = leafDigest c96 pw.index pw.salt pw.value ∧
        ∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) := by
  intro s0 c96 pw
  have hplen_bd : input.proof.length ≤ 8239714016 := hvalid
  have hle_cur : pOff + tailBytes tOff ≤ input.proof.length := hcur.le
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hi_lt : (posAt input.positions ord).val < 16777216 := (posAt input.positions ord).isLt
  -- pc[34]: LD x20, 0(x24)
  have ha34 : s.getReg .x24 + signExtend12 0#12 = BitVec.ofNat 64 (6174019552 + 8 * ord) := by
    rw [hx24, se12_0, BitVec.add_zero]
  have hv34 : memoryArgumentsValid s (.LD .x20 .x24 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha34]
    exact accessValid_ofNat (6174019552 + 8 * ord) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst34 := step_ordinary oracle s 34 (.LD .x20 .x24 0#12) (by decide) hpc rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv34])
  let s1 := execInstrBr s (.LD .x20 .x24 0#12)
  have hpc1 : s1.pc = pcWord 35 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hidx_mem : s.getMem (BitVec.ofNat 64 (6174019552 + 8 * ord)) =
      BitVec.ofNat 64 (posAt input.positions ord).val := by
    rw [hhigh.getMem_eq (by omega) (by omega) (by omega), check_initial_index input ord hord,
      posAt_val input.positions ord hord]
  have hx20_1 : s1.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha34]
    rw [MachineState.getReg_setReg_eq (by decide), hidx_mem]
  have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (10603204576 + pOff) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25), hcur.x25]
  -- pc[35]: ADDI x6, x25, 15; pc[36]: BLTU x31, x6, pc[261]
  have hst35 := step_ordinary oracle s1 35 (.ADDI .x6 .x25 15#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x6 .x25 15#12)
  have hpc2 : s2.pc = pcWord 36 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (10603204576 + pOff + 15) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx25_1, chk_se12_15]
    change BitVec.ofNat 64 (10603204576 + pOff) + BitVec.ofNat 64 15 = _
    exact bv64_add _ 15
  have hx31_2 : s2.getReg .x31 = BitVec.ofNat 64 (10603204576 + (input.proof.length - tailBytes tOff)) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x31), hcur.x31]
  have hst36 := step_ordinary oracle s2 36 (.BLTU .x31 .x6 900#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BLTU .x31 .x6 900#13)
  have hult : BitVec.ult (s2.getReg .x31) (s2.getReg .x6) = decide (input.proof.length < pOff + 15 + tailBytes tOff) := by
    rw [hx31_2, hx6_2, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pOff + 15 + tailBytes tOff
  · have hpc3 : s3.pc = pcWord 261 := by
      simp only [s3, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc2]
      exact pc_36_reject
    exact .rejected 6 0 [] hshort (by decide) (by decide)
      (by simpa using ((hst34.trans hst35).trans hst36).halt (halt_reject oracle s3 hpc3))
  · have hge15 : pOff + 15 + tailBytes tOff ≤ input.proof.length := by omega
    have hpc3 : s3.pc = pcWord 37 := by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      have h32 : s3.mem = s2.mem := by
        simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      rw [h32]; simp only [s2, s1, execInstrBr, mem_setPC, mem_setReg]
    have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x20 → s3.getReg r = s.getReg r := fun r hr6 hr20 => by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.getReg_setPC]
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr6.symm]
      simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ hr20.symm
    have hx20_3 : s3.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.getReg_setPC]
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x20), hx20_1]
    -- pc[37..39]: ADDI x12, x21, 0; call readN(15) -> buf[0..15)
    have hst37 := step_ordinary oracle s3 37 (.ADDI .x12 .x21 0#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x12 .x21 0#12)
    have hpc4 : s4.pc = pcWord 38 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hmem4 : s4.mem = s.mem := by simpa [s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
    obtain ⟨s5, hs5, hpc5, hx25_5, hreg5, hcopy5, hout5⟩ :=
      step_call_read_n oracle 38 15 s4 (10603204576 + pOff) 256 (by decide) (by decide) (by decide)
        rfl rfl hpc4
        (by simp only [s4, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
              hreg3 .x25 (by decide) (by decide), hcur.x25])
        (by simp only [s4, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide),
              hreg3 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
        (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
    have hreg5_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x25 → s5.getReg r = s.getReg r :=
      fun r h1 h6 h10 h12 h20 h25 => by
        rw [hreg5 r h1 h6 h10 h12 h25]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg3 r h6 h20]
    have hx20_5 : s5.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
      rw [hreg5 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x20), hx20_3]
    -- pc[40..46]: reconstruct buf[15] = bit120(ord)
    have hst40 := step_ordinary oracle s5 40 (.SRLI .x6 .x15 3#6) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.SRLI .x6 .x15 3#6)
    have hpc6 : s6.pc = pcWord 41 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
    have hst41 := step_ordinary oracle s6 41 (.ADD .x6 .x14 .x6) (by decide) hpc6 rfl (by intro h; cases h) rfl
    let s7 := execInstrBr s6 (.ADD .x6 .x14 .x6)
    have hpc7 : s7.pc = pcWord 42 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
    have hmem7 : s7.mem = s5.mem := by simp [s7, s6, execInstrBr, mem_setPC, mem_setReg]
    have hx6_7 : s7.getReg .x6 = BitVec.ofNat 64 (10603204576 + ord / 8) := by
      simp only [s7, s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x14),
        MachineState.getReg_setReg_eq (by decide),
        hreg5_s .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx14,
        hreg5_s .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx15,
        show (3#6 : BitVec 6).toNat = 3 by decide, bv64_shr ord 3 (by omega), bv64_add]
      rfl
    have ha42 : s7.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (10603204576 + ord / 8) := by
      rw [hx6_7, se12_0, BitVec.add_zero]
    have hv42 : memoryArgumentsValid s7 (.LBU .x6 .x6 0#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha42]
      exact accessValid_ofNat _ 1 (by unfold MEMORY_BYTES; omega) (by omega)
    have hst42 := step_ordinary oracle s7 42 (.LBU .x6 .x6 0#12) (by decide) hpc7 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv42])
    let s8 := execInstrBr s7 (.LBU .x6 .x6 0#12)
    have hpc8 : s8.pc = pcWord 43 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
    let topByte := s0.getByte (BitVec.ofNat 64 (10603204576 + ord / 8))
    have htopByte_lt : topByte.toNat < 256 := topByte.isLt
    have hhigh5 : HighMemPreserved s0 s5 :=
      hhigh.trans ((MemEqOutside.of_mem_eq hmem4 0 4294971392).trans (hout5.mono (by omega) (by omega)))
    have hx6_8 : s8.getReg .x6 = BitVec.ofNat 64 topByte.toNat := by
      simp only [s8, execInstrBr, MachineState.getReg_setPC, ha42]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hb : s7.getByte (BitVec.ofNat 64 (10603204576 + ord / 8)) = topByte := by
        have h75 : s7.getByte (BitVec.ofNat 64 (10603204576 + ord / 8)) = s5.getByte (BitVec.ofNat 64 (10603204576 + ord / 8)) := by
          simp [MachineState.getByte, MachineState.getMem, hmem7]
        rw [h75]; exact hhigh5 (10603204576 + ord / 8) (by omega) (by omega)
      rw [hb]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.zeroExtend, BitVec.toNat_setWidth]
    have hst43 := step_ordinary oracle s8 43 (.ANDI .x7 .x15 7#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
    let s9 := execInstrBr s8 (.ANDI .x7 .x15 7#12)
    have hpc9 : s9.pc = pcWord 44 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
    have hx7_9 : s9.getReg .x7 = BitVec.ofNat 64 (ord % 8) := by
      simp only [s9, s8, s7, s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x15), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x15), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x15),
        hreg5_s .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx15, chk_se12_7]
      exact chk_bv64_and_7 ord (by omega)
    have hx6_9 : s9.getReg .x6 = BitVec.ofNat 64 topByte.toNat := by
      simp only [s9, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_8]
    have hst44 := step_ordinary oracle s9 44 (.SRL .x6 .x6 .x7) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.SRL .x6 .x6 .x7)
    have hpc10 : s10.pc = pcWord 45 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
    have hx6_10 : s10.getReg .x6 = BitVec.ofNat 64 (topByte.toNat / 2 ^ (ord % 8)) := by
      simp only [s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hx6_9, hx7_9,
        toNat_ofNat64 (ord % 8) (by omega), Nat.mod_eq_of_lt (by omega : ord % 8 < 64)]
      exact bv64_shr topByte.toNat (ord % 8) (by omega)
    have hst45 := step_ordinary oracle s10 45 (.ANDI .x6 .x6 1#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
    let s11 := execInstrBr s10 (.ANDI .x6 .x6 1#12)
    have hpc11 : s11.pc = pcWord 46 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
    have hmem11 : s11.mem = s5.mem := by simp [s11, s10, s9, s8, execInstrBr, mem_setPC, mem_setReg, hmem7]
    have hreg11 : ∀ r, r ≠ .x6 → r ≠ .x7 → s11.getReg r = s5.getReg r := fun r h6r h7r => by
      simp only [s11, s10, s9, s8, s7, s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h7r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6r.symm]
    have hx6_11 : s11.getReg .x6 = BitVec.ofNat 64 (if saltTopBitFromMem s0 ord then 1 else 0) := by
      simp only [s11, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hx6_10, se12_1,
        bv64_and_one _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        chk_byte_getLsbD_eq_div_mod topByte (ord % 8) (by omega)]
      rfl
    have ha46 : s11.getReg .x21 + signExtend12 15#12 = BitVec.ofNat 64 271 := by
      rw [hreg11 .x21 (by decide) (by decide),
        hreg5_s .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hfix.x21, chk_se12_15]
      decide
    have hv46 : memoryArgumentsValid s11 (.SB .x21 .x6 15#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha46]
      exact accessValid_ofNat 271 1 (by unfold MEMORY_BYTES; omega) (by decide)
    have hst46 := step_ordinary oracle s11 46 (.SB .x21 .x6 15#12) (by decide) hpc11 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv46])
    let s12 := execInstrBr s11 (.SB .x21 .x6 15#12)
    have hpc12 : s12.pc = pcWord 47 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
    have hreg12 : ∀ r, r ≠ .x6 → r ≠ .x7 → s12.getReg r = s5.getReg r := fun r h6r h7r => by
      have : s12.getReg r = s11.getReg r := by
        simp [s12, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      exact this.trans (hreg11 r h6r h7r)
    have hout12 : MemEqOutside s5 s12 271 272 := by
      intro a ha hout
      simp only [s12, execInstrBr, ha46, MachineState.getByte, MachineState.getMem_setPC]
      exact (MemEqOutside_setByte s11 271 _ (by omega) a ha hout).trans
        (by simp [MachineState.getByte, MachineState.getMem, hmem11])
    have hsalt12 : readBuffer s12 256 16 = salt121Word16 pw.salt := by
      apply parseSalt121_word16_bytes s12 s0 256 pOff ord
      · intro j hj
        rw [hout12 (256 + j) (by omega) (by omega), hcopy5 j hj]
        exact (hhigh.trans (MemEqOutside.of_mem_eq hmem4 0 4294971392)) (10603204576 + pOff + j) (by omega) (by omega)
      · simp only [s12, execInstrBr, ha46, hx6_11, MachineState.getByte, MachineState.getMem_setPC]
        change (s11.setByte (BitVec.ofNat 64 271) _).getByte (BitVec.ofNat 64 271) = _
        rw [set_byte_read, if_pos rfl]
        cases saltTopBitFromMem s0 ord <;> decide
    -- pc[47..50]: write leafTag i = 4072 + 256 * i at buf[16..24) (addr 272)
    have hcodeTag : ∀ j (hj : j < leafTagInstrs.length), checkInstr (47 + j) = .base (leafTagInstrs[j]'hj) := by
      intro j hj; have hj' : j < 3 := hj; interval_cases j <;> rfl
    have hpureTag : ∀ j (hj : j < leafTagInstrs.length),
        Instruction.base (leafTagInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (leafTagInstrs[j]'hj)) = some (execInstrBr st (leafTagInstrs[j]'hj)) ∧
              (execInstrBr st (leafTagInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (leafTagInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 3 := hj
      interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs13, hpc13, hmem13⟩ := step_pure_list oracle 47 leafTagInstrs s12 (by decide) hcodeTag hpureTag hpc12
    let s13 := runInstrs s12 leafTagInstrs
    have hs13 : StepsTo oracle s12 s13 3 0 [] := hs13
    have hpc13 : s13.pc = pcWord 50 := hpc13
    have hx6_13 : s13.getReg .x6 = leafTag (posAt input.positions ord) := by
      have harith : ((BitVec.ofNat 64 (posAt input.positions ord).val <<< (8#6 : BitVec 6).toNat) +
          signExtend12 2036#12) + signExtend12 2036#12 = leafTag (posAt input.positions ord) := by
        rw [show (8#6 : BitVec 6).toNat = 8 by decide, bv64_shl _ 8 (by omega), chk_se12_2036]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 2036 + BitVec.ofNat 64 2036 = _
        rw [bv64_add, bv64_add]; unfold leafTag; congr 1; omega
      simpa only [s13, runInstrs, leafTagInstrs, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq,
        hreg12 .x20 (by decide) (by decide), hx20_5] using harith
    have hreg13 : ∀ r, r ≠ .x6 → r ≠ .x7 → s13.getReg r = s5.getReg r := fun r h6r h7r => by
      simp only [s13, runInstrs, leafTagInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6r.symm, hreg12 r h6r h7r]
    have ha50 : s13.getReg .x21 + signExtend12 16#12 = BitVec.ofNat 64 272 := by
      rw [hreg13 .x21 (by decide) (by decide),
        hreg5_s .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_16]; decide
    have hv50 : memoryArgumentsValid s13 (.SD .x21 .x6 16#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha50]
      exact accessValid_ofNat 272 8 (by unfold MEMORY_BYTES; omega) (by decide)
    have hst50 := step_ordinary oracle s13 50 (.SD .x21 .x6 16#12) (by decide) hpc13 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv50])
    let s14 := execInstrBr s13 (.SD .x21 .x6 16#12)
    have hpc14 : s14.pc = pcWord 51 := by simp only [s14, execInstrBr, MachineState.setPC, hpc13, pcWord_add_four]
    have hreg14 : ∀ r, r ≠ .x6 → r ≠ .x7 → s14.getReg r = s5.getReg r := fun r h6r h7r => by
      have : s14.getReg r = s13.getReg r := by
        simp [s14, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      exact this.trans (hreg13 r h6r h7r)
    have hout14_12 : MemEqOutside s12 s14 272 280 := by
      intro a ha hout
      simp only [s14, execInstrBr, ha50, MachineState.getByte, MachineState.getMem_setPC]
      exact (setMem_getByte_ofNat s13 272 a _ (by decide) (by omega) ha hout).trans
        (by simp only [s13, MachineState.getByte, MachineState.getMem, hmem13])
    have htag14 : readBuffer s14 272 8 = leafTag pw.index := by
      rw [readBuffer_word s14 272 (by decide)]
      simp only [s14, execInstrBr, ha50, hx6_13, MachineState.getMem_setPC, MachineState.getMem_setMem_eq]; rfl
    have hout_s14 : MemEqOutside s s14 256 280 :=
      (MemEqOutside.of_mem_eq hmem4 256 280).trans
        ((hout5.mono (by omega) (by omega)).trans
          ((hout12.mono (by omega) (by omega)).trans (hout14_12.mono (by omega) (by omega))))
    -- pc[51..68]: copy 9 dwords val[0..72) -> buf[24..96) (addr 280..352)
    have hcodeC0 : ∀ j < 9,
        checkInstr (51 + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (0 + 8 * j))) ∧
        checkInstr (51 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (24 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s15, hs15, hpc15, hreg15, hcopy15, hout15⟩ :=
      step_copy_dwords oracle 51 9 .x8 .x21 0 24 s14 (6308237280 + 256 * ord) 256
        (by decide) (by decide) (by decide) (by decide) (by decide) hcodeC0 hpc14
        ((hreg14 .x8 (by decide) (by decide)).trans
          ((hreg5_s .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8))
        ((hreg14 .x21 (by decide) (by decide)).trans
          ((hreg5_s .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
        (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
    -- pc[69..71]: Call 0 -> buf[0..32)
    have hst69 := step_ordinary oracle s15 69 (.ADDI .x10 .x21 0#12) (by decide) hpc15 rfl (by intro h; cases h) rfl
    let s16 := execInstrBr s15 (.ADDI .x10 .x21 0#12)
    have hpc16 : s16.pc = pcWord 70 := by simp only [s16, execInstrBr, MachineState.setPC, hpc15, pcWord_add_four]
    have hst70 := step_ordinary oracle s16 70 (.ADDI .x12 .x21 0#12) (by decide) hpc16 rfl (by intro h; cases h) rfl
    let s17 := execInstrBr s16 (.ADDI .x12 .x21 0#12)
    have hpc17 : s17.pc = pcWord 71 := by simp only [s17, execInstrBr, MachineState.setPC, hpc16, pcWord_add_four]
    have hmem17 : s17.mem = s15.mem := by simp [s17, s16, execInstrBr, mem_setPC, mem_setReg]
    have hreg17_5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → s17.getReg r = s5.getReg r :=
      fun r h6r h7r h10r h12r => by
        simp only [s17, s16, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12r.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h10r.symm, hreg15 r h6r, hreg14 r h6r h7r]
    have hx10_17 : s17.getReg .x10 = 256#64 := by
      simp only [s17, s16, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hreg15 .x21 (by decide), hreg14 .x21 (by decide) (by decide),
        hreg5_s .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero]
    have hx12_17 : s17.getReg .x12 = 256#64 := by
      simp only [s17, s16, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
        hreg15 .x21 (by decide), hreg14 .x21 (by decide) (by decide),
        hreg5_s .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero]
    let i0 := leafCall0Input pw.index pw.salt pw.value
    have hinp0 : readBuffer s17 256 96 = i0 := by
      rw [readBuffer_call0 s17 256]
      have h16 : readBuffer s17 256 16 = salt121Word16 pw.salt := by
        rw [(MemEqOutside.of_mem_eq hmem17 0 0).readBuffer_eq (by omega) (by omega),
          hout15.readBuffer_eq (by omega) (by omega), hout14_12.readBuffer_eq (by omega) (by omega), hsalt12]
      have h8 : readBuffer s17 272 8 = leafTag pw.index := by
        rw [(MemEqOutside.of_mem_eq hmem17 0 0).readBuffer_eq (by omega) (by omega),
          hout15.readBuffer_eq (by omega) (by omega), htag14]
      have h72 : readBuffer s17 280 72 = pw.value.extractLsb' 0 576 := by
        have hval : readBuffer s0 (6308237280 + 256 * ord) 72 = pw.value.extractLsb' 0 576 := by
          simpa only [Nat.add_zero, Nat.mul_zero, pw, parsePartialWitness, valAt, dif_pos hord] using
            check_initial_value_slice input ord 0 72 hord (by decide)
        rw [(MemEqOutside.of_mem_eq hmem17 0 0).readBuffer_eq (by omega) (by omega), ← hval]
        apply readBuffer_congr2; intro j hj
        rw [show 280 + j = 256 + 24 + j by omega, hcopy15 j hj, Nat.add_zero]
        exact (hhigh.trans (hout_s14.mono (by omega) (by omega))) (6308237280 + 256 * ord + j) (by omega) (by omega)
      rw [h16, h8, h72]; rfl
    have hec0 := step_ecall_compress h768 oracle s17 71 256 256 (by decide) hpc17 rfl
      ((hreg17_5 .x5 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg5_s .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5))
      ((hreg17_5 .x11 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg5_s .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11))
      ((hreg17_5 .x13 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg5_s .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13))
      hx10_17 hx12_17 (by decide) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
    rw [hinp0] at hec0
    let cv0 := c96 i0
    let s18 := writeBits s17 (BitVec.ofNat 64 256) cv0
    have hpc18 : s18.pc = pcWord 72 := by simp only [s18, writeBits, MachineState.setPC, hpc17, pcWord_add_four]
    have hreg18_5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → s18.getReg r = s5.getReg r :=
      fun r h6r h7r h10r h12r => (writeBits_register s17 _ cv0 r).trans (hreg17_5 r h6r h7r h10r h12r)
    have hfix18 : CheckFixedRegs s18 :=
      hfix.of_agree (fun r hr => (hreg18_5 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
        (hreg5_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
    have hout_s18 : MemEqOutside s s18 256 352 :=
      (hout_s14.mono (by omega) (by omega)).trans
        ((hout15.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem17 256 352).trans
            ((MemEqOutside_writeBits_digest s17 256 cv0 (by omega)).mono (by omega) (by omega))))
    have hx8_18 : s18.getReg .x8 = BitVec.ofNat 64 (6308237280 + 256 * ord) :=
      (hreg18_5 .x8 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg5_s .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
    have hhs0_18 : StepsTo oracle s s18 129 1 [(i0.cast h768.symm, cv0)] := by
      have h1 := ((hst34.trans hst35).trans hst36).trans (hst37.trans hs5)
      have h2 := ((hst40.trans hst41).trans hst42).trans ((hst43.trans hst44).trans (hst45.trans hst46))
      have h3 := (hs13.trans hst50).trans (hs15.trans ((hst69.trans hst70).trans hec0))
      exact ((h1.trans h2).trans h3).eq_of rfl (by decide) rfl (by simp; rfl)
    -- Call 1: pc[72..90] -> pc[91]
    obtain ⟨s19, hs19, hpc19, hfix19, hreg19, hout19, hcv1⟩ :=
      step_leaf_chain_call h768 oracle input ord 72 72 hord (by decide) (by decide) (by decide)
        (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩) rfl rfl rfl
        s18 hpc18 hfix18 (hhigh.trans (hout_s18.mono (by omega) (by omega))) hx8_18 cv0
        (writeBits_readBuffer_digest s17 256 cv0)
    -- Call 2: pc[91..109] -> pc[110]
    let i1 := leafCall1Input cv0 pw.value
    let cv1 := c96 i1
    obtain ⟨s20, hs20, hpc20, hfix20, hreg20, hout20, hcv2⟩ :=
      step_leaf_chain_call h768 oracle input ord 91 136 hord (by decide) (by decide) (by decide)
        (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩) rfl rfl rfl
        s19 hpc19 hfix19 (hhigh.trans ((hout_s18.trans hout19).mono (by omega) (by omega)))
        ((hreg19 .x8 (by decide) (by decide) (by decide)).trans hx8_18) cv1 hcv1
    -- Call 3: pc[110..128] -> pc[129]
    let i2 := leafCall2Input cv1 pw.value
    let cv2 := c96 i2
    obtain ⟨s21, hs21, hpc21, hfix21, hreg21, hout21, hcv3⟩ :=
      step_leaf_chain_call h768 oracle input ord 110 192 hord (by decide) (by decide) (by decide)
        (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩) rfl rfl rfl
        s20 hpc20 hfix20 (hhigh.trans (((hout_s18.trans hout19).trans hout20).mono (by omega) (by omega)))
        ((hreg20 .x8 (by decide) (by decide) (by decide)).trans ((hreg19 .x8 (by decide) (by decide) (by decide)).trans hx8_18))
        cv2 hcv2
    let i3 := leafCall3Input cv2 pw.value
    have hreg21_5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → s21.getReg r = s5.getReg r :=
      fun r h6r h7r h10r h12r =>
        (hreg21 r h6r h10r h12r).trans ((hreg20 r h6r h10r h12r).trans ((hreg19 r h6r h10r h12r).trans
          (hreg18_5 r h6r h7r h10r h12r)))
    have hcur21 : ProofCursor s0 input.proof.length (pOff + 15) tOff s21 := by
      refine ⟨hge15, ?_, ?_, ?_, ?_⟩
      · rw [hreg21_5 .x25 (by decide) (by decide) (by decide) (by decide), hx25_5, Nat.add_assoc]
      · rw [hreg21_5 .x31 (by decide) (by decide) (by decide) (by decide),
          hreg5_s .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
      · rw [hreg21_5 .x3 (by decide) (by decide) (by decide) (by decide),
          hreg5_s .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
      · rw [hreg21_5 .x4 (by decide) (by decide) (by decide) (by decide),
          hreg5_s .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
    have htot := ((hhs0_18.trans hs19).trans hs20).trans hs21
    refine .continued s21 186 4
        ([(i0.cast h768.symm, c96 i0), (i1.cast h768.symm, c96 i1),
          (i2.cast h768.symm, c96 i2), (i3.cast h768.symm, c96 i3)])
        (by decide) (by decide)
        (htot.eq_of rfl (by decide) (by decide) (by rfl))
        ⟨rfl, hpc21, hfix21, hcur21, ((hout_s18.trans hout19).trans hout20).trans hout21,
         (hreg21_5 .x14 (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg5_s .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14),
         (hreg21_5 .x15 (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg5_s .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15),
         (hreg21_5 .x20 (by decide) (by decide) (by decide) (by decide)).trans hx20_5,
         (hreg21_5 .x24 (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg5_s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24),
         (hreg21_5 .x8  (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg5_s .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8),
         (hreg21_5 .x27 (by decide) (by decide) (by decide) (by decide)).trans
           ((hreg5_s .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
         hcv3, ?_⟩
    intro x hx
    change x ∈ [i0, i1, i2, i3] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          · exact (List.not_mem_nil hx).elim

private def l0SetupTailInstrs : List Instr :=
  [.ADDI .x22 .x20 0#12, .ADDI .x29 .x2 0#12, .ADDI .x30 .x2 512#12]

/-- Phase 1B: mask L0 leaf digest to 238 bits, zero the 32B binary gap `S[64..96)`, and initialize
the L0..L15 loop registers (`pc[129..138]` -> `pc[139]`, 10 steps, 0 calls). -/
theorem step_pos_l0_setup (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (ord pOff tOff rem : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 129)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 15) tOff s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 10603204576)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 ord)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hleaf : readBuffer s 256 32 =
      leafDigest (fun x => oracle.compression (x.cast h768.symm))
        (posAt input.positions ord)
        (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff ord
          (posAt input.positions ord) (valAt input ord)).salt
        (valAt input ord)) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness s0 input.proof.length pOff tOff ord (posAt input.positions ord) (valAt input ord)
    ∃ s', StepsTo oracle s s' 10 0 [] ∧
      s'.pc = pcWord 139 ∧
      CheckFixedRegs s' ∧
      ProofCursor s0 input.proof.length (pOff + 15) tOff s' ∧
      MemEqOutside s s' 256 352 ∧
      s'.getReg .x14 = BitVec.ofNat 64 10603204576 ∧
      s'.getReg .x15 = BitVec.ofNat 64 ord ∧
      s'.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> 0) ∧
      s'.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * ord) ∧
      s'.getReg .x8  = BitVec.ofNat 64 (6308237280 + 256 * ord) ∧
      s'.getReg .x27 = BitVec.ofNat 64 rem ∧
      s'.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 0) ∧
      s'.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
      readBuffer s' 256 32 = pw.evalLevel c96 0 ∧
      readBuffer s' 320 32 = 0 := by
  intro s0 c96 pw
  -- pc[129..131]: mask238 at S[0..32)
  obtain ⟨s1, hs1, hpc1, hreg1, hdig1_raw, hout1⟩ :=
    step_mask238 oracle 129 .x21 s 256 (by decide) (by decide) rfl rfl rfl hpc hfix.x21 hfix.x9
      (by decide) (by unfold MEMORY_BYTES; omega)
  have hdig1 : readBuffer s1 256 32 = pw.evalLevel c96 0 := by
    rw [hdig1_raw, hleaf]
    rfl
  -- pc[132..135]: zero binary gap S[64..96)
  obtain ⟨s2, hs2, hpc2, hreg2, hgap2, hout2⟩ :=
    step_zero_gap oracle s1 hpc1 ((hreg1 .x21 (by decide)).trans hfix.x21)
  -- pc[136..138]: ADDI x22, x20, 0; ADDI x29, x2, 0; ADDI x30, x2, 512
  have hcodeT : ∀ j (hj : j < l0SetupTailInstrs.length), checkInstr (136 + j) = .base (l0SetupTailInstrs[j]'hj) := by
    intro j hj; have hj' : j < 3 := hj; interval_cases j <;> rfl
  have hpureT : ∀ j (hj : j < l0SetupTailInstrs.length),
      Instruction.base (l0SetupTailInstrs[j]'hj) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (l0SetupTailInstrs[j]'hj)) = some (execInstrBr st (l0SetupTailInstrs[j]'hj)) ∧
            (execInstrBr st (l0SetupTailInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (l0SetupTailInstrs[j]'hj)).mem = st.mem := by
    intro j hj; have hj' : j < 3 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs3, hpc3, hmem3⟩ := step_pure_list oracle 136 l0SetupTailInstrs s2 (by decide) hcodeT hpureT hpc2
  let s3 := runInstrs s2 l0SetupTailInstrs
  have hs3 : StepsTo oracle s2 s3 3 0 [] := hs3
  have hpc3 : s3.pc = pcWord 139 := hpc3
  have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x22 → r ≠ .x29 → r ≠ .x30 → s3.getReg r = s.getReg r :=
    fun r h6 h22 h29 h30 => by
      have hr32 : s3.getReg r = s2.getReg r := by
        simp only [s3, runInstrs, l0SetupTailInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h30.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h29.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
      exact hr32.trans ((hreg2 r).trans (hreg1 r h6))
  have hx22_3 : s3.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val >>> 0) := by
    simp only [s3, runInstrs, l0SetupTailInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero, hreg2, hreg1 .x20 (by decide), hx20,
      Nat.shiftRight_zero]
  have hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 0) := by
    simp only [s3, runInstrs, l0SetupTailInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero, hreg2, hreg1 .x2 (by decide), hfix.x2,
      Nat.mul_zero, Nat.add_zero]
  have hx30_3 : s3.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
    simp only [s3, runInstrs, l0SetupTailInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, se12_512, hreg2, hreg1 .x2 (by decide), hfix.x2]
    exact bv64_add 68719475936 512
  have hout_all : MemEqOutside s s3 256 352 :=
    (hout1.mono (by omega) (by omega)).trans
      ((hout2.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem3 256 352))
  refine ⟨s3, ((hs1.trans hs2).trans hs3).eq_of rfl (by decide) (by decide) (by simp),
    hpc3,
    hfix.of_agree (fun r hr => hreg3 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
      (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
    hcur.of_agree (fun r hr => hreg3 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
      (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
    hout_all,
    (hreg3 .x14 (by decide) (by decide) (by decide) (by decide)).trans hx14,
    (hreg3 .x15 (by decide) (by decide) (by decide) (by decide)).trans hx15,
    hx22_3,
    (hreg3 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24,
    (hreg3 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8,
    (hreg3 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27,
    hx29_3, hx30_3,
    ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)).trans
      ((hout2.readBuffer_eq (by omega) (by omega)).trans hdig1),
    ((MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)).trans hgap2⟩

end CommitGolfCandidate
