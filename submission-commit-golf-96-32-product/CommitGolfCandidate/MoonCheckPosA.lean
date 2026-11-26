import CommitGolfCandidate.MoonCheckBase

/-! Symbolic execution of the checker prologue and per-position leaf/L0/L1 phases (`pc[0..140]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private def prologuePrefix : List Instr :=
  [.ADDI .x26 .x11 0#12, .ADDI .x24 .x13 0#12, .ADDI .x8 .x14 0#12,
   .ADDI .x25 .x15 0#12, .ADD .x31 .x15 .x17, .ADDI .x27 .x16 0#12]

private def prologueNonemptySetup : List Instr :=
  [.ADDI .x3 .x0 0#12, .ADDI .x4 .x0 0#12,
   .ADDI .x9 .x0 1#12, .SLLI .x9 .x9 46#6, .ADDI .x9 .x9 4095#12,
   .ADDI .x21 .x0 256#12, .ADDI .x18 .x0 2#12, .SLLI .x18 .x18 11#6,
   .ADDI .x19 .x0 4#12, .SLLI .x19 .x19 11#6, .ADDI .x5 .x0 0#12,
   .ADDI .x11 .x0 96#12, .ADDI .x13 .x0 0#12]

theorem initialState_check_regs (input : CheckInput) :
    let s0 := submission.initialState .check input
    s0.pc = pcWord 0 ∧
    s0.getReg .x2  = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x11 = BitVec.ofNat 64 4294971392 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6912218176 ∧
    s0.getReg .x14 = BitVec.ofNat 64 7046435904 ∧
    s0.getReg .x15 = BitVec.ofNat 64 11341403200 ∧
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
    intro i hi
    have hi' : i < 6 := hi
    interval_cases i <;> rfl
  have hpure : ∀ i (hi : i < prologuePrefix.length),
      Instruction.base (prologuePrefix[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologuePrefix[i]'hi)) = some (execInstrBr st (prologuePrefix[i]'hi)) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).mem = st.mem := by
    intro i hi
    have hi' : i < 6 := hi
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
  have hst7 := step_ordinary oracle s2 7 (.BNE .x17 .x0 1292#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x17 .x0 1292#13)
  have hplen_lt : input.proof.length < 2 ^ 64 := by
    change input.proof.length ≤ 8556390424 at hvalid; omega
  by_cases hpz : input.proof.length = 0
  · simp only [hpz, ite_true]
    have hx17_z : s2.getReg .x17 = 0#64 := by rw [hx17_2, hpz]
    have hpc3 : s3.pc = pcWord 8 := by
      simp only [s3, execInstrBr, hx17_z, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
        ite_false, MachineState.setPC, hpc2, pcWord_add_four]
    have hst8 := step_ordinary oracle s3 8 (.JAL .x0 1276#21) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.JAL .x0 1276#21)
    have hpc4 : s4.pc = pcWord 327 := by
      simp only [s4, execInstrBr, MachineState.setPC, hpc3]; decide
    have htot := ((hs1.trans hst6).trans (hst7.trans hst8)).halt (halt_accept oracle s4 hpc4)
    simpa using htot
  · simp only [hpz, ite_false]
    have hne : s2.getReg .x17 ≠ 0#64 := by
      rw [hx17_2]
      change BitVec.ofNat 64 input.proof.length ≠ BitVec.ofNat 64 0
      rw [ne_eq, bv64_eq_iff _ 0 hplen_lt (by decide)]
      exact hpz
    have hneb : (s2.getReg .x17 != s2.getReg .x0) = true := by
      change (s2.getReg .x17 != 0#64) = true
      rw [bne_iff_ne]; exact hne
    have hpc3 : s3.pc = pcWord 330 := by
      simp only [s3, execInstrBr, hneb, ite_true, MachineState.setPC, hpc2]; decide
    have htot := ((hs1.trans hst6).trans hst7).halt (halt_reject oracle s3 hpc3)
    exact (by simpa using htot : HaltsWith oracle s0 11 0 .failure []).mono (by decide)

/-- When `positions.card ≥ 1`, the prologue reaches `pc[22]` in 20 steps with 0 oracle calls. -/
theorem step_prologue_nonempty (oracle : Oracle) (input : CheckInput)
    (hne : input.positions.card ≠ 0) :
    ∃ s1, StepsTo oracle (submission.initialState .check input) s1 20 0 [] ∧
      s1.pc = pcWord 22 ∧
      s1.mem = (submission.initialState .check input).mem ∧
      CheckFixedRegs s1 ∧
      ProofCursor (submission.initialState .check input) input.proof.length 0 0 s1 ∧
      s1.getReg .x24 = BitVec.ofNat 64 6912218176 ∧
      s1.getReg .x8  = BitVec.ofNat 64 7046435904 ∧
      s1.getReg .x27 = BitVec.ofNat 64 input.positions.card := by
  let s0 := submission.initialState .check input
  have hcard_lt : input.positions.card < 2 ^ 64 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at this; omega
  obtain ⟨hpc0, hx2, hx11, hx13, hx14, hx15, hx16, hx17⟩ := initialState_check_regs input
  have hcode1 : ∀ i (hi : i < prologuePrefix.length),
      checkInstr (0 + i) = .base (prologuePrefix[i]'hi) := by
    intro i hi
    have hi' : i < 6 := hi
    interval_cases i <;> rfl
  have hpure1 : ∀ i (hi : i < prologuePrefix.length),
      Instruction.base (prologuePrefix[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologuePrefix[i]'hi)) = some (execInstrBr st (prologuePrefix[i]'hi)) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologuePrefix[i]'hi)).mem = st.mem := by
    intro i hi
    have hi' : i < 6 := hi
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
  have hneb : (s1.getReg .x27 != s1.getReg .x0) = true := by
    change (s1.getReg .x27 != 0#64) = true
    rw [bne_iff_ne, hx27_1]
    change BitVec.ofNat 64 input.positions.card ≠ BitVec.ofNat 64 0
    rw [ne_eq, bv64_eq_iff _ 0 hcard_lt (by decide)]
    exact hne
  have hst6 := step_ordinary oracle s1 6 (.BNE .x27 .x0 12#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BNE .x27 .x0 12#13)
  have hpc2 : s2.pc = pcWord 9 := by
    simp only [s2, execInstrBr, hneb, ite_true, MachineState.setPC, hpc1]; decide
  have hmem2 : s2.mem = s0.mem := by
    simpa [s2, execInstrBr, hneb, MachineState.setPC] using hmem1
  have hcode2 : ∀ i (hi : i < prologueNonemptySetup.length),
      checkInstr (9 + i) = .base (prologueNonemptySetup[i]'hi) := by
    intro i hi
    have hi' : i < 13 := hi
    interval_cases i <;> rfl
  have hpure2 : ∀ i (hi : i < prologueNonemptySetup.length),
      Instruction.base (prologueNonemptySetup[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologueNonemptySetup[i]'hi)) = some (execInstrBr st (prologueNonemptySetup[i]'hi)) ∧
            (execInstrBr st (prologueNonemptySetup[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologueNonemptySetup[i]'hi)).mem = st.mem := by
    intro i hi
    have hi' : i < 13 := hi
    interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs3, hpc3, hmem3⟩ := step_pure_list oracle 9 prologueNonemptySetup s2 (by decide) hcode2 hpure2 hpc2
  let s3 := runInstrs s2 prologueNonemptySetup
  have hs3 : StepsTo oracle s2 s3 13 0 [] := hs3
  have hpc3 : s3.pc = pcWord 22 := hpc3
  have hreg_s2 : ∀ r, s2.getReg r = s1.getReg r := fun r => by
    simp [s2, execInstrBr, hneb, MachineState.getReg_setPC]
  have hreg_s3 : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x9 → r ≠ .x11 → r ≠ .x13 →
      r ≠ .x18 → r ≠ .x19 → r ≠ .x21 → s3.getReg r = s2.getReg r :=
    fun r h3 h4 h5 h9 h11 h13 h18 h19 h21 => by
      simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h13.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h11.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h5.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h19.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h19.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h18.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h18.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h21.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h4.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h3.symm]
  have hfixed : CheckFixedRegs s3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hreg_s3 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, decide_not,
        not_false_eq_true, reduceCtorEq]
      exact hx2
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · rw [hreg_s3 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
      exact hx11
  have hcur : ProofCursor s0 input.proof.length 0 0 s3 := by
    refine ⟨by simp [tailBytes_zero], ?_, ?_, ?_, ?_⟩
    · rw [hreg_s3 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero, Nat.add_zero]
      exact hx15
    · rw [hreg_s3 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, tailBytes_zero, Nat.sub_zero]
      have h15 : s0.getReg .x15 = BitVec.ofNat 64 11341403200 := hx15
      have h17 : s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := hx17
      rw [h15, h17, bv64_add]
    · rw [tailBuf_zero]
      simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    · rw [tailCnt_zero]
      simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  refine ⟨s3, by simpa using (hs1.trans hst6).trans hs3, hpc3, hmem3.trans hmem2, hfixed, hcur, ?_, ?_, ?_⟩
  · rw [hreg_s3 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx13
  · rw [hreg_s3 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx14
  · rw [hreg_s3 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2, hx27_1]

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

def l0Bytes (i : Index) : Nat :=
  if i.val / 3 = FULL_TRIPLETS then 0 else 64

def binStepBytes (g step : Nat) : Nat :=
  if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step) then
    if 2 + step < 6 then 30 else 29
  else 0

def binPathOff (g : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => binPathOff g n + binStepBytes g n

def binStepTails (g step : Nat) : Nat :=
  if ((g >>> (step + 5)) ^^^ 1) < levelSize (6 + step) then 1 else 0

def binTailOff (g : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => binTailOff g n + binStepTails g n

def recordLen (i : Index) : Nat :=
  24 + l0Bytes i + 32 + binPathOff (i.val / 3) 13

def recordTailCount (i : Index) : Nat :=
  binTailOff (i.val / 3) 9

def posRecordOff (positions : Positions) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, recordLen (posAt positions j)

def posTailOff (positions : Positions) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, recordTailCount (posAt positions j)

theorem posRecordOff_succ (positions : Positions) (n : Nat) :
    posRecordOff positions (n + 1) = posRecordOff positions n + recordLen (posAt positions n) :=
  Finset.sum_range_succ _ n

theorem posRecordOff_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    posRecordOff positions a ≤ posRecordOff positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem posTailOff_zero (positions : Positions) : posTailOff positions 0 = 0 := by
  simp [posTailOff]

theorem posTailOff_succ (positions : Positions) (n : Nat) :
    posTailOff positions (n + 1) = posTailOff positions n + recordTailCount (posAt positions n) :=
  Finset.sum_range_succ _ n

theorem posTailOff_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    posTailOff positions a ≤ posTailOff positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

def parsePartialWitness (s0 : MachineState) (proofLen pOff tOff : Nat)
    (i : Index) (val : Entry) : WitnessPath where
  index := i
  value := val
  salt := readBuffer s0 (11341403200 + pOff) 24
  l0Sib0 := if i.val / 3 = FULL_TRIPLETS then 0 else readBuffer s0 (11341403200 + pOff + 24) 32
  l0Sib1 := if i.val / 3 = FULL_TRIPLETS then 0 else readBuffer s0 (11341403200 + pOff + 56) 32
  binSib := fun prev =>
    if prev = 1 then
      readBuffer s0 (11341403200 + pOff + 24 + l0Bytes i) 32
    else if 2 ≤ prev ∧ prev ≤ 5 then
      proofDigest30 s0 (11341403200 + pOff + 24 + l0Bytes i + 32 + binPathOff (i.val / 3) (prev - 2))
    else if 6 ≤ prev ∧ prev ≤ 14 then
      proofDigest238 s0 proofLen
        (11341403200 + pOff + 24 + l0Bytes i + 32 + binPathOff (i.val / 3) (prev - 2))
        (tOff + binTailOff (i.val / 3) (prev - 6))
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

/-! #### Per-Position Sub-Phases (`pc[22..140]`) -/

private def leafAOutInstrs : List Instr :=
  [.ADDI .x10 .x21 0#12, .ANDI .x7 .x20 1#12, .SLLI .x7 .x7 5#6,
   .ADD .x12 .x21 .x7, .ADDI .x12 .x12 96#12]

/-- Phase 1A: check 24B salt availability and execute the 4-call late-salt leaf chain (`pc[22..66]` -> `pc[67]`). -/
theorem step_pos_leaf (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 22)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOff tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness s0 input.proof.length pOff tOff (posAt input.positions ord) (valAt input ord)
    PhaseOutcome oracle s 190 4 (input.proof.length < pOff + 24 + tailBytes tOff)
      (fun s' q tr =>
        q = 4 ∧
        s'.pc = pcWord 67 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 24) tOff s' ∧
        MemEqOutside s s' 256 448 ∧
        s'.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = leafDigest c96 pw.index pw.salt pw.value ∧
        ∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) := by
  intro s0 c96 pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hle_cur : pOff + tailBytes tOff ≤ input.proof.length := hcur.le
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hi_lt : (posAt input.positions ord).val < 16777216 := (posAt input.positions ord).isLt
  -- pc[22]: LD x20, 0(x24)
  have ha22 : s.getReg .x24 + signExtend12 0#12 = BitVec.ofNat 64 (6912218176 + 8 * ord) := by
    rw [hx24, se12_0, BitVec.add_zero]
  have hv22 : memoryArgumentsValid s (.LD .x20 .x24 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha22]
    exact accessValid_ofNat (6912218176 + 8 * ord) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst22 := step_ordinary oracle s 22 (.LD .x20 .x24 0#12) (by decide) hpc rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv22])
  let s1 := execInstrBr s (.LD .x20 .x24 0#12)
  have hpc1 : s1.pc = pcWord 23 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hidx_mem : s.getMem (BitVec.ofNat 64 (6912218176 + 8 * ord)) =
      BitVec.ofNat 64 (posAt input.positions ord).val := by
    rw [hhigh.getMem_eq (by omega) (by omega) (by omega), check_initial_index input ord hord,
      posAt_val input.positions ord hord]
  have hx20_1 : s1.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha22]
    rw [MachineState.getReg_setReg_eq (by decide), hidx_mem]
  have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOff) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25), hcur.x25]
  -- pc[23]: ADDI x6, x25, 24
  have hst23 := step_ordinary oracle s1 23 (.ADDI .x6 .x25 24#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x6 .x25 24#12)
  have hpc2 : s2.pc = pcWord 24 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (11341403200 + pOff + 24) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx25_1, se12_24]
    change BitVec.ofNat 64 (11341403200 + pOff) + BitVec.ofNat 64 24 = _
    exact bv64_add _ 24
  have hx31_2 : s2.getReg .x31 = BitVec.ofNat 64 (11341403200 + (input.proof.length - tailBytes tOff)) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x31), hcur.x31]
  -- pc[24]: BLTU x31, x6, pc[330]
  have hst24 := step_ordinary oracle s2 24 (.BLTU .x31 .x6 1224#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BLTU .x31 .x6 1224#13)
  have hult : BitVec.ult (s2.getReg .x31) (s2.getReg .x6) = decide (input.proof.length < pOff + 24 + tailBytes tOff) := by
    rw [hx31_2, hx6_2, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pOff + 24 + tailBytes tOff
  · have hpc3 : s3.pc = pcWord 330 := by
      simp only [s3, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc2]; decide
    exact .rejected 6 0 [] hshort (by decide) (by decide)
      (by simpa using ((hst22.trans hst23).trans hst24).halt (halt_reject oracle s3 hpc3))
  · have hge24 : pOff + 24 + tailBytes tOff ≤ input.proof.length := by omega
    have hpc3 : s3.pc = pcWord 25 := by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      have h32 : s3.mem = s2.mem := by
        simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      rw [h32]
      simp only [s2, s1, execInstrBr, mem_setPC, mem_setReg]
    have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x20 → s3.getReg r = s.getReg r := by
      intro r hr6 hr20
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
    -- pc[25..27]: Call 0 — U = compress(val[0..96)) -> S[0..32)
    have hst25 := step_ordinary oracle s3 25 (.ADDI .x10 .x8 0#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x10 .x8 0#12)
    have hpc4 : s4.pc = pcWord 26 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hst26 := step_ordinary oracle s4 26 (.ADDI .x12 .x21 0#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ADDI .x12 .x21 0#12)
    have hpc5 : s5.pc = pcWord 27 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hmem5 : s5.mem = s.mem := by
      simpa [s5, s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
    have hreg5 : ∀ r, r ≠ .x10 → r ≠ .x12 → s5.getReg r = s3.getReg r := fun r h10 h12 => by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
    have hx10_5 : s5.getReg .x10 = BitVec.ofNat 64 (7046435904 + 256 * ord) := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hreg3 .x8 (by decide) (by decide), hx8, se12_0, BitVec.add_zero]
    have hx12_5 : s5.getReg .x12 = BitVec.ofNat 64 256 := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
        hreg3 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero]
    have hinpU : readBuffer s5 (7046435904 + 256 * ord) 96 = leafUInput pw.value := by
      have h50 : HighMemPreserved s0 s5 := hhigh.trans (MemEqOutside.of_mem_eq hmem5 0 4294971392)
      rw [h50.readBuffer_eq (by omega) (by omega)]
      have hval := check_initial_value_slice input ord 0 96 hord (by decide)
      simpa only [Nat.add_zero, Nat.mul_zero, leafUInput, pw, parsePartialWitness, valAt, dif_pos hord] using hval
    have hec0 := step_ecall_compress h768 oracle s5 27 (7046435904 + 256 * ord) 256 (by decide) hpc5 rfl
      ((hreg5 .x5 (by decide) (by decide)).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))
      ((hreg5 .x11 (by decide) (by decide)).trans ((hreg3 .x11 (by decide) (by decide)).trans hfix.x11))
      ((hreg5 .x13 (by decide) (by decide)).trans ((hreg3 .x13 (by decide) (by decide)).trans hfix.x13))
      hx10_5 hx12_5 (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide)
    rw [hinpU] at hec0
    let u := c96 (leafUInput pw.value)
    let s6 := writeBits s5 (BitVec.ofNat 64 256) u
    have hpc6 : s6.pc = pcWord 28 := by simp only [s6, writeBits, MachineState.setPC, hpc5, pcWord_add_four]
    have hu6 : readBuffer s6 256 32 = u := writeBits_readBuffer_digest s5 256 u
    have hout_s6 : MemEqOutside s s6 256 288 :=
      (MemEqOutside.of_mem_eq hmem5 256 288).trans (MemEqOutside_writeBits_digest s5 256 u (by decide))
    have hreg6 : ∀ r, s6.getReg r = s5.getReg r := fun r => writeBits_register s5 _ u r
    -- pc[28..43]: copy 8 dwords (64B) val[96..160) -> S[32..96)
    have hcA : ∀ j < 8,
        checkInstr (28 + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (96 + 8 * j))) ∧
        checkInstr (28 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s7, hs7, hpc7, hreg7, hcopy7, hout7⟩ :=
      step_copy_dwords oracle 28 8 .x8 .x21 96 32 s6 (7046435904 + 256 * ord) 256
        (by decide) (by decide) (by decide) (by decide) (by decide) hcA hpc6
        ((hreg6 .x8).trans ((hreg5 .x8 (by decide) (by decide)).trans ((hreg3 .x8 (by decide) (by decide)).trans hx8)))
        ((hreg6 .x21).trans ((hreg5 .x21 (by decide) (by decide)).trans ((hreg3 .x21 (by decide) (by decide)).trans hfix.x21)))
        (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
    have hinpA : readBuffer s7 256 96 = leafAInput u pw.value := by
      rw [readBuffer_leafA]
      have hlo : readBuffer s7 256 32 = u := (hout7.readBuffer_eq (by decide) (by omega)).trans hu6
      have hhi64 : readBuffer s7 288 64 = pw.value.extractLsb' 768 512 := by
        have hval : readBuffer s0 (7046435904 + 256 * ord + 96) 64 = pw.value.extractLsb' 768 512 := by
          simpa only [pw, parsePartialWitness, valAt, dif_pos hord] using
            check_initial_value_slice input ord 96 64 hord (by decide)
        rw [← hval]
        apply readBuffer_congr2; intro j hj
        rw [show 288 + j = 256 + 32 + j by omega, hcopy7 j hj]
        exact (hhigh.trans (hout_s6.mono (by omega) (by omega))) (7046435904 + 256 * ord + 96 + j) (by omega) (by omega)
      rw [hlo, hhi64]; rfl
    -- pc[44..48]: a0=256, a2=352 + 32*(i%2)
    have hcodeA : ∀ j (hj : j < leafAOutInstrs.length), checkInstr (44 + j) = .base (leafAOutInstrs[j]'hj) := by
      intro j hj; have hj' : j < 5 := hj; interval_cases j <;> rfl
    have hpureA : ∀ j (hj : j < leafAOutInstrs.length),
        Instruction.base (leafAOutInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (leafAOutInstrs[j]'hj)) = some (execInstrBr st (leafAOutInstrs[j]'hj)) ∧
              (execInstrBr st (leafAOutInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (leafAOutInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 5 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs8, hpc8, hmem8⟩ := step_pure_list oracle 44 leafAOutInstrs s7 (by decide) hcodeA hpureA hpc7
    let s8 := runInstrs s7 leafAOutInstrs
    have hs8 : StepsTo oracle s7 s8 5 0 [] := hs8
    have hpc8 : s8.pc = pcWord 49 := hpc8
    let dstA : Nat := 352 + 32 * ((posAt input.positions ord).val % 2)
    let dstB : Nat := 384 + 32 * ((posAt input.positions ord).val % 2)
    have hx20_7 : s7.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
      rw [hreg7 .x20 (by decide), hreg6 .x20, hreg5 .x20 (by decide) (by decide), hx20_3]
    have hx21_7 : s7.getReg .x21 = 256#64 := by
      rw [hreg7 .x21 (by decide), hreg6 .x21, hreg5 .x21 (by decide) (by decide), hreg3 .x21 (by decide) (by decide), hfix.x21]
    have hx10_8 : s8.getReg .x10 = BitVec.ofNat 64 256 := by
      simp only [s8, runInstrs, leafAOutInstrs, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hx21_7, se12_0, BitVec.add_zero]
    have hx12_8 : s8.getReg .x12 = BitVec.ofNat 64 dstA := by
      have harith : (256#64 + ((BitVec.ofNat 64 (posAt input.positions ord).val &&& signExtend12 1#12) <<< 5)) +
          signExtend12 96#12 = BitVec.ofNat 64 dstA := by
        rw [se12_1, bv64_and_one _ (by omega), bv64_shl _ 5 (by omega), se12_96]
        change BitVec.ofNat 64 256 + BitVec.ofNat 64 _ + BitVec.ofNat 64 96 = _
        rw [bv64_add, bv64_add]
        congr 1; dsimp only [dstA]; omega
      simpa only [s8, runInstrs, leafAOutInstrs, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hx20_7, hx21_7,
        show (5#6 : BitVec 6).toNat = 5 by decide] using harith
    have hreg8 : ∀ r, r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → s8.getReg r = s7.getReg r := fun r h7 h10 h12 => by
      simp only [s8, runInstrs, leafAOutInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
    -- pc[49]: Call 1 — A = compress(leafAInput u val) -> R[dstA..dstA+32)
    have hec1 := step_ecall_compress h768 oracle s8 49 256 dstA (by decide) hpc8 rfl
      ((hreg8 .x5 (by decide) (by decide) (by decide)).trans ((hreg7 .x5 (by decide)).trans
        ((hreg6 .x5).trans ((hreg5 .x5 (by decide) (by decide)).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5)))))
      ((hreg8 .x11 (by decide) (by decide) (by decide)).trans ((hreg7 .x11 (by decide)).trans
        ((hreg6 .x11).trans ((hreg5 .x11 (by decide) (by decide)).trans ((hreg3 .x11 (by decide) (by decide)).trans hfix.x11)))))
      ((hreg8 .x13 (by decide) (by decide) (by decide)).trans ((hreg7 .x13 (by decide)).trans
        ((hreg6 .x13).trans ((hreg5 .x13 (by decide) (by decide)).trans ((hreg3 .x13 (by decide) (by decide)).trans hfix.x13)))))
      hx10_8 hx12_8 (by decide) (by dsimp only [dstA]; omega)
      (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; dsimp only [dstA]; omega)
    rw [(MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by decide) (by omega), hinpA] at hec1
    let a := c96 (leafAInput u pw.value)
    let s9 := writeBits s8 (BitVec.ofNat 64 dstA) a
    have hpc9 : s9.pc = pcWord 50 := by simp only [s9, writeBits, MachineState.setPC, hpc8, pcWord_add_four]
    have ha9 : readBuffer s9 dstA 32 = a := writeBits_readBuffer_digest s8 dstA a
    have hreg9 : ∀ r, s9.getReg r = s8.getReg r := fun r => writeBits_register s8 _ a r
    -- pc[50..52]: Call 2 — B = compress(val[160..256)) -> R[dstB..dstB+32)
    have hst50 := step_ordinary oracle s9 50 (.ADDI .x10 .x8 160#12) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.ADDI .x10 .x8 160#12)
    have hpc10 : s10.pc = pcWord 51 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
    have hst51 := step_ordinary oracle s10 51 (.ADDI .x12 .x12 32#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
    let s11 := execInstrBr s10 (.ADDI .x12 .x12 32#12)
    have hpc11 : s11.pc = pcWord 52 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
    have hmem11 : s11.mem = s9.mem := by simp [s11, s10, execInstrBr, mem_setPC, mem_setReg]
    have hreg11 : ∀ r, r ≠ .x10 → r ≠ .x12 → s11.getReg r = s8.getReg r := fun r h10 h12 => by
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm, hreg9 r]
    have hx10_11 : s11.getReg .x10 = BitVec.ofNat 64 (7046435904 + 256 * ord + 160) := by
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hreg9 .x8, hreg8 .x8 (by decide) (by decide) (by decide),
        hreg7 .x8 (by decide), hreg6 .x8, hreg5 .x8 (by decide) (by decide), hreg3 .x8 (by decide) (by decide),
        hx8, se12_160]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 160 = _
      exact bv64_add _ 160
    have hx12_11 : s11.getReg .x12 = BitVec.ofNat 64 dstB := by
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x12), hreg9 .x12, hx12_8, se12_32]
      change BitVec.ofNat 64 dstA + BitVec.ofNat 64 32 = _
      rw [bv64_add]; congr 1; dsimp only [dstA, dstB]; omega
    have hout_s11 : MemEqOutside s s11 256 448 :=
      (hout_s6.mono (by omega) (by omega)).trans
        ((hout7.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem8 256 448).trans
            (((MemEqOutside_writeBits_digest s8 dstA a (by dsimp only [dstA]; omega)).mono
              (by dsimp only [dstA]; omega) (by dsimp only [dstA]; omega)).trans
              (MemEqOutside.of_mem_eq hmem11 256 448))))
    have hinpB : readBuffer s11 (7046435904 + 256 * ord + 160) 96 = leafBInput pw.value := by
      rw [(hhigh.trans (hout_s11.mono (by omega) (by omega))).readBuffer_eq (by omega) (by omega)]
      simpa only [leafBInput, pw, parsePartialWitness, valAt, dif_pos hord] using
        check_initial_value_slice input ord 160 96 hord (by decide)
    have hec2 := step_ecall_compress h768 oracle s11 52 (7046435904 + 256 * ord + 160) dstB (by decide) hpc11 rfl
      ((hreg11 .x5 (by decide) (by decide)).trans ((hreg8 .x5 (by decide) (by decide) (by decide)).trans
        ((hreg7 .x5 (by decide)).trans ((hreg6 .x5).trans ((hreg5 .x5 (by decide) (by decide)).trans
          ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))))))
      ((hreg11 .x11 (by decide) (by decide)).trans ((hreg8 .x11 (by decide) (by decide) (by decide)).trans
        ((hreg7 .x11 (by decide)).trans ((hreg6 .x11).trans ((hreg5 .x11 (by decide) (by decide)).trans
          ((hreg3 .x11 (by decide) (by decide)).trans hfix.x11))))))
      ((hreg11 .x13 (by decide) (by decide)).trans ((hreg8 .x13 (by decide) (by decide) (by decide)).trans
        ((hreg7 .x13 (by decide)).trans ((hreg6 .x13).trans ((hreg5 .x13 (by decide) (by decide)).trans
          ((hreg3 .x13 (by decide) (by decide)).trans hfix.x13))))))
      hx10_11 hx12_11 (by omega) (by dsimp only [dstB]; omega)
      (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; dsimp only [dstB]; omega)
    rw [hinpB] at hec2
    let b := c96 (leafBInput pw.value)
    let s12 := writeBits s11 (BitVec.ofNat 64 dstB) b
    have hpc12 : s12.pc = pcWord 53 := by simp only [s12, writeBits, MachineState.setPC, hpc11, pcWord_add_four]
    have ha12 : readBuffer s12 dstA 32 = a := by
      rw [(MemEqOutside_writeBits_digest s11 dstB b (by dsimp only [dstB]; omega)).readBuffer_eq
            (by dsimp only [dstA]; omega) (by dsimp only [dstA, dstB]; omega),
          (MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by dsimp only [dstA]; omega) (by omega), ha9]
    have hb12 : readBuffer s12 dstB 32 = b := writeBits_readBuffer_digest s11 dstB b
    have hout_s12 : MemEqOutside s s12 256 448 :=
      hout_s11.trans ((MemEqOutside_writeBits_digest s11 dstB b (by dsimp only [dstB]; omega)).mono
        (by dsimp only [dstB]; omega) (by dsimp only [dstB]; omega))
    have hreg12_base : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → s12.getReg r = s.getReg r :=
      fun r h6 h7 h10 h12 h20 => by
        rw [writeBits_register s11 _ b r, hreg11 r h10 h12, hreg8 r h7 h10 h12, hreg7 r h6, hreg6 r,
          hreg5 r h10 h12, hreg3 r h6 h20]
    have hx20_12 : s12.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
      rw [writeBits_register s11 _ b .x20, hreg11 .x20 (by decide) (by decide),
        hreg8 .x20 (by decide) (by decide) (by decide), hx20_7]
    -- pc[53..54]: branch on i % 2
    have hst53 := step_ordinary oracle s12 53 (.ANDI .x7 .x20 1#12) (by decide) hpc12 rfl (by intro h; cases h) rfl
    let s13 := execInstrBr s12 (.ANDI .x7 .x20 1#12)
    have hpc13 : s13.pc = pcWord 54 := by simp only [s13, execInstrBr, MachineState.setPC, hpc12, pcWord_add_four]
    have hx7_13 : s13.getReg .x7 = BitVec.ofNat 64 ((posAt input.positions ord).val % 2) := by
      simp only [s13, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hx20_12, se12_1]
      exact bv64_and_one _ (by omega)
    have hst54 := step_ordinary oracle s13 54 (.BNE .x7 .x0 24#13) (by decide) hpc13 rfl (by intro h; cases h) rfl
    let s14 := execInstrBr s13 (.BNE .x7 .x0 24#13)
    have hmem13 : s13.mem = s12.mem := by simp [s13, execInstrBr, mem_setPC, mem_setReg]
    have hpre_steps : StepsTo oracle s s14 33 3
        [((leafUInput pw.value).cast h768.symm, u),
         ((leafAInput u pw.value).cast h768.symm, a),
         ((leafBInput pw.value).cast h768.symm, b)] := by
      have h0 := (((hst22.trans hst23).trans hst24).trans ((hst25.trans hst26).trans hec0))
      have h1 := ((hs7.trans hs8).trans hec1)
      have h2 := (((hst50.trans hst51).trans hec2).trans (hst53.trans hst54))
      exact ((h0.trans h1).trans h2).eq_of rfl (by decide) (by decide)
        (by simp only [List.nil_append, List.append_nil, List.cons_append]; rfl)
    -- Common finish from pc[64..66] once R[0..96) = leafFinalInput pw.index a b pw.salt and x25 advanced by 24
    have hfinish : ∀ (s18 : MachineState) (kMid : Nat),
        kMid ≤ 154 →
        StepsTo oracle s14 s18 kMid 0 [] →
        s18.pc = pcWord 64 →
        CheckFixedRegs s18 →
        ProofCursor s0 input.proof.length (pOff + 24) tOff s18 →
        MemEqOutside s14 s18 352 448 →
        s18.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val →
        s18.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
        s18.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
        s18.getReg .x27 = BitVec.ofNat 64 rem →
        readBuffer s18 352 96 = leafFinalInput pw.index a b pw.salt →
        PhaseOutcome oracle s 190 4 (input.proof.length < pOff + 24 + tailBytes tOff)
          (fun s' q tr =>
            q = 4 ∧ s'.pc = pcWord 67 ∧ CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length (pOff + 24) tOff s' ∧
            MemEqOutside s s' 256 448 ∧
            s'.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val ∧
            s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            readBuffer s' 256 32 = leafDigest c96 pw.index pw.salt pw.value ∧
            ∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) := by
      intro s18 kMid hkMid hmid hpc18 hfix18 hcur18 hout18 hx20_18 hx24_18 hx8_18 hx27_18 hinpF
      have hst64 := step_ordinary oracle s18 64 (.ADDI .x10 .x21 96#12) (by decide) hpc18 rfl (by intro h; cases h) rfl
      let s19 := execInstrBr s18 (.ADDI .x10 .x21 96#12)
      have hpc19 : s19.pc = pcWord 65 := by simp only [s19, execInstrBr, MachineState.setPC, hpc18, pcWord_add_four]
      have hst65 := step_ordinary oracle s19 65 (.ADDI .x12 .x21 0#12) (by decide) hpc19 rfl (by intro h; cases h) rfl
      let s20 := execInstrBr s19 (.ADDI .x12 .x21 0#12)
      have hpc20 : s20.pc = pcWord 66 := by simp only [s20, execInstrBr, MachineState.setPC, hpc19, pcWord_add_four]
      have hmem20 : s20.mem = s18.mem := by simp [s20, s19, execInstrBr, mem_setPC, mem_setReg]
      have hreg20 : ∀ r, r ≠ .x10 → r ≠ .x12 → s20.getReg r = s18.getReg r := fun r h10 h12 => by
        simp only [s20, s19, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_20 : s20.getReg .x10 = BitVec.ofNat 64 352 := by
        simp only [s20, s19, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix18.x21, se12_96]; decide
      have hx12_20 : s20.getReg .x12 = BitVec.ofNat 64 256 := by
        simp only [s20, s19, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21), hfix18.x21, se12_0, BitVec.add_zero]
      have hec3 := step_ecall_compress h768 oracle s20 66 352 256 (by decide) hpc20 rfl
        ((hreg20 .x5 (by decide) (by decide)).trans hfix18.x5)
        ((hreg20 .x11 (by decide) (by decide)).trans hfix18.x11)
        ((hreg20 .x13 (by decide) (by decide)).trans hfix18.x13)
        hx10_20 hx12_20 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem20 0 0).readBuffer_eq (by decide) (by omega), hinpF] at hec3
      let dF := c96 (leafFinalInput pw.index a b pw.salt)
      let sFin := writeBits s20 (BitVec.ofNat 64 256) dF
      have hpcFin : sFin.pc = pcWord 67 := by simp only [sFin, writeBits, MachineState.setPC, hpc20, pcWord_add_four]
      have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → sFin.getReg r = s18.getReg r := fun r h10 h12 =>
        (writeBits_register s20 _ dF r).trans (hreg20 r h10 h12)
      have hmem14_12 : s14.mem = s12.mem := by
        simp only [s14, execInstrBr]; split <;> simpa [MachineState.setPC] using hmem13
      have houtFin : MemEqOutside s sFin 256 448 :=
        hout_s12.trans ((MemEqOutside.of_mem_eq hmem14_12 256 448).trans
          ((hout18.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem20 256 448).trans
              ((MemEqOutside_writeBits_digest s20 256 dF (by decide)).mono (by omega) (by omega)))))
      have htot := (hpre_steps.trans hmid).trans ((hst64.trans hst65).trans hec3)
      refine .continued sFin (33 + kMid + 3) 4
        [((leafUInput pw.value).cast h768.symm, u),
         ((leafAInput u pw.value).cast h768.symm, a),
         ((leafBInput pw.value).cast h768.symm, b),
         ((leafFinalInput pw.index a b pw.salt).cast h768.symm, dF)]
        (by omega) (by decide)
        (htot.eq_of rfl (by omega) (by decide) (by simp only [List.nil_append, List.append_nil, List.cons_append]; rfl))
        ⟨rfl, hpcFin,
         hfix18.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         hcur18.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         houtFin,
         (hregFin .x20 (by decide) (by decide)).trans hx20_18,
         (hregFin .x24 (by decide) (by decide)).trans hx24_18,
         (hregFin .x8  (by decide) (by decide)).trans hx8_18,
         (hregFin .x27 (by decide) (by decide)).trans hx27_18,
         writeBits_readBuffer_digest s20 256 dF, ?_⟩
      intro x hx
      unfold WitnessPath.leafInputs at hx
      dsimp only at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp only [InTrace, u, c96]
        exact List.mem_cons_self
      · simp only [InTrace, a, u, c96]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp only [InTrace, b, c96]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · simp only [InTrace, dF, a, u, b, c96]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    -- Split on i % 2 = 0 (even: pc[55..59]) vs i % 2 = 1 (odd: pc[60..63])
    by_cases heven : (posAt input.positions ord).val % 2 = 0
    · -- Even branch: pc[55..59] -> pc[64]
      have hx7z : s13.getReg .x7 = 0#64 := by rw [hx7_13, heven]
      have hpc14 : s14.pc = pcWord 55 := by
        simp only [s14, execInstrBr, hx7z, getReg_x0, bne_self_eq_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc13, pcWord_add_four]
      have hmem14 : s14.mem = s12.mem := by
        simpa [s14, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem13
      have hreg14 : ∀ r, r ≠ .x7 → s14.getReg r = s12.getReg r := fun r h7 => by
        simp only [s14, execInstrBr, hx7z, getReg_x0, bne_self_eq_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
      have hx21_14 : s14.getReg .x21 = 256#64 := by
        rw [hreg14 .x21 (by decide), hreg12_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide), hfix.x21]
      have ha55 : s14.getReg .x21 + signExtend12 160#12 = BitVec.ofNat 64 416 := by
        rw [hx21_14, se12_160]; decide
      have hv55 : memoryArgumentsValid s14 (.SD .x21 .x0 160#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha55]
        exact accessValid_ofNat 416 8 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst55 := step_ordinary oracle s14 55 (.SD .x21 .x0 160#12) (by decide) hpc14 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv55])
      let s15 := execInstrBr s14 (.SD .x21 .x0 160#12)
      have hpc15 : s15.pc = pcWord 56 := by simp only [s15, execInstrBr, MachineState.setPC, hpc14, pcWord_add_four]
      have hreg15 : ∀ r, s15.getReg r = s14.getReg r := fun r => by
        simp [s15, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      have hout15 : MemEqOutside s14 s15 416 424 := by
        intro a ha hout
        simp only [s15, execInstrBr, ha55, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact setMem_getByte_ofNat s14 416 a 0#64 (by decide) (by decide) ha hout
      have hgap15 : readBuffer s15 416 8 = 0 := by
        rw [readBuffer_word s15 416 (by decide)]
        simp only [s15, execInstrBr, ha55, MachineState.getMem_setPC, MachineState.getMem_setMem_eq, getReg_x0]; rfl
      have hst56 := step_ordinary oracle s15 56 (.ADDI .x12 .x21 168#12) (by decide) hpc15 rfl (by intro h; cases h) rfl
      let s16 := execInstrBr s15 (.ADDI .x12 .x21 168#12)
      have hpc16 : s16.pc = pcWord 57 := by simp only [s16, execInstrBr, MachineState.setPC, hpc15, pcWord_add_four]
      have hmem16 : s16.mem = s15.mem := by simp [s16, execInstrBr, mem_setPC, mem_setReg]
      have hsrc16 : s16.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOff) := by
        simp only [s16, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg15,
          hreg14 .x25 (by decide), hreg12_base .x25 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x25]
      have hdst16 : s16.getReg .x12 = BitVec.ofNat 64 424 := by
        simp only [s16, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg15, hx21_14, se12_168]; decide
      obtain ⟨s17, hs17, hpc17, hx25_17, hreg17, hcopy17, hout17⟩ :=
        step_call_read_n oracle 57 24 s16 (11341403200 + pOff) 424 (by decide) (by decide) (by decide)
          rfl rfl hpc16 hsrc16 hdst16 (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hst59 := step_ordinary oracle s17 59 (.JAL .x0 20#21) (by decide) hpc17 rfl (by intro h; cases h) rfl
      let s18 := execInstrBr s17 (.JAL .x0 20#21)
      have hpc18 : s18.pc = pcWord 64 := by simp only [s18, execInstrBr, MachineState.setPC, hpc17]; decide
      have hmem18 : s18.mem = s17.mem := by simp [s18, execInstrBr, mem_setPC, mem_setReg]
      have hout18 : MemEqOutside s14 s18 416 448 :=
        (hout15.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem16 416 448).trans
            ((hout17.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem18 416 448)))
      have hreg18 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s18.getReg r = s14.getReg r :=
        fun r h1 h6 h10 h12 h25 => by
          have h18_17 : s18.getReg r = s17.getReg r := by simp [s18, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [h18_17, hreg17 r h1 h6 h10 h12 h25]
          simp only [s16, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg15 r]
      have hgap18 : readBuffer s18 416 8 = 0 := by
        rw [(MemEqOutside.of_mem_eq hmem18 0 0).readBuffer_eq (by decide) (by omega),
          hout17.readBuffer_eq (by decide) (by omega),
          (MemEqOutside.of_mem_eq hmem16 0 0).readBuffer_eq (by decide) (by omega), hgap15]
      have hinpF : readBuffer s18 352 96 = leafFinalInput pw.index a b pw.salt := by
        rw [readBuffer_lateEven s18 352 hgap18]
        have hdstA : dstA = 352 := by dsimp only [dstA]; omega
        have hdstB : dstB = 384 := by dsimp only [dstB]; omega
        have ha18 : readBuffer s18 352 32 = a := by
          rw [hout18.readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem14 0 0).readBuffer_eq (by decide) (by omega), ← hdstA, ha12]
        have hb18 : readBuffer s18 384 32 = b := by
          rw [hout18.readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem14 0 0).readBuffer_eq (by decide) (by omega), ← hdstB, hb12]
        have hsalt18 : readBuffer s18 424 24 = pw.salt := by
          unfold pw parsePartialWitness
          rw [(MemEqOutside.of_mem_eq hmem18 0 0).readBuffer_eq (by decide) (by omega)]
          apply readBuffer_congr2; intro j hj
          rw [hcopy17 j hj]
          have h16_0 : HighMemPreserved s0 s16 :=
            hhigh.trans ((hout_s12.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem14 0 4294971392).trans
                ((hout15.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem16 0 4294971392))))
          exact h16_0 (11341403200 + pOff + j) (by omega) (by omega)
        rw [ha18, hb18, hsalt18]
        simp only [leafFinalInput, show pw.index.val % 2 = 0 from heven, ite_true]
      have hcur18 : ProofCursor s0 input.proof.length (pOff + 24) tOff s18 := by
        refine ⟨hge24, ?_, ?_, ?_, ?_⟩
        · have : s18.getReg .x25 = s17.getReg .x25 := by simp [s18, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [this, hx25_17]; congr 1
        · rw [hreg18 .x31 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg14 .x31 (by decide), hreg12_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg18 .x3 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg14 .x3 (by decide), hreg12_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg18 .x4 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg14 .x4 (by decide), hreg12_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      refine hfinish s18 150 (by decide)
        (by simpa using ((hst55.trans hst56).trans hs17).trans hst59) hpc18
        (hfix.of_agree (fun r hr => (hreg18 r (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
          ((hreg14 r (isFixedReg_ne_of_false hr rfl)).trans
            (hreg12_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))))
        hcur18 (hout18.mono (by omega) (by omega))
        ((hreg18 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x20 (by decide)).trans hx20_12))
        ((hreg18 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x24 (by decide)).trans
          ((hreg12_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)))
        ((hreg18 .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x8  (by decide)).trans
          ((hreg12_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)))
        ((hreg18 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x27 (by decide)).trans
          ((hreg12_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)))
        hinpF
    · -- Odd branch: pc[60..63] -> pc[64]
      have hodd : (posAt input.positions ord).val % 2 = 1 := by omega
      have hx7o : s13.getReg .x7 = 1#64 := by rw [hx7_13, hodd]
      have hpc14 : s14.pc = pcWord 60 := by
        simp only [s14, execInstrBr, hx7o, getReg_x0, show (1#64 != 0#64) = true by decide, ite_true,
          MachineState.setPC, hpc13]; decide
      have hmem14 : s14.mem = s12.mem := by
        simpa [s14, execInstrBr, hx7o, getReg_x0, show (1#64 != 0#64) = true by decide,
          MachineState.setPC] using hmem13
      have hreg14 : ∀ r, r ≠ .x7 → s14.getReg r = s12.getReg r := fun r h7 => by
        simp only [s14, execInstrBr, hx7o, getReg_x0, show (1#64 != 0#64) = true by decide, ite_true,
          MachineState.getReg_setPC]
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
      have hx21_14 : s14.getReg .x21 = 256#64 := by
        rw [hreg14 .x21 (by decide), hreg12_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide), hfix.x21]
      have ha60 : s14.getReg .x21 + signExtend12 120#12 = BitVec.ofNat 64 376 := by
        rw [hx21_14, se12_120]; decide
      have hv60 : memoryArgumentsValid s14 (.SD .x21 .x0 120#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha60]
        exact accessValid_ofNat 376 8 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst60 := step_ordinary oracle s14 60 (.SD .x21 .x0 120#12) (by decide) hpc14 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv60])
      let s15 := execInstrBr s14 (.SD .x21 .x0 120#12)
      have hpc15 : s15.pc = pcWord 61 := by simp only [s15, execInstrBr, MachineState.setPC, hpc14, pcWord_add_four]
      have hreg15 : ∀ r, s15.getReg r = s14.getReg r := fun r => by
        simp [s15, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      have hout15 : MemEqOutside s14 s15 376 384 := by
        intro a ha hout
        simp only [s15, execInstrBr, ha60, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact setMem_getByte_ofNat s14 376 a 0#64 (by decide) (by decide) ha hout
      have hgap15 : readBuffer s15 376 8 = 0 := by
        rw [readBuffer_word s15 376 (by decide)]
        simp only [s15, execInstrBr, ha60, MachineState.getMem_setPC, MachineState.getMem_setMem_eq, getReg_x0]; rfl
      have hst61 := step_ordinary oracle s15 61 (.ADDI .x12 .x21 96#12) (by decide) hpc15 rfl (by intro h; cases h) rfl
      let s16 := execInstrBr s15 (.ADDI .x12 .x21 96#12)
      have hpc16 : s16.pc = pcWord 62 := by simp only [s16, execInstrBr, MachineState.setPC, hpc15, pcWord_add_four]
      have hmem16 : s16.mem = s15.mem := by simp [s16, execInstrBr, mem_setPC, mem_setReg]
      have hsrc16 : s16.getReg .x25 = BitVec.ofNat 64 (11341403200 + pOff) := by
        simp only [s16, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg15,
          hreg14 .x25 (by decide), hreg12_base .x25 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x25]
      have hdst16 : s16.getReg .x12 = BitVec.ofNat 64 352 := by
        simp only [s16, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg15, hx21_14, se12_96]; decide
      obtain ⟨s17, hs17, hpc17, hx25_17, hreg17, hcopy17, hout17⟩ :=
        step_call_read_n oracle 62 24 s16 (11341403200 + pOff) 352 (by decide) (by decide) (by decide)
          rfl rfl hpc16 hsrc16 hdst16 (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hout17_all : MemEqOutside s14 s17 352 384 :=
        (hout15.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem16 352 384).trans (hout17.mono (by omega) (by omega)))
      have hreg17_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s17.getReg r = s14.getReg r :=
        fun r h1 h6 h10 h12 h25 => by
          rw [hreg17 r h1 h6 h10 h12 h25]
          simp only [s16, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg15 r]
      have hgap17 : readBuffer s17 376 8 = 0 := by
        rw [hout17.readBuffer_eq (by decide) (by omega),
          (MemEqOutside.of_mem_eq hmem16 0 0).readBuffer_eq (by decide) (by omega), hgap15]
      have hinpF : readBuffer s17 352 96 = leafFinalInput pw.index a b pw.salt := by
        rw [readBuffer_lateOdd s17 352 hgap17]
        have hdstA : dstA = 384 := by dsimp only [dstA]; omega
        have hdstB : dstB = 416 := by dsimp only [dstB]; omega
        have hsalt17 : readBuffer s17 352 24 = pw.salt := by
          unfold pw parsePartialWitness
          apply readBuffer_congr2; intro j hj
          rw [hcopy17 j hj]
          have h16_0 : HighMemPreserved s0 s16 :=
            hhigh.trans ((hout_s12.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem14 0 4294971392).trans
                ((hout15.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem16 0 4294971392))))
          exact h16_0 (11341403200 + pOff + j) (by omega) (by omega)
        have ha17 : readBuffer s17 384 32 = a := by
          rw [hout17_all.readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem14 0 0).readBuffer_eq (by decide) (by omega), ← hdstA, ha12]
        have hb17 : readBuffer s17 416 32 = b := by
          rw [hout17_all.readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem14 0 0).readBuffer_eq (by decide) (by omega), ← hdstB, hb12]
        rw [hsalt17, ha17, hb17]
        simp only [leafFinalInput, show pw.index.val % 2 ≠ 0 from heven, ite_false]
      have hcur17 : ProofCursor s0 input.proof.length (pOff + 24) tOff s17 := by
        refine ⟨hge24, ?_, ?_, ?_, ?_⟩
        · rw [hx25_17]; congr 1
        · rw [hreg17_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg14 .x31 (by decide), hreg12_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg17_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg14 .x3 (by decide), hreg12_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg17_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg14 .x4 (by decide), hreg12_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      refine hfinish s17 149 (by decide)
        (by simpa using (hst60.trans hst61).trans hs17) hpc17
        (hfix.of_agree (fun r hr => (hreg17_base r (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
          ((hreg14 r (isFixedReg_ne_of_false hr rfl)).trans
            (hreg12_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))))
        hcur17 (hout17_all.mono (by omega) (by omega))
        ((hreg17_base .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x20 (by decide)).trans hx20_12))
        ((hreg17_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x24 (by decide)).trans
          ((hreg12_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)))
        ((hreg17_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x8  (by decide)).trans
          ((hreg12_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)))
        ((hreg17_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg14 .x27 (by decide)).trans
          ((hreg12_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)))
        hinpF

private def l0SetupInstrs : List Instr :=
  [.ADDI .x7 .x0 3#12, .DIVU .x22 .x20 .x7, .REMU .x23 .x20 .x7,
   .ADDI .x6 .x0 1#12, .SLLI .x6 .x6 11#6, .ADDI .x6 .x6 682#12,
   .SLLI .x6 .x6 11#6, .ADDI .x6 .x6 1365#12]

/-- Phase 1B: L0 3-ary step (`pc[67..113]` -> `pc[114]`). -/
theorem step_pos_l0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 67)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 24) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hleaf : readBuffer s 256 32 =
      leafDigest (fun x => oracle.compression (x.cast h768.symm))
        (posAt input.positions ord)
        (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
          (posAt input.positions ord) (valAt input ord)).salt
        (valAt input ord)) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 420 1 (input.proof.length < pOff + 24 + l0Bytes i + tailBytes tOff)
      (fun s' q tr =>
        q ≤ 1 ∧
        s'.pc = pcWord 114 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i) tOff s' ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalL1 c96 ∧
        (i.val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96))) := by
  intro s0 c96 i pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hle_cur : pOff + 24 + tailBytes tOff ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hcode1 : ∀ j (hj : j < l0SetupInstrs.length), checkInstr (67 + j) = .base (l0SetupInstrs[j]'hj) := by
    intro j hj; have hj' : j < 8 := hj; interval_cases j <;> rfl
  have hpure1 : ∀ j (hj : j < l0SetupInstrs.length),
      Instruction.base (l0SetupInstrs[j]'hj) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (l0SetupInstrs[j]'hj)) = some (execInstrBr st (l0SetupInstrs[j]'hj)) ∧
            (execInstrBr st (l0SetupInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (l0SetupInstrs[j]'hj)).mem = st.mem := by
    intro j hj; have hj' : j < 8 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 67 l0SetupInstrs s (by decide) hcode1 hpure1 hpc
  let s1 := runInstrs s l0SetupInstrs
  have hs1 : StepsTo oracle s s1 8 0 [] := hs1
  have hpc1 : s1.pc = pcWord 75 := hpc1
  have hx22_1 : s1.getReg .x22 = BitVec.ofNat 64 (i.val / 3) := by
    have hdiv : rv64_divu (BitVec.ofNat 64 i.val) 3#64 = BitVec.ofNat 64 (i.val / 3) := by
      rw [rv64_divu_three, toNat_ofNat64 i.val (by omega)]
    have h3 : (0#64 + signExtend12 3#12 : Word) = 3#64 := by decide
    simpa only [s1, runInstrs, l0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, getReg_x0, hx20, h3] using hdiv
  have hx23_1 : s1.getReg .x23 = BitVec.ofNat 64 (i.val % 3) := by
    have hrem : rv64_remu (BitVec.ofNat 64 i.val) 3#64 = BitVec.ofNat 64 (i.val % 3) := by
      rw [rv64_remu_three, toNat_ofNat64 i.val (by omega)]
    have h3 : (0#64 + signExtend12 3#12 : Word) = 3#64 := by decide
    simpa only [s1, runInstrs, l0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, getReg_x0, hx20, h3] using hrem
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 FULL_TRIPLETS := by
    rw [full_triplets_eq]
    have hval : ((((0#64 + signExtend12 1#12) <<< 11 + signExtend12 682#12) <<< 11) + signExtend12 1365#12) =
        BitVec.ofNat 64 5592405 := by decide
    simpa only [s1, runInstrs, l0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, getReg_x0, show (11#6 : BitVec 6).toNat = 11 by decide] using hval
  have hreg1 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x23 → s1.getReg r = s.getReg r := by
    intro r h6 h7 h22 h23
    simp only [s1, runInstrs, l0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h23.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h22.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
  -- pc[75]: BEQ x22, x6, pc[114]
  have hst75 := step_ordinary oracle s1 75 (.BEQ .x22 .x6 156#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BEQ .x22 .x6 156#13)
  have heq_full : (s1.getReg .x22 == s1.getReg .x6) = decide (i.val / 3 = FULL_TRIPLETS) := by
    rw [hx22_1, hx6_1]
    exact bv64_beq_eq _ _ (by omega) (by rw [full_triplets_eq]; decide)
  by_cases hfull : i.val / 3 = FULL_TRIPLETS
  · have hl0 : l0Bytes i = 0 := by unfold l0Bytes; exact if_pos hfull
    have hpc2 : s2.pc = pcWord 114 := by
      simp only [s2, execInstrBr, heq_full, hfull, decide_true, ite_true, MachineState.setPC, hpc1]; decide
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x23 → s2.getReg r = s.getReg r := by
      intro r h6 h7 h22 h23
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hreg1 r h6 h7 h22 h23
    have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (i.val / 3) := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hx22_1
    refine .continued s2 9 0 [] (by decide) (by decide) (by simpa using hs1.trans hst75)
      ⟨by decide, hpc2,
       hfix.of_agree (fun r hr => hreg2 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
         (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       by rw [hl0, Nat.add_zero]
          exact hcur.of_agree (fun r hr => hreg2 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
       MemEqOutside.of_mem_eq hmem2 256 352,
       hx22_2,
       (hreg2 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24,
       (hreg2 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8,
       (hreg2 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27,
       ?_, fun hne => (hne hfull).elim⟩
    rw [(MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega), hleaf]
    simp only [WitnessPath.evalL1, pw, parsePartialWitness, hfull, ite_true]; rfl
  · -- Full triplet: l0Bytes i = 64
    have hl0 : l0Bytes i = 64 := by unfold l0Bytes; exact if_neg hfull
    have hpc2 : s2.pc = pcWord 76 := by
      simp only [s2, execInstrBr, heq_full, hfull, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x23 → s2.getReg r = s.getReg r := fun r h6 h7 h22 h23 => by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hreg1 r h6 h7 h22 h23
    have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (i.val / 3) := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hx22_1
    have hx23_2 : s2.getReg .x23 = BitVec.ofNat 64 (i.val % 3) := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hx23_1
    -- pc[76]: ADDI x6, x25, 64; pc[77]: BLTU x31, x6, pc[330]
    have hst76 := step_ordinary oracle s2 76 (.ADDI .x6 .x25 64#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x6 .x25 64#12)
    have hpc3 : s3.pc = pcWord 77 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (11341403200 + (pOff + 24) + 64) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        hreg2 .x25 (by decide) (by decide) (by decide) (by decide), hcur.x25, se12_64]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 64 = _
      exact bv64_add _ 64
    have hx31_3 : s3.getReg .x31 = BitVec.ofNat 64 (11341403200 + (input.proof.length - tailBytes tOff)) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
        hreg2 .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31]
    have hst77 := step_ordinary oracle s3 77 (.BLTU .x31 .x6 1012#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.BLTU .x31 .x6 1012#13)
    have hult : BitVec.ult (s3.getReg .x31) (s3.getReg .x6) = decide (input.proof.length < pOff + 24 + 64 + tailBytes tOff) := by
      rw [hx31_3, hx6_3, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases hshort : input.proof.length < pOff + 24 + 64 + tailBytes tOff
    · have hpc4 : s4.pc = pcWord 330 := by
        simp only [s4, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc3]; decide
      exact .rejected 14 0 [] (by rw [hl0]; exact hshort) (by decide) (by decide)
        (by simpa using ((hs1.trans hst75).trans (hst76.trans hst77)).halt (halt_reject oracle s4 hpc4))
    · have hge64 : pOff + 24 + 64 + tailBytes tOff ≤ input.proof.length := by omega
      have hpc4 : s4.pc = pcWord 78 := by
        simp only [s4, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc3, pcWord_add_four]
      have hmem4 : s4.mem = s.mem := by
        have h43 : s4.mem = s3.mem := by
          simp only [s4, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
        have h32 : s3.mem = s2.mem := by
          simp only [s3, execInstrBr, mem_setPC, mem_setReg]
        exact h43.trans (h32.trans hmem2)
      have hreg43 : ∀ r, s4.getReg r = s3.getReg r := fun r => by
        simp only [s4, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x23 → s4.getReg r = s.getReg r := fun r h6 h7 h22 h23 => by
        rw [hreg43]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
        exact hreg2 r h6 h7 h22 h23
      have hx22_4 : s4.getReg .x22 = BitVec.ofNat 64 (i.val / 3) := by
        rw [hreg43]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x22), hx22_2]
      have hx23_4 : s4.getReg .x23 = BitVec.ofNat 64 (i.val % 3) := by
        rw [hreg43]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x23), hx23_2]
      -- Common finish from pc[111] once S[0..96) = pw.l0Input c96
      have hfinish : ∀ (s111 : MachineState) (kMid : Nat),
          kMid ≤ 406 →
          StepsTo oracle s4 s111 kMid 0 [] →
          s111.pc = pcWord 111 →
          CheckFixedRegs s111 →
          ProofCursor s0 input.proof.length (pOff + 24 + 64) tOff s111 →
          MemEqOutside s4 s111 256 352 →
          s111.getReg .x22 = BitVec.ofNat 64 (i.val / 3) →
          s111.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
          s111.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
          s111.getReg .x27 = BitVec.ofNat 64 rem →
          readBuffer s111 256 96 = pw.l0Input c96 →
          PhaseOutcome oracle s 420 1 (input.proof.length < pOff + 24 + l0Bytes i + tailBytes tOff)
            (fun s' q tr =>
              q ≤ 1 ∧ s'.pc = pcWord 114 ∧ CheckFixedRegs s' ∧
              ProofCursor s0 input.proof.length (pOff + 24 + l0Bytes i) tOff s' ∧
              MemEqOutside s s' 256 352 ∧ s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
              s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
              s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
              s'.getReg .x27 = BitVec.ofNat 64 rem ∧
              readBuffer s' 256 32 = pw.evalL1 c96 ∧
              (i.val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96))) := by
        intro s111 kMid hkMid hmid hpc111 hfix111 hcur111 hout111 h22 h24 h8 h27 hinp111
        have hst111 := step_ordinary oracle s111 111 (.ADDI .x10 .x21 0#12) (by decide) hpc111 rfl (by intro h; cases h) rfl
        let s112 := execInstrBr s111 (.ADDI .x10 .x21 0#12)
        have hpc112 : s112.pc = pcWord 112 := by simp only [s112, execInstrBr, MachineState.setPC, hpc111, pcWord_add_four]
        have hst112 := step_ordinary oracle s112 112 (.ADDI .x12 .x21 0#12) (by decide) hpc112 rfl (by intro h; cases h) rfl
        let s113 := execInstrBr s112 (.ADDI .x12 .x21 0#12)
        have hpc113 : s113.pc = pcWord 113 := by simp only [s113, execInstrBr, MachineState.setPC, hpc112, pcWord_add_four]
        have hmem113 : s113.mem = s111.mem := by simp [s113, s112, execInstrBr, mem_setPC, mem_setReg]
        have hreg113 : ∀ r, r ≠ .x10 → r ≠ .x12 → s113.getReg r = s111.getReg r := fun r h10 h12 => by
          simp only [s113, s112, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
        have hx10_113 : s113.getReg .x10 = 256#64 := by
          simp only [s113, s112, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide), hfix111.x21, se12_0, BitVec.add_zero]
        have hx12_113 : s113.getReg .x12 = 256#64 := by
          simp only [s113, s112, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
            hfix111.x21, se12_0, BitVec.add_zero]
        have hec := step_ecall_compress h768 oracle s113 113 256 256 (by decide) hpc113 rfl
          ((hreg113 .x5 (by decide) (by decide)).trans hfix111.x5)
          ((hreg113 .x11 (by decide) (by decide)).trans hfix111.x11)
          ((hreg113 .x13 (by decide) (by decide)).trans hfix111.x13)
          hx10_113 hx12_113 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
        rw [(MemEqOutside.of_mem_eq hmem113 0 0).readBuffer_eq (by decide) (by omega), hinp111] at hec
        let sFin := writeBits s113 (BitVec.ofNat 64 256) (c96 (pw.l0Input c96))
        have hpcFin : sFin.pc = pcWord 114 := by simp only [sFin, writeBits, MachineState.setPC, hpc113, pcWord_add_four]
        have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → sFin.getReg r = s111.getReg r := fun r h10 h12 =>
          (writeBits_register s113 _ _ r).trans (hreg113 r h10 h12)
        have htot := (((hs1.trans hst75).trans (hst76.trans hst77)).trans hmid).trans
          ((hst111.trans hst112).trans hec)
        refine .continued sFin (11 + kMid + 3) 1 [((pw.l0Input c96).cast h768.symm, c96 (pw.l0Input c96))]
          (by omega) (by decide)
          (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
          ⟨by decide, hpcFin,
           hfix111.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
           by rw [hl0]
              exact hcur111.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
           (MemEqOutside.of_mem_eq hmem4 256 352).trans
             (hout111.trans ((MemEqOutside.of_mem_eq hmem113 256 352).trans
               ((MemEqOutside_writeBits_digest s113 256 _ (by decide)).mono (by omega) (by omega)))),
           (hregFin .x22 (by decide) (by decide)).trans h22,
           (hregFin .x24 (by decide) (by decide)).trans h24,
           (hregFin .x8  (by decide) (by decide)).trans h8,
           (hregFin .x27 (by decide) (by decide)).trans h27,
           ?_, fun _ => InTrace.singleton h768 oracle (pw.l0Input c96)⟩
        rw [writeBits_readBuffer_digest]
        simp only [WitnessPath.evalL1, pw, parsePartialWitness, hfull, ite_false]
      -- Three remainder cases: r = 0 (pc[93..96]), r = 1 (pc[97..110]), r = 2 (pc[81..92])
      have hst78 := step_ordinary oracle s4 78 (.BEQ .x23 .x0 60#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
      let s5 := execInstrBr s4 (.BEQ .x23 .x0 60#13)
      have hleaf4 : readBuffer s4 256 32 = leafDigest c96 pw.index pw.salt pw.value :=
        ((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hleaf
      have hhigh4 : HighMemPreserved s0 s4 := hhigh.trans (MemEqOutside.of_mem_eq hmem4 0 4294971392)
      have hsib0 : readBuffer s4 (11341403200 + pOff + 24) 32 = pw.l0Sib0 := by
        simp only [pw, parsePartialWitness, hfull, ite_false]
        exact hhigh4.readBuffer_eq (by omega) (by omega)
      have hsib1 : readBuffer s4 (11341403200 + pOff + 56) 32 = pw.l0Sib1 := by
        simp only [pw, parsePartialWitness, hfull, ite_false]
        exact hhigh4.readBuffer_eq (by omega) (by omega)
      have hrem_cases : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hrem_cases with hr0 | hr1 | hr2
      · -- Case r = 0: jump to pc[93..96] -> pc[111]
        have hx23z : s4.getReg .x23 = 0#64 := by rw [hx23_4, hr0]
        have hpc5 : s5.pc = pcWord 93 := by
          simp only [s5, execInstrBr, hx23z, getReg_x0, beq_self_eq_true, ite_true,
            MachineState.setPC, hpc4]; decide
        have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
          simp [s5, execInstrBr, hx23z, getReg_x0, MachineState.getReg_setPC]
        have hmem5 : s5.mem = s4.mem := by
          simp [s5, execInstrBr, hx23z, getReg_x0, MachineState.setPC]
        have hst93 := step_ordinary oracle s5 93 (.ADDI .x12 .x21 32#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s6 := execInstrBr s5 (.ADDI .x12 .x21 32#12)
        have hpc6 : s6.pc = pcWord 94 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
        obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
          step_call_read_n oracle 94 64 s6 (11341403200 + (pOff + 24)) 288 (by decide) (by decide) (by decide)
            rfl rfl hpc6
            (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg5,
                  hreg4 .x25 (by decide) (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg5,
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hst96 := step_ordinary oracle s7 96 (.JAL .x0 60#21) (by decide) hpc7 rfl (by intro h; cases h) rfl
        let s8 := execInstrBr s7 (.JAL .x0 60#21)
        have hpc8 : s8.pc = pcWord 111 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7]; decide
        have hmem6 : s6.mem = s4.mem := by simpa [s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
        have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s4 s8 256 352 :=
          (MemEqOutside.of_mem_eq hmem6 256 352).trans
            ((hout7.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem8 256 352))
        have hreg8 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s8.getReg r = s4.getReg r :=
          fun r h1 h6 h10 h12 h25 => by
            have h87 : s8.getReg r = s7.getReg r := by simp [s8, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            rw [h87, hreg7 r h1 h6 h10 h12 h25]
            simp only [s6, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg5]
        have hinp : readBuffer s8 256 96 = pw.l0Input c96 := by
          rw [readBuffer_ternary]
          have hd0 : readBuffer s8 256 32 = leafDigest c96 pw.index pw.salt pw.value := by
            have h0 : MemEqOutside s4 s8 288 352 :=
              (MemEqOutside.of_mem_eq hmem6 288 352).trans
                ((hout7.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem8 288 352))
            exact (h0.readBuffer_eq (by decide) (by omega)).trans hleaf4
          have hd1 : readBuffer s8 288 32 = pw.l0Sib0 := by
            rw [(MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by decide) (by omega), ← hsib0]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy7 j (by omega)
            simp only [MachineState.getByte, MachineState.getMem, hmem6] at hc ⊢
            simpa only [Nat.add_assoc] using hc
          have hd2 : readBuffer s8 320 32 = pw.l0Sib1 := by
            rw [(MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by decide) (by omega), ← hsib1]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy7 (32 + j) (by omega)
            simp only [MachineState.getByte, MachineState.getMem, hmem6] at hc ⊢
            rw [show 320 + j = 288 + (32 + j) by omega, hc,
              show 11341403200 + (pOff + 24) + (32 + j) = 11341403200 + pOff + 56 + j by omega]
          rw [hd0, hd1, hd2]
          simp only [WitnessPath.l0Input, show pw.index.val % 3 = 0 from hr0, ite_true]
        have hcur8 : ProofCursor s0 input.proof.length (pOff + 24 + 64) tOff s8 := by
          refine ⟨hge64, ?_, ?_, ?_, ?_⟩
          · have : s8.getReg .x25 = s7.getReg .x25 := by simp [s8, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            rw [this, hx25_7]; congr 1
          · rw [hreg8 .x31 (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg8 .x3 (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x3 (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg8 .x4 (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x4 (by decide) (by decide) (by decide) (by decide), hcur.x4]
        refine hfinish s8 390 (by decide)
          (by simpa using ((hst78.trans hst93).trans hs7).trans hst96) hpc8
          (hfix.of_agree (fun r hr => (hreg8 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
            (hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          hcur8 hout_all
          ((hreg8 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_4)
          ((hreg8 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
          ((hreg8 .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
          ((hreg8 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
          hinp
      · -- Case r = 1: pc[78] fallthrough -> pc[79..80] jump to pc[97..110] -> pc[111]
        have hx23o : s4.getReg .x23 = 1#64 := by rw [hx23_4, hr1]
        have hpc5 : s5.pc = pcWord 79 := by
          simp only [s5, execInstrBr, hx23o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc4, pcWord_add_four]
        have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
          simp [s5, execInstrBr, hx23o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
        have hmem5 : s5.mem = s4.mem := by
          simp [s5, execInstrBr, hx23o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC]
        have hst79 := step_ordinary oracle s5 79 (.ADDI .x7 .x0 1#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s5a := execInstrBr s5 (.ADDI .x7 .x0 1#12)
        have hpc5a : s5a.pc = pcWord 80 := by simp only [s5a, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
        have hst80 := step_ordinary oracle s5a 80 (.BEQ .x23 .x7 68#13) (by decide) hpc5a rfl (by intro h; cases h) rfl
        let s5b := execInstrBr s5a (.BEQ .x23 .x7 68#13)
        have hx23_5a : s5a.getReg .x23 = 1#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x23), hreg5, hx23o]
        have hx7_5a : s5a.getReg .x7 = 1#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        have hpc5b : s5b.pc = pcWord 97 := by
          simp only [s5b, execInstrBr, hx23_5a, hx7_5a, beq_self_eq_true, ite_true, MachineState.setPC, hpc5a]; decide
        have hmem5b : s5b.mem = s4.mem := by
          have hba : s5b.mem = s5a.mem := by
            simp only [s5b, execInstrBr, hx23_5a, hx7_5a, beq_self_eq_true, ite_true, mem_setPC]
          have ha5 : s5a.mem = s5.mem := by simp only [s5a, execInstrBr, mem_setPC, mem_setReg]
          exact hba.trans (ha5.trans hmem5)
        have hreg5b : ∀ r, r ≠ .x7 → s5b.getReg r = s4.getReg r := fun r h7 => by
          have hba : s5b.getReg r = s5a.getReg r := by
            simp only [s5b, execInstrBr, hx23_5a, hx7_5a, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
          rw [hba]
          simp only [s5a, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg5]
        -- pc[97..104]: copy 4 dwords S[0..32) -> S[32..64)
        have hcp1 : ∀ j < 4,
            checkInstr (97 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (97 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
          step_copy_dwords oracle 97 4 .x21 .x21 0 32 s5b 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp1 hpc5b
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
        -- pc[105..107]: read sib0 -> S[0..32)
        have hst105 := step_ordinary oracle s6 105 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
        let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
        have hpc7 : s7.pc = pcWord 106 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
        obtain ⟨s8, hs8, hpc8, hx25_8, hreg8, hcopy8, hout8⟩ :=
          step_call_read_n oracle 106 32 s7 (11341403200 + (pOff + 24)) 256 (by decide) (by decide) (by decide)
            rfl rfl hpc7
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg6 .x25 (by decide),
                  hreg5b .x25 (by decide), hreg4 .x25 (by decide) (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide), hreg5b .x21 (by decide),
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        -- pc[108..110]: read sib1 -> S[64..96)
        have hst108 := step_ordinary oracle s8 108 (.ADDI .x12 .x21 64#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 64#12)
        have hpc9 : s9.pc = pcWord 109 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hx25_10, hreg10, hcopy10, hout10⟩ :=
          step_call_read_n oracle 109 32 s9 (11341403200 + (pOff + 24) + 32) 320 (by decide) (by decide) (by decide)
            rfl rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hx25_8])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg8 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
                simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg6 .x21 (by decide),
                  hreg5b .x21 (by decide), hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_64]; decide)
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s4 s10 256 352 :=
          (MemEqOutside.of_mem_eq hmem5b 256 352).trans
            ((hout6.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem7 256 352).trans
                ((hout8.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem9 256 352).trans (hout10.mono (by omega) (by omega))))))
        have hreg10_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s10.getReg r = s4.getReg r :=
          fun r h1 h6 h7 h10 h12 h25 => by
            rw [hreg10 r h1 h6 h10 h12 h25]
            simp only [s9, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg8 r h1 h6 h10 h12 h25]
            simp only [s7, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg6 r h6, hreg5b r h7]
        have hinp : readBuffer s10 256 96 = pw.l0Input c96 := by
          rw [readBuffer_ternary]
          have hd0 : readBuffer s10 256 32 = pw.l0Sib0 := by
            rw [hout10.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hsib0]
            apply readBuffer_congr2; intro j hj
            rw [hcopy8 j hj]
            have h74 : MemEqOutside s4 s7 288 320 :=
              (MemEqOutside.of_mem_eq hmem5b 288 320).trans (hout6.trans (MemEqOutside.of_mem_eq hmem7 288 320))
            rw [show 11341403200 + (pOff + 24) + j = 11341403200 + pOff + 24 + j by omega]
            exact h74 (11341403200 + pOff + 24 + j) (by omega) (by omega)
          have hd1 : readBuffer s10 288 32 = leafDigest c96 pw.index pw.salt pw.value := by
            rw [hout10.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega),
              hout8.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by decide) (by omega), ← hleaf4]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy6 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem5b] at hc ⊢
            exact hc
          have hd2 : readBuffer s10 320 32 = pw.l0Sib1 := by
            rw [← hsib1]
            apply readBuffer_congr2; intro j hj
            rw [hcopy10 j hj]
            have h94 : MemEqOutside s4 s9 256 320 :=
              (MemEqOutside.of_mem_eq hmem5b 256 320).trans
                ((hout6.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem7 256 320).trans
                    ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 320))))
            rw [show 11341403200 + (pOff + 24) + 32 + j = 11341403200 + pOff + 56 + j by omega]
            exact h94 (11341403200 + pOff + 56 + j) (by omega) (by omega)
          rw [hd0, hd1, hd2]
          simp only [WitnessPath.l0Input, show pw.index.val % 3 = 1 from hr1,
            show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
        have hcur10 : ProofCursor s0 input.proof.length (pOff + 24 + 64) tOff s10 := by
          refine ⟨hge64, ?_, ?_, ?_, ?_⟩
          · rw [hx25_10]; congr 1
          · rw [hreg10_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg10_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x3 (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg10_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x4 (by decide) (by decide) (by decide) (by decide), hcur.x4]
        refine hfinish s10 403 (by decide)
          (by simpa using (((hst78.trans hst79).trans hst80).trans hs6).trans ((hst105.trans hs8).trans (hst108.trans hs10)))
          hpc10 (hfix.of_agree (fun r hr => (hreg10_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl)).trans
            (hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          hcur10 hout_all
          ((hreg10_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_4)
          ((hreg10_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
          ((hreg10_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
          ((hreg10_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
          hinp
      · -- Case r = 2: fall through to pc[81..92] -> pc[111]
        have hx23t : s4.getReg .x23 = 2#64 := by rw [hx23_4, hr2]
        have hpc5 : s5.pc = pcWord 79 := by
          simp only [s5, execInstrBr, hx23t, getReg_x0, show (2#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc4, pcWord_add_four]
        have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
          simp [s5, execInstrBr, hx23t, getReg_x0, show (2#64 == 0#64) = false by decide, MachineState.getReg_setPC]
        have hmem5 : s5.mem = s4.mem := by
          simp [s5, execInstrBr, hx23t, getReg_x0, show (2#64 == 0#64) = false by decide, MachineState.setPC]
        have hst79 := step_ordinary oracle s5 79 (.ADDI .x7 .x0 1#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s5a := execInstrBr s5 (.ADDI .x7 .x0 1#12)
        have hpc5a : s5a.pc = pcWord 80 := by simp only [s5a, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
        have hst80 := step_ordinary oracle s5a 80 (.BEQ .x23 .x7 68#13) (by decide) hpc5a rfl (by intro h; cases h) rfl
        let s5b := execInstrBr s5a (.BEQ .x23 .x7 68#13)
        have hx23_5a : s5a.getReg .x23 = 2#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x23), hreg5, hx23t]
        have hx7_5a : s5a.getReg .x7 = 1#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
            ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        have hpc5b : s5b.pc = pcWord 81 := by
          simp only [s5b, execInstrBr, hx23_5a, hx7_5a, show (2#64 == 1#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc5a, pcWord_add_four]
        have hmem5b : s5b.mem = s4.mem := by
          have hba : s5b.mem = s5a.mem := by
            simp only [s5b, execInstrBr, hx23_5a, hx7_5a, show (2#64 == 1#64) = false by decide,
              Bool.false_eq_true, ite_false, mem_setPC]
          have ha5 : s5a.mem = s5.mem := by simp only [s5a, execInstrBr, mem_setPC, mem_setReg]
          exact hba.trans (ha5.trans hmem5)
        have hreg5b : ∀ r, r ≠ .x7 → s5b.getReg r = s4.getReg r := fun r h7 => by
          have hba : s5b.getReg r = s5a.getReg r := by
            simp only [s5b, execInstrBr, hx23_5a, hx7_5a, show (2#64 == 1#64) = false by decide,
              Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
          rw [hba]
          simp only [s5a, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg5]
        -- pc[81..88]: copy 4 dwords S[0..32) -> S[64..96)
        have hcp2 : ∀ j < 4,
            checkInstr (81 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (81 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (64 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
          step_copy_dwords oracle 81 4 .x21 .x21 0 64 s5b 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp2 hpc5b
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
        -- pc[89..91]: read 64 bytes (sib0 ++ sib1) -> S[0..64)
        have hst89 := step_ordinary oracle s6 89 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
        let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
        have hpc7 : s7.pc = pcWord 90 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
        obtain ⟨s8, hs8, hpc8, hx25_8, hreg8, hcopy8, hout8⟩ :=
          step_call_read_n oracle 90 64 s7 (11341403200 + (pOff + 24)) 256 (by decide) (by decide) (by decide)
            rfl rfl hpc7
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg6 .x25 (by decide),
                  hreg5b .x25 (by decide), hreg4 .x25 (by decide) (by decide) (by decide) (by decide), hcur.x25])
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide), hreg5b .x21 (by decide),
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hst92 := step_ordinary oracle s8 92 (.JAL .x0 76#21) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.JAL .x0 76#21)
        have hpc9 : s9.pc = pcWord 111 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8]; decide
        have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s4 s9 256 352 :=
          (MemEqOutside.of_mem_eq hmem5b 256 352).trans
            ((hout6.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem7 256 352).trans
                ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 352))))
        have hreg9_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s9.getReg r = s4.getReg r :=
          fun r h1 h6 h7 h10 h12 h25 => by
            have : s9.getReg r = s8.getReg r := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            rw [this, hreg8 r h1 h6 h10 h12 h25]
            simp only [s7, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg6 r h6, hreg5b r h7]
        have hinp : readBuffer s9 256 96 = pw.l0Input c96 := by
          rw [readBuffer_ternary]
          have h74 : MemEqOutside s4 s7 320 352 :=
            (MemEqOutside.of_mem_eq hmem5b 320 352).trans (hout6.trans (MemEqOutside.of_mem_eq hmem7 320 352))
          have hd0 : readBuffer s9 256 32 = pw.l0Sib0 := by
            rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hsib0]
            apply readBuffer_congr2; intro j hj
            rw [hcopy8 j (by omega), show 11341403200 + (pOff + 24) + j = 11341403200 + pOff + 24 + j by omega]
            exact h74 (11341403200 + pOff + 24 + j) (by omega) (by omega)
          have hd1 : readBuffer s9 288 32 = pw.l0Sib1 := by
            rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hsib1]
            apply readBuffer_congr2; intro j hj
            rw [show 288 + j = 256 + (32 + j) by omega, hcopy8 (32 + j) (by omega),
              show 11341403200 + (pOff + 24) + (32 + j) = 11341403200 + pOff + 56 + j by omega]
            exact h74 (11341403200 + pOff + 56 + j) (by omega) (by omega)
          have hd2 : readBuffer s9 320 32 = leafDigest c96 pw.index pw.salt pw.value := by
            rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega),
              hout8.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by decide) (by omega), ← hleaf4]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy6 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem5b] at hc ⊢
            exact hc
          rw [hd0, hd1, hd2]
          simp only [WitnessPath.l0Input, show pw.index.val % 3 = 2 from hr2,
            show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false]
        have hcur9 : ProofCursor s0 input.proof.length (pOff + 24 + 64) tOff s9 := by
          refine ⟨hge64, ?_, ?_, ?_, ?_⟩
          · have : s9.getReg .x25 = s8.getReg .x25 := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            rw [this, hx25_8]; congr 1
          · rw [hreg9_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31]
          · rw [hreg9_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x3 (by decide) (by decide) (by decide) (by decide), hcur.x3]
          · rw [hreg9_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg4 .x4 (by decide) (by decide) (by decide) (by decide), hcur.x4]
        refine hfinish s9 400 (by decide)
          (by simpa using (((hst78.trans hst79).trans hst80).trans hs6).trans ((hst89.trans hs8).trans hst92))
          hpc9 (hfix.of_agree (fun r hr => (hreg9_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl)).trans
            (hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          hcur9 hout_all
          ((hreg9_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_4)
          ((hreg9_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
          ((hreg9_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
          ((hreg9_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
          hinp

/-- Phase 1C: L1 binary step (`pc[114..140]` -> `pc[141]`), outputting masked 240-bit L2 digest
and zeroing the gap `S[64..96)`. -/
theorem step_pos_l1 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 114)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length
      (pOff + 24 + l0Bytes (posAt input.positions ord)) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl1 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalL1
        (fun x => oracle.compression (x.cast h768.symm))) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pOff2 := pOff + 24 + l0Bytes i
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 220 1 (input.proof.length < pOff2 + 32 + tailBytes tOff)
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = pcWord 141 ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length (pOff2 + 32) tOff s' ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 2 ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 1, InTrace h768 oracle tr x) := by
  intro s0 c96 i pOff2 pw
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hle_cur : pOff2 + tailBytes tOff ≤ input.proof.length := hcur.le
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_lt : i.val / 3 < 5592406 := by omega
  have hpair1 : ((i.val / 3) ^^^ 1) < levelSize 1 := by
    rw [levelSize_1]; exact xor_one_lt_even (m := 2796203) (by omega)
  -- pc[114]: ADDI x6, x25, 32; pc[115]: BLTU x31, x6, pc[330]
  have hst114 := step_ordinary oracle s 114 (.ADDI .x6 .x25 32#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x6 .x25 32#12)
  have hpc1 : s1.pc = pcWord 115 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 (11341403200 + pOff2 + 32) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hcur.x25, se12_32]
    change BitVec.ofNat 64 (11341403200 + pOff2) + BitVec.ofNat 64 32 = _
    exact bv64_add _ 32
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (11341403200 + (input.proof.length - tailBytes tOff)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hcur.x31]
  have hst115 := step_ordinary oracle s1 115 (.BLTU .x31 .x6 860#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BLTU .x31 .x6 860#13)
  have hult : BitVec.ult (s1.getReg .x31) (s1.getReg .x6) = decide (input.proof.length < pOff2 + 32 + tailBytes tOff) := by
    rw [hx31_1, hx6_1, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pOff2 + 32 + tailBytes tOff
  · have hpc2 : s2.pc = pcWord 330 := by
      simp only [s2, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc1]; decide
    exact .rejected 5 0 [] hshort (by decide) (by decide)
      (by simpa using (hst114.trans hst115).halt (halt_reject oracle s2 hpc2))
  · have hge32 : pOff2 + 32 + tailBytes tOff ≤ input.proof.length := by omega
    have hpc2 : s2.pc = pcWord 116 := by
      simp only [s2, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      have h21 : s2.mem = s1.mem := by
        simp only [s2, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      rw [h21]
      simp only [s1, execInstrBr, mem_setPC, mem_setReg]
    have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r h6 => by
      have h21 : s2.getReg r = s1.getReg r := by
        simp only [s2, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      rw [h21]
      simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
    -- pc[116..119]: zero gap S[64..96)
    obtain ⟨s3, hs3, hpc3, hreg3, hgap3, hout3⟩ :=
      step_zero_gap oracle s2 hpc2 ((hreg2 .x21 (by decide)).trans hfix.x21)
    -- pc[120]: ANDI x7, x22, 1; pc[121]: BEQ x7, x0, pc[134]
    have hst120 := step_ordinary oracle s3 120 (.ANDI .x7 .x22 1#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ANDI .x7 .x22 1#12)
    have hpc4 : s4.pc = pcWord 121 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hx7_4 : s4.getReg .x7 = BitVec.ofNat 64 ((i.val / 3) % 2) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x22, hreg2 .x22 (by decide), hx22, se12_1]
      exact bv64_and_one (i.val / 3) (by omega)
    have hst121 := step_ordinary oracle s4 121 (.BEQ .x7 .x0 52#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.BEQ .x7 .x0 52#13)
    have hmem4 : s4.mem = s3.mem := by simp [s4, execInstrBr, mem_setPC, mem_setReg]
    -- Target compression input at L1
    let inp1 : BitVec 768 :=
      if (i.val / 3) % 2 = 0 then binaryInput (pw.evalL1 c96) (pw.binSib 1)
      else binaryInput (pw.binSib 1) (pw.evalL1 c96)
    have heval2 : pw.evalLevel c96 2 = mask240 (c96 inp1) := by
      simp only [WitnessPath.evalLevel, show (pw.index.val / 3) >>> 0 = i.val / 3 by rfl,
        hpair1, ite_true]
      rfl
    have hlinp1 : pw.levelInput c96 1 = [inp1] := by
      simp only [WitnessPath.levelInput, show (pw.index.val / 3) >>> 0 = i.val / 3 by rfl,
        hpair1, ite_true]
      rfl
    -- Common finish from pc[137] once S[0..96) = inp1 and S[64..96) = 0
    have hfinish : ∀ (s137 : MachineState) (kMid : Nat),
        kMid ≤ 208 →
        StepsTo oracle s5 s137 kMid 0 [] →
        s137.pc = pcWord 137 →
        CheckFixedRegs s137 →
        ProofCursor s0 input.proof.length (pOff2 + 32) tOff s137 →
        MemEqOutside s5 s137 256 320 →
        s137.getReg .x22 = BitVec.ofNat 64 (i.val / 3) →
        s137.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) →
        s137.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) →
        s137.getReg .x27 = BitVec.ofNat 64 rem →
        readBuffer s137 256 96 = inp1 →
        readBuffer s137 320 32 = 0 →
        PhaseOutcome oracle s 220 1 (input.proof.length < pOff2 + 32 + tailBytes tOff)
          (fun s' q tr =>
            q = 1 ∧ s'.pc = pcWord 141 ∧ CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length (pOff2 + 32) tOff s' ∧
            MemEqOutside s s' 256 352 ∧ s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (7046435904 + 256 * ord) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            readBuffer s' 256 32 = pw.evalLevel c96 2 ∧
            readBuffer s' 320 32 = 0 ∧
            ∀ x ∈ pw.levelInput c96 1, InTrace h768 oracle tr x) := by
      intro s137 kMid hkMid hmid hpc137 hfix137 hcur137 hout137 h22 h24 h8 h27 hinp137 hgap137
      have hst137 := step_ordinary oracle s137 137 (.ADDI .x10 .x21 0#12) (by decide) hpc137 rfl (by intro h; cases h) rfl
      let s138 := execInstrBr s137 (.ADDI .x10 .x21 0#12)
      have hpc138 : s138.pc = pcWord 138 := by simp only [s138, execInstrBr, MachineState.setPC, hpc137, pcWord_add_four]
      have hst138 := step_ordinary oracle s138 138 (.ADDI .x12 .x21 0#12) (by decide) hpc138 rfl (by intro h; cases h) rfl
      let s139 := execInstrBr s138 (.ADDI .x12 .x21 0#12)
      have hpc139 : s139.pc = pcWord 139 := by simp only [s139, execInstrBr, MachineState.setPC, hpc138, pcWord_add_four]
      have hmem139 : s139.mem = s137.mem := by simp [s139, s138, execInstrBr, mem_setPC, mem_setReg]
      have hreg139 : ∀ r, r ≠ .x10 → r ≠ .x12 → s139.getReg r = s137.getReg r := fun r h10 h12 => by
        simp only [s139, s138, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_139 : s139.getReg .x10 = 256#64 := by
        simp only [s139, s138, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix137.x21, se12_0, BitVec.add_zero]
      have hx12_139 : s139.getReg .x12 = 256#64 := by
        simp only [s139, s138, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hfix137.x21, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h768 oracle s139 139 256 256 (by decide) hpc139 rfl
        ((hreg139 .x5 (by decide) (by decide)).trans hfix137.x5)
        ((hreg139 .x11 (by decide) (by decide)).trans hfix137.x11)
        ((hreg139 .x13 (by decide) (by decide)).trans hfix137.x13)
        hx10_139 hx12_139 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem139 0 0).readBuffer_eq (by decide) (by omega), hinp137] at hec
      let s140 := writeBits s139 (BitVec.ofNat 64 256) (c96 inp1)
      have hpc140 : s140.pc = pcWord 140 := by simp only [s140, writeBits, MachineState.setPC, hpc139, pcWord_add_four]
      have hx21_140 : s140.getReg .x21 = 256#64 :=
        (writeBits_register s139 _ _ .x21).trans ((hreg139 .x21 (by decide) (by decide)).trans hfix137.x21)
      have ha140 : s140.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
        rw [hx21_140]; decide
      have hv140 : memoryArgumentsValid s140 (.SH .x21 .x0 30#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha140]
        exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst140 := step_ordinary oracle s140 140 (.SH .x21 .x0 30#12) (by decide) hpc140 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv140])
      let sFin := execInstrBr s140 (.SH .x21 .x0 30#12)
      have hpcFin : sFin.pc = pcWord 141 := by simp only [sFin, execInstrBr, MachineState.setPC, hpc140, pcWord_add_four]
      have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → sFin.getReg r = s137.getReg r := fun r h10 h12 => by
        have : sFin.getReg r = s140.getReg r := by
          simp [sFin, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        exact this.trans ((writeBits_register s139 _ _ r).trans (hreg139 r h10 h12))
      have hmem_s5 : s5.mem = s3.mem := by
        simp only [s5, execInstrBr]
        split <;> simpa [MachineState.setPC] using hmem4
      have hout_sh : MemEqOutside s140 sFin 286 288 := by
        intro a ha hout
        simp only [sFin, execInstrBr, ha140, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact MemEqOutside_setHalfword s140 286 _ (by decide) (by decide) a ha hout
      have hout_all : MemEqOutside s sFin 256 352 :=
        (MemEqOutside.of_mem_eq hmem2 256 352).trans
          ((hout3.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem_s5 256 352).trans
              ((hout137.mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem139 256 352).trans
                  (((MemEqOutside_writeBits_digest s139 256 _ (by decide)).mono (by omega) (by omega)).trans
                    (hout_sh.mono (by omega) (by omega)))))))
      have hdigFin : readBuffer sFin 256 32 = pw.evalLevel c96 2 := by
        rw [heval2]
        have hsh : readBuffer sFin 256 32 =
            readBuffer (s140.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
          apply readBuffer_congr2; intro j hj
          simp [sFin, execInstrBr, ha140, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
            show (0#64 : Word).truncate 16 = 0#16 by decide]
        rw [hsh, sh_zero_mask240 s140 256 (by decide) (by decide), writeBits_readBuffer_digest]
      have hgapFin : readBuffer sFin 320 32 = 0 := by
        rw [hout_sh.readBuffer_eq (by decide) (by omega),
          (MemEqOutside_writeBits_digest s139 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
          (MemEqOutside.of_mem_eq hmem139 0 0).readBuffer_eq (by decide) (by omega), hgap137]
      have htot := (((hst114.trans hst115).trans hs3).trans ((hst120.trans hst121).trans hmid)).trans
        (((hst137.trans hst138).trans hec).trans hst140)
      refine .continued sFin (2 + 4 + (1 + 1 + kMid) + 4) 1 [(inp1.cast h768.symm, c96 inp1)]
        (by omega) (by decide)
        (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
        ⟨rfl, hpcFin,
         hfix137.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         hcur137.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         hout_all,
         (hregFin .x22 (by decide) (by decide)).trans h22,
         (hregFin .x24 (by decide) (by decide)).trans h24,
         (hregFin .x8  (by decide) (by decide)).trans h8,
         (hregFin .x27 (by decide) (by decide)).trans h27,
         hdigFin, hgapFin, ?_⟩
      intro x hx
      rw [hlinp1, List.mem_singleton] at hx
      subst hx
      exact InTrace.singleton h768 oracle inp1
    have hcur3 : readBuffer s3 256 32 = pw.evalL1 c96 :=
      (hout3.readBuffer_eq (by decide) (by omega)).trans
        (((MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega)).trans hl1)
    have hhigh3 : HighMemPreserved s0 s3 :=
      hhigh.trans ((MemEqOutside.of_mem_eq hmem2 0 4294971392).trans (hout3.mono (by omega) (by omega)))
    have hsib1 : readBuffer s3 (11341403200 + pOff2) 32 = pw.binSib 1 := by
      have : pw.binSib 1 = readBuffer s0 (11341403200 + pOff2) 32 := by
        simp [pw, parsePartialWitness, pOff2, Nat.add_assoc]
      rw [this]
      exact hhigh3.readBuffer_eq (by omega) (by omega)
    by_cases heven : (i.val / 3) % 2 = 0
    · -- Even: jump to pc[134..136] -> pc[137]
      have hx7z : s4.getReg .x7 = 0#64 := by rw [hx7_4, heven]
      have hpc5 : s5.pc = pcWord 134 := by
        simp only [s5, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
          MachineState.setPC, hpc4]; decide
      have hmem5 : s5.mem = s3.mem := by
        simpa [s5, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem4
      have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → s5.getReg r = s.getReg r := fun r h6 h7 => by
        have h54 : s5.getReg r = s4.getReg r := by
          simp only [s5, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        rw [h54]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg3 r, hreg2 r h6]
      have hst134 := step_ordinary oracle s5 134 (.ADDI .x12 .x21 32#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ADDI .x12 .x21 32#12)
      have hpc6 : s6.pc = pcWord 135 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
        step_call_read_n oracle 135 32 s6 (11341403200 + pOff2) 288 (by decide) (by decide) (by decide)
          rfl rfl hpc6
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg5 .x25 (by decide) (by decide), hcur.x25])
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide),
                hreg5 .x21 (by decide) (by decide), hfix.x21, se12_32]; decide)
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
      have hout_57 : MemEqOutside s5 s7 256 320 :=
        (MemEqOutside.of_mem_eq hmem6 256 320).trans (hout7.mono (by omega) (by omega))
      have hreg7_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s7.getReg r = s.getReg r :=
        fun r h1 h6 h7 h10 h12 h25 => by
          rw [hreg7 r h1 h6 h10 h12 h25]
          simp only [s6, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg5 r h6 h7]
      have hgap7 : readBuffer s7 320 32 = 0 :=
        (hout_57.readBuffer_eq (by decide) (by omega)).trans
          (((MemEqOutside.of_mem_eq hmem5 0 0).readBuffer_eq (by decide) (by omega)).trans hgap3)
      have hinp7 : readBuffer s7 256 96 = inp1 := by
        rw [readBuffer_binary_of_zero_gap s7 256 hgap7]
        have hL : readBuffer s7 256 32 = pw.evalL1 c96 :=
          (hout7.readBuffer_eq (by decide) (by omega)).trans
            (((MemEqOutside.of_mem_eq (hmem6.trans hmem5) 0 0).readBuffer_eq (by decide) (by omega)).trans hcur3)
        have hR : readBuffer s7 288 32 = pw.binSib 1 := by
          rw [← hsib1]; apply readBuffer_congr2; intro j hj
          have hc := hcopy7 j hj
          simp only [MachineState.getByte, MachineState.getMem, hmem6, hmem5] at hc ⊢
          exact hc
        rw [hL, hR]; simp only [inp1, heven, ite_true]
      have hcur7 : ProofCursor s0 input.proof.length (pOff2 + 32) tOff s7 := by
        refine ⟨hge32, ?_, ?_, ?_, ?_⟩
        · rw [hx25_7]; congr 1
        · rw [hreg7_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg7_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg7_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      refine hfinish s7 196 (by decide) (by simpa using hst134.trans hs7) hpc7
        (hfix.of_agree (fun r hr => hreg7_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl)))
        hcur7 hout_57
        ((hreg7_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg7_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg7_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        hinp7 hgap7
    · -- Odd: fall through to pc[122..133] -> pc[137]
      have hodd : (i.val / 3) % 2 = 1 := by omega
      have hx7o : s4.getReg .x7 = 1#64 := by rw [hx7_4, hodd]
      have hpc5 : s5.pc = pcWord 122 := by
        simp only [s5, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc4, pcWord_add_four]
      have hmem5 : s5.mem = s3.mem := by
        simpa [s5, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          MachineState.setPC] using hmem4
      have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → s5.getReg r = s.getReg r := fun r h6 h7 => by
        have h54 : s5.getReg r = s4.getReg r := by
          simp only [s5, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        rw [h54]
        simp only [s4, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg3 r, hreg2 r h6]
      have hcp : ∀ j < 4,
          checkInstr (122 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
          checkInstr (122 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
      obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
        step_copy_dwords oracle 122 4 .x21 .x21 0 32 s5 256 256 (by decide) (by decide)
          (by decide) (by decide) (by decide) hcp hpc5
          ((hreg5 .x21 (by decide) (by decide)).trans hfix.x21)
          ((hreg5 .x21 (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
      have hst130 := step_ordinary oracle s6 130 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
      have hpc7 : s7.pc = pcWord 131 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      obtain ⟨s8, hs8, hpc8, hx25_8, hreg8, hcopy8, hout8⟩ :=
        step_call_read_n oracle 131 32 s7 (11341403200 + pOff2) 256 (by decide) (by decide) (by decide)
          rfl rfl hpc7
          (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg6 .x25 (by decide),
                hreg5 .x25 (by decide) (by decide), hcur.x25])
          (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide),
                hreg5 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hst133 := step_ordinary oracle s8 133 (.JAL .x0 16#21) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let s9 := execInstrBr s8 (.JAL .x0 16#21)
      have hpc9 : s9.pc = pcWord 137 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8]; decide
      have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
      have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
      have hout_59 : MemEqOutside s5 s9 256 320 :=
        (hout6.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem7 256 320).trans
            ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 320)))
      have hreg9_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s9.getReg r = s.getReg r :=
        fun r h1 h6 h7 h10 h12 h25 => by
          have : s9.getReg r = s8.getReg r := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [this, hreg8 r h1 h6 h10 h12 h25]
          simp only [s7, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg6 r h6, hreg5 r h6 h7]
      have hgap9 : readBuffer s9 320 32 = 0 :=
        (hout_59.readBuffer_eq (by decide) (by omega)).trans
          (((MemEqOutside.of_mem_eq hmem5 0 0).readBuffer_eq (by decide) (by omega)).trans hgap3)
      have hinp9 : readBuffer s9 256 96 = inp1 := by
        rw [readBuffer_binary_of_zero_gap s9 256 hgap9]
        have hL : readBuffer s9 256 32 = pw.binSib 1 := by
          rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hsib1]
          apply readBuffer_congr2; intro j hj
          rw [hcopy8 j hj]
          have h73 : MemEqOutside s3 s7 288 320 :=
            (MemEqOutside.of_mem_eq hmem5 288 320).trans (hout6.trans (MemEqOutside.of_mem_eq hmem7 288 320))
          exact h73 (11341403200 + pOff2 + j) (by omega) (by omega)
        have hR : readBuffer s9 288 32 = pw.evalL1 c96 := by
          rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega),
            hout8.readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by decide) (by omega), ← hcur3]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy6 j hj
          simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem5] at hc ⊢
          exact hc
        rw [hL, hR]; simp only [inp1, heven, ite_false]
      have hcur9 : ProofCursor s0 input.proof.length (pOff2 + 32) tOff s9 := by
        refine ⟨hge32, ?_, ?_, ?_, ?_⟩
        · have : s9.getReg .x25 = s8.getReg .x25 := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [this, hx25_8]; congr 1
        · rw [hreg9_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg9_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg9_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      refine hfinish s9 205 (by decide) (by simpa using (hs6.trans hst130).trans (hs8.trans hst133)) hpc9
        (hfix.of_agree (fun r hr => hreg9_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl)))
        hcur9 hout_59
        ((hreg9_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg9_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg9_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg9_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        hinp9 hgap9

end CommitGolfCandidate
