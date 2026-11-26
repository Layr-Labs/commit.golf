import CommitGolfCandidate.MoonCheckBase

/-! Symbolic execution of the checker prologue and per-position verification loop (`pc[0..248]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private def prologuePrefix : List Instr :=
  [.ADDI .x26 .x11 0#12, .ADDI .x24 .x13 0#12, .ADDI .x8 .x14 0#12,
   .ADDI .x25 .x15 0#12, .ADD .x31 .x15 .x17, .ADDI .x27 .x16 0#12]

private def prologueNonemptySetup : List Instr :=
  [.ADDI .x21 .x0 256#12, .ADDI .x18 .x0 2#12, .SLLI .x18 .x18 11#6,
   .ADDI .x19 .x0 4#12, .SLLI .x19 .x19 11#6, .ADDI .x5 .x0 0#12,
   .ADDI .x11 .x0 96#12, .ADDI .x13 .x0 0#12]

theorem initialState_check_regs (input : CheckInput) :
    let s0 := submission.initialState .check input
    s0.pc = pcWord 0 ∧
    s0.getReg .x2  = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x11 = BitVec.ofNat 64 4294971392 ∧
    s0.getReg .x13 = BitVec.ofNat 64 5637149760 ∧
    s0.getReg .x14 = BitVec.ofNat 64 5771367488 ∧
    s0.getReg .x15 = BitVec.ofNat 64 10066334784 ∧
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
  have hst7 := step_ordinary oracle s2 7 (.BNE .x17 .x0 1316#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x17 .x0 1316#13)
  have hplen_lt : input.proof.length < 2 ^ 64 := by
    change input.proof.length ≤ 8422172696 at hvalid; omega
  by_cases hpz : input.proof.length = 0
  · simp only [hpz, ite_true]
    have hx17_z : s2.getReg .x17 = 0#64 := by rw [hx17_2, hpz]
    have hpc3 : s3.pc = pcWord 8 := by
      simp only [s3, execInstrBr, hx17_z, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
        ite_false, MachineState.setPC, hpc2, pcWord_add_four]
    have hst8 := step_ordinary oracle s3 8 (.JAL .x0 1300#21) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.JAL .x0 1300#21)
    have hpc4 : s4.pc = pcWord 333 := by
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
    have hpc3 : s3.pc = pcWord 336 := by
      simp only [s3, execInstrBr, hneb, ite_true, MachineState.setPC, hpc2]; decide
    have htot := ((hs1.trans hst6).trans hst7).halt (halt_reject oracle s3 hpc3)
    exact (by simpa using htot : HaltsWith oracle s0 11 0 .failure []).mono (by decide)

/-- When `positions.card ≥ 1`, the prologue reaches `pc[17]` in 15 steps with 0 oracle calls. -/
theorem step_prologue_nonempty (oracle : Oracle) (input : CheckInput)
    (hne : input.positions.card ≠ 0) :
    ∃ s1, StepsTo oracle (submission.initialState .check input) s1 15 0 [] ∧
      s1.pc = pcWord 17 ∧
      s1.mem = (submission.initialState .check input).mem ∧
      CheckFixedRegs s1 input.proof.length ∧
      s1.getReg .x24 = BitVec.ofNat 64 5637149760 ∧
      s1.getReg .x8  = BitVec.ofNat 64 5771367488 ∧
      s1.getReg .x25 = BitVec.ofNat 64 10066334784 ∧
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
    have hi' : i < 8 := hi
    interval_cases i <;> rfl
  have hpure2 : ∀ i (hi : i < prologueNonemptySetup.length),
      Instruction.base (prologueNonemptySetup[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologueNonemptySetup[i]'hi)) = some (execInstrBr st (prologueNonemptySetup[i]'hi)) ∧
            (execInstrBr st (prologueNonemptySetup[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologueNonemptySetup[i]'hi)).mem = st.mem := by
    intro i hi
    have hi' : i < 8 := hi
    interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs3, hpc3, hmem3⟩ := step_pure_list oracle 9 prologueNonemptySetup s2 (by decide) hcode2 hpure2 hpc2
  let s3 := runInstrs s2 prologueNonemptySetup
  have hs3 : StepsTo oracle s2 s3 8 0 [] := hs3
  have hpc3 : s3.pc = pcWord 17 := hpc3
  have hreg_s2 : ∀ r, s2.getReg r = s1.getReg r := fun r => by
    simp [s2, execInstrBr, hneb, MachineState.getReg_setPC]
  have hreg_s3 : ∀ r, r ≠ .x5 → r ≠ .x11 → r ≠ .x13 → r ≠ .x18 → r ≠ .x19 → r ≠ .x21 →
      s3.getReg r = s2.getReg r := fun r h5 h11 h13 h18 h19 h21 => by
    simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
      MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h13.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h11.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h5.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h19.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h19.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h18.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h18.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h21.symm]
  have hfixed : CheckFixedRegs s3 input.proof.length := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hreg_s3 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
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
    · rw [hreg_s3 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
      exact hx11
    · rw [hreg_s3 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq]
      have h15 : s0.getReg .x15 = BitVec.ofNat 64 10066334784 := hx15
      have h17 : s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := hx17
      rw [h15, h17, bv64_add]
  refine ⟨s3, by simpa using (hs1.trans hst6).trans hs3, hpc3, hmem3.trans hmem2, hfixed, ?_, ?_, ?_, ?_⟩
  · rw [hreg_s3 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx13
  · rw [hreg_s3 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx14
  · rw [hreg_s3 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx15
  · rw [hreg_s3 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2, hx27_1]

/-! #### Deterministic Proof-Offset Schedule and Witness Parser -/

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
  if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step) then 30 else 0

def binPathOff (g : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => binPathOff g n + binStepBytes g n

def recordLen (i : Index) : Nat :=
  16 + l0Bytes i + 32 + binPathOff (i.val / 3) 13

def posRecordOff (positions : Positions) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, recordLen (posAt positions j)

theorem l0Bytes_even (i : Index) : l0Bytes i % 2 = 0 := by
  unfold l0Bytes; split <;> decide

theorem binStepBytes_even (g step : Nat) : binStepBytes g step % 2 = 0 := by
  unfold binStepBytes; split <;> decide

theorem binPathOff_even (g n : Nat) : binPathOff g n % 2 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold binPathOff
    have := binStepBytes_even g k
    omega

theorem recordLen_even (i : Index) : recordLen i % 2 = 0 := by
  unfold recordLen
  have h1 := l0Bytes_even i
  have h2 := binPathOff_even (i.val / 3) 13
  omega

theorem posRecordOff_even (positions : Positions) (n : Nat) :
    posRecordOff positions n % 2 = 0 := by
  induction n with
  | zero => simp [posRecordOff]
  | succ k ih =>
    rw [posRecordOff, Finset.sum_range_succ]
    change (posRecordOff positions k + recordLen (posAt positions k)) % 2 = 0
    have := recordLen_even (posAt positions k)
    omega

theorem posRecordOff_succ (positions : Positions) (n : Nat) :
    posRecordOff positions (n + 1) = posRecordOff positions n + recordLen (posAt positions n) :=
  Finset.sum_range_succ _ n

theorem posRecordOff_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    posRecordOff positions a ≤ posRecordOff positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

def parsePartialWitness (s0 : MachineState) (pOff : Nat) (i : Index) (val : Entry) : WitnessPath where
  index := i
  value := val
  salt := readBuffer s0 (10066334784 + pOff) 16
  l0Sib0 := if i.val / 3 = FULL_TRIPLETS then 0 else readBuffer s0 (10066334784 + pOff + 16) 32
  l0Sib1 := if i.val / 3 = FULL_TRIPLETS then 0 else readBuffer s0 (10066334784 + pOff + 48) 32
  binSib := fun prev =>
    if prev = 1 then
      readBuffer s0 (10066334784 + pOff + 16 + l0Bytes i) 32
    else if 2 ≤ prev ∧ prev ≤ 14 then
      proofDigest30 s0 (10066334784 + pOff + 16 + l0Bytes i + 32 + binPathOff (i.val / 3) (prev - 2))
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

/-! #### Per-Position Sub-Phases (`pc[17..248]`) -/

private def leafTagInstrs : List Instr :=
  [.ADDI .x25 .x25 16#12, .SLLI .x6 .x20 8#6, .ADDI .x7 .x0 1#12,
   .SLLI .x7 .x7 11#6, .ADDI .x7 .x7 2024#12, .ADD .x6 .x6 .x7]

/-- Phase 1A: read 16B salt and execute the 4-call overlap leaf chain (`pc[17..100]` -> `pc[101]`). -/
theorem step_pos_leaf (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff rem : Nat) (hord : ord < input.positions.card)
    (hpeven : pOff % 2 = 0) (hple : pOff ≤ input.proof.length)
    (s : MachineState) (hpc : s.pc = pcWord 17)
    (hfix : CheckFixedRegs s input.proof.length)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + pOff))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pw := parsePartialWitness s0 pOff (posAt input.positions ord) (valAt input ord)
    PhaseOutcome oracle s 105 4 (input.proof.length < pOff + 16)
      (fun s' q tr =>
        q = 4 ∧
        pOff + 16 ≤ input.proof.length ∧
        s'.pc = pcWord 101 ∧
        CheckFixedRegs s' input.proof.length ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val ∧
        s'.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) ∧
        s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = leafDigest c96 pw.index pw.salt pw.value ∧
        ∀ x ∈ pw.leafInputs c96, InTrace h768 oracle tr x) := by
  intro s0 c96 pw
  have hplen_bd : input.proof.length ≤ 8422172696 := hvalid
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hi_lt : (posAt input.positions ord).val < 16777216 := (posAt input.positions ord).isLt
  -- pc[17]: LD x20, 0(x24)
  have ha17 : s.getReg .x24 + signExtend12 0#12 = BitVec.ofNat 64 (5637149760 + 8 * ord) := by
    rw [hx24, se12_0, BitVec.add_zero]
  have hv17 : memoryArgumentsValid s (.LD .x20 .x24 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha17]
    exact accessValid_ofNat (5637149760 + 8 * ord) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst17 := step_ordinary oracle s 17 (.LD .x20 .x24 0#12) (by decide) hpc rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv17])
  let s1 := execInstrBr s (.LD .x20 .x24 0#12)
  have hpc1 : s1.pc = pcWord 18 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hidx_mem : s.getMem (BitVec.ofNat 64 (5637149760 + 8 * ord)) =
      BitVec.ofNat 64 (posAt input.positions ord).val := by
    rw [hhigh.getMem_eq (by omega) (by omega) (by omega), check_initial_index input ord hord,
      posAt_val input.positions ord hord]
  have hx20_1 : s1.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha17]
    rw [MachineState.getReg_setReg_eq (by decide), hidx_mem]
  have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (10066334784 + pOff) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25), hx25]
  -- pc[18]: ADDI x6, x25, 16
  have hst18 := step_ordinary oracle s1 18 (.ADDI .x6 .x25 16#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x6 .x25 16#12)
  have hpc2 : s2.pc = pcWord 19 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (10066334784 + pOff + 16) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx25_1, se12_16]
    change BitVec.ofNat 64 (10066334784 + pOff) + BitVec.ofNat 64 16 = _
    exact bv64_add _ 16
  have hx31_2 : s2.getReg .x31 = BitVec.ofNat 64 (10066334784 + input.proof.length) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x31), hfix.x31]
  -- pc[19]: BLTU x31, x6, pc[336]
  have hst19 := step_ordinary oracle s2 19 (.BLTU .x31 .x6 1268#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BLTU .x31 .x6 1268#13)
  have hult : BitVec.ult (s2.getReg .x31) (s2.getReg .x6) = decide (input.proof.length < pOff + 16) := by
    rw [hx31_2, hx6_2, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pOff + 16
  · have hpc3 : s3.pc = pcWord 336 := by
      simp only [s3, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc2]; decide
    exact .rejected 6 0 [] hshort (by decide) (by decide)
      (by simpa using ((hst17.trans hst18).trans hst19).halt (halt_reject oracle s3 hpc3))
  · have hge16 : pOff + 16 ≤ input.proof.length := by omega
    have hpc3 : s3.pc = pcWord 20 := by
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
    -- pc[20]: ADDI x12, x21, 0; pc[21]: JAL x1, chk_read16 (pc[339])
    have hst20 := step_ordinary oracle s3 20 (.ADDI .x12 .x21 0#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ADDI .x12 .x21 0#12)
    have hpc4 : s4.pc = pcWord 21 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hst21 := step_ordinary oracle s4 21 (.JAL .x1 1272#21) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.JAL .x1 1272#21)
    have hpc5 : s5.pc = pcWord 339 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4]; decide
    have hret5 : s5.getReg .x1 = pcWord 22 := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC, hpc4, pcWord_add_four]
      exact MachineState.getReg_setReg_eq (by decide)
    have hsrc5 : s5.getReg .x25 = BitVec.ofNat 64 (10066334784 + pOff) := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x25), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
        hreg3 .x25 (by decide) (by decide), hx25]
    have hdst5 : s5.getReg .x12 = BitVec.ofNat 64 256 := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x12)]
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x21 (by decide) (by decide), hfix.x21,
        se12_0, BitVec.add_zero]
    have hmem5 : s5.mem = s.mem := by
      simpa [s5, s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
    obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
      step_chk_read16 oracle s5 22 (10066334784 + pOff) 256 hpc5 hret5 (by decide) hsrc5 hdst5
        (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide)
        (by omega)
    have hsalt6 : readBuffer s6 256 16 = pw.salt := by
      unfold pw parsePartialWitness
      apply readBuffer_congr2
      intro j hj
      have h5s : s5.getByte (BitVec.ofNat 64 (10066334784 + pOff + j)) =
          s.getByte (BitVec.ofNat 64 (10066334784 + pOff + j)) := by
        simp only [MachineState.getByte, MachineState.getMem, hmem5]
      exact (hcopy6 j hj).trans (h5s.trans (hhigh (10066334784 + pOff + j) (by omega) (by omega)))
    -- pc[22..27]: advance x25 by 16 and compute leafTag in x6
    have hcode_lt : ∀ i (hi : i < leafTagInstrs.length), checkInstr (22 + i) = .base (leafTagInstrs[i]'hi) := by
      intro i hi; have hi' : i < 6 := hi; interval_cases i <;> rfl
    have hpure_lt : ∀ i (hi : i < leafTagInstrs.length),
        Instruction.base (leafTagInstrs[i]'hi) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (leafTagInstrs[i]'hi)) = some (execInstrBr st (leafTagInstrs[i]'hi)) ∧
              (execInstrBr st (leafTagInstrs[i]'hi)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (leafTagInstrs[i]'hi)).mem = st.mem := by
      intro i hi; have hi' : i < 6 := hi; interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs7, hpc7, hmem7⟩ := step_pure_list oracle 22 leafTagInstrs s6 (by decide) hcode_lt hpure_lt hpc6
    let s7 := runInstrs s6 leafTagInstrs
    have hs7 : StepsTo oracle s6 s7 6 0 [] := hs7
    have hpc7 : s7.pc = pcWord 28 := hpc7
    have hx20_6 : s6.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
      rw [hreg6 .x20 (by decide)]
      have h53 : s5.getReg .x20 = s3.getReg .x20 := by
        simp only [s5, s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
          ne_eq, decide_not, not_false_eq_true, reduceCtorEq]
      have h32 : s3.getReg .x20 = s2.getReg .x20 := by
        simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      rw [h53, h32]
      simp only [s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, hx20_1]
    have hx6_7 : s7.getReg .x6 = leafTag (posAt input.positions ord) := by
      have htag : BitVec.ofNat 64 (posAt input.positions ord).val <<< 8 +
          ((0#64 + signExtend12 1#12) <<< 11 + signExtend12 2024#12) =
          leafTag (posAt input.positions ord) := by
        rw [bv64_shl _ 8 (by omega), show ((0#64 + signExtend12 1#12) <<< 11 + signExtend12 2024#12) =
          BitVec.ofNat 64 4072 by decide, bv64_add]
        unfold leafTag; congr 1 <;> omega
      simpa only [s7, runInstrs, leafTagInstrs, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hx20_6, getReg_x0,
        show (8#6 : BitVec 6).toNat = 8 by decide, show (11#6 : BitVec 6).toNat = 11 by decide] using htag
    have hx21_7 : s7.getReg .x21 = 256#64 := by
      have : s7.getReg .x21 = s6.getReg .x21 := by
        simp only [s7, runInstrs, leafTagInstrs, List.foldl, execInstrBr,
          MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, decide_not,
          not_false_eq_true, reduceCtorEq]
      rw [this, hreg6 .x21 (by decide)]
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x21), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21),
        hreg3 .x21 (by decide) (by decide), hfix.x21]
    -- pc[28]: SD x21, x6, 16
    have ha28 : s7.getReg .x21 + signExtend12 16#12 = BitVec.ofNat 64 272 := by
      rw [hx21_7, se12_16]; decide
    have hv28 : memoryArgumentsValid s7 (.SD .x21 .x6 16#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha28]
      exact accessValid_ofNat 272 8 (by unfold MEMORY_BYTES; decide) (by decide)
    have hst28 := step_ordinary oracle s7 28 (.SD .x21 .x6 16#12) (by decide) hpc7 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv28])
    let s8 := execInstrBr s7 (.SD .x21 .x6 16#12)
    have hpc8 : s8.pc = pcWord 29 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
    have hreg8_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x20 → r ≠ .x25 →
        s8.getReg r = s.getReg r := by
      intro r hr1 hr6 hr7 hr12 hr20 hr25
      have h87 : s8.getReg r = s7.getReg r := by
        simp [s8, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [h87]
      have h76 : s7.getReg r = s6.getReg r := by
        simp only [s7, runInstrs, leafTagInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ hr6.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ hr7.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ hr7.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ hr7.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ hr6.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ hr25.symm]
      rw [h76, hreg6 r hr6]
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr1.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ hr12.symm]
      exact hreg3 r hr6 hr20
    have hout_s8 : MemEqOutside s s8 256 280 := by
      have h87 : MemEqOutside s7 s8 272 280 := by
        intro a ha hout
        simp only [s8, execInstrBr, ha28, MachineState.getByte, MachineState.getMem_setPC]
        exact setMem_getByte_ofNat s7 272 a _ (by decide) (by decide) ha hout
      exact ((MemEqOutside.of_mem_eq hmem5 256 280).trans
        ((hout6.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem7 256 280).trans (h87.mono (by omega) (by omega)))))
    have hsalt8 : readBuffer s8 256 16 = pw.salt := by
      have h87 : MemEqOutside s7 s8 272 280 := by
        intro a ha hout
        simp only [s8, execInstrBr, ha28, MachineState.getByte, MachineState.getMem_setPC]
        exact setMem_getByte_ofNat s7 272 a _ (by decide) (by decide) ha hout
      rw [h87.readBuffer_eq (by decide) (by omega),
        (MemEqOutside.of_mem_eq hmem7 272 280).readBuffer_eq (by decide) (by omega), hsalt6]
    have htag8 : readBuffer s8 272 8 = leafTag (posAt input.positions ord) := by
      rw [readBuffer_word s8 272 (by decide)]
      simp only [s8, execInstrBr, ha28, MachineState.getMem_setPC, MachineState.getMem_setMem_eq, hx6_7]
    -- pc[29..46]: copy 9 dwords (72 bytes) from x8 + 0 to x21 + 24
    have hc0 : ∀ j < 9,
        checkInstr (29 + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (0 + 8 * j))) ∧
        checkInstr (29 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (24 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s9, hs9, hpc9, hreg9, hcopy9, hout9⟩ :=
      step_copy_dwords oracle 29 9 .x8 .x21 0 24 s8 (5771367488 + 256 * ord) 256
        (by decide) (by decide) (by decide) (by decide) (by decide) hc0 hpc8
        ((hreg8_base .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        ((hreg8_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
        (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
    -- pc[47..49]: a0=256, a2=256, ECALL (Call 0)
    have hst47 := step_ordinary oracle s9 47 (.ADDI .x10 .x21 0#12) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.ADDI .x10 .x21 0#12)
    have hpc10 : s10.pc = pcWord 48 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
    have hst48 := step_ordinary oracle s10 48 (.ADDI .x12 .x21 0#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
    let s11 := execInstrBr s10 (.ADDI .x12 .x21 0#12)
    have hpc11 : s11.pc = pcWord 49 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
    have hmem11 : s11.mem = s9.mem := by simp [s11, s10, execInstrBr, mem_setPC, mem_setReg]
    have hinp0 : readBuffer s11 256 96 = leafCall0Input pw.index pw.salt pw.value := by
      rw [(MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega), readBuffer_call0]
      have h16 : readBuffer s9 256 16 = pw.salt :=
        (hout9.readBuffer_eq (by decide) (by omega)).trans hsalt8
      have h8 : readBuffer s9 272 8 = leafTag pw.index :=
        (hout9.readBuffer_eq (by decide) (by omega)).trans htag8
      have h72 : readBuffer s9 280 72 = pw.value.extractLsb' 0 576 := by
        have hval0 : readBuffer s0 (5771367488 + 256 * ord) 72 = pw.value.extractLsb' 0 576 := by
          have := check_initial_value_slice input ord 0 72 hord (by decide)
          simpa only [Nat.add_zero, Nat.mul_zero, pw, parsePartialWitness, valAt, dif_pos hord] using this
        rw [← hval0]
        apply readBuffer_congr2; intro j hj
        rw [hcopy9 j hj]
        exact (hhigh.trans (hout_s8.mono (by omega) (by omega))) (5771367488 + 256 * ord + j) (by omega) (by omega)
      rw [h16, h8, h72]; rfl
    have hreg11_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x25 →
        s11.getReg r = s.getReg r := by
      intro r hr1 hr6 hr7 hr10 hr12 hr20 hr25
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ hr10.symm, hreg9 r hr6]
      exact hreg8_base r hr1 hr6 hr7 hr12 hr20 hr25
    have hx10_11 : s11.getReg .x10 = BitVec.ofNat 64 256 := by
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide), hreg9 .x21 (by decide),
        hreg8_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfix.x21, se12_0, BitVec.add_zero]
    have hx12_11 : s11.getReg .x12 = BitVec.ofNat 64 256 := by
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21), hreg9 .x21 (by decide),
        hreg8_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfix.x21, se12_0, BitVec.add_zero]
    have hec0 := step_ecall_compress h768 oracle s11 49 256 256 (by decide) hpc11 rfl
      ((hreg11_base .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5)
      ((hreg11_base .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11)
      ((hreg11_base .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13)
      hx10_11 hx12_11 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
    rw [hinp0] at hec0
    let cv0 := c96 (leafCall0Input pw.index pw.salt pw.value)
    let s12 := writeBits s11 (BitVec.ofNat 64 256) cv0
    have hpc12 : s12.pc = pcWord 50 := by
      simp only [s12, writeBits, MachineState.setPC, hpc11, pcWord_add_four]
    have hcv0 : readBuffer s12 256 32 = cv0 := writeBits_readBuffer_digest s11 256 cv0
    have hout_s12 : MemEqOutside s s12 256 352 :=
      (hout_s8.mono (by omega) (by omega)).trans
        ((hout9.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem11 256 352).trans
            ((MemEqOutside_writeBits_digest s11 256 cv0 (by decide)).mono (by omega) (by omega))))
    have hreg12 : ∀ r, s12.getReg r = s11.getReg r := fun r => writeBits_register s11 _ cv0 r
    -- Helper for Calls 1, 2, 3 (each: copy 8 dwords from x8 + off -> x21 + 32, then ECALL)
    have hchain_step : ∀ (st : MachineState) (baseVal offVal : Nat) (cvIn : Digest),
        baseVal + 17 ≤ 101 → offVal + 64 ≤ 256 → offVal % 8 = 0 →
        (∀ j < 8,
          checkInstr (baseVal + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (offVal + 8 * j))) ∧
          checkInstr (baseVal + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j)))) →
        checkInstr (baseVal + 16) = .base .ECALL →
        st.pc = pcWord baseVal →
        st.getReg .x5 = 0#64 → st.getReg .x11 = 96#64 → st.getReg .x13 = 0#64 →
        st.getReg .x10 = 256#64 → st.getReg .x12 = 256#64 → st.getReg .x21 = 256#64 →
        st.getReg .x8 = BitVec.ofNat 64 (5771367488 + 256 * ord) →
        HighMemPreserved s0 st →
        readBuffer st 256 32 = cvIn →
        let inp := pw.value.extractLsb' (8 * offVal) 512 ++ cvIn
        ∃ st', StepsTo oracle st st' 17 1 [(inp.cast h768.symm, c96 inp)] ∧
          st'.pc = pcWord (baseVal + 17) ∧
          (∀ r, r ≠ .x6 → st'.getReg r = st.getReg r) ∧
          MemEqOutside st st' 256 352 ∧
          readBuffer st' 256 32 = c96 inp := by
      intro st baseVal offVal cvIn hbv hoff hof_al hcd hec hpc_st hx5 hx11 hx13 hx10 hx12 hx21 hx8_st hhi_st hcv_st inp
      obtain ⟨st1, hst_cp, hpc_cp, hreg_cp, hcopy_cp, hout_cp⟩ :=
        step_copy_dwords oracle baseVal 8 .x8 .x21 offVal 32 st (5771367488 + 256 * ord) 256
          (by decide) (by decide) (by omega) (by decide) (by omega) hcd hpc_st hx8_st hx21
          (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hinp_st : readBuffer st1 256 96 = inp := by
        rw [read_leaf_query]
        have hlo : readBuffer st1 256 32 = cvIn :=
          (hout_cp.readBuffer_eq (by decide) (by omega)).trans hcv_st
        have hhi64 : readBuffer st1 288 64 = pw.value.extractLsb' (8 * offVal) 512 := by
          have hval : readBuffer s0 (5771367488 + 256 * ord + offVal) 64 =
              pw.value.extractLsb' (8 * offVal) 512 := by
            simpa only [pw, parsePartialWitness, valAt, dif_pos hord] using
              check_initial_value_slice input ord offVal 64 hord hoff
          rw [← hval]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy_cp j hj
          rw [show 288 + j = 256 + 32 + j by omega]
          exact hc.trans (hhi_st (5771367488 + 256 * ord + offVal + j) (by omega) (by omega))
        rw [hlo, hhi64]
      have hec_st := step_ecall_compress h768 oracle st1 (baseVal + 16) 256 256 (by omega) hpc_cp hec
        ((hreg_cp .x5 (by decide)).trans hx5) ((hreg_cp .x11 (by decide)).trans hx11)
        ((hreg_cp .x13 (by decide)).trans hx13) ((hreg_cp .x10 (by decide)).trans hx10)
        ((hreg_cp .x12 (by decide)).trans hx12) (by decide) (by decide)
        (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [hinp_st] at hec_st
      let st2 := writeBits st1 (BitVec.ofNat 64 256) (c96 inp)
      refine ⟨st2, (hst_cp.trans hec_st).eq_of rfl rfl rfl rfl, ?_, ?_, ?_, writeBits_readBuffer_digest st1 256 (c96 inp)⟩
      · simp only [st2, writeBits, MachineState.setPC, hpc_cp, pcWord_add_four]
      · intro r hr; exact (writeBits_register st1 _ _ r).trans (hreg_cp r hr)
      · exact (hout_cp.mono (by omega) (by omega)).trans
          ((MemEqOutside_writeBits_digest st1 256 (c96 inp) (by decide)).mono (by omega) (by omega))
    -- Call 1 (pc[50..66]), Call 2 (pc[67..83]), Call 3 (pc[84..100])
    have hc1 : ∀ j < 8,
        checkInstr (50 + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (72 + 8 * j))) ∧
        checkInstr (50 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s13, hs13, hpc13, hreg13, hout13, hcv1⟩ :=
      hchain_step s12 50 72 cv0 (by decide) (by decide) (by decide) hc1 rfl hpc12
        ((hreg12 .x5).trans ((hreg11_base .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5))
        ((hreg12 .x11).trans ((hreg11_base .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11))
        ((hreg12 .x13).trans ((hreg11_base .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13))
        ((hreg12 .x10).trans hx10_11) ((hreg12 .x12).trans hx12_11)
        ((hreg12 .x21).trans ((hreg11_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
        ((hreg12 .x8).trans ((hreg11_base .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8))
        (hhigh.trans (hout_s12.mono (by omega) (by omega))) hcv0
    have hc2 : ∀ j < 8,
        checkInstr (67 + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (136 + 8 * j))) ∧
        checkInstr (67 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s14, hs14, hpc14, hreg14, hout14, hcv2⟩ :=
      hchain_step s13 67 136 _ (by decide) (by decide) (by decide) hc2 rfl hpc13
        ((hreg13 .x5 (by decide)).trans ((hreg12 .x5).trans ((hreg11_base .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5)))
        ((hreg13 .x11 (by decide)).trans ((hreg12 .x11).trans ((hreg11_base .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11)))
        ((hreg13 .x13 (by decide)).trans ((hreg12 .x13).trans ((hreg11_base .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13)))
        ((hreg13 .x10 (by decide)).trans ((hreg12 .x10).trans hx10_11))
        ((hreg13 .x12 (by decide)).trans ((hreg12 .x12).trans hx12_11))
        ((hreg13 .x21 (by decide)).trans ((hreg12 .x21).trans ((hreg11_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)))
        ((hreg13 .x8 (by decide)).trans ((hreg12 .x8).trans ((hreg11_base .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)))
        (hhigh.trans ((hout_s12.trans hout13).mono (by omega) (by omega))) hcv1
    have hc3 : ∀ j < 8,
        checkInstr (84 + 2 * j) = .base (.LD .x6 .x8 (BitVec.ofNat 12 (192 + 8 * j))) ∧
        checkInstr (84 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
      intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
    obtain ⟨s15, hs15, hpc15, hreg15, hout15, hcv3⟩ :=
      hchain_step s14 84 192 _ (by decide) (by decide) (by decide) hc3 rfl hpc14
        ((hreg14 .x5 (by decide)).trans ((hreg13 .x5 (by decide)).trans ((hreg12 .x5).trans ((hreg11_base .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5))))
        ((hreg14 .x11 (by decide)).trans ((hreg13 .x11 (by decide)).trans ((hreg12 .x11).trans ((hreg11_base .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11))))
        ((hreg14 .x13 (by decide)).trans ((hreg13 .x13 (by decide)).trans ((hreg12 .x13).trans ((hreg11_base .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13))))
        ((hreg14 .x10 (by decide)).trans ((hreg13 .x10 (by decide)).trans ((hreg12 .x10).trans hx10_11)))
        ((hreg14 .x12 (by decide)).trans ((hreg13 .x12 (by decide)).trans ((hreg12 .x12).trans hx12_11)))
        ((hreg14 .x21 (by decide)).trans ((hreg13 .x21 (by decide)).trans ((hreg12 .x21).trans ((hreg11_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))))
        ((hreg14 .x8 (by decide)).trans ((hreg13 .x8 (by decide)).trans ((hreg12 .x8).trans ((hreg11_base .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8))))
        (hhigh.trans (((hout_s12.trans hout13).trans hout14).mono (by omega) (by omega))) hcv2
    -- Compose all steps (3 + 2 + 17 + 6 + 1 + 18 + 2 + 1 + 17 + 17 + 17 = 101 steps, 4 calls)
    have hpre : StepsTo oracle s s12 50 1 [((leafCall0Input pw.index pw.salt pw.value).cast h768.symm, cv0)] := by
      have a := ((hst17.trans hst18).trans hst19).trans ((hst20.trans hst21).trans hs6)
      have b := (hs7.trans hst28).trans (hs9.trans ((hst47.trans hst48).trans hec0))
      exact (a.trans b).eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl)
    have hall := hpre.trans (hs13.trans (hs14.trans hs15))
    have hreg15_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x25 →
        s15.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h20 h25 =>
      (hreg15 r h6).trans ((hreg14 r h6).trans ((hreg13 r h6).trans ((hreg12 r).trans
        (hreg11_base r h1 h6 h7 h10 h12 h20 h25))))
    have hx25_15 : s15.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16)) := by
      rw [hreg15 .x25 (by decide), hreg14 .x25 (by decide), hreg13 .x25 (by decide), hreg12 .x25]
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x25), hreg9 .x25 (by decide)]
      have h87 : s8.getReg .x25 = s7.getReg .x25 := by
        simp [s8, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [h87]
      have h76 : s7.getReg .x25 = s6.getReg .x25 + 16#64 := by
        simp only [s7, runInstrs, leafTagInstrs, List.foldl, execInstrBr,
          MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
          ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_16]
      rw [h76, hreg6 .x25 (by decide), hsrc5]
      change BitVec.ofNat 64 (10066334784 + pOff) + BitVec.ofNat 64 16 = _
      rw [bv64_add] <;> (congr 1 <;> omega)
    have hx20_15 : s15.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val := by
      rw [hreg15 .x20 (by decide), hreg14 .x20 (by decide), hreg13 .x20 (by decide), hreg12 .x20]
      simp only [s11, s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x20), MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x20), hreg9 .x20 (by decide)]
      have h87 : s8.getReg .x20 = s7.getReg .x20 := by
        simp [s8, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [h87]
      have h76 : s7.getReg .x20 = s6.getReg .x20 := by
        simp only [s7, runInstrs, leafTagInstrs, List.foldl, execInstrBr,
          MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, decide_not,
          not_false_eq_true, reduceCtorEq]
      rw [h76, hx20_6]
    refine .continued s15 (50 + (17 + (17 + 17))) (1 + (1 + (1 + 1))) _ (by decide) (by decide) hall
      ⟨rfl, hge16, hpc15, hfix.of_agree (fun r hr => hreg15_base r (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       ((hout_s12.trans hout13).trans hout14).trans hout15,
       hx20_15,
       (hreg15_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24,
       (hreg15_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8,
       hx25_15,
       (hreg15_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27,
       hcv3, ?_⟩
    intro x hx
    simp only [WitnessPath.leafInputs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (InTrace.singleton h768 oracle _).append_left
    · exact ((InTrace.singleton h768 oracle _).append_left).append_right
    · exact (((InTrace.singleton h768 oracle _).append_left).append_right).append_right
    · exact (((InTrace.singleton h768 oracle _).append_right).append_right).append_right

private def l0SetupInstrs : List Instr :=
  [.ADDI .x7 .x0 3#12, .DIVU .x22 .x20 .x7, .REMU .x23 .x20 .x7,
   .ADDI .x6 .x0 1#12, .SLLI .x6 .x6 11#6, .ADDI .x6 .x6 682#12,
   .SLLI .x6 .x6 11#6, .ADDI .x6 .x6 1365#12]

/-- Phase 1B: L0 3-ary step (`pc[101..153]` -> `pc[154]`). -/
theorem step_pos_l0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff rem : Nat) (hord : ord < input.positions.card)
    (hpeven : pOff % 2 = 0) (hple : pOff + 16 ≤ input.proof.length)
    (s : MachineState) (hpc : s.pc = pcWord 101)
    (hfix : CheckFixedRegs s input.proof.length)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (posAt input.positions ord).val)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16)))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hleaf : readBuffer s 256 32 =
      leafDigest (fun x => oracle.compression (x.cast h768.symm))
        (posAt input.positions ord)
        (parsePartialWitness (submission.initialState .check input) pOff (posAt input.positions ord) (valAt input ord)).salt
        (valAt input ord)) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 pOff i (valAt input ord)
    PhaseOutcome oracle s 105 1 (input.proof.length < pOff + 16 + l0Bytes i)
      (fun s' q tr =>
        q ≤ 1 ∧
        pOff + 16 + l0Bytes i ≤ input.proof.length ∧
        s'.pc = pcWord 154 ∧
        CheckFixedRegs s' input.proof.length ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) ∧
        s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16 + l0Bytes i)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalL1 c96 ∧
        (i.val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96))) := by
  intro s0 c96 i pw
  have hplen_bd : input.proof.length ≤ 8422172696 := hvalid
  have hi_lt : i.val < 16777216 := i.isLt
  have hcode1 : ∀ j (hj : j < l0SetupInstrs.length), checkInstr (101 + j) = .base (l0SetupInstrs[j]'hj) := by
    intro j hj; have hj' : j < 8 := hj; interval_cases j <;> rfl
  have hpure1 : ∀ j (hj : j < l0SetupInstrs.length),
      Instruction.base (l0SetupInstrs[j]'hj) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (l0SetupInstrs[j]'hj)) = some (execInstrBr st (l0SetupInstrs[j]'hj)) ∧
            (execInstrBr st (l0SetupInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (l0SetupInstrs[j]'hj)).mem = st.mem := by
    intro j hj; have hj' : j < 8 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs1, hpc1, hmem1⟩ := step_pure_list oracle 101 l0SetupInstrs s (by decide) hcode1 hpure1 hpc
  let s1 := runInstrs s l0SetupInstrs
  have hs1 : StepsTo oracle s s1 8 0 [] := hs1
  have hpc1 : s1.pc = pcWord 109 := hpc1
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
  -- pc[109]: BEQ x22, x6, pc[154]
  have hst109 := step_ordinary oracle s1 109 (.BEQ .x22 .x6 180#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BEQ .x22 .x6 180#13)
  have heq_full : (s1.getReg .x22 == s1.getReg .x6) = decide (i.val / 3 = FULL_TRIPLETS) := by
    rw [hx22_1, hx6_1]
    exact bv64_beq_eq _ _ (by omega) (by rw [full_triplets_eq]; decide)
  by_cases hfull : i.val / 3 = FULL_TRIPLETS
  · have hl0 : l0Bytes i = 0 := by unfold l0Bytes; exact if_pos hfull
    have hpc2 : s2.pc = pcWord 154 := by
      simp only [s2, execInstrBr, heq_full, hfull, decide_true, ite_true, MachineState.setPC, hpc1]; decide
    have hmem2 : s2.mem = s.mem := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.setPC] using hmem1
    have hreg2 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x23 → s2.getReg r = s.getReg r := by
      intro r h6 h7 h22 h23
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hreg1 r h6 h7 h22 h23
    have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (i.val / 3) := by
      simpa [s2, execInstrBr, heq_full, hfull, MachineState.getReg_setPC] using hx22_1
    refine .continued s2 9 0 [] (by decide) (by decide) (by simpa using hs1.trans hst109)
      ⟨by decide, by rw [hl0, Nat.add_zero]; exact hple, hpc2,
       hfix.of_agree (fun r hr => hreg2 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
         (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
       MemEqOutside.of_mem_eq hmem2 256 352,
       hx22_2,
       (hreg2 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24,
       (hreg2 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8,
       by rw [hl0, Nat.add_zero]; exact (hreg2 .x25 (by decide) (by decide) (by decide) (by decide)).trans hx25,
       (hreg2 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27,
       ?_, fun hne => (hne hfull).elim⟩
    rw [(MemEqOutside.of_mem_eq hmem2 0 0).readBuffer_eq (by decide) (by omega), hleaf]
    simp only [WitnessPath.evalL1, pw, parsePartialWitness, hfull, ite_true]; rfl
  · -- Full triplet: l0Bytes i = 64
    have hl0 : l0Bytes i = 64 := by unfold l0Bytes; exact if_neg hfull
    have hpc2 : s2.pc = pcWord 110 := by
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
    -- pc[110]: ADDI x6, x25, 64; pc[111]: BLTU x31, x6, pc[336]
    have hst110 := step_ordinary oracle s2 110 (.ADDI .x6 .x25 64#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x6 .x25 64#12)
    have hpc3 : s3.pc = pcWord 111 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (10066334784 + (pOff + 16) + 64) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        hreg2 .x25 (by decide) (by decide) (by decide) (by decide), hx25, se12_64]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 64 = _
      exact bv64_add _ 64
    have hx31_3 : s3.getReg .x31 = BitVec.ofNat 64 (10066334784 + input.proof.length) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
        hreg2 .x31 (by decide) (by decide) (by decide) (by decide), hfix.x31]
    have hst111 := step_ordinary oracle s3 111 (.BLTU .x31 .x6 900#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.BLTU .x31 .x6 900#13)
    have hult : BitVec.ult (s3.getReg .x31) (s3.getReg .x6) = decide (input.proof.length < pOff + 16 + 64) := by
      rw [hx31_3, hx6_3, bv64_ult_eq _ _ (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases hshort : input.proof.length < pOff + 16 + 64
    · have hpc4 : s4.pc = pcWord 336 := by
        simp only [s4, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc3]; decide
      exact .rejected 14 0 [] (by rw [hl0]; exact hshort) (by decide) (by decide)
        (by simpa using ((hs1.trans hst109).trans (hst110.trans hst111)).halt (halt_reject oracle s4 hpc4))
    · have hge64 : pOff + 16 + 64 ≤ input.proof.length := by omega
      have hpc4 : s4.pc = pcWord 112 := by
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
      -- Common finish from pc[151] once S[0..96) = pw.l0Input c96
      have hfinish : ∀ (s151 : MachineState) (kMid : Nat),
          kMid ≤ 90 →
          StepsTo oracle s4 s151 kMid 0 [] →
          s151.pc = pcWord 151 →
          CheckFixedRegs s151 input.proof.length →
          MemEqOutside s4 s151 256 352 →
          s151.getReg .x22 = BitVec.ofNat 64 (i.val / 3) →
          s151.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) →
          s151.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) →
          s151.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16 + 64)) →
          s151.getReg .x27 = BitVec.ofNat 64 rem →
          readBuffer s151 256 96 = pw.l0Input c96 →
          PhaseOutcome oracle s 105 1 (input.proof.length < pOff + 16 + l0Bytes i)
            (fun s' q tr =>
              q ≤ 1 ∧ pOff + 16 + l0Bytes i ≤ input.proof.length ∧ s'.pc = pcWord 154 ∧ CheckFixedRegs s' input.proof.length ∧
              MemEqOutside s s' 256 352 ∧ s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
              s'.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) ∧
              s'.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) ∧
              s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16 + l0Bytes i)) ∧
              s'.getReg .x27 = BitVec.ofNat 64 rem ∧
              readBuffer s' 256 32 = pw.evalL1 c96 ∧
              (i.val / 3 ≠ FULL_TRIPLETS → InTrace h768 oracle tr (pw.l0Input c96))) := by
        intro s151 kMid hkMid hmid hpc151 hfix151 hout151 h22 h24 h8 h25 h27 hinp151
        have hst151 := step_ordinary oracle s151 151 (.ADDI .x10 .x21 0#12) (by decide) hpc151 rfl (by intro h; cases h) rfl
        let s152 := execInstrBr s151 (.ADDI .x10 .x21 0#12)
        have hpc152 : s152.pc = pcWord 152 := by simp only [s152, execInstrBr, MachineState.setPC, hpc151, pcWord_add_four]
        have hst152 := step_ordinary oracle s152 152 (.ADDI .x12 .x21 0#12) (by decide) hpc152 rfl (by intro h; cases h) rfl
        let s153 := execInstrBr s152 (.ADDI .x12 .x21 0#12)
        have hpc153 : s153.pc = pcWord 153 := by simp only [s153, execInstrBr, MachineState.setPC, hpc152, pcWord_add_four]
        have hmem153 : s153.mem = s151.mem := by simp [s153, s152, execInstrBr, mem_setPC, mem_setReg]
        have hreg153 : ∀ r, r ≠ .x10 → r ≠ .x12 → s153.getReg r = s151.getReg r := fun r h10 h12 => by
          simp only [s153, s152, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
        have hx10_153 : s153.getReg .x10 = 256#64 := by
          simp only [s153, s152, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide), hfix151.x21, se12_0, BitVec.add_zero]
        have hx12_153 : s153.getReg .x12 = 256#64 := by
          simp only [s153, s152, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
            hfix151.x21, se12_0, BitVec.add_zero]
        have hec := step_ecall_compress h768 oracle s153 153 256 256 (by decide) hpc153 rfl
          ((hreg153 .x5 (by decide) (by decide)).trans hfix151.x5)
          ((hreg153 .x11 (by decide) (by decide)).trans hfix151.x11)
          ((hreg153 .x13 (by decide) (by decide)).trans hfix151.x13)
          hx10_153 hx12_153 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
        rw [(MemEqOutside.of_mem_eq hmem153 0 0).readBuffer_eq (by decide) (by omega), hinp151] at hec
        let sFin := writeBits s153 (BitVec.ofNat 64 256) (c96 (pw.l0Input c96))
        have hpcFin : sFin.pc = pcWord 154 := by simp only [sFin, writeBits, MachineState.setPC, hpc153, pcWord_add_four]
        have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → sFin.getReg r = s151.getReg r := fun r h10 h12 =>
          (writeBits_register s153 _ _ r).trans (hreg153 r h10 h12)
        have htot := (((hs1.trans hst109).trans (hst110.trans hst111)).trans hmid).trans
          ((hst151.trans hst152).trans hec)
        refine .continued sFin (11 + kMid + 3) 1 [((pw.l0Input c96).cast h768.symm, c96 (pw.l0Input c96))]
          (by omega) (by decide)
          (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
          ⟨by decide, by rw [hl0]; exact hge64, hpcFin,
           hfix151.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
           (MemEqOutside.of_mem_eq hmem4 256 352).trans
             (hout151.trans ((MemEqOutside.of_mem_eq hmem153 256 352).trans
               ((MemEqOutside_writeBits_digest s153 256 _ (by decide)).mono (by omega) (by omega)))),
           (hregFin .x22 (by decide) (by decide)).trans h22,
           (hregFin .x24 (by decide) (by decide)).trans h24,
           (hregFin .x8  (by decide) (by decide)).trans h8,
           by rw [hl0]; exact (hregFin .x25 (by decide) (by decide)).trans h25,
           (hregFin .x27 (by decide) (by decide)).trans h27,
           ?_, fun _ => InTrace.singleton h768 oracle (pw.l0Input c96)⟩
        rw [writeBits_readBuffer_digest]
        simp only [WitnessPath.evalL1, pw, parsePartialWitness, hfull, ite_false]
      -- Three remainder cases: r = 0, r = 1, r = 2
      have hst112 := step_ordinary oracle s4 112 (.BEQ .x23 .x0 72#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
      let s5 := execInstrBr s4 (.BEQ .x23 .x0 72#13)
      have hleaf4 : readBuffer s4 256 32 = leafDigest c96 pw.index pw.salt pw.value :=
        ((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega)).trans hleaf
      have hhigh4 : HighMemPreserved s0 s4 := hhigh.trans (MemEqOutside.of_mem_eq hmem4 0 4294971392)
      have hsib0 : readBuffer s4 (10066334784 + pOff + 16) 32 = pw.l0Sib0 := by
        simp only [pw, parsePartialWitness, hfull, ite_false]
        exact hhigh4.readBuffer_eq (by omega) (by omega)
      have hsib1 : readBuffer s4 (10066334784 + pOff + 48) 32 = pw.l0Sib1 := by
        simp only [pw, parsePartialWitness, hfull, ite_false]
        exact hhigh4.readBuffer_eq (by omega) (by omega)
      have hrem_cases : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hrem_cases with hr0 | hr1 | hr2
      · -- Case r = 0: jump to pc[130]
        have hx23z : s4.getReg .x23 = 0#64 := by rw [hx23_4, hr0]
        have hpc5 : s5.pc = pcWord 130 := by
          simp only [s5, execInstrBr, hx23z, getReg_x0, beq_self_eq_true, ite_true,
            MachineState.setPC, hpc4]; decide
        have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
          simp [s5, execInstrBr, hx23z, getReg_x0, MachineState.getReg_setPC]
        have hmem5 : s5.mem = s4.mem := by
          simp [s5, execInstrBr, hx23z, getReg_x0, MachineState.setPC]
        have hst130 := step_ordinary oracle s5 130 (.ADDI .x12 .x21 32#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s6 := execInstrBr s5 (.ADDI .x12 .x21 32#12)
        have hpc6 : s6.pc = pcWord 131 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
        obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
          step_call_read32 oracle 131 s6 (10066334784 + (pOff + 16)) 288 (by decide) rfl rfl hpc6
            (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg5,
                  hreg4 .x25 (by decide) (by decide) (by decide) (by decide), hx25])
            (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg5,
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_32]; decide)
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hst133 := step_ordinary oracle s7 133 (.ADDI .x12 .x21 64#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
        let s8 := execInstrBr s7 (.ADDI .x12 .x21 64#12)
        have hpc8 : s8.pc = pcWord 134 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
        obtain ⟨s9, hs9, hpc9, hx25_9, hreg9, hcopy9, hout9⟩ :=
          step_call_read32 oracle 134 s8 (10066334784 + (pOff + 16) + 32) 320 (by decide) rfl rfl hpc8
            (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hx25_7])
            (by simp only [s8, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg7 .x21 (by decide) (by decide) (by decide)]
                simp only [s6, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg5,
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_64]; decide)
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hst136 := step_ordinary oracle s9 136 (.JAL .x0 60#21) (by decide) hpc9 rfl (by intro h; cases h) rfl
        let s10 := execInstrBr s9 (.JAL .x0 60#21)
        have hpc10 : s10.pc = pcWord 151 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9]; decide
        have hmem6 : s6.mem = s4.mem := by simpa [s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
        have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, mem_setPC, mem_setReg]
        have hmem10 : s10.mem = s9.mem := by simp [s10, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s4 s10 256 352 :=
          (MemEqOutside.of_mem_eq hmem6 256 352).trans
            ((hout7.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem8 256 352).trans
                ((hout9.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem10 256 352))))
        have hreg10 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s10.getReg r = s4.getReg r := fun r h1 h6 h12 h25 => by
          have h10_9 : s10.getReg r = s9.getReg r := by simp [s10, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [h10_9, hreg9 r h1 h6 h25]
          simp only [s8, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg7 r h1 h6 h25]
          simp only [s6, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg5]
        have hinp : readBuffer s10 256 96 = pw.l0Input c96 := by
          rw [readBuffer_ternary]
          have hd0 : readBuffer s10 256 32 = leafDigest c96 pw.index pw.salt pw.value := by
            have h0 : MemEqOutside s4 s10 288 352 :=
              (MemEqOutside.of_mem_eq hmem6 288 352).trans
                ((hout7.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem8 288 352).trans
                    ((hout9.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem10 288 352))))
            exact (h0.readBuffer_eq (by decide) (by omega)).trans hleaf4
          have hd1 : readBuffer s10 288 32 = pw.l0Sib0 := by
            rw [(MemEqOutside.of_mem_eq hmem10 320 352).readBuffer_eq (by decide) (by omega),
              hout9.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by decide) (by omega), ← hsib0]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy7 j hj
            simp only [MachineState.getByte, MachineState.getMem, hmem6] at hc ⊢
            simpa only [Nat.add_assoc] using hc
          have hd2 : readBuffer s10 320 32 = pw.l0Sib1 := by
            rw [(MemEqOutside.of_mem_eq hmem10 0 0).readBuffer_eq (by decide) (by omega), ← hsib1]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy9 j hj
            have h84 : MemEqOutside s4 s8 288 320 :=
              (MemEqOutside.of_mem_eq hmem6 288 320).trans (hout7.trans (MemEqOutside.of_mem_eq hmem8 288 320))
            rw [hc, show 10066334784 + (pOff + 16) + 32 + j = 10066334784 + pOff + 48 + j by omega]
            exact h84 (10066334784 + pOff + 48 + j) (by omega) (by omega)
          rw [hd0, hd1, hd2]
          simp only [WitnessPath.l0Input, show pw.index.val % 3 = 0 from hr0, ite_true]
        refine hfinish s10 74 (by decide)
          (by simpa using ((hst112.trans hst130).trans hs7).trans ((hst133.trans hs9).trans hst136))
          hpc10 (hfix.of_agree (fun r hr => (hreg10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
            (hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          hout_all
          ((hreg10 .x22 (by decide) (by decide) (by decide) (by decide)).trans hx22_4)
          ((hreg10 .x24 (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
          ((hreg10 .x8  (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
          (by have : s10.getReg .x25 = s9.getReg .x25 := by simp [s10, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
              rw [this, hx25_9]; congr 1 <;> omega)
          ((hreg10 .x27 (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
          hinp
      · -- Case r = 1: pc[112] fallthrough -> pc[113..114] jump to pc[137..150] -> pc[151]
        have hx23o : s4.getReg .x23 = 1#64 := by rw [hx23_4, hr1]
        have hpc5 : s5.pc = pcWord 113 := by
          simp only [s5, execInstrBr, hx23o, getReg_x0, show (1#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc4, pcWord_add_four]
        have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
          simp [s5, execInstrBr, hx23o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
        have hmem5 : s5.mem = s4.mem := by
          simp [s5, execInstrBr, hx23o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC]
        have hst113 := step_ordinary oracle s5 113 (.ADDI .x7 .x0 1#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s5a := execInstrBr s5 (.ADDI .x7 .x0 1#12)
        have hpc5a : s5a.pc = pcWord 114 := by simp only [s5a, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
        have hst114 := step_ordinary oracle s5a 114 (.BEQ .x23 .x7 92#13) (by decide) hpc5a rfl (by intro h; cases h) rfl
        let s5b := execInstrBr s5a (.BEQ .x23 .x7 92#13)
        have hx23_5a : s5a.getReg .x23 = 1#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x23), hreg5, hx23o]
        have hx7_5a : s5a.getReg .x7 = 1#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        have hpc5b : s5b.pc = pcWord 137 := by
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
        -- pc[137..144]: copy 4 dwords S[0..32) -> S[32..64)
        have hcp1 : ∀ j < 4,
            checkInstr (137 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (137 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
          step_copy_dwords oracle 137 4 .x21 .x21 0 32 s5b 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp1 hpc5b
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
        -- pc[145..147]: read sib0 -> S[0..32)
        have hst145 := step_ordinary oracle s6 145 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
        let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
        have hpc7 : s7.pc = pcWord 146 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
        obtain ⟨s8, hs8, hpc8, hx25_8, hreg8, hcopy8, hout8⟩ :=
          step_call_read32 oracle 146 s7 (10066334784 + (pOff + 16)) 256 (by decide) rfl rfl hpc7
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg6 .x25 (by decide),
                  hreg5b .x25 (by decide), hreg4 .x25 (by decide) (by decide) (by decide) (by decide), hx25])
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide), hreg5b .x21 (by decide),
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        -- pc[148..150]: read sib1 -> S[64..96)
        have hst148 := step_ordinary oracle s8 148 (.ADDI .x12 .x21 64#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 64#12)
        have hpc9 : s9.pc = pcWord 149 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hx25_10, hreg10, hcopy10, hout10⟩ :=
          step_call_read32 oracle 149 s9 (10066334784 + (pOff + 16) + 32) 320 (by decide) rfl rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hx25_8])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg8 .x21 (by decide) (by decide) (by decide)]
                simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg6 .x21 (by decide),
                  hreg5b .x21 (by decide), hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21,
                  se12_64]; decide)
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s4 s10 256 352 :=
          (MemEqOutside.of_mem_eq hmem5b 256 352).trans
            ((hout6.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem7 256 352).trans
                ((hout8.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem9 256 352).trans (hout10.mono (by omega) (by omega))))))
        have hreg10_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → s10.getReg r = s4.getReg r :=
          fun r h1 h6 h7 h12 h25 => by
            rw [hreg10 r h1 h6 h25]
            simp only [s9, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg8 r h1 h6 h25]
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
            rw [show 10066334784 + (pOff + 16) + j = 10066334784 + pOff + 16 + j by omega]
            exact h74 (10066334784 + pOff + 16 + j) (by omega) (by omega)
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
            rw [← hsib1]; apply readBuffer_congr2; intro j hj
            rw [hcopy10 j hj]
            have h94 : MemEqOutside s4 s9 256 320 :=
              (MemEqOutside.of_mem_eq hmem5b 256 320).trans
                ((hout6.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem7 256 320).trans
                    ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 320))))
            rw [show 10066334784 + (pOff + 16) + 32 + j = 10066334784 + pOff + 48 + j by omega]
            exact h94 (10066334784 + pOff + 48 + j) (by omega) (by omega)
          rw [hd0, hd1, hd2]
          simp only [WitnessPath.l0Input, show pw.index.val % 3 = 1 from hr1,
            show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
        refine hfinish s10 83 (by decide)
          (by simpa using (((hst112.trans hst113).trans hst114).trans hs6).trans ((hst145.trans hs8).trans (hst148.trans hs10)))
          hpc10 (hfix.of_agree (fun r hr => (hreg10_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
            (hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          hout_all
          ((hreg10_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_4)
          ((hreg10_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
          ((hreg10_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
          (by rw [hx25_10]; congr 1 <;> omega)
          ((hreg10_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
          hinp
      · -- Case r = 2: pc[112..114] fallthrough -> pc[115..129] -> pc[151]
        have hx23t : s4.getReg .x23 = 2#64 := by rw [hx23_4, hr2]
        have hpc5 : s5.pc = pcWord 113 := by
          simp only [s5, execInstrBr, hx23t, getReg_x0, show (2#64 == 0#64) = false by decide,
            Bool.false_eq_true, ite_false, MachineState.setPC, hpc4, pcWord_add_four]
        have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => by
          simp [s5, execInstrBr, hx23t, getReg_x0, show (2#64 == 0#64) = false by decide, MachineState.getReg_setPC]
        have hmem5 : s5.mem = s4.mem := by
          simp [s5, execInstrBr, hx23t, getReg_x0, show (2#64 == 0#64) = false by decide, MachineState.setPC]
        have hst113 := step_ordinary oracle s5 113 (.ADDI .x7 .x0 1#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
        let s5a := execInstrBr s5 (.ADDI .x7 .x0 1#12)
        have hpc5a : s5a.pc = pcWord 114 := by simp only [s5a, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
        have hst114 := step_ordinary oracle s5a 114 (.BEQ .x23 .x7 92#13) (by decide) hpc5a rfl (by intro h; cases h) rfl
        let s5b := execInstrBr s5a (.BEQ .x23 .x7 92#13)
        have hx23_5a : s5a.getReg .x23 = 2#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x23), hreg5, hx23t]
        have hx7_5a : s5a.getReg .x7 = 1#64 := by
          simp only [s5a, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
        have hpc5b : s5b.pc = pcWord 115 := by
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
        -- pc[115..122]: copy 4 dwords S[0..32) -> S[64..96)
        have hcp2 : ∀ j < 4,
            checkInstr (115 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
            checkInstr (115 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (64 + 8 * j))) := by
          intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
        obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
          step_copy_dwords oracle 115 4 .x21 .x21 0 64 s5b 256 256 (by decide) (by decide)
            (by decide) (by decide) (by decide) hcp2 hpc5b
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            ((hreg5b .x21 (by decide)).trans ((hreg4 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
            (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
        -- pc[123..125]: read sib0 -> S[0..32)
        have hst123 := step_ordinary oracle s6 123 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
        let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
        have hpc7 : s7.pc = pcWord 124 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
        obtain ⟨s8, hs8, hpc8, hx25_8, hreg8, hcopy8, hout8⟩ :=
          step_call_read32 oracle 124 s7 (10066334784 + (pOff + 16)) 256 (by decide) rfl rfl hpc7
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg6 .x25 (by decide),
                  hreg5b .x25 (by decide), hreg4 .x25 (by decide) (by decide) (by decide) (by decide), hx25])
            (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide), hreg5b .x21 (by decide),
                  hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        -- pc[126..128]: read sib1 -> S[32..64)
        have hst126 := step_ordinary oracle s8 126 (.ADDI .x12 .x21 32#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
        let s9 := execInstrBr s8 (.ADDI .x12 .x21 32#12)
        have hpc9 : s9.pc = pcWord 127 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
        obtain ⟨s10, hs10, hpc10, hx25_10, hreg10, hcopy10, hout10⟩ :=
          step_call_read32 oracle 127 s9 (10066334784 + (pOff + 16) + 32) 288 (by decide) rfl rfl hpc9
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hx25_8])
            (by simp only [s9, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide), hreg8 .x21 (by decide) (by decide) (by decide)]
                simp only [s7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x21), hreg6 .x21 (by decide),
                  hreg5b .x21 (by decide), hreg4 .x21 (by decide) (by decide) (by decide) (by decide), hfix.x21,
                  se12_32]; decide)
            (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
        have hst129 := step_ordinary oracle s10 129 (.JAL .x0 88#21) (by decide) hpc10 rfl (by intro h; cases h) rfl
        let s11 := execInstrBr s10 (.JAL .x0 88#21)
        have hpc11 : s11.pc = pcWord 151 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10]; decide
        have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
        have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
        have hmem11 : s11.mem = s10.mem := by simp [s11, execInstrBr, mem_setPC, mem_setReg]
        have hout_all : MemEqOutside s4 s11 256 352 :=
          (MemEqOutside.of_mem_eq hmem5b 256 352).trans
            ((hout6.mono (by omega) (by omega)).trans
              ((MemEqOutside.of_mem_eq hmem7 256 352).trans
                ((hout8.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem9 256 352).trans
                    ((hout10.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem11 256 352))))))
        have hreg11_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → s11.getReg r = s4.getReg r :=
          fun r h1 h6 h7 h12 h25 => by
            have : s11.getReg r = s10.getReg r := by simp [s11, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            rw [this, hreg10 r h1 h6 h25]
            simp only [s9, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg8 r h1 h6 h25]
            simp only [s7, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg6 r h6, hreg5b r h7]
        have hinp : readBuffer s11 256 96 = pw.l0Input c96 := by
          rw [readBuffer_ternary]
          have hd0 : readBuffer s11 256 32 = pw.l0Sib0 := by
            rw [(MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega),
              hout10.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega), ← hsib0]
            apply readBuffer_congr2; intro j hj
            rw [hcopy8 j hj]
            have h74 : MemEqOutside s4 s7 320 352 :=
              (MemEqOutside.of_mem_eq hmem5b 320 352).trans (hout6.trans (MemEqOutside.of_mem_eq hmem7 320 352))
            rw [show 10066334784 + (pOff + 16) + j = 10066334784 + pOff + 16 + j by omega]
            exact h74 (10066334784 + pOff + 16 + j) (by omega) (by omega)
          have hd1 : readBuffer s11 288 32 = pw.l0Sib1 := by
            rw [(MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega), ← hsib1]
            apply readBuffer_congr2; intro j hj
            rw [hcopy10 j hj]
            have h94 : MemEqOutside s4 s9 256 352 :=
              (MemEqOutside.of_mem_eq hmem5b 256 352).trans
                ((hout6.mono (by omega) (by omega)).trans
                  ((MemEqOutside.of_mem_eq hmem7 256 352).trans
                    ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 352))))
            rw [show 10066334784 + (pOff + 16) + 32 + j = 10066334784 + pOff + 48 + j by omega]
            exact h94 (10066334784 + pOff + 48 + j) (by omega) (by omega)
          have hd2 : readBuffer s11 320 32 = leafDigest c96 pw.index pw.salt pw.value := by
            rw [(MemEqOutside.of_mem_eq hmem11 0 0).readBuffer_eq (by decide) (by omega),
              hout10.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega),
              hout8.readBuffer_eq (by decide) (by omega),
              (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by decide) (by omega), ← hleaf4]
            apply readBuffer_congr2; intro j hj
            have hc := hcopy6 j hj
            simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem5b] at hc ⊢
            exact hc
          rw [hd0, hd1, hd2]
          simp only [WitnessPath.l0Input, show pw.index.val % 3 = 2 from hr2,
            show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false]
        refine hfinish s11 84 (by decide)
          (by simpa using (((hst112.trans hst113).trans hst114).trans hs6).trans ((hst123.trans hs8).trans ((hst126.trans hs10).trans hst129)))
          hpc11 (hfix.of_agree (fun r hr => (hreg11_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
            (hreg4 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          hout_all
          ((hreg11_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22_4)
          ((hreg11_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x24 (by decide) (by decide) (by decide) (by decide)).trans hx24))
          ((hreg11_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x8  (by decide) (by decide) (by decide) (by decide)).trans hx8))
          (by have : s11.getReg .x25 = s10.getReg .x25 := by simp [s11, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
              rw [this, hx25_10]; congr 1 <;> omega)
          ((hreg11_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg4 .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27))
          hinp

/-- Phase 1C: L1 binary step (`pc[154..180]` -> `pc[181]`), outputting masked 240-bit L2 digest
and zeroing the gap `S[64..96)`. -/
theorem step_pos_l1 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff rem : Nat) (hord : ord < input.positions.card)
    (hpeven : pOff % 2 = 0)
    (hple : pOff + 16 + l0Bytes (posAt input.positions ord) ≤ input.proof.length)
    (s : MachineState) (hpc : s.pc = pcWord 154)
    (hfix : CheckFixedRegs s input.proof.length)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((posAt input.positions ord).val / 3))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff + 16 + l0Bytes (posAt input.positions ord))))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hl1 : readBuffer s 256 32 =
      (parsePartialWitness (submission.initialState .check input) pOff (posAt input.positions ord) (valAt input ord)).evalL1
        (fun x => oracle.compression (x.cast h768.symm))) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let pOff2 := pOff + 16 + l0Bytes i
    let pw := parsePartialWitness s0 pOff i (valAt input ord)
    PhaseOutcome oracle s 60 1 (input.proof.length < pOff2 + 32)
      (fun s' q tr =>
        q = 1 ∧
        pOff2 + 32 ≤ input.proof.length ∧
        s'.pc = pcWord 181 ∧
        CheckFixedRegs s' input.proof.length ∧
        MemEqOutside s s' 256 352 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) ∧
        s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff2 + 32)) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 256 32 = pw.evalLevel c96 2 ∧
        readBuffer s' 320 32 = 0 ∧
        ∀ x ∈ pw.levelInput c96 1, InTrace h768 oracle tr x) := by
  intro s0 c96 i pOff2 pw
  have hplen_bd : input.proof.length ≤ 8422172696 := hvalid
  have hp2_even : pOff2 % 2 = 0 := by
    have := l0Bytes_even i; change (pOff + 16 + l0Bytes i) % 2 = 0; omega
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_lt : i.val / 3 < 5592406 := by omega
  have hpair1 : ((i.val / 3) ^^^ 1) < levelSize 1 := by
    rw [levelSize_1]; exact xor_one_lt_even (m := 2796203) (by omega)
  -- pc[154]: ADDI x6, x25, 32; pc[155]: BLTU x31, x6, pc[336]
  have hst154 := step_ordinary oracle s 154 (.ADDI .x6 .x25 32#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x6 .x25 32#12)
  have hpc1 : s1.pc = pcWord 155 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 (10066334784 + pOff2 + 32) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx25, se12_32]
    change BitVec.ofNat 64 (10066334784 + pOff2) + BitVec.ofNat 64 32 = _
    exact bv64_add _ 32
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (10066334784 + input.proof.length) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hfix.x31]
  have hst155 := step_ordinary oracle s1 155 (.BLTU .x31 .x6 724#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BLTU .x31 .x6 724#13)
  have hpOff2_le : pOff2 ≤ input.proof.length := hple
  have hult : BitVec.ult (s1.getReg .x31) (s1.getReg .x6) = decide (input.proof.length < pOff2 + 32) := by
    rw [hx31_1, hx6_1, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pOff2 + 32
  · have hpc2 : s2.pc = pcWord 336 := by
      simp only [s2, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc1]; decide
    exact .rejected 5 0 [] hshort (by decide) (by decide)
      (by simpa using (hst154.trans hst155).halt (halt_reject oracle s2 hpc2))
  · have hge32 : pOff2 + 32 ≤ input.proof.length := by omega
    have hpc2 : s2.pc = pcWord 156 := by
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
    -- pc[156..159]: zero gap S[64..96)
    obtain ⟨s3, hs3, hpc3, hreg3, hgap3, hout3⟩ :=
      step_zero_gap oracle s2 hpc2 ((hreg2 .x21 (by decide)).trans hfix.x21)
    -- pc[160]: ANDI x7, x22, 1; pc[161]: BEQ x7, x0, pc[174]
    have hst160 := step_ordinary oracle s3 160 (.ANDI .x7 .x22 1#12) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.ANDI .x7 .x22 1#12)
    have hpc4 : s4.pc = pcWord 161 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hx7_4 : s4.getReg .x7 = BitVec.ofNat 64 ((i.val / 3) % 2) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg3 .x22, hreg2 .x22 (by decide), hx22, se12_1]
      exact bv64_and_one (i.val / 3) (by omega)
    have hst161 := step_ordinary oracle s4 161 (.BEQ .x7 .x0 52#13) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.BEQ .x7 .x0 52#13)
    have hmem4 : s4.mem = s3.mem := by simp [s4, execInstrBr, mem_setPC, mem_setReg]
    -- Target compression input at L1
    let inp1 : BitVec 768 :=
      if (i.val / 3) % 2 = 0 then binaryInput (pw.evalL1 c96) (pw.binSib 1)
      else binaryInput (pw.binSib 1) (pw.evalL1 c96)
    have heval2 : pw.evalLevel c96 2 = mask240 (c96 inp1) := by
      simp only [WitnessPath.evalLevel, show (pw.index.val / 3) >>> 0 = i.val / 3 by rfl,
        hpair1, ite_true, show (2 : Nat) ≠ 24 by decide, ite_false]
      rfl
    have hlinp1 : pw.levelInput c96 1 = [inp1] := by
      simp only [WitnessPath.levelInput, show (pw.index.val / 3) >>> 0 = i.val / 3 by rfl,
        hpair1, ite_true]
      rfl
    -- Common finish from pc[177] once S[0..96) = inp1 and S[64..96) = 0
    have hfinish : ∀ (s177 : MachineState) (kMid : Nat),
        kMid ≤ 48 →
        StepsTo oracle s5 s177 kMid 0 [] →
        s177.pc = pcWord 177 →
        CheckFixedRegs s177 input.proof.length →
        MemEqOutside s5 s177 256 320 →
        s177.getReg .x22 = BitVec.ofNat 64 (i.val / 3) →
        s177.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) →
        s177.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) →
        s177.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff2 + 32)) →
        s177.getReg .x27 = BitVec.ofNat 64 rem →
        readBuffer s177 256 96 = inp1 →
        readBuffer s177 320 32 = 0 →
        PhaseOutcome oracle s 60 1 (input.proof.length < pOff2 + 32)
          (fun s' q tr =>
            q = 1 ∧ pOff2 + 32 ≤ input.proof.length ∧ s'.pc = pcWord 181 ∧ CheckFixedRegs s' input.proof.length ∧
            MemEqOutside s s' 256 352 ∧ s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 (5771367488 + 256 * ord) ∧
            s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (pOff2 + 32)) ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            readBuffer s' 256 32 = pw.evalLevel c96 2 ∧
            readBuffer s' 320 32 = 0 ∧
            ∀ x ∈ pw.levelInput c96 1, InTrace h768 oracle tr x) := by
      intro s177 kMid hkMid hmid hpc177 hfix177 hout177 h22 h24 h8 h25 h27 hinp177 hgap177
      have hst177 := step_ordinary oracle s177 177 (.ADDI .x10 .x21 0#12) (by decide) hpc177 rfl (by intro h; cases h) rfl
      let s178 := execInstrBr s177 (.ADDI .x10 .x21 0#12)
      have hpc178 : s178.pc = pcWord 178 := by simp only [s178, execInstrBr, MachineState.setPC, hpc177, pcWord_add_four]
      have hst178 := step_ordinary oracle s178 178 (.ADDI .x12 .x21 0#12) (by decide) hpc178 rfl (by intro h; cases h) rfl
      let s179 := execInstrBr s178 (.ADDI .x12 .x21 0#12)
      have hpc179 : s179.pc = pcWord 179 := by simp only [s179, execInstrBr, MachineState.setPC, hpc178, pcWord_add_four]
      have hmem179 : s179.mem = s177.mem := by simp [s179, s178, execInstrBr, mem_setPC, mem_setReg]
      have hreg179 : ∀ r, r ≠ .x10 → r ≠ .x12 → s179.getReg r = s177.getReg r := fun r h10 h12 => by
        simp only [s179, s178, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_179 : s179.getReg .x10 = 256#64 := by
        simp only [s179, s178, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix177.x21, se12_0, BitVec.add_zero]
      have hx12_179 : s179.getReg .x12 = 256#64 := by
        simp only [s179, s178, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hfix177.x21, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h768 oracle s179 179 256 256 (by decide) hpc179 rfl
        ((hreg179 .x5 (by decide) (by decide)).trans hfix177.x5)
        ((hreg179 .x11 (by decide) (by decide)).trans hfix177.x11)
        ((hreg179 .x13 (by decide) (by decide)).trans hfix177.x13)
        hx10_179 hx12_179 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem179 0 0).readBuffer_eq (by decide) (by omega), hinp177] at hec
      let s180 := writeBits s179 (BitVec.ofNat 64 256) (c96 inp1)
      have hpc180 : s180.pc = pcWord 180 := by simp only [s180, writeBits, MachineState.setPC, hpc179, pcWord_add_four]
      have hx21_180 : s180.getReg .x21 = 256#64 :=
        (writeBits_register s179 _ _ .x21).trans ((hreg179 .x21 (by decide) (by decide)).trans hfix177.x21)
      have ha180 : s180.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 286 := by
        rw [hx21_180]; decide
      have hv180 : memoryArgumentsValid s180 (.SH .x21 .x0 30#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha180]
        exact accessValid_ofNat 286 2 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst180 := step_ordinary oracle s180 180 (.SH .x21 .x0 30#12) (by decide) hpc180 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv180])
      let sFin := execInstrBr s180 (.SH .x21 .x0 30#12)
      have hpcFin : sFin.pc = pcWord 181 := by simp only [sFin, execInstrBr, MachineState.setPC, hpc180, pcWord_add_four]
      have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → sFin.getReg r = s177.getReg r := fun r h10 h12 => by
        have : sFin.getReg r = s180.getReg r := by
          simp [sFin, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        exact this.trans ((writeBits_register s179 _ _ r).trans (hreg179 r h10 h12))
      have hmem_s5 : s5.mem = s3.mem := by
        simp only [s5, execInstrBr]
        split <;> simpa [MachineState.setPC] using hmem4
      have hout_sh : MemEqOutside s180 sFin 286 288 := by
        intro a ha hout
        simp only [sFin, execInstrBr, ha180, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact MemEqOutside_setHalfword s180 286 _ (by decide) (by decide) a ha hout
      have hout_all : MemEqOutside s sFin 256 352 :=
        (MemEqOutside.of_mem_eq hmem2 256 352).trans
          ((hout3.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem_s5 256 352).trans
              ((hout177.mono (by omega) (by omega)).trans
                ((MemEqOutside.of_mem_eq hmem179 256 352).trans
                  (((MemEqOutside_writeBits_digest s179 256 _ (by decide)).mono (by omega) (by omega)).trans
                    (hout_sh.mono (by omega) (by omega)))))))
      have hdigFin : readBuffer sFin 256 32 = pw.evalLevel c96 2 := by
        rw [heval2]
        have hsh : readBuffer sFin 256 32 =
            readBuffer (s180.setHalfword (BitVec.ofNat 64 (256 + 30)) 0#16) 256 32 := by
          apply readBuffer_congr2; intro j hj
          simp [sFin, execInstrBr, ha180, MachineState.getByte, MachineState.getMem_setPC, getReg_x0,
            show (0#64 : Word).truncate 16 = 0#16 by decide]
        rw [hsh, sh_zero_mask240 s180 256 (by decide) (by decide), writeBits_readBuffer_digest]
      have hgapFin : readBuffer sFin 320 32 = 0 := by
        rw [hout_sh.readBuffer_eq (by decide) (by omega),
          (MemEqOutside_writeBits_digest s179 256 _ (by decide)).readBuffer_eq (by decide) (by omega),
          (MemEqOutside.of_mem_eq hmem179 0 0).readBuffer_eq (by decide) (by omega), hgap177]
      have htot := (((hst154.trans hst155).trans hs3).trans ((hst160.trans hst161).trans hmid)).trans
        (((hst177.trans hst178).trans hec).trans hst180)
      refine .continued sFin (2 + 4 + (1 + 1 + kMid) + 4) 1 [(inp1.cast h768.symm, c96 inp1)]
        (by omega) (by decide)
        (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl))
        ⟨rfl, hge32, hpcFin,
         hfix177.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         hout_all,
         (hregFin .x22 (by decide) (by decide)).trans h22,
         (hregFin .x24 (by decide) (by decide)).trans h24,
         (hregFin .x8  (by decide) (by decide)).trans h8,
         (hregFin .x25 (by decide) (by decide)).trans h25,
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
    have hsib1 : readBuffer s3 (10066334784 + pOff2) 32 = pw.binSib 1 := by
      have : pw.binSib 1 = readBuffer s0 (10066334784 + pOff2) 32 := by
        simp [pw, parsePartialWitness, pOff2, Nat.add_assoc]
      rw [this]
      exact hhigh3.readBuffer_eq (by omega) (by omega)
    by_cases heven : (i.val / 3) % 2 = 0
    · -- Even: jump to pc[174..176] -> pc[177]
      have hx7z : s4.getReg .x7 = 0#64 := by rw [hx7_4, heven]
      have hpc5 : s5.pc = pcWord 174 := by
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
      have hst174 := step_ordinary oracle s5 174 (.ADDI .x12 .x21 32#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ADDI .x12 .x21 32#12)
      have hpc6 : s6.pc = pcWord 175 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
      obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
        step_call_read32 oracle 175 s6 (10066334784 + pOff2) 288 (by decide) rfl rfl hpc6
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
                hreg5 .x25 (by decide) (by decide), hx25])
          (by simp only [s6, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide),
                hreg5 .x21 (by decide) (by decide), hfix.x21, se12_32]; decide)
          (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
      have hout_57 : MemEqOutside s5 s7 256 320 :=
        (MemEqOutside.of_mem_eq hmem6 256 320).trans (hout7.mono (by omega) (by omega))
      have hreg7_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → s7.getReg r = s.getReg r :=
        fun r h1 h6 h7 h12 h25 => by
          rw [hreg7 r h1 h6 h25]
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
      refine hfinish s7 36 (by decide) (by simpa using hst174.trans hs7) hpc7
        (hfix.of_agree (fun r hr => hreg7_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        hout_57
        ((hreg7_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg7_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg7_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        (by rw [hx25_7]; congr 1 <;> omega)
        ((hreg7_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        hinp7 hgap7
    · -- Odd: fall through to pc[162..173] -> pc[177]
      have hodd : (i.val / 3) % 2 = 1 := by omega
      have hx7o : s4.getReg .x7 = 1#64 := by rw [hx7_4, hodd]
      have hpc5 : s5.pc = pcWord 162 := by
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
          checkInstr (162 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (0 + 8 * j))) ∧
          checkInstr (162 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
      obtain ⟨s6, hs6, hpc6, hreg6, hcopy6, hout6⟩ :=
        step_copy_dwords oracle 162 4 .x21 .x21 0 32 s5 256 256 (by decide) (by decide)
          (by decide) (by decide) (by decide) hcp hpc5
          ((hreg5 .x21 (by decide) (by decide)).trans hfix.x21)
          ((hreg5 .x21 (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by decide)
      have hst170 := step_ordinary oracle s6 170 (.ADDI .x12 .x21 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.ADDI .x12 .x21 0#12)
      have hpc7 : s7.pc = pcWord 171 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
      obtain ⟨s8, hs8, hpc8, hx25_8, hreg8, hcopy8, hout8⟩ :=
        step_call_read32 oracle 171 s7 (10066334784 + pOff2) 256 (by decide) rfl rfl hpc7
          (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg6 .x25 (by decide),
                hreg5 .x25 (by decide) (by decide), hx25])
          (by simp only [s7, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_eq (by decide), hreg6 .x21 (by decide),
                hreg5 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero])
          (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hst173 := step_ordinary oracle s8 173 (.JAL .x0 16#21) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let s9 := execInstrBr s8 (.JAL .x0 16#21)
      have hpc9 : s9.pc = pcWord 177 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8]; decide
      have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, mem_setPC, mem_setReg]
      have hmem9 : s9.mem = s8.mem := by simp [s9, execInstrBr, mem_setPC, mem_setReg]
      have hout_59 : MemEqOutside s5 s9 256 320 :=
        (hout6.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem7 256 320).trans
            ((hout8.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem9 256 320)))
      have hreg9_base : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → s9.getReg r = s.getReg r :=
        fun r h1 h6 h7 h12 h25 => by
          have : s9.getReg r = s8.getReg r := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [this, hreg8 r h1 h6 h25]
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
          exact h73 (10066334784 + pOff2 + j) (by omega) (by omega)
        have hR : readBuffer s9 288 32 = pw.evalL1 c96 := by
          rw [(MemEqOutside.of_mem_eq hmem9 0 0).readBuffer_eq (by decide) (by omega),
            hout8.readBuffer_eq (by decide) (by omega),
            (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by decide) (by omega), ← hcur3]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy6 j hj
          simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem5] at hc ⊢
          exact hc
        rw [hL, hR]; simp only [inp1, heven, ite_false]
      refine hfinish s9 45 (by decide) (by simpa using (hs6.trans hst170).trans (hs8.trans hst173)) hpc9
        (hfix.of_agree (fun r hr => hreg9_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        hout_59
        ((hreg9_base .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg9_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
        ((hreg9_base .x8  (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8)
        (by have : s9.getReg .x25 = s8.getReg .x25 := by simp [s9, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
            rw [this, hx25_8]; congr 1 <;> omega)
        ((hreg9_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
        hinp9 hgap9

end CommitGolfCandidate
