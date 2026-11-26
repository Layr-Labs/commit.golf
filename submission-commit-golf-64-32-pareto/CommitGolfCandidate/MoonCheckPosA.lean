import CommitGolfCandidate.MoonCheckBase

/-! Symbolic execution of the checker prologue and per-position leaf/L0/L1 phases (`pc[0..104]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private def prologuePrefix : List Instr :=
  [.ADDI .x26 .x11 0#12, .ADDI .x24 .x13 0#12, .ADDI .x8 .x14 0#12,
   .ADDI .x25 .x15 0#12, .ADD .x31 .x15 .x17, .ADDI .x27 .x16 0#12]

private def prologueNonemptySetup : List Instr :=
  [.ADDI .x3 .x0 0#12, .ADDI .x4 .x0 0#12,
   .ADDI .x9 .x0 1#12, .SLLI .x9 .x9 46#6, .ADDI .x9 .x9 4095#12,
   .ADDI .x21 .x0 1#12, .SLLI .x21 .x21 12#6,
   .ADDI .x18 .x0 1#12, .SLLI .x18 .x18 13#6,
   .ADDI .x19 .x0 1#12, .SLLI .x19 .x19 14#6,
   .ADDI .x28 .x0 1#12, .SLLI .x28 .x28 24#6,
   .ADDI .x5 .x0 0#12]

theorem initialState_check_regs (input : CheckInput) :
    let s0 := submission.initialState .check input
    s0.pc = pcWord 0 ∧
    s0.getReg .x11 = BitVec.ofNat 64 4294971392 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6375346208 ∧
    s0.getReg .x14 = BitVec.ofNat 64 6509563936 ∧
    s0.getReg .x15 = BitVec.ofNat 64 10804531232 ∧
    s0.getReg .x16 = BitVec.ofNat 64 input.positions.card ∧
    s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := by
  intro s0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (
    simp only [s0, Submission.initialState, submission_layout, inputCount, inputProofLength,
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
  obtain ⟨hpc0, _, _, _, _, hx16, hx17⟩ := initialState_check_regs input
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
  have hst7 := step_ordinary oracle s2 7 (.BNE .x17 .x0 944#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BNE .x17 .x0 944#13)
  have hplen_lt : input.proof.length < 2 ^ 64 := by
    change input.proof.length ≤ 8480886496 at hvalid; omega
  by_cases hpz : input.proof.length = 0
  · simp only [hpz, ite_true]
    have hx17_z : s2.getReg .x17 = 0#64 := by rw [hx17_2, hpz]
    have hpc3 : s3.pc = pcWord 8 := by
      simp only [s3, execInstrBr, hx17_z, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
        ite_false, MachineState.setPC, hpc2, pcWord_add_four]
    have hst8 := step_ordinary oracle s3 8 (.JAL .x0 928#21) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.JAL .x0 928#21)
    have hpc4 : s4.pc = pcWord 240 := by
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
    have hpc3 : s3.pc = pcWord 243 := by
      simp only [s3, execInstrBr, hneb, ite_true, MachineState.setPC, hpc2]; decide
    have htot := ((hs1.trans hst6).trans hst7).halt (halt_reject oracle s3 hpc3)
    exact (by simpa using htot : HaltsWith oracle s0 11 0 .failure []).mono (by decide)

/-- When `positions.card ≥ 1`, the prologue reaches `pc[23]` in 21 steps with 0 oracle calls. -/
theorem step_prologue_nonempty (oracle : Oracle) (input : CheckInput)
    (hne : input.positions.card ≠ 0) :
    ∃ s1, StepsTo oracle (submission.initialState .check input) s1 21 0 [] ∧
      s1.pc = pcWord 23 ∧
      s1.mem = (submission.initialState .check input).mem ∧
      CheckFixedRegs s1 ∧
      ProofCursor (submission.initialState .check input) input.proof.length 0 0 s1 ∧
      s1.getReg .x24 = BitVec.ofNat 64 6375346208 ∧
      s1.getReg .x8  = BitVec.ofNat 64 6509563936 ∧
      s1.getReg .x27 = BitVec.ofNat 64 input.positions.card := by
  let s0 := submission.initialState .check input
  have hcard_lt : input.positions.card < 2 ^ 64 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at this; omega
  obtain ⟨hpc0, hx11, hx13, hx14, hx15, hx16, hx17⟩ := initialState_check_regs input
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
    rw [ne_eq, bv64_eq_iff _ 0 hcard_lt (by omega)]
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
    have hi' : i < 14 := hi
    interval_cases i <;> rfl
  have hpure2 : ∀ i (hi : i < prologueNonemptySetup.length),
      Instruction.base (prologueNonemptySetup[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (prologueNonemptySetup[i]'hi)) = some (execInstrBr st (prologueNonemptySetup[i]'hi)) ∧
            (execInstrBr st (prologueNonemptySetup[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (prologueNonemptySetup[i]'hi)).mem = st.mem := by
    intro i hi
    have hi' : i < 14 := hi
    interval_cases i <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hs3, hpc3, hmem3⟩ := step_pure_list oracle 9 prologueNonemptySetup s2 (by decide) hcode2 hpure2 hpc2
  let s3 := runInstrs s2 prologueNonemptySetup
  have hs3 : StepsTo oracle s2 s3 14 0 [] := hs3
  have hpc3 : s3.pc = pcWord 23 := hpc3
  have hreg_s2 : ∀ r, s2.getReg r = s1.getReg r := fun r => by
    simp [s2, execInstrBr, hneb, MachineState.getReg_setPC]
  have hreg_s3 : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x9 →
      r ≠ .x18 → r ≠ .x19 → r ≠ .x21 → r ≠ .x28 → s3.getReg r = s2.getReg r :=
    fun r h3 h4 h5 h9 h18 h19 h21 h28 => by
      simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h5.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h19.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h19.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h18.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h18.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h21.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h21.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h4.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h3.symm]
  have hfixed : CheckFixedRegs s3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · rw [hreg_s3 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
      exact hx11
    · simp only [s3, runInstrs, prologueNonemptySetup, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hcur : ProofCursor s0 input.proof.length 0 0 s3 := by
    refine ⟨by simp [tailBytes_zero], ?_, ?_, ?_, ?_⟩
    · rw [hreg_s3 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero, Nat.add_zero]
      exact hx15
    · rw [hreg_s3 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
      simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, decide_not, not_false_eq_true, reduceCtorEq, tailBytes_zero, Nat.sub_zero]
      have h15 : s0.getReg .x15 = BitVec.ofNat 64 10804531232 := hx15
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
  · rw [hreg_s3 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx13
  · rw [hreg_s3 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2]
    simp only [s1, runInstrs, prologuePrefix, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      ne_eq, decide_not, not_false_eq_true, reduceCtorEq, se12_0, BitVec.add_zero]
    exact hx14
  · rw [hreg_s3 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hreg_s2, hx27_1]

/-! #### Sorted Position Accessors, Heap-Index Helpers, and Witness Parser -/

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

theorem heapIdx_zero (idx : Nat) : heapIdx 0 idx = 16777216 + idx := by
  unfold heapIdx; rw [levelSize_0]

theorem heapIdx_16 (idx : Nat) : heapIdx 16 idx = 256 + idx := by
  unfold heapIdx; rw [levelSize_16]

theorem heapIdx_mod_two (l idx : Nat) (hl : l < 24) :
    heapIdx l idx % 2 = idx % 2 := by
  unfold heapIdx
  rw [levelSize_double l hl]
  omega

theorem heapIdx_shiftRight_div2 (i : Index) (l : Nat) (hl : l < 24) :
    heapIdx l (i.val >>> l) / 2 = heapIdx (l + 1) (i.val >>> (l + 1)) := by
  rw [heapIdx_parent l _ hl, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem heapIdx_shiftRight_lt (i : Index) (l : Nat) (hl : l ≤ 24) :
    heapIdx l (i.val >>> l) < 2 ^ 25 := by
  apply heapIdx_lt l (i.val >>> l) hl
  have hi : i.val < 2 ^ 24 := i.isLt
  rw [Nat.shiftRight_eq_div_pow]
  unfold levelSize
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2)), ← Nat.pow_add,
    show 24 - l + l = 24 by omega]
  exact hi

/-- Parse the lower-path siblings (`L0..L15`) and salt for position `ord` at proof offsets
`(pOff, tOff) = (498 * ord, 10 * ord)`. -/
def parsePartialWitness (s0 : MachineState) (proofLen pOff tOff : Nat)
    (i : Index) (val : Entry) : WitnessPath where
  index := i
  value := val
  salt := readBuffer s0 (10804531232 + pOff) 24
  binSib := fun l =>
    if l = 0 then
      readBuffer s0 (10804531232 + pOff + 24) 32
    else if l = 1 then
      readBuffer s0 (10804531232 + pOff + 56) 32
    else if 2 ≤ l ∧ l ≤ 5 then
      proofDigest30 s0 (10804531232 + pOff + 88 + 30 * (l - 2))
    else if 6 ≤ l ∧ l ≤ 15 then
      proofDigest238 s0 proofLen (10804531232 + pOff + 208 + 29 * (l - 6)) (tOff + (l - 6))
    else 0

/-! #### Per-Position Sub-Phases (`pc[23..104]`) -/

private def leafC0SetupInstrs : List Instr :=
  [.ADDI .x11 .x0 64#12, .ADDI .x13 .x0 0#12, .ADDI .x10 .x8 192#12, .ADDI .x12 .x10 0#12]

private def leafP1SetupInstrs : List Instr :=
  [.ADDI .x11 .x0 200#12, .ADDI .x13 .x0 1#12, .ADDI .x10 .x8 24#12, .ADDI .x12 .x10 0#12]

private def leafC2SetupInstrs : List Instr :=
  [.ADDI .x11 .x0 64#12, .ADDI .x13 .x0 0#12, .ADDI .x10 .x8 0#12,
   .ANDI .x7 .x20 1#12, .SLLI .x7 .x7 5#6, .ADD .x12 .x21 .x7]

private theorem pc_25_reject : pcWord 25 + signExtend13 872#13 = pcWord 243 := by decide
private theorem pc_44_odd : pcWord 44 + signExtend13 24#13 = pcWord 50 := by decide
private theorem pc_49_join : pcWord 49 + signExtend21 20#21 = pcWord 54 := by decide

/-- Phase 1A: check 24B salt availability and execute the 4-call `C0 -> P1 -> C2 -> SM-PLS-40(C3)`
leaf chain (`pc[23..57]` -> `pc[58]`). Mutates only `[4096, 4160)` and `values[ord]`. -/
theorem step_pos_leaf (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat) (hord : ord < input.positions.card)
    (s : MachineState) (hpc : s.pc = pcWord 23)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pOff tOff s)
    (hinp : InputMemPreserved (submission.initialState .check input) ord s)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 180 4 (input.proof.length < pOff + 24 + tailBytes tOff)
      (fun s' q tr =>
        q = 4 ∧
        s'.pc = pcWord 58 ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 24) tOff s' ∧
        InputMemPreserved s0 (ord + 1) s' ∧
        (∀ a : Nat, 4160 ≤ a → a < 4294971392 →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
        s'.getReg .x22 = BitVec.ofNat 64 (heapIdx 0 i.val) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = leafDigest c64 oracle.permutation pw.index pw.salt pw.value ∧
        (∀ x ∈ pw.leafCompInputs c64 oracle.permutation, InCompRows h512 oracle tr x) ∧
        InPermRows oracle tr (pw.leafPermInput c64)) := by
  intro s0 c64 i pw
  have hplen_bd : input.proof.length ≤ 8480886496 := hvalid
  have hle_cur : pOff + tailBytes tOff ≤ input.proof.length := hcur.le
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hi_lt : i.val < 16777216 := i.isLt
  let valBase : Nat := 6509563936 + 256 * ord
  -- pc[23]: LD x20, 0(x24)
  have ha23 : s.getReg .x24 + signExtend12 0#12 = BitVec.ofNat 64 (6375346208 + 8 * ord) := by
    rw [hx24, se12_0, BitVec.add_zero]
  have hv23 : memoryArgumentsValid s (.LD .x20 .x24 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha23]
    exact accessValid_ofNat (6375346208 + 8 * ord) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst23 := step_ordinary oracle s 23 (.LD .x20 .x24 0#12) (by decide) hpc rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv23])
  let s1 := execInstrBr s (.LD .x20 .x24 0#12)
  have hpc1 : s1.pc = pcWord 24 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hidx_mem : s.getMem (BitVec.ofNat 64 (6375346208 + 8 * ord)) = BitVec.ofNat 64 i.val := by
    rw [hinp.getMem_eq (by omega) (by omega) (Or.inl (by omega)), check_initial_index input ord hord,
      posAt_val input.positions ord hord]
  have hx20_1 : s1.getReg .x20 = BitVec.ofNat 64 i.val := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha23]
    rw [MachineState.getReg_setReg_eq (by decide), hidx_mem]
  have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (10804531232 + pOff) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25), hcur.x25]
  -- pc[24]: ADDI x6, x25, 24; pc[25]: BLTU x31, x6, pc[243]
  have hst24 := step_ordinary oracle s1 24 (.ADDI .x6 .x25 24#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x6 .x25 24#12)
  have hpc2 : s2.pc = pcWord 25 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (10804531232 + pOff + 24) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx25_1, se12_24]
    change BitVec.ofNat 64 (10804531232 + pOff) + BitVec.ofNat 64 24 = _
    exact bv64_add _ 24
  have hx31_2 : s2.getReg .x31 = BitVec.ofNat 64 (10804531232 + (input.proof.length - tailBytes tOff)) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x31), hcur.x31]
  have hst25 := step_ordinary oracle s2 25 (.BLTU .x31 .x6 872#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BLTU .x31 .x6 872#13)
  have hult : BitVec.ult (s2.getReg .x31) (s2.getReg .x6) = decide (input.proof.length < pOff + 24 + tailBytes tOff) := by
    rw [hx31_2, hx6_2, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : input.proof.length < pOff + 24 + tailBytes tOff
  · have hpc3 : s3.pc = pcWord 243 := by
      simp only [s3, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc2]
      exact pc_25_reject
    exact .rejected 6 0 [] hshort (by decide) (by decide)
      (by simpa using ((hst23.trans hst24).trans hst25).halt (halt_reject oracle s3 hpc3))
  · have hge24 : pOff + 24 + tailBytes tOff ≤ input.proof.length := by omega
    have hpc3 : s3.pc = pcWord 26 := by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      have h32 : s3.mem = s2.mem := by
        simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      exact h32.trans (by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg])
    have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x20 → s3.getReg r = s.getReg r := fun r hr6 hr20 => by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.getReg_setPC]
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr6.symm]
      simp only [s1, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ hr20.symm
    have hx20_3 : s3.getReg .x20 = BitVec.ofNat 64 i.val := by
      simp only [s3, execInstrBr, hult, hshort, decide_false, Bool.false_eq_true, ite_false,
        MachineState.getReg_setPC]
      simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x20), hx20_1]
    -- pc[26..30]: C0 = compress(val[192..256)) -> val[192..224)
    have hcodeC0 : ∀ j (hj : j < leafC0SetupInstrs.length), checkInstr (26 + j) = .base (leafC0SetupInstrs[j]'hj) := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> rfl
    have hpureC0 : ∀ j (hj : j < leafC0SetupInstrs.length),
        Instruction.base (leafC0SetupInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (leafC0SetupInstrs[j]'hj)) = some (execInstrBr st (leafC0SetupInstrs[j]'hj)) ∧
              (execInstrBr st (leafC0SetupInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (leafC0SetupInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs4, hpc4, hmem4'⟩ := step_pure_list oracle 26 leafC0SetupInstrs s3 (by decide) hcodeC0 hpureC0 hpc3
    let s4 := runInstrs s3 leafC0SetupInstrs
    have hpc4 : s4.pc = pcWord 30 := hpc4
    have hmem4 : s4.mem = s.mem := hmem4'.trans hmem3
    have hreg4 : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s4.getReg r = s3.getReg r :=
      fun r h10 h11 h12 h13 => by
        simp only [s4, runInstrs, leafC0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h13.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h11.symm]
    have hx11_4 : s4.getReg .x11 = 64#64 := by
      simp only [s4, runInstrs, leafC0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    have hx13_4 : s4.getReg .x13 = 0#64 := by
      simp only [s4, runInstrs, leafC0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    have hx10_4 : s4.getReg .x10 = BitVec.ofNat 64 (valBase + 192) := by
      simp only [s4, runInstrs, leafC0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hreg3 .x8 (by decide) (by decide), hx8, se12_192]
      exact bv64_add valBase 192
    have hx12_4 : s4.getReg .x12 = BitVec.ofNat 64 (valBase + 192) := by
      simp only [s4, runInstrs, leafC0SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hreg3 .x8 (by decide) (by decide), hx8, se12_192, se12_0,
        BitVec.add_zero]
      exact bv64_add valBase 192
    let iC0 := leafC0Input pw.value
    let c0 := c64 iC0
    have hinpC0 : readBuffer s4 (valBase + 192) 64 = iC0 := by
      rw [(hinp.trans_mem_eq hmem4).readBuffer_eq (by dsimp only [valBase]; omega) (Or.inr (by dsimp only [valBase]; omega))]
      simpa only [iC0, leafC0Input, pw, parsePartialWitness, valAt, dif_pos hord] using
        check_initial_value_slice input ord 192 64 hord (by decide)
    have hec0 := step_ecall_compress h512 oracle s4 30 (valBase + 192) (valBase + 192) (by decide) hpc4 rfl
      ((hreg4 .x5 (by decide) (by decide) (by decide) (by decide)).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))
      hx11_4 hx13_4 hx10_4 hx12_4 (by dsimp only [valBase]; omega) (by dsimp only [valBase]; omega)
      (by unfold MEMORY_BYTES; dsimp only [valBase]; omega) (by unfold MEMORY_BYTES; dsimp only [valBase]; omega)
    rw [hinpC0] at hec0
    let s5 := writeBits s4 (BitVec.ofNat 64 (valBase + 192)) c0
    have hpc5 : s5.pc = pcWord 31 := by simp only [s5, writeBits, MachineState.setPC, hpc4, pcWord_add_four]
    have hreg5 : ∀ r, s5.getReg r = s4.getReg r := fun r => writeBits_register s4 _ c0 r
    have hc0_5 : readBuffer s5 (valBase + 192) 32 = c0 := writeBits_readBuffer_digest s4 (valBase + 192) c0
    have hout_s5 : MemEqOutside s s5 (valBase + 192) (valBase + 224) :=
      (MemEqOutside.of_mem_eq hmem4 (valBase + 192) (valBase + 224)).trans
        (MemEqOutside_writeBits_digest s4 (valBase + 192) c0 (by dsimp only [valBase]; omega))
    -- pc[31..35]: P1 = perm(val[24..192) || c0) -> val[24..224)
    have hcodeP1 : ∀ j (hj : j < leafP1SetupInstrs.length), checkInstr (31 + j) = .base (leafP1SetupInstrs[j]'hj) := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> rfl
    have hpureP1 : ∀ j (hj : j < leafP1SetupInstrs.length),
        Instruction.base (leafP1SetupInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (leafP1SetupInstrs[j]'hj)) = some (execInstrBr st (leafP1SetupInstrs[j]'hj)) ∧
              (execInstrBr st (leafP1SetupInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (leafP1SetupInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs6, hpc6, hmem6⟩ := step_pure_list oracle 31 leafP1SetupInstrs s5 (by decide) hcodeP1 hpureP1 hpc5
    let s6 := runInstrs s5 leafP1SetupInstrs
    have hpc6 : s6.pc = pcWord 35 := hpc6
    have hreg6 : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s6.getReg r = s3.getReg r :=
      fun r h10 h11 h12 h13 => by
        have h65 : s6.getReg r = s5.getReg r := by
          simp only [s6, runInstrs, leafP1SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h13.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h11.symm]
        exact h65.trans ((hreg5 r).trans (hreg4 r h10 h11 h12 h13))
    have hx8_5 : s5.getReg .x8 = BitVec.ofNat 64 valBase :=
      (hreg5 .x8).trans ((hreg4 .x8 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg3 .x8 (by decide) (by decide)).trans hx8))
    have hx11_6 : s6.getReg .x11 = 200#64 := by
      simp only [s6, runInstrs, leafP1SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    have hx13_6 : s6.getReg .x13 = 1#64 := by
      simp only [s6, runInstrs, leafP1SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    have hx10_6 : s6.getReg .x10 = BitVec.ofNat 64 (valBase + 24) := by
      simp only [s6, runInstrs, leafP1SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hx8_5, se12_24]
      exact bv64_add valBase 24
    have hx12_6 : s6.getReg .x12 = BitVec.ofNat 64 (valBase + 24) := by
      simp only [s6, runInstrs, leafP1SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hx8_5, se12_24, se12_0, BitVec.add_zero]
      exact bv64_add valBase 24
    let iP1 := leafP1Input c0 pw.value
    let y := oracle.permutation iP1
    have hinpP1 : readBuffer s6 (valBase + 24) 200 = iP1 := by
      rw [readBuffer_p1 s6 (valBase + 24)]
      have hhi : readBuffer s6 (valBase + 24 + 168) 32 = c0 := by
        rw [show valBase + 24 + 168 = valBase + 192 by omega,
          (MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by dsimp only [valBase]; omega) (by omega), hc0_5]
      have hlo : readBuffer s6 (valBase + 24) 168 = pw.value.extractLsb' 192 1344 := by
        rw [(MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by dsimp only [valBase]; omega) (by omega),
          hout_s5.readBuffer_eq (by dsimp only [valBase]; omega) (by omega),
          hinp.readBuffer_eq (by dsimp only [valBase]; omega) (Or.inr (by dsimp only [valBase]; omega))]
        simpa only [pw, parsePartialWitness, valAt, dif_pos hord] using
          check_initial_value_slice input ord 24 168 hord (by decide)
      rw [hhi, hlo]; rfl
    have hec1 := step_ecall_perm oracle s6 35 (valBase + 24) (valBase + 24) (by decide) hpc6 rfl
      ((hreg6 .x5 (by decide) (by decide) (by decide) (by decide)).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))
      hx11_6 hx13_6 hx10_6 hx12_6 (by dsimp only [valBase]; omega) (by dsimp only [valBase]; omega)
      (by unfold MEMORY_BYTES; dsimp only [valBase]; omega) (by unfold MEMORY_BYTES; dsimp only [valBase]; omega)
    rw [hinpP1] at hec1
    let s7 := writeBits s6 (BitVec.ofNat 64 (valBase + 24)) y
    have hpc7 : s7.pc = pcWord 36 := by simp only [s7, writeBits, MachineState.setPC, hpc6, pcWord_add_four]
    have hreg7 : ∀ r, s7.getReg r = s6.getReg r := fun r => writeBits_register s6 _ y r
    have hy40_7 : readBuffer s7 (valBase + 24) 40 = y.extractLsb' 0 320 := writeBits_readBuffer_perm40 s6 (valBase + 24) y
    have hout_s7 : MemEqOutside s s7 (valBase + 24) (valBase + 224) :=
      (hout_s5.mono (by omega) (by omega)).trans
        ((MemEqOutside.of_mem_eq hmem6 (valBase + 24) (valBase + 224)).trans
          (MemEqOutside_writeBits_perm s6 (valBase + 24) y (by dsimp only [valBase]; omega)))
    -- pc[36..42]: C2 = compress(val[0..24) || y[0..40)) -> [dstA, dstA + 32)
    have hcodeC2 : ∀ j (hj : j < leafC2SetupInstrs.length), checkInstr (36 + j) = .base (leafC2SetupInstrs[j]'hj) := by
      intro j hj; have hj' : j < 6 := hj; interval_cases j <;> rfl
    have hpureC2 : ∀ j (hj : j < leafC2SetupInstrs.length),
        Instruction.base (leafC2SetupInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (leafC2SetupInstrs[j]'hj)) = some (execInstrBr st (leafC2SetupInstrs[j]'hj)) ∧
              (execInstrBr st (leafC2SetupInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (leafC2SetupInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 6 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs8, hpc8, hmem8⟩ := step_pure_list oracle 36 leafC2SetupInstrs s7 (by decide) hcodeC2 hpureC2 hpc7
    let s8 := runInstrs s7 leafC2SetupInstrs
    have hpc8 : s8.pc = pcWord 42 := hpc8
    have hmem8 : s8.mem = s7.mem := hmem8
    let dstA : Nat := 4096 + 32 * (i.val % 2)
    have hreg8 : ∀ r, r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s8.getReg r = s3.getReg r :=
      fun r h7 h10 h11 h12 h13 => by
        have h87 : s8.getReg r = s7.getReg r := by
          simp only [s8, runInstrs, leafC2SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h13.symm, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ h11.symm]
        exact h87.trans ((hreg7 r).trans (hreg6 r h10 h11 h12 h13))
    have hx8_7 : s7.getReg .x8 = BitVec.ofNat 64 valBase :=
      (hreg7 .x8).trans ((hreg6 .x8 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg3 .x8 (by decide) (by decide)).trans hx8))
    have hx20_7 : s7.getReg .x20 = BitVec.ofNat 64 i.val :=
      (hreg7 .x20).trans ((hreg6 .x20 (by decide) (by decide) (by decide) (by decide)).trans hx20_3)
    have hx21_7 : s7.getReg .x21 = 4096#64 :=
      (hreg7 .x21).trans ((hreg6 .x21 (by decide) (by decide) (by decide) (by decide)).trans
        ((hreg3 .x21 (by decide) (by decide)).trans hfix.x21))
    have hx11_8 : s8.getReg .x11 = 64#64 := by
      simp only [s8, runInstrs, leafC2SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    have hx13_8 : s8.getReg .x13 = 0#64 := by
      simp only [s8, runInstrs, leafC2SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, getReg_x0]; decide
    have hx10_8 : s8.getReg .x10 = BitVec.ofNat 64 valBase := by
      simp only [s8, runInstrs, leafC2SetupInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hx8_7, se12_0, BitVec.add_zero]
    have hx12_8 : s8.getReg .x12 = BitVec.ofNat 64 dstA := by
      have harith : (4096#64 + ((BitVec.ofNat 64 i.val &&& signExtend12 1#12) <<< 5)) = BitVec.ofNat 64 dstA := by
        rw [se12_1, bv64_and_one i.val (by omega), bv64_shl _ 5 (by omega)]
        change BitVec.ofNat 64 4096 + BitVec.ofNat 64 _ = _
        rw [bv64_add]
        exact congrArg (BitVec.ofNat 64) (by dsimp only [dstA]; omega)
      simpa only [s8, runInstrs, leafC2SetupInstrs, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hx20_7, hx21_7,
        show (5#6 : BitVec 6).toNat = 5 by decide] using harith
    let iC2 := leafC2Input y pw.value
    let a := c64 iC2
    have hinpC2 : readBuffer s8 valBase 64 = iC2 := by
      rw [readBuffer_c2 s8 valBase]
      have hhi : readBuffer s8 (valBase + 24) 40 = y.extractLsb' 0 320 := by
        rw [(MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by dsimp only [valBase]; omega) (by omega), hy40_7]
      have hlo : readBuffer s8 valBase 24 = pw.value.extractLsb' 0 192 := by
        rw [(MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by dsimp only [valBase]; omega) (by omega),
          hout_s7.readBuffer_eq (by dsimp only [valBase]; omega) (by omega),
          hinp.readBuffer_eq (by dsimp only [valBase]; omega) (Or.inr (by dsimp only [valBase]; omega))]
        simpa only [Nat.add_zero, Nat.mul_zero, pw, parsePartialWitness, valAt, dif_pos hord] using
          check_initial_value_slice input ord 0 24 hord (by decide)
      rw [hhi, hlo]; rfl
    have hec2 := step_ecall_compress h512 oracle s8 42 valBase dstA (by decide) hpc8 rfl
      ((hreg8 .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))
      hx11_8 hx13_8 hx10_8 hx12_8 (by dsimp only [valBase]; omega) (by dsimp only [dstA]; omega)
      (by unfold MEMORY_BYTES; dsimp only [valBase]; omega) (by unfold MEMORY_BYTES; dsimp only [dstA]; omega)
    rw [hinpC2] at hec2
    let s9 := writeBits s8 (BitVec.ofNat 64 dstA) a
    have hpc9 : s9.pc = pcWord 43 := by simp only [s9, writeBits, MachineState.setPC, hpc8, pcWord_add_four]
    have hreg9 : ∀ r, s9.getReg r = s8.getReg r := fun r => writeBits_register s8 _ a r
    have ha9 : readBuffer s9 dstA 32 = a := writeBits_readBuffer_digest s8 dstA a
    have hinp9 : InputMemPreserved s0 (ord + 1) s9 := by
      intro q hq hreg
      have h98 : s9.getByte (BitVec.ofNat 64 q) = s8.getByte (BitVec.ofNat 64 q) :=
        MemEqOutside_writeBits_digest s8 dstA a (by dsimp only [dstA]; omega) q hq (by dsimp only [dstA]; omega)
      have h87 : s8.getByte (BitVec.ofNat 64 q) = s7.getByte (BitVec.ofNat 64 q) := by
        simp only [MachineState.getByte, MachineState.getMem, hmem8]
      have h7s : s7.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q) :=
        hout_s7 q hq (by dsimp only [valBase]; omega)
      exact h98.trans (h87.trans (h7s.trans (hinp q hq (by omega))))
    have hlow9 : ∀ q : Nat, 4160 ≤ q → q < 4294971392 →
        s9.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q) := fun q hlo hhi => by
      have h98 : s9.getByte (BitVec.ofNat 64 q) = s8.getByte (BitVec.ofNat 64 q) :=
        MemEqOutside_writeBits_digest s8 dstA a (by dsimp only [dstA]; omega) q (by omega) (by dsimp only [dstA]; omega)
      have h87 : s8.getByte (BitVec.ofNat 64 q) = s7.getByte (BitVec.ofNat 64 q) := by
        simp only [MachineState.getByte, MachineState.getMem, hmem8]
      have h7s : s7.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q) :=
        hout_s7 q (by omega) (by dsimp only [valBase]; omega)
      exact h98.trans (h87.trans h7s)
    have hreg9_base : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x20 →
        s9.getReg r = s.getReg r := fun r h6 h7 h10 h11 h12 h13 h20 =>
      (hreg9 r).trans ((hreg8 r h7 h10 h11 h12 h13).trans (hreg3 r h6 h20))
    have hx20_9 : s9.getReg .x20 = BitVec.ofNat 64 i.val :=
      (hreg9 .x20).trans ((hreg8 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20_3)
    have hx11_9 : s9.getReg .x11 = 64#64 := (hreg9 .x11).trans hx11_8
    have hx13_9 : s9.getReg .x13 = 0#64 := (hreg9 .x13).trans hx13_8
    -- pc[43..44]: parity dispatch
    have hst43 := step_ordinary oracle s9 43 (.ANDI .x7 .x20 1#12) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.ANDI .x7 .x20 1#12)
    have hpc10 : s10.pc = pcWord 44 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
    have hx7_10 : s10.getReg .x7 = BitVec.ofNat 64 (i.val % 2) := by
      simp only [s10, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hx20_9, se12_1]
      exact bv64_and_one i.val (by omega)
    have hst44 := step_ordinary oracle s10 44 (.BNE .x7 .x0 24#13) (by decide) hpc10 rfl (by intro h; cases h) rfl
    let s11 := execInstrBr s10 (.BNE .x7 .x0 24#13)
    have hmem10 : s10.mem = s9.mem := by simp [s10, execInstrBr, mem_setPC, mem_setReg]
    have hpre11 : StepsTo oracle s s11 22 3
        [PublicRow.compression (iC0.cast h512.symm) c0,
         PublicRow.permutation iP1 y,
         PublicRow.compression (iC2.cast h512.symm) a] := by
      have hA := ((hst23.trans hst24).trans hst25).trans (hs4.trans hec0)
      have hB := (hs6.trans hec1).trans (hs8.trans hec2)
      have hC := (hA.trans hB).trans (hst43.trans hst44)
      exact hC.eq_of rfl (by decide) (by decide) (by simp [c64, c0, y, a])
    -- Common finish from pc[54..57] -> pc[58]
    let iC3 := leafFinalInput pw.index a pw.salt
    have hfinish : ∀ (s54 : MachineState) (kMid : Nat),
        kMid ≤ 150 →
        StepsTo oracle s11 s54 kMid 0 [] →
        s54.pc = pcWord 54 →
        CheckFixedRegs s54 →
        s54.getReg .x11 = 64#64 →
        s54.getReg .x13 = 0#64 →
        ProofCursor s0 input.proof.length (pOff + 24) tOff s54 →
        MemEqOutside s9 s54 4096 4160 →
        s54.getReg .x20 = BitVec.ofNat 64 i.val →
        s54.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) →
        s54.getReg .x8  = BitVec.ofNat 64 valBase →
        s54.getReg .x27 = BitVec.ofNat 64 rem →
        readBuffer s54 4096 64 = iC3 →
        PhaseOutcome oracle s 180 4 (input.proof.length < pOff + 24 + tailBytes tOff)
          (fun s' q tr =>
            q = 4 ∧ s'.pc = pcWord 58 ∧ CheckFixedRegs s' ∧
            s'.getReg .x11 = 64#64 ∧ s'.getReg .x13 = 0#64 ∧
            ProofCursor s0 input.proof.length (pOff + 24) tOff s' ∧
            InputMemPreserved s0 (ord + 1) s' ∧
            (∀ a : Nat, 4160 ≤ a → a < 4294971392 →
              s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
            s'.getReg .x22 = BitVec.ofNat 64 (heapIdx 0 i.val) ∧
            s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
            s'.getReg .x8  = BitVec.ofNat 64 valBase ∧
            s'.getReg .x27 = BitVec.ofNat 64 rem ∧
            readBuffer s' 4096 32 = leafDigest c64 oracle.permutation pw.index pw.salt pw.value ∧
            (∀ x ∈ pw.leafCompInputs c64 oracle.permutation, InCompRows h512 oracle tr x) ∧
            InPermRows oracle tr (pw.leafPermInput c64)) := by
      intro s54 kMid hkMid hmid hpc54 hfix54 h11_54 h13_54 hcur54 hout54 h20 h24 h8 h27 hinpF
      have hst54 := step_ordinary oracle s54 54 (.ADDI .x10 .x21 0#12) (by decide) hpc54 rfl (by intro h; cases h) rfl
      let s55 := execInstrBr s54 (.ADDI .x10 .x21 0#12)
      have hpc55 : s55.pc = pcWord 55 := by simp only [s55, execInstrBr, MachineState.setPC, hpc54, pcWord_add_four]
      have hst55 := step_ordinary oracle s55 55 (.ADDI .x12 .x21 0#12) (by decide) hpc55 rfl (by intro h; cases h) rfl
      let s56 := execInstrBr s55 (.ADDI .x12 .x21 0#12)
      have hpc56 : s56.pc = pcWord 56 := by simp only [s56, execInstrBr, MachineState.setPC, hpc55, pcWord_add_four]
      have hmem56 : s56.mem = s54.mem := by simp [s56, s55, execInstrBr, mem_setPC, mem_setReg]
      have hreg56 : ∀ r, r ≠ .x10 → r ≠ .x12 → s56.getReg r = s54.getReg r := fun r h10 h12 => by
        simp only [s56, s55, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx10_56 : s56.getReg .x10 = 4096#64 := by
        simp only [s56, s55, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hfix54.x21, se12_0, BitVec.add_zero]
      have hx12_56 : s56.getReg .x12 = 4096#64 := by
        simp only [s56, s55, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hfix54.x21, se12_0, BitVec.add_zero]
      have hec3 := step_ecall_compress h512 oracle s56 56 4096 4096 (by decide) hpc56 rfl
        ((hreg56 .x5 (by decide) (by decide)).trans hfix54.x5)
        ((hreg56 .x11 (by decide) (by decide)).trans h11_54)
        ((hreg56 .x13 (by decide) (by decide)).trans h13_54)
        hx10_56 hx12_56 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem56 0 0).readBuffer_eq (by omega) (by omega), hinpF] at hec3
      let s57 := writeBits s56 (BitVec.ofNat 64 4096) (c64 iC3)
      have hpc57 : s57.pc = pcWord 57 := by simp only [s57, writeBits, MachineState.setPC, hpc56, pcWord_add_four]
      have hreg57 : ∀ r, r ≠ .x10 → r ≠ .x12 → s57.getReg r = s54.getReg r := fun r h10 h12 =>
        (writeBits_register s56 _ _ r).trans (hreg56 r h10 h12)
      have hst57 := step_ordinary oracle s57 57 (.ADD .x22 .x28 .x20) (by decide) hpc57 rfl (by intro h; cases h) rfl
      let sFin := execInstrBr s57 (.ADD .x22 .x28 .x20)
      have hpcFin : sFin.pc = pcWord 58 := by simp only [sFin, execInstrBr, MachineState.setPC, hpc57, pcWord_add_four]
      have hmemFin : sFin.mem = s57.mem := by simp [sFin, execInstrBr, mem_setPC, mem_setReg]
      have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sFin.getReg r = s54.getReg r := fun r h10 h12 h22 => by
        simp only [sFin, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h22.symm]
        exact hreg57 r h10 h12
      have hx22Fin : sFin.getReg .x22 = BitVec.ofNat 64 (heapIdx 0 i.val) := by
        simp only [sFin, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          hreg57 .x28 (by decide) (by decide), hfix54.x28,
          hreg57 .x20 (by decide) (by decide), h20, bv64_add, heapIdx_zero]
      have hout_9_fin : MemEqOutside s9 sFin 4096 4160 :=
        hout54.trans ((MemEqOutside.of_mem_eq hmem56 4096 4160).trans
          (((MemEqOutside_writeBits_digest s56 4096 _ (by omega)).mono (by omega) (by omega)).trans
            (MemEqOutside.of_mem_eq hmemFin 4096 4160)))
      let trAll : List PublicRow :=
        [PublicRow.compression (iC0.cast h512.symm) c0,
         PublicRow.permutation iP1 y,
         PublicRow.compression (iC2.cast h512.symm) a,
         PublicRow.compression (iC3.cast h512.symm) (c64 iC3)]
      have htot := (hpre11.trans hmid).trans (((hst54.trans hst55).trans hec3).trans hst57)
      refine .continued sFin (22 + kMid + 4) 4 trAll (by omega) (by decide)
        (htot.eq_of rfl (by omega) (by decide) (by simp [trAll, c64, c0, y, a]))
        ⟨rfl, hpcFin,
         hfix54.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)
           (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
         (hregFin .x11 (by decide) (by decide) (by decide)).trans h11_54,
         (hregFin .x13 (by decide) (by decide) (by decide)).trans h13_54,
         hcur54.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)
           (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         hinp9.trans_low hout_9_fin (by omega),
         fun q hlo hhi => (hout_9_fin q (by omega) (by omega)).trans (hlow9 q hlo hhi),
         hx22Fin,
         (hregFin .x24 (by decide) (by decide) (by decide)).trans h24,
         (hregFin .x8  (by decide) (by decide) (by decide)).trans h8,
         (hregFin .x27 (by decide) (by decide) (by decide)).trans h27,
         ?_, ?_, ?_⟩
      · rw [(MemEqOutside.of_mem_eq hmemFin 0 0).readBuffer_eq (by omega) (by omega),
          writeBits_readBuffer_digest]
        rfl
      · intro x hx
        simp only [WitnessPath.leafCompInputs, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    by_cases heven : i.val % 2 = 0
    · -- Even branch: pc[45..49] -> pc[54]
      have hx7z : s10.getReg .x7 = 0#64 := by rw [hx7_10, heven]
      have hpc11 : s11.pc = pcWord 45 := by
        simp only [s11, execInstrBr, hx7z, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
          ite_false, MachineState.setPC, hpc10, pcWord_add_four]
      have hmem11 : s11.mem = s9.mem := by
        simpa [s11, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem10
      have hreg11 : ∀ r, r ≠ .x7 → s11.getReg r = s9.getReg r := fun r h7 => by
        simp only [s11, execInstrBr, hx7z, getReg_x0, bne_self_eq_false, Bool.false_eq_true,
          ite_false, MachineState.getReg_setPC]
        simp only [s10, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
      have hx21_11 : s11.getReg .x21 = 4096#64 :=
        (hreg11 .x21 (by decide)).trans
          ((hreg9_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
      have ha45 : s11.getReg .x21 + signExtend12 32#12 = BitVec.ofNat 64 4128 := by
        rw [hx21_11, se12_32]; decide
      have hv45 : memoryArgumentsValid s11 (.SD .x21 .x0 32#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha45]
        exact accessValid_ofNat 4128 8 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst45 := step_ordinary oracle s11 45 (.SD .x21 .x0 32#12) (by decide) hpc11 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv45])
      let s12 := execInstrBr s11 (.SD .x21 .x0 32#12)
      have hpc12 : s12.pc = pcWord 46 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
      have hreg12 : ∀ r, s12.getReg r = s11.getReg r := fun r => by
        simp [s12, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      have hout12 : MemEqOutside s11 s12 4128 4136 := by
        intro q hq hout
        simp only [s12, execInstrBr, ha45, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact setMem_getByte_ofNat s11 4128 q 0#64 (by decide) (by omega) hq hout
      have hgap12 : readBuffer s12 4128 8 = 0 := by
        rw [readBuffer_word s12 4128 (by decide)]
        simp only [s12, execInstrBr, ha45, MachineState.getMem_setPC, MachineState.getMem_setMem_eq, getReg_x0]; rfl
      have hst46 := step_ordinary oracle s12 46 (.ADDI .x12 .x21 40#12) (by decide) hpc12 rfl (by intro h; cases h) rfl
      let s13 := execInstrBr s12 (.ADDI .x12 .x21 40#12)
      have hpc13 : s13.pc = pcWord 47 := by simp only [s13, execInstrBr, MachineState.setPC, hpc12, pcWord_add_four]
      have hmem13 : s13.mem = s12.mem := by simp [s13, execInstrBr, mem_setPC, mem_setReg]
      have hsrc13 : s13.getReg .x25 = BitVec.ofNat 64 (10804531232 + pOff) := by
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg12,
          hreg11 .x25 (by decide),
          hreg9_base .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x25]
      have hdst13 : s13.getReg .x12 = BitVec.ofNat 64 4136 := by
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg12, hx21_11, se12_40]; decide
      obtain ⟨s14, hs14, hpc14, hx25_14, hreg14, hcopy14, hout14⟩ :=
        step_call_read_n oracle 47 24 s13 (10804531232 + pOff) 4136 (by decide) (by decide) (by decide)
          rfl rfl hpc13 hsrc13 hdst13 (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hst49 := step_ordinary oracle s14 49 (.JAL .x0 20#21) (by decide) hpc14 rfl (by intro h; cases h) rfl
      let s15 := execInstrBr s14 (.JAL .x0 20#21)
      have hpc15 : s15.pc = pcWord 54 := by
        simp only [s15, execInstrBr, MachineState.setPC, hpc14]; exact pc_49_join
      have hmem15 : s15.mem = s14.mem := by simp [s15, execInstrBr, mem_setPC, mem_setReg]
      have hout_9_15 : MemEqOutside s9 s15 4128 4160 :=
        (MemEqOutside.of_mem_eq hmem11 4128 4160).trans
          ((hout12.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem13 4128 4160).trans
              ((hout14.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem15 4128 4160))))
      have hreg15 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s15.getReg r = s9.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        have h15_14 : s15.getReg r = s14.getReg r := by
          simp [s15, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        rw [h15_14, hreg14 r h1 h6 h10 h12 h25]
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg12 r, hreg11 r h7]
      have hgap15 : readBuffer s15 (4096 + 32) 8 = 0 := by
        rw [show 4096 + 32 = 4128 by omega,
          (MemEqOutside.of_mem_eq hmem15 0 0).readBuffer_eq (by omega) (by omega),
          hout14.readBuffer_eq (by omega) (by omega),
          (MemEqOutside.of_mem_eq hmem13 0 0).readBuffer_eq (by omega) (by omega), hgap12]
      have hinpF : readBuffer s15 4096 64 = iC3 := by
        rw [readBuffer_lateEven s15 4096 hgap15]
        have hdstA : dstA = 4096 := by dsimp only [dstA]; omega
        have ha15 : readBuffer s15 4096 32 = a :=
          (hout_9_15.readBuffer_eq (by omega) (by omega)).trans (by rw [← hdstA, ha9])
        have hsalt15 : readBuffer s15 (4096 + 40) 24 = pw.salt := by
          unfold pw parsePartialWitness
          rw [show 4096 + 40 = 4136 by omega,
            (MemEqOutside.of_mem_eq hmem15 0 0).readBuffer_eq (by omega) (by omega)]
          apply readBuffer_congr2; intro j hj
          rw [hcopy14 j hj]
          have h13_0 : InputMemPreserved s0 (ord + 1) s13 :=
            hinp9.trans_low ((MemEqOutside.of_mem_eq hmem11 4128 4136).trans
              (hout12.trans (MemEqOutside.of_mem_eq hmem13 4128 4136))) (by omega)
          exact h13_0 (10804531232 + pOff + j) (by omega) (Or.inr (by omega))
        rw [ha15, hsalt15]
        simp only [iC3, leafFinalInput, show pw.index.val % 2 = 0 from heven, ite_true]
      have hcur15 : ProofCursor s0 input.proof.length (pOff + 24) tOff s15 := by
        refine ⟨hge24, ?_, ?_, ?_, ?_⟩
        · have : s15.getReg .x25 = s14.getReg .x25 := by
            simp [s15, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
          rw [this, hx25_14]; congr 1
        · rw [hreg15 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg9_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg15 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg9_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg15 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg9_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      refine hfinish s15 150 (by decide)
        (((hst45.trans hst46).trans hs14).trans hst49 |>.eq_of rfl (by decide) (by decide) (by simp))
        hpc15
        (hfix.of_agree (fun r hr => (hreg15 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl)).trans
          (hreg9_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl))))
        ((hreg15 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11_9)
        ((hreg15 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13_9)
        hcur15 (hout_9_15.mono (by omega) (by omega))
        ((hreg15 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20_9)
        ((hreg15 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg9_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24))
        ((hreg15 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg9_base .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8))
        ((hreg15 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg9_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27))
        hinpF
    · -- Odd branch: pc[50..53] -> pc[54]
      have hodd : i.val % 2 = 1 := by omega
      have hx7o : s10.getReg .x7 = 1#64 := by rw [hx7_10, hodd]
      have hpc11 : s11.pc = pcWord 50 := by
        simp only [s11, execInstrBr, hx7o, getReg_x0, show (1#64 != 0#64) = true by decide, ite_true,
          MachineState.setPC, hpc10]; exact pc_44_odd
      have hmem11 : s11.mem = s9.mem := by
        simpa [s11, execInstrBr, hx7o, getReg_x0, show (1#64 != 0#64) = true by decide,
          MachineState.setPC] using hmem10
      have hreg11 : ∀ r, r ≠ .x7 → s11.getReg r = s9.getReg r := fun r h7 => by
        simp only [s11, execInstrBr, hx7o, getReg_x0, show (1#64 != 0#64) = true by decide, ite_true,
          MachineState.getReg_setPC]
        simp only [s10, execInstrBr, MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ h7.symm
      have hx21_11 : s11.getReg .x21 = 4096#64 :=
        (hreg11 .x21 (by decide)).trans
          ((hreg9_base .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
      have ha50 : s11.getReg .x21 + signExtend12 24#12 = BitVec.ofNat 64 4120 := by
        rw [hx21_11, se12_24]; decide
      have hv50 : memoryArgumentsValid s11 (.SD .x21 .x0 24#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha50]
        exact accessValid_ofNat 4120 8 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst50 := step_ordinary oracle s11 50 (.SD .x21 .x0 24#12) (by decide) hpc11 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv50])
      let s12 := execInstrBr s11 (.SD .x21 .x0 24#12)
      have hpc12 : s12.pc = pcWord 51 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
      have hreg12 : ∀ r, s12.getReg r = s11.getReg r := fun r => by
        simp [s12, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      have hout12 : MemEqOutside s11 s12 4120 4128 := by
        intro q hq hout
        simp only [s12, execInstrBr, ha50, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
        exact setMem_getByte_ofNat s11 4120 q 0#64 (by decide) (by omega) hq hout
      have hgap12 : readBuffer s12 4120 8 = 0 := by
        rw [readBuffer_word s12 4120 (by decide)]
        simp only [s12, execInstrBr, ha50, MachineState.getMem_setPC, MachineState.getMem_setMem_eq, getReg_x0]; rfl
      have hst51 := step_ordinary oracle s12 51 (.ADDI .x12 .x21 0#12) (by decide) hpc12 rfl (by intro h; cases h) rfl
      let s13 := execInstrBr s12 (.ADDI .x12 .x21 0#12)
      have hpc13 : s13.pc = pcWord 52 := by simp only [s13, execInstrBr, MachineState.setPC, hpc12, pcWord_add_four]
      have hmem13 : s13.mem = s12.mem := by simp [s13, execInstrBr, mem_setPC, mem_setReg]
      have hsrc13 : s13.getReg .x25 = BitVec.ofNat 64 (10804531232 + pOff) := by
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), hreg12,
          hreg11 .x25 (by decide),
          hreg9_base .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x25]
      have hdst13 : s13.getReg .x12 = BitVec.ofNat 64 4096 := by
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg12, hx21_11, se12_0, BitVec.add_zero]
      obtain ⟨s14, hs14, hpc14, hx25_14, hreg14, hcopy14, hout14⟩ :=
        step_call_read_n oracle 52 24 s13 (10804531232 + pOff) 4096 (by decide) (by decide) (by decide)
          rfl rfl hpc13 hsrc13 hdst13 (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hout_9_14 : MemEqOutside s9 s14 4096 4128 :=
        (MemEqOutside.of_mem_eq hmem11 4096 4128).trans
          ((hout12.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem13 4096 4128).trans (hout14.mono (by omega) (by omega))))
      have hreg14_9 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s14.getReg r = s9.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        rw [hreg14 r h1 h6 h10 h12 h25]
        simp only [s13, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg12 r, hreg11 r h7]
      have hgap14 : readBuffer s14 (4096 + 24) 8 = 0 := by
        rw [show 4096 + 24 = 4120 by omega,
          hout14.readBuffer_eq (by omega) (by omega),
          (MemEqOutside.of_mem_eq hmem13 0 0).readBuffer_eq (by omega) (by omega), hgap12]
      have hinpF : readBuffer s14 4096 64 = iC3 := by
        rw [readBuffer_lateOdd s14 4096 hgap14]
        have hdstA : dstA = 4128 := by dsimp only [dstA]; omega
        have ha14 : readBuffer s14 (4096 + 32) 32 = a :=
          (hout_9_14.readBuffer_eq (by omega) (by omega)).trans (by rw [show 4096 + 32 = 4128 by omega, ← hdstA, ha9])
        have hsalt14 : readBuffer s14 4096 24 = pw.salt := by
          unfold pw parsePartialWitness
          apply readBuffer_congr2; intro j hj
          rw [hcopy14 j hj]
          have h13_0 : InputMemPreserved s0 (ord + 1) s13 :=
            hinp9.trans_low ((MemEqOutside.of_mem_eq hmem11 4120 4128).trans
              (hout12.trans (MemEqOutside.of_mem_eq hmem13 4120 4128))) (by omega)
          exact h13_0 (10804531232 + pOff + j) (by omega) (Or.inr (by omega))
        rw [ha14, hsalt14]
        simp only [iC3, leafFinalInput, show pw.index.val % 2 ≠ 0 from heven, ite_false]
      have hcur14 : ProofCursor s0 input.proof.length (pOff + 24) tOff s14 := by
        refine ⟨hge24, ?_, ?_, ?_, ?_⟩
        · rw [hx25_14]; congr 1
        · rw [hreg14_9 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg9_base .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x31]
        · rw [hreg14_9 .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg9_base .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x3]
        · rw [hreg14_9 .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg9_base .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcur.x4]
      refine hfinish s14 149 (by decide)
        (((hst50.trans hst51).trans hs14).eq_of rfl (by decide) (by decide) (by simp))
        hpc14
        (hfix.of_agree (fun r hr => (hreg14_9 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl)).trans
          (hreg9_base r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl))))
        ((hreg14_9 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11_9)
        ((hreg14_9 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13_9)
        hcur14 (hout_9_14.mono (by omega) (by omega))
        ((hreg14_9 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20_9)
        ((hreg14_9 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg9_base .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24))
        ((hreg14_9 .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg9_base .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8))
        ((hreg14_9 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg9_base .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27))
        hinpF

/-- Shared 32-byte sibling load + compression block used by both L0 (`base = 58`) and L1 (`base = 81`):
bounds check (2), parity dispatch (2), odd copy+read32 or even read32 (≤ 205), compress (3) -> `base + 22`. -/
private theorem step_bin32_block (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (s0 : MachineState) (proofLen : Nat) (hplen : proofLen ≤ proofCap)
    (base pCur tOff idxVal : Nat) (curD : Digest)
    (hhi : base + 22 ≤ 243)
    (hidx_lt : idxVal < 2 ^ 64)
    (hc0 : checkInstr base = .base (.ADDI .x6 .x25 32#12))
    (hc1 : checkInstr (base + 1) = .base (.BLTU .x31 .x6 (BitVec.ofNat 13 (4 * (243 - (base + 1))))))
    (hc2 : checkInstr (base + 2) = .base (.ANDI .x7 .x22 1#12))
    (hc3 : checkInstr (base + 3) = .base (.BEQ .x7 .x0 52#13))
    (hcopy : ∀ j < 4,
      checkInstr (base + 4 + 2 * j) = .base (.LD .x6 .x21 (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 4 + 2 * j + 1) = .base (.SD .x21 .x6 (BitVec.ofNat 12 (32 + 8 * j))))
    (hc12 : checkInstr (base + 12) = .base (.ADDI .x12 .x21 0#12))
    (hc13 : checkInstr (base + 13) = .base (.ADDI .x10 .x0 32#12))
    (hc14 : checkInstr (base + 14) = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (246 - (base + 14))))))
    (hc15 : checkInstr (base + 15) = .base (.JAL .x0 16#21))
    (hc16 : checkInstr (base + 16) = .base (.ADDI .x12 .x21 32#12))
    (hc17 : checkInstr (base + 17) = .base (.ADDI .x10 .x0 32#12))
    (hc18 : checkInstr (base + 18) = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (246 - (base + 18))))))
    (hc19 : checkInstr (base + 19) = .base (.ADDI .x10 .x21 0#12))
    (hc20 : checkInstr (base + 20) = .base (.ADDI .x12 .x21 0#12))
    (hc21 : checkInstr (base + 21) = .base .ECALL)
    (s : MachineState) (hpc : s.pc = pcWord base)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor s0 proofLen pCur tOff s)
    (hhigh : HighMemPreserved s0 s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idxVal)
    (hcurD : readBuffer s 4096 32 = curD) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let sibD := readBuffer s0 (10804531232 + pCur) 32
    let inp := if idxVal % 2 = 0 then binaryInput curD sibD else binaryInput sibD curD
    PhaseOutcome oracle s 215 1 (proofLen < pCur + 32 + tailBytes tOff)
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = pcWord (base + 22) ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 proofLen (pCur + 32) tOff s' ∧
        MemEqOutside s s' 4096 4160 ∧
        (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s'.getReg r = s.getReg r) ∧
        readBuffer s' 4096 32 = c64 inp ∧
        InCompRows h512 oracle tr inp) := by
  intro c64 sibD inp
  have hplen_bd : proofLen ≤ 8480886496 := hplen
  have hle_cur : pCur + tailBytes tOff ≤ proofLen := hcur.le
  -- base..base+1: bounds check 32B
  have hst0 := step_ordinary oracle s base (.ADDI .x6 .x25 32#12) (by omega) hpc hc0 (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x6 .x25 32#12)
  have hpc1 : s1.pc = pcWord (base + 1) := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 (10804531232 + pCur + 32) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hcur.x25, se12_32]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; exact bv64_add _ 32
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (10804531232 + (proofLen - tailBytes tOff)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hcur.x31]
  let offRej := BitVec.ofNat 13 (4 * (243 - (base + 1)))
  have hst1 := step_ordinary oracle s1 (base + 1) (.BLTU .x31 .x6 offRej) (by omega) hpc1 hc1 (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BLTU .x31 .x6 offRej)
  have hult : BitVec.ult (s1.getReg .x31) (s1.getReg .x6) = decide (proofLen < pCur + 32 + tailBytes tOff) := by
    rw [hx31_1, hx6_1, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort : proofLen < pCur + 32 + tailBytes tOff
  · have hpc2 : s2.pc = pcWord 243 := by
      simp only [s2, execInstrBr, hult, hshort, decide_true, ite_true, MachineState.setPC, hpc1]
      have hse : signExtend13 offRej = BitVec.ofNat 64 (4 * (243 - (base + 1))) :=
        signExtend13_ofNat_lt4096 _ (by omega)
      rw [hse, pcWord, bv64_add]; congr 1; omega
    exact .rejected 5 0 [] hshort (by decide) (by decide)
      (by simpa using (hst0.trans hst1).halt (halt_reject oracle s2 hpc2))
  · have hge32 : pCur + 32 + tailBytes tOff ≤ proofLen := by omega
    have hpc2 : s2.pc = pcWord (base + 2) := by
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
    -- base+2..base+3: parity test
    have hst2 := step_ordinary oracle s2 (base + 2) (.ANDI .x7 .x22 1#12) (by omega) hpc2 hc2 (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ANDI .x7 .x22 1#12)
    have hpc3 : s3.pc = pcWord (base + 3) := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (idxVal % 2) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x22 (by decide), hx22, se12_1]
      exact bv64_and_one idxVal hidx_lt
    have hst3 := step_ordinary oracle s3 (base + 3) (.BEQ .x7 .x0 52#13) (by omega) hpc3 hc3 (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.BEQ .x7 .x0 52#13)
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hpre4 : StepsTo oracle s s4 4 0 [] :=
      ((hst0.trans hst1).trans (hst2.trans hst3)).eq_of rfl (by decide) (by decide) (by simp)
    -- Common finish base+19..base+21 -> base+22
    have hfinish : ∀ (s19 : MachineState) (kMid : Nat),
        kMid ≤ 208 →
        StepsTo oracle s4 s19 kMid 0 [] →
        s19.pc = pcWord (base + 19) →
        ProofCursor s0 proofLen (pCur + 32) tOff s19 →
        MemEqOutside s s19 4096 4160 →
        (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s19.getReg r = s.getReg r) →
        readBuffer s19 4096 64 = inp →
        PhaseOutcome oracle s 215 1 (proofLen < pCur + 32 + tailBytes tOff)
          (fun s' q tr =>
            q = 1 ∧ s'.pc = pcWord (base + 22) ∧ CheckFixedRegs s' ∧
            s'.getReg .x11 = 64#64 ∧ s'.getReg .x13 = 0#64 ∧
            ProofCursor s0 proofLen (pCur + 32) tOff s' ∧
            MemEqOutside s s' 4096 4160 ∧
            (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
              s'.getReg r = s.getReg r) ∧
            readBuffer s' 4096 32 = c64 inp ∧
            InCompRows h512 oracle tr inp) := by
      intro s19 kMid hkMid hmid hpc19 hcur19 hout19 hreg19 hinp19
      have hst19 := step_ordinary oracle s19 (base + 19) (.ADDI .x10 .x21 0#12) (by omega) hpc19 hc19 (by intro h; cases h) rfl
      let s20 := execInstrBr s19 (.ADDI .x10 .x21 0#12)
      have hpc20 : s20.pc = pcWord (base + 20) := by simp only [s20, execInstrBr, MachineState.setPC, hpc19, pcWord_add_four]
      have hst20 := step_ordinary oracle s20 (base + 20) (.ADDI .x12 .x21 0#12) (by omega) hpc20 hc20 (by intro h; cases h) rfl
      let s21 := execInstrBr s20 (.ADDI .x12 .x21 0#12)
      have hpc21 : s21.pc = pcWord (base + 21) := by simp only [s21, execInstrBr, MachineState.setPC, hpc20, pcWord_add_four]
      have hmem21 : s21.mem = s19.mem := by simp [s21, s20, execInstrBr, mem_setPC, mem_setReg]
      have hreg21 : ∀ r, r ≠ .x10 → r ≠ .x12 → s21.getReg r = s19.getReg r := fun r h10 h12 => by
        simp only [s21, s20, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h10.symm]
      have hx21_19 : s19.getReg .x21 = 4096#64 :=
        (hreg19 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21
      have hx10_21 : s21.getReg .x10 = 4096#64 := by
        simp only [s21, s20, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide), hx21_19, se12_0, BitVec.add_zero]
      have hx12_21 : s21.getReg .x12 = 4096#64 := by
        simp only [s21, s20, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide),
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x21),
          hx21_19, se12_0, BitVec.add_zero]
      have hec := step_ecall_compress h512 oracle s21 (base + 21) 4096 4096 (by omega) hpc21 hc21
        ((hreg21 .x5 (by decide) (by decide)).trans ((hreg19 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5))
        ((hreg21 .x11 (by decide) (by decide)).trans ((hreg19 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
        ((hreg21 .x13 (by decide) (by decide)).trans ((hreg19 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
        hx10_21 hx12_21 (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      rw [(MemEqOutside.of_mem_eq hmem21 0 0).readBuffer_eq (by omega) (by omega), hinp19] at hec
      let sFin := writeBits s21 (BitVec.ofNat 64 4096) (c64 inp)
      have hpcFin : sFin.pc = pcWord (base + 22) := by
        simp only [sFin, writeBits, MachineState.setPC, hpc21, pcWord_add_four]
      have hregFin : ∀ r, r ≠ .x10 → r ≠ .x12 → sFin.getReg r = s19.getReg r := fun r h10 h12 =>
        (writeBits_register s21 _ _ r).trans (hreg21 r h10 h12)
      have hregFin_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          sFin.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 =>
        (hregFin r h10 h12).trans (hreg19 r h1 h6 h7 h10 h12 h25)
      have htot := (hpre4.trans hmid).trans ((hst19.trans hst20).trans hec)
      refine .continued sFin (4 + kMid + 3) 1 [PublicRow.compression (inp.cast h512.symm) (c64 inp)]
        (by omega) (by decide)
        (htot.eq_of rfl (by omega) (by decide) (by simp [c64]))
        ⟨rfl, hpcFin,
         hfix.of_agree (fun r hr => hregFin_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
           (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
           (isFixedReg_ne_of_false hr rfl)),
         (hregFin_s .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11,
         (hregFin_s .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13,
         hcur19.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
         hout19.trans ((MemEqOutside.of_mem_eq hmem21 4096 4160).trans
           ((MemEqOutside_writeBits_digest s21 4096 _ (by omega)).mono (by omega) (by omega))),
         hregFin_s, writeBits_readBuffer_digest s21 4096 (c64 inp), InCompRows.singleton h512 oracle inp⟩
    by_cases heven : idxVal % 2 = 0
    · -- Even: BEQ jumps to base+16..base+18 -> base+19
      have hx7z : s3.getReg .x7 = 0#64 := by rw [hx7_3, heven]
      have hpc4 : s4.pc = pcWord (base + 16) := by
        simp only [s4, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc3]
        rw [signExtend13_ofNat_lt4096 52 (by decide), pcWord, bv64_add]; congr 1
      have hmem4 : s4.mem = s.mem := by
        simpa [s4, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem3
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → s4.getReg r = s.getReg r := fun r h6 h7 => by
        simp only [s4, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg2 r h6
      have hst16 := step_ordinary oracle s4 (base + 16) (.ADDI .x12 .x21 32#12) (by omega) hpc4 hc16 (by intro h; cases h) rfl
      let s5 := execInstrBr s4 (.ADDI .x12 .x21 32#12)
      have hpc5 : s5.pc = pcWord (base + 17) := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
      have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
      have hsrc5 : s5.getReg .x25 = BitVec.ofNat 64 (10804531232 + pCur) := by
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
          hreg4 .x25 (by decide) (by decide), hcur.x25]
      have hdst5 : s5.getReg .x12 = BitVec.ofNat 64 4128 := by
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg4 .x21 (by decide) (by decide), hfix.x21, se12_32]; decide
      obtain ⟨s6, hs6, hpc6, hx25_6, hreg6, hcopy6, hout6⟩ :=
        step_call_read_n oracle (base + 17) 32 s5 (10804531232 + pCur) 4128 (by decide) (by decide) (by omega)
          hc17 (by simpa [show base + 17 + 1 = base + 18 by omega] using hc18) hpc5 hsrc5 hdst5
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hpc6' : s6.pc = pcWord (base + 19) := by simpa only [show base + 17 + 2 = base + 19 by omega] using hpc6
      have hout_all : MemEqOutside s s6 4128 4160 :=
        (MemEqOutside.of_mem_eq hmem5 4128 4160).trans hout6
      have hreg6_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s6.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        rw [hreg6 r h1 h6 h10 h12 h25]
        simp only [s5, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm]
        exact hreg4 r h6 h7
      have hinp6 : readBuffer s6 4096 64 = inp := by
        rw [readBuffer_binary s6 4096]
        have hL : readBuffer s6 4096 32 = curD :=
          (hout_all.readBuffer_eq (by omega) (by omega)).trans hcurD
        have hR : readBuffer s6 (4096 + 32) 32 = sibD := by
          rw [show 4096 + 32 = 4128 by omega]
          apply readBuffer_congr2; intro j hj
          rw [hcopy6 j hj]
          exact (hhigh.trans_mem_eq hmem5) (10804531232 + pCur + j) (by omega) (Or.inr (by omega))
        rw [hL, hR]; simp only [inp, heven, ite_true]
      have hcur6 : ProofCursor s0 proofLen (pCur + 32) tOff s6 := by
        refine ⟨hge32, by rw [hx25_6]; congr 1,
          (hreg6_s .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x31,
          (hreg6_s .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x3,
          (hreg6_s .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x4⟩
      exact hfinish s6 196 (by decide)
        ((hst16.trans hs6).eq_of rfl (by decide) (by decide) (by simp))
        hpc6' hcur6 (hout_all.mono (by omega) (by omega)) hreg6_s hinp6
    · -- Odd: fall through to base+4..base+15 -> base+19
      have hodd : idxVal % 2 = 1 := by omega
      have hx7o : s3.getReg .x7 = 1#64 := by rw [hx7_3, hodd]
      have hpc4 : s4.pc = pcWord (base + 4) := by
        simp only [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc3, pcWord_add_four]
      have hmem4 : s4.mem = s.mem := by
        simpa [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          MachineState.setPC] using hmem3
      have hreg4 : ∀ r, r ≠ .x6 → r ≠ .x7 → s4.getReg r = s.getReg r := fun r h6 h7 => by
        simp only [s4, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
          Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
        exact hreg2 r h6
      obtain ⟨s5, hs5, hpc5, hreg5, hcopy5, hout5⟩ :=
        step_copy_dwords oracle (base + 4) 4 .x21 .x21 0 32 s4 4096 4096
          (by decide) (by decide) (by decide) (by decide) (by omega)
          (fun j hj => by simpa only [Nat.zero_add] using hcopy j hj) hpc4
          ((hreg4 .x21 (by decide) (by decide)).trans hfix.x21)
          ((hreg4 .x21 (by decide) (by decide)).trans hfix.x21)
          (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide) (by omega)
      have hpc5' : s5.pc = pcWord (base + 12) := by simpa only [show base + 4 + 2 * 4 = base + 12 by omega] using hpc5
      have hst12 := step_ordinary oracle s5 (base + 12) (.ADDI .x12 .x21 0#12) (by omega) hpc5' hc12 (by intro h; cases h) rfl
      let s6 := execInstrBr s5 (.ADDI .x12 .x21 0#12)
      have hpc6 : s6.pc = pcWord (base + 13) := by simp only [s6, execInstrBr, MachineState.setPC, hpc5', pcWord_add_four]
      have hmem6 : s6.mem = s5.mem := by simp [s6, execInstrBr, mem_setPC, mem_setReg]
      have hsrc6 : s6.getReg .x25 = BitVec.ofNat 64 (10804531232 + pCur) := by
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25),
          hreg5 .x25 (by decide), hreg4 .x25 (by decide) (by decide), hcur.x25]
      have hdst6 : s6.getReg .x12 = BitVec.ofNat 64 4096 := by
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg5 .x21 (by decide),
          hreg4 .x21 (by decide) (by decide), hfix.x21, se12_0, BitVec.add_zero]
      obtain ⟨s7, hs7, hpc7, hx25_7, hreg7, hcopy7, hout7⟩ :=
        step_call_read_n oracle (base + 13) 32 s6 (10804531232 + pCur) 4096 (by decide) (by decide) (by omega)
          hc13 (by simpa [show base + 13 + 1 = base + 14 by omega] using hc14) hpc6 hsrc6 hdst6
          (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide) (by omega)
      have hpc7' : s7.pc = pcWord (base + 15) := by simpa only [show base + 13 + 2 = base + 15 by omega] using hpc7
      have hst15 := step_ordinary oracle s7 (base + 15) (.JAL .x0 16#21) (by omega) hpc7' hc15 (by intro h; cases h) rfl
      let s8 := execInstrBr s7 (.JAL .x0 16#21)
      have hpc8 : s8.pc = pcWord (base + 19) := by
        simp only [s8, execInstrBr, MachineState.setPC, hpc7']
        rw [signExtend21_ofNat_lt 16 (by decide), pcWord, bv64_add]; congr 1
      have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, mem_setPC, mem_setReg]
      have hout_all : MemEqOutside s s8 4096 4160 :=
        (MemEqOutside.of_mem_eq hmem4 4096 4160).trans
          ((hout5.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem6 4096 4160).trans
              ((hout7.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem8 4096 4160))))
      have hreg8_s : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 →
          s8.getReg r = s.getReg r := fun r h1 h6 h7 h10 h12 h25 => by
        have h87 : s8.getReg r = s7.getReg r := by simp [s8, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        rw [h87, hreg7 r h1 h6 h10 h12 h25]
        simp only [s6, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg5 r h6]
        exact hreg4 r h6 h7
      have hinp8 : readBuffer s8 4096 64 = inp := by
        rw [readBuffer_binary s8 4096]
        have hL : readBuffer s8 4096 32 = sibD := by
          rw [(MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by omega) (by omega)]
          apply readBuffer_congr2; intro j hj
          rw [hcopy7 j hj]
          have h6_0 : HighMemPreserved s0 s6 :=
            hhigh.trans_low ((MemEqOutside.of_mem_eq hmem4 4128 4160).trans
              (hout5.trans (MemEqOutside.of_mem_eq hmem6 4128 4160))) (by omega)
          exact h6_0 (10804531232 + pCur + j) (by omega) (Or.inr (by omega))
        have hR : readBuffer s8 (4096 + 32) 32 = curD := by
          rw [show 4096 + 32 = 4128 by omega,
            (MemEqOutside.of_mem_eq hmem8 0 0).readBuffer_eq (by omega) (by omega),
            hout7.readBuffer_eq (by omega) (by omega),
            (MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega), ← hcurD]
          apply readBuffer_congr2; intro j hj
          have hc := hcopy5 j hj
          simp only [Nat.add_zero, show 4096 + 32 = 4128 by omega] at hc
          rw [hc]; simp only [MachineState.getByte, MachineState.getMem, hmem4]
        rw [hL, hR]; simp only [inp, heven, ite_false]
      have hcur8 : ProofCursor s0 proofLen (pCur + 32) tOff s8 := by
        refine ⟨hge32, ?_,
          (hreg8_s .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x31,
          (hreg8_s .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x3,
          (hreg8_s .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcur.x4⟩
        have : s8.getReg .x25 = s7.getReg .x25 := by simp [s8, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        rw [this, hx25_7]; congr 1
      exact hfinish s8 205 (by decide)
        ((((hs5.trans hst12).trans hs7).trans hst15).eq_of rfl (by decide) (by decide) (by simp))
        hpc8 hcur8 hout_all hreg8_s hinp8

/-- Phase 1B: L0 binary step (`pc[58..80]` -> `pc[81]`, unmasked 256-bit output). -/
theorem step_pos_l0 (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 58)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 24) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx 0 (posAt input.positions ord).val))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hcurD : readBuffer s 4096 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation 0) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 220 1 (input.proof.length < pOff + 56 + tailBytes tOff)
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = pcWord 81 ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 56) tOff s' ∧
        MemEqOutside s s' 4096 4160 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (heapIdx 1 (i.val >>> 1)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation 1 ∧
        InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation 0)) := by
  intro s0 c64 i pw
  have hidx_lt : heapIdx 0 i.val < 2 ^ 64 := Nat.lt_trans (heapIdx_shiftRight_lt i 0 (by omega)) (by omega)
  have hblk := step_bin32_block h512 oracle s0 input.proof.length hvalid 58 (pOff + 24) tOff
    (heapIdx 0 i.val) (pw.evalLevel c64 oracle.permutation 0) (by decide) hidx_lt
    rfl rfl rfl rfl (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    s hpc hfix hx11 hx13 hcur hhigh hx22 hcurD
  have hmod : heapIdx 0 i.val % 2 = (i.val >>> 0) % 2 := by
    simpa only [Nat.shiftRight_zero] using heapIdx_mod_two 0 i.val (by omega)
  have hinp_eq :
      (if heapIdx 0 i.val % 2 = 0 then binaryInput (pw.evalLevel c64 oracle.permutation 0) (readBuffer s0 (10804531232 + (pOff + 24)) 32)
       else binaryInput (readBuffer s0 (10804531232 + (pOff + 24)) 32) (pw.evalLevel c64 oracle.permutation 0)) =
      pw.levelInput c64 oracle.permutation 0 := by
    have hsib0 : pw.binSib 0 = readBuffer s0 (10804531232 + (pOff + 24)) 32 := by
      dsimp only [pw, parsePartialWitness]
      simp only [ite_true, Nat.add_assoc]
    unfold WitnessPath.levelInput
    rw [hmod, hsib0]; rfl
  have hbound_eq : (pOff + 24 + 32 : Nat) = pOff + 56 := by omega
  refine (hblk.bind_dep (K2 := 1) (Q2 := 0) (by rw [hbound_eq]; exact id) (fun s80 q1 tr1 ⟨hq1, hpc80, hfix80, h11_80, h13_80,
      hcur80, hout80, hreg80, hdig80, htr80⟩ => by
    have hst80 := step_ordinary oracle s80 80 (.SRLI .x22 .x22 1#6) (by decide) hpc80 rfl (by intro h; cases h) rfl
    let s81 := execInstrBr s80 (.SRLI .x22 .x22 1#6)
    have hpc81 : s81.pc = pcWord 81 := by simp only [s81, execInstrBr, MachineState.setPC, hpc80, pcWord_add_four]
    have hmem81 : s81.mem = s80.mem := by simp [s81, execInstrBr, mem_setPC, mem_setReg]
    have hreg81 : ∀ r, r ≠ .x22 → s81.getReg r = s80.getReg r := fun r h22 => by
      simp only [s81, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h22.symm
    have hx22_81 : s81.getReg .x22 = BitVec.ofNat 64 (heapIdx 1 (i.val >>> 1)) := by
      simp only [s81, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        hreg80 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hx22, show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr _ 1 hidx_lt, Nat.pow_one]
      simpa only [Nat.shiftRight_zero] using congrArg (BitVec.ofNat 64) (heapIdx_shiftRight_div2 i 0 (by omega))
    refine .continued s81 1 0 [] (by decide) (by decide) hst80 ?_
    rw [hq1, Nat.add_zero, List.append_nil]
    refine ⟨rfl, hpc81,
      hfix80.of_agree (fun r hr => hreg81 r (isFixedReg_ne_of_false hr rfl)),
      (hreg81 .x11 (by decide)).trans h11_80,
      (hreg81 .x13 (by decide)).trans h13_80,
      by rw [← hbound_eq]; exact hcur80.of_agree (fun r hr => hreg81 r (isCursorReg_ne_of_false hr rfl)),
      hout80.trans (MemEqOutside.of_mem_eq hmem81 4096 4160),
      hx22_81,
      (hreg81 .x24 (by decide)).trans ((hreg80 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24),
      (hreg81 .x8  (by decide)).trans ((hreg80 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8),
      (hreg81 .x27 (by decide)).trans ((hreg80 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
      ?_, by rwa [← hinp_eq]⟩
    rw [(MemEqOutside.of_mem_eq hmem81 0 0).readBuffer_eq (by omega) (by omega), hdig80, hinp_eq]
    rfl)).weaken (by decide) (by decide) id (fun _ _ _ h => h)

/-- Phase 1C: L1 binary step (`pc[81..104]` -> `pc[105]`, `SH` 240-bit mask). -/
theorem step_pos_l1 (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (ord pOff tOff rem : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 81)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length (pOff + 56) tOff s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx 1 ((posAt input.positions ord).val >>> 1)))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord))
    (hx8  : s.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 rem)
    (hcurD : readBuffer s 4096 32 =
      (parsePartialWitness (submission.initialState .check input) input.proof.length pOff tOff
        (posAt input.positions ord) (valAt input ord)).evalLevel
        (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation 1) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let i := posAt input.positions ord
    let pw := parsePartialWitness s0 input.proof.length pOff tOff i (valAt input ord)
    PhaseOutcome oracle s 220 1 (input.proof.length < pOff + 88 + tailBytes tOff)
      (fun s' q tr =>
        q = 1 ∧
        s'.pc = pcWord 105 ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length (pOff + 88) tOff s' ∧
        MemEqOutside s s' 4096 4160 ∧
        s'.getReg .x22 = BitVec.ofNat 64 (heapIdx 2 (i.val >>> 2)) ∧
        s'.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * ord) ∧
        s'.getReg .x8  = BitVec.ofNat 64 (6509563936 + 256 * ord) ∧
        s'.getReg .x27 = BitVec.ofNat 64 rem ∧
        readBuffer s' 4096 32 = pw.evalLevel c64 oracle.permutation 2 ∧
        InCompRows h512 oracle tr (pw.levelInput c64 oracle.permutation 1)) := by
  intro s0 c64 i pw
  have hidx_lt : heapIdx 1 (i.val >>> 1) < 2 ^ 64 := Nat.lt_trans (heapIdx_shiftRight_lt i 1 (by omega)) (by omega)
  have hblk := step_bin32_block h512 oracle s0 input.proof.length hvalid 81 (pOff + 56) tOff
    (heapIdx 1 (i.val >>> 1)) (pw.evalLevel c64 oracle.permutation 1) (by decide) hidx_lt
    rfl rfl rfl rfl (fun j hj => by interval_cases j <;> exact ⟨rfl, rfl⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    s hpc hfix hx11 hx13 hcur hhigh hx22 hcurD
  have hmod : heapIdx 1 (i.val >>> 1) % 2 = (i.val >>> 1) % 2 := heapIdx_mod_two 1 (i.val >>> 1) (by omega)
  have hinp_eq :
      (if heapIdx 1 (i.val >>> 1) % 2 = 0
       then binaryInput (pw.evalLevel c64 oracle.permutation 1) (readBuffer s0 (10804531232 + (pOff + 56)) 32)
       else binaryInput (readBuffer s0 (10804531232 + (pOff + 56)) 32) (pw.evalLevel c64 oracle.permutation 1)) =
      pw.levelInput c64 oracle.permutation 1 := by
    have hsib1 : pw.binSib 1 = readBuffer s0 (10804531232 + (pOff + 56)) 32 := by
      dsimp only [pw, parsePartialWitness]
      simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, Nat.add_assoc]
    unfold WitnessPath.levelInput
    rw [hmod, hsib1]; rfl
  have hbound_eq : (pOff + 56 + 32 : Nat) = pOff + 88 := by omega
  refine (hblk.bind_dep (K2 := 2) (Q2 := 0) (by rw [hbound_eq]; exact id) (fun s103 q1 tr1 ⟨hq1, hpc103, hfix103, h11_103, h13_103,
      hcur103, hout103, hreg103, hdig103, htr103⟩ => by
    -- pc[103]: SH x21, x0, 30
    have ha103 : s103.getReg .x21 + signExtend12 30#12 = BitVec.ofNat 64 4126 := by
      rw [hfix103.x21, se12_30]; decide
    have hv103 : memoryArgumentsValid s103 (.SH .x21 .x0 30#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha103]
      exact accessValid_ofNat 4126 2 (by unfold MEMORY_BYTES; decide) (by decide)
    have hst103 := step_ordinary oracle s103 103 (.SH .x21 .x0 30#12) (by decide) hpc103 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv103])
    let s104 := execInstrBr s103 (.SH .x21 .x0 30#12)
    have hpc104 : s104.pc = pcWord 104 := by simp only [s104, execInstrBr, MachineState.setPC, hpc103, pcWord_add_four]
    have hreg104 : ∀ r, s104.getReg r = s103.getReg r := fun r => by
      simp [s104, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    have hout104 : MemEqOutside s103 s104 4126 4128 := by
      intro q hq hout
      simp only [s104, execInstrBr, ha103, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
      exact MemEqOutside_setHalfword s103 4126 _ (by decide) (by omega) q hq hout
    -- pc[104]: SRLI x22, x22, 1
    have hst104 := step_ordinary oracle s104 104 (.SRLI .x22 .x22 1#6) (by decide) hpc104 rfl (by intro h; cases h) rfl
    let s105 := execInstrBr s104 (.SRLI .x22 .x22 1#6)
    have hpc105 : s105.pc = pcWord 105 := by simp only [s105, execInstrBr, MachineState.setPC, hpc104, pcWord_add_four]
    have hmem105 : s105.mem = s104.mem := by simp [s105, execInstrBr, mem_setPC, mem_setReg]
    have hreg105 : ∀ r, r ≠ .x22 → s105.getReg r = s103.getReg r := fun r h22 => by
      simp only [s105, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h22.symm, hreg104 r]
    have hx22_105 : s105.getReg .x22 = BitVec.ofNat 64 (heapIdx 2 (i.val >>> 2)) := by
      simp only [s105, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg104 .x22,
        hreg103 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hx22, show (1#6 : BitVec 6).toNat = 1 by decide, bv64_shr _ 1 hidx_lt, Nat.pow_one]
      exact congrArg (BitVec.ofNat 64) (heapIdx_shiftRight_div2 i 1 (by omega))
    refine .continued s105 2 0 [] (by decide) (by decide)
      ((hst103.trans hst104).eq_of rfl (by decide) (by decide) (by simp)) ?_
    rw [hq1, Nat.add_zero, List.append_nil]
    refine ⟨rfl, hpc105,
      hfix103.of_agree (fun r hr => hreg105 r (isFixedReg_ne_of_false hr rfl)),
      (hreg105 .x11 (by decide)).trans h11_103,
      (hreg105 .x13 (by decide)).trans h13_103,
      by rw [← hbound_eq]; exact hcur103.of_agree (fun r hr => hreg105 r (isCursorReg_ne_of_false hr rfl)),
      hout103.trans ((hout104.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem105 4096 4160)),
      hx22_105,
      (hreg105 .x24 (by decide)).trans ((hreg103 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24),
      (hreg105 .x8  (by decide)).trans ((hreg103 .x8  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8),
      (hreg105 .x27 (by decide)).trans ((hreg103 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
      ?_, by rwa [← hinp_eq]⟩
    have hsh : readBuffer s104 4096 32 =
        readBuffer (s103.setHalfword (BitVec.ofNat 64 (4096 + 30)) 0#16) 4096 32 := by
      apply readBuffer_congr2; intro j hj
      simp [s104, execInstrBr, ha103, MachineState.getByte, MachineState.setHalfword,
        MachineState.getMem, MachineState.setMem, mem_setPC, getReg_x0,
        show (0#64 : Word).truncate 16 = 0#16 by decide]
    rw [(MemEqOutside.of_mem_eq hmem105 0 0).readBuffer_eq (by omega) (by omega),
      hsh, sh_zero_mask240 s103 4096 (by decide) (by omega), hdig103, hinp_eq]
    rfl)).weaken (by decide) (by decide) id (fun _ _ _ h => h)

end CommitGolfCandidate
