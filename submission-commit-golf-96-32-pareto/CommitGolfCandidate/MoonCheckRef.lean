import CommitGolfCandidate.MoonCheckExec
import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! End-to-end verification of the submitted pure-binary `check` image:
- `check_run_termination`: universal termination on all inputs within step fuel and `28 * k` oracle calls.
- `check_honest_accepts`: perfect completeness and `CHECK_BUDGET` bound on `referenceProof`.
- `check_sound`: `CheckSound h768` witness-path and compression-trace extraction for adaptive 238-bit binding. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Initial Invariant and Master Pipeline Composition -/

private theorem check_steps_eq : submission.steps .check = 274877906944 := rfl

private theorem submission_run_check_valid (s : Submission) (input : CheckInput)
    (h : input.proof.length ≤ s.sizes.proof) :
    s.run .check input = execute (s.image .check) (s.steps .check) (s.initialState .check input) false := by
  unfold Submission.run
  have hdec : decide (input.proof.length ≤ s.sizes.proof) = true := decide_eq_true h
  have hne : (Program.check != Program.check) = false := rfl
  dsimp only
  simp only [hdec, hne, ite_true]

private theorem submission_run_check_invalid (s : Submission) (input : CheckInput)
    (h : ¬ input.proof.length ≤ s.sizes.proof) :
    s.run .check input = pure ⟨.failure, initialMachine, 0, 0⟩ := by
  unfold Submission.run
  have hdec : decide (input.proof.length ≤ s.sizes.proof) = false := decide_eq_false h
  dsimp only
  simp only [hdec, Bool.false_eq_true, ite_false]

private theorem posLoopInv_init (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hne : input.positions.card ≠ 0)
    (s1 : MachineState) (hpc1 : s1.pc = pcWord 22)
    (hmem1 : s1.mem = (submission.initialState .check input).mem)
    (hfix1 : CheckFixedRegs s1)
    (hcur1 : ProofCursor (submission.initialState .check input) input.proof.length 0 0 s1)
    (hx24 : s1.getReg .x24 = BitVec.ofNat 64 7449087968)
    (hx8  : s1.getReg .x8  = BitVec.ofNat 64 7583305696)
    (hx27 : s1.getReg .x27 = BitVec.ofNat 64 input.positions.card) :
    PosLoopInv h768 oracle input 0 s1 [] := by
  have hbyte0 : ∀ a < 4294971392, s1.getByte (BitVec.ofNat 64 a) = 0#8 := fun a ha => by
    simp only [MachineState.getByte, MachineState.getMem, hmem1]
    exact check_initial_zero_low input a ha
  refine ⟨hfix1, by simpa [posRecordOff, posTailOff] using hcur1,
    MemEqOutside.of_mem_eq hmem1 0 4294971392,
    by simp [Nat.ne_of_lt (Nat.pos_of_ne_zero hne), hpc1],
    by simpa using hx24, by simpa using hx8, by simpa using hx27,
    ?_, ?_, ?_, ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  · intro c hc
    rw [posMarked16_zero, if_neg (by decide)]
    exact hbyte0 (4096 + c) (by omega)
  · intro a ha1 ha2
    exact hbyte0 a (by omega)
  · intro q hq b hb
    exact hbyte0 (8192 + 96 * q + 64 + b) (by omega)
  · intro a ha1 ha2
    exact hbyte0 a (by omega)

/-- Unified symbolic execution of the non-empty `check` program from `initialState` to `HALT`. -/
private theorem check_pipeline_nonempty (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let pTotal := posRecordOff input.positions.card + 29 * capFrontierCount input.positions
    let tTotal := posTailOff input.positions.card + capFrontierCount input.positions
    (¬ PosConsistent c96 s0 input input.positions.card ∧
      ∃ k q tr, k ≤ submission.steps .check ∧ q ≤ 28 * input.positions.card ∧
        HaltsWith oracle s0 k q .failure tr) ∨
    (input.proof.length < pTotal + tailBytes tTotal ∧
      ∃ k q tr, k ≤ submission.steps .check ∧ q ≤ 28 * input.positions.card ∧
        HaltsWith oracle s0 k q .failure tr) ∨
    (∃ sPos sCap qPos qCap trPos trCap kFin,
      kFin ≤ submission.steps .check ∧
      qPos + qCap ≤ 28 * input.positions.card ∧
      PosLoopInv h768 oracle input input.positions.card sPos trPos ∧
      CapWalkInv h768 oracle input sPos 8 sCap trCap ∧
      HaltsWith oracle s0 kFin (qPos + qCap)
        (if pTotal + tailBytes tTotal == input.proof.length &&
            tailBuf s0 input.proof.length tTotal == 0 &&
            readBuffer sCap (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
         then Exit.success else Exit.failure)
        (trPos ++ trCap)) := by
  intro s0 c96 pTotal tTotal
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hsteps_bd : 20 + 3677 * input.positions.card + 60000 + 25 ≤ submission.steps .check := by
    rw [check_steps_eq]; omega
  obtain ⟨s1, hs1, hpc1, hmem1, hfix1, hcur1, hx24, hx8, hx27⟩ :=
    step_prologue_nonempty oracle input hne
  have hinit := posLoopInv_init h768 oracle input hne s1 hpc1 hmem1 hfix1 hcur1 hx24 hx8 hx27
  have hpos := step_pos_loop h768 oracle input hvalid hne s1 hinit
  cases hpos with
  | rejected kPos qPos trPos hnot hkPos hqPos hhPos =>
    left
    refine ⟨hnot, 20 + kPos, qPos, trPos, by omega, by omega, ?_⟩
    simpa using hs1.halt hhPos
  | continued sPos kPos qPos trPos hkPos hqPos hsPos hpPos =>
    obtain ⟨hqPos_le, hinvPos⟩ := hpPos
    have hcap := step_cap_walk h768 oracle input hvalid sPos trPos hinvPos
    cases hcap with
    | rejected kCap qCap trCap hshort hkCap hqCap hhCap =>
      right; left
      refine ⟨hshort, 20 + kPos + kCap, qPos + qCap, trPos ++ trCap, by omega, by omega, ?_⟩
      simpa [Nat.add_assoc] using (hs1.trans hsPos).halt hhCap
    | continued sCap kCap qCap trCap hkCap hqCap hsCap hpCap =>
      obtain ⟨hqCap_le, hinvCap⟩ := hpCap
      have hpc212 : sCap.pc = pcWord 212 := by have := hinvCap.pc; rwa [if_pos rfl] at this
      have hcur_fin : ProofCursor s0 input.proof.length pTotal tTotal sCap := by
        simpa only [capFrontierPrefix_8, pTotal, tTotal] using hinvCap.cursor
      have hepi := step_epilogue oracle input hvalid pTotal tTotal sCap hpc212
        hinvCap.fixed hcur_fin hinvCap.high
      right; right
      refine ⟨sPos, sCap, qPos, qCap, trPos, trCap, 20 + kPos + kCap + 25,
        by omega, by omega, hinvPos, hinvCap, ?_⟩
      simpa [Nat.add_assoc] using ((hs1.trans hsPos).trans hsCap).halt hepi

/-! ### 2. Termination (`check_run_termination`) -/

theorem check_run_termination (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) :
    ∃ exec : Execution,
      oracle.run (submission.run .check input) = pure (exec, exec.oracleCalls) ∧
      exec.exit ≠ .unfinished ∧
      exec.oracleCalls ≤ 28 * input.positions.card := by
  by_cases hvalid : input.proof.length ≤ submission.sizes.proof
  · have hrun : submission.run .check input =
        execute (submission.image .check) (submission.steps .check)
          (submission.initialState .check input) false :=
      submission_run_check_valid submission input hvalid
    rw [hrun, oracle_run_execute_false]
    let r := detExec oracle (submission.image .check) (submission.steps .check)
      (submission.initialState .check input)
    refine ⟨r.1, rfl, ?_⟩
    by_cases hempty : input.positions.card = 0
    · have hh := step_prologue_empty oracle input hvalid hempty
      have hev := hh.eval_of_le (show 12 ≤ submission.steps .check by rw [check_steps_eq]; omega)
      refine ⟨?_, ?_⟩
      · rw [hev.1]; split <;> decide
      · rw [hev.2.1]; omega
    · rcases check_pipeline_nonempty h768 oracle input hvalid hempty with
        ⟨_, k, q, tr, hk, hq, hh⟩ | ⟨_, k, q, tr, hk, hq, hh⟩ |
        ⟨_, _, qPos, qCap, _, _, kFin, hk, hq, _, _, hh⟩
      · have hev := hh.eval_of_le hk
        exact ⟨by rw [hev.1]; decide, by rw [hev.2.1]; exact hq⟩
      · have hev := hh.eval_of_le hk
        exact ⟨by rw [hev.1]; decide, by rw [hev.2.1]; exact hq⟩
      · have hev := hh.eval_of_le hk
        exact ⟨by rw [hev.1]; split <;> decide, by rw [hev.2.1]; exact hq⟩
  · have hrun : submission.run .check input = pure ⟨.failure, initialMachine, 0, 0⟩ :=
      submission_run_check_invalid submission input hvalid
    rw [hrun, oracle_run_pure]
    exact ⟨⟨.failure, initialMachine, 0, 0⟩, rfl, by decide, Nat.zero_le _⟩

/-! ### 3. Soundness (`check_sound`) -/

private theorem valAt_eq_of_posAt (input : CheckInput) (ord : Nat)
    (hord : ord < input.positions.card) (i : Index) (hi : i ∈ input.positions)
    (hpos : posAt input.positions ord = i) :
    valAt input ord = input.values ⟨i, hi⟩ := by
  unfold valAt
  rw [dif_pos hord]
  congr 1
  apply Subtype.ext
  apply Fin.ext
  rw [sorted_value_index input.positions ord hord, ← posAt_val input.positions ord hord, hpos]

private theorem shiftRight_succ_eq_div2 (g k : Nat) :
    g >>> (k + 1) = (g >>> k) / 2 := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]

private theorem maskLevel_cap_eq (l : Nat) (hl1 : 16 ≤ l) (hl2 : l < 24) (d : Digest) :
    maskLevel (l + 1) d = if l = 23 then d else mask238 d := by
  unfold maskLevel FIRST_240_LVL FIRST_238_LVL
  by_cases h23 : l = 23
  · simp [h23]
  · rw [if_neg (by omega), if_neg (by omega), if_neg h23]

private theorem getElem_eq_of_idx {α : Type} {l : List α} {i1 i2 : Nat} (h : i1 = i2)
    (h1 : i1 < l.length) (h2 : i2 < l.length) : l[i1]'h1 = l[i2]'h2 := by
  subst h; rfl

private theorem evalLevel_congr_low (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt)
    (hbin : ∀ prev < 16, w1.binSib prev = w2.binSib prev) :
    ∀ l ≤ 16, w1.evalLevel c l = w2.evalLevel c l := by
  intro l hl
  induction l with
  | zero => simp [WitnessPath.evalLevel, hidx, hval, hsalt]
  | succ k ih =>
    have hih := ih (by omega)
    have hsb := hbin k (by omega)
    simp only [WitnessPath.evalLevel, hidx, hih, hsb]

private theorem check_sound_cap_climb (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) (sPos sCap : MachineState) (trCap : CompressionReplies)
    (hinvCap : CapWalkInv h768 oracle input sPos 8 sCap trCap)
    (i : Index) (hi : i ∈ input.positions) (w : WitnessPath)
    (hw_idx : w.index = i)
    (hw16 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 16 =
      readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32)
    (hbin_cap : ∀ prev, ¬ (prev < 16) →
      w.binSib prev = readBuffer sCap (8192 + capValOff prev + gapOffset ((i.val >>> prev) ^^^ 1)) 32) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∀ d ≤ 8,
      let idx := i.val >>> (16 + d)
      idx < levelSize (16 + d) ∧
      capMark input.positions (16 + d) idx = true ∧
      w.evalLevel c96 (16 + d) = readBuffer sCap (8192 + capValOff (16 + d) + gapOffset idx) 32 ∧
      ∀ d' < d, InTrace h768 oracle trCap (w.levelInput c96 (16 + d')) := by
  intro c96 d hd
  induction d with
  | zero =>
    refine ⟨by rw [levelSize_16]; exact capLeafOf_lt i,
      by rw [capMark_16, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩,
      ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    have hc_lt : capLeafOf i < 256 := capLeafOf_lt i
    have hcm16 : capMark input.positions 16 (capLeafOf i) = true := by
      rw [capMark_16, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩
    have h16 := hinvCap.val16_marked (capLeafOf i) hc_lt hcm16
    simpa only [Nat.add_zero, show i.val >>> 16 = capLeafOf i from rfl] using
      hw16.trans h16.symm
  | succ d ih =>
    obtain ⟨hidx_lt, hcm_d, heval_d, htr_d⟩ := ih (by omega)
    let l := 16 + d
    let idx := i.val >>> (16 + d)
    let q := idx / 2
    have hidx_lt' : idx < levelSize l := hidx_lt
    have hcm_d' : capMark input.positions l idx = true := hcm_d
    have heval_d' : w.evalLevel c96 l = readBuffer sCap (8192 + capValOff l + gapOffset idx) 32 := heval_d
    have hidx_next : i.val >>> (16 + (d + 1)) = q :=
      shiftRight_succ_eq_div2 i.val (16 + d)
    have hls_even : levelSize l % 2 = 0 := levelSize_even l (by omega)
    have hq_pairs : q < levelSize l / 2 := by dsimp only [q]; omega
    have h2q1_lt : 2 * q + 1 < levelSize l := by omega
    have hq_lt : q < levelSize (l + 1) := by
      rw [levelSize_step l (by omega)]; exact hq_pairs
    have hcm_next : capMark input.positions (l + 1) q = true := by
      rw [capMark_succ input.positions l q (by omega), if_pos h2q1_lt]
      rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
      · have hqm : q = m := by dsimp only [q]; omega
        have : 2 * q = idx := by omega
        rw [this, hcm_d']; rfl
      · have hqm : q = m := by dsimp only [q]; omega
        have : 2 * q + 1 = idx := by omega
        rw [this, hcm_d', Bool.or_true]
    obtain ⟨hcap_val, hcap_tr, _, _⟩ :=
      hinvCap.levels_done d (by omega) q hq_pairs hcm_next
    have hnot16 : ¬ (l < 16) := by omega
    have hsib_eq : w.binSib l = readBuffer sCap (8192 + capValOff l + gapOffset (idx ^^^ 1)) 32 :=
      hbin_cap l hnot16
    have hinp_eq : w.levelInput c96 l =
        binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * q)) 32)
          (readBuffer sCap (8192 + capValOff l + gapOffset (2 * q + 1)) 32) := by
      unfold WitnessPath.levelInput
      rw [hw_idx]
      change (if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
              else binaryInput (w.binSib l) (w.evalLevel c96 l)) = _
      rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
      · have hqm : q = m := by dsimp only [q]; omega
        have hev_i : idx % 2 = 0 := by omega
        have h2q : 2 * q = idx := by omega
        have h2q1 : 2 * q + 1 = idx ^^^ 1 := by rw [hm, xor_one_even]; omega
        rw [if_pos hev_i, heval_d', hsib_eq, h2q1, h2q]
      · have hqm : q = m := by dsimp only [q]; omega
        have hodd_i : idx % 2 ≠ 0 := by omega
        have h2q1 : 2 * q + 1 = idx := by omega
        have h2q : 2 * q = idx ^^^ 1 := by rw [hm, xor_one_odd]; omega
        rw [if_neg hodd_i, heval_d', hsib_eq, h2q1, h2q]
    refine ⟨by rw [hidx_next, show 16 + (d + 1) = l + 1 by omega]; exact hq_lt,
      by rw [hidx_next, show 16 + (d + 1) = l + 1 by omega]; exact hcm_next, ?_, ?_⟩
    · rw [hidx_next, show 16 + (d + 1) = l + 1 by omega]
      change maskLevel (l + 1) (c96 (w.levelInput c96 l)) = _
      rw [hinp_eq, maskLevel_cap_eq l (by omega) (by omega)]
      exact hcap_val.symm
    · intro d' hd'
      by_cases hlt : d' < d
      · exact htr_d d' hlt
      · have : d' = d := by omega
        subst this
        change InTrace h768 oracle trCap (w.levelInput c96 l)
        rw [hinp_eq]
        exact hcap_tr

private theorem evalRoot_eq_evalLevel24 (c : Comp96) (w : WitnessPath) :
    w.evalRoot c = w.evalLevel c 24 := rfl

private theorem leafInputs_congr {c : Comp96} {w1 w2 : WitnessPath}
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt) :
    w1.leafInputs c = w2.leafInputs c := by
  unfold WitnessPath.leafInputs; rw [hidx, hval, hsalt]

private theorem check_sound_cap_root (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) (sPos sCap : MachineState) (trCap : CompressionReplies)
    (hinvCap : CapWalkInv h768 oracle input sPos 8 sCap trCap)
    (i : Index) (hi : i ∈ input.positions) (w : WitnessPath)
    (hw_idx : w.index = i)
    (hw16 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 16 =
      readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32)
    (hbin_cap : ∀ prev, ¬ (prev < 16) →
      w.binSib prev = readBuffer sCap (8192 + capValOff prev + gapOffset ((i.val >>> prev) ^^^ 1)) 32) :
    w.evalRoot (fun x => oracle.compression (x.cast h768.symm)) =
      readBuffer sCap (8192 + capValOff 24) 32 ∧
    ∀ d' < 8, InTrace h768 oracle trCap (w.levelInput (fun x => oracle.compression (x.cast h768.symm)) (16 + d')) := by
  obtain ⟨hidx24_lt, _, heval24, htr_cap⟩ :=
    check_sound_cap_climb h768 oracle input sPos sCap trCap hinvCap i hi w hw_idx hw16 hbin_cap 8 (le_refl 8)
  have h168 : (16 + 8 : Nat) = 24 := rfl
  rw [h168] at hidx24_lt heval24
  have hidx24_zero : i.val >>> 24 = 0 := by
    rw [levelSize_24] at hidx24_lt; omega
  have hgo0 : gapOffset 0 = 0 := by decide
  rw [hidx24_zero, hgo0, Nat.add_zero] at heval24
  exact ⟨(evalRoot_eq_evalLevel24 _ w).trans heval24, htr_cap⟩

theorem check_sound (h768 : COMPRESSION_INPUT_LENGTH = 768) : CheckSound h768 := by
  intro oracle input hacc
  rw [scheme_check_eval_eq] at hacc
  have hexit_eq : (checkEval oracle (submission.run .check input)).1.exit = .success :=
    beq_iff_eq.mp hacc
  have hvalid : input.proof.length ≤ submission.sizes.proof := by
    by_contra hnot
    have hrun : submission.run .check input = pure ⟨.failure, initialMachine, 0, 0⟩ :=
      submission_run_check_invalid submission input hnot
    rw [hrun, checkEval_pure] at hexit_eq
    cases hexit_eq
  have hrun : submission.run .check input =
      execute (submission.image .check) (submission.steps .check)
        (submission.initialState .check input) false :=
    submission_run_check_valid submission input hvalid
  let r := detExec oracle (submission.image .check) (submission.steps .check)
    (submission.initialState .check input)
  rw [hrun, checkEval_execute_false] at hexit_eq
  dsimp only at hexit_eq
  refine ⟨r.1, r.2, ?_, ?_⟩
  · rw [hrun, fixedOracleRun_trace_execute_false]
  · intro i hi
    have hne : input.positions.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, hi⟩)
    rcases check_pipeline_nonempty h768 oracle input hvalid hne with
      ⟨_, k, q, tr, hk, _, hh⟩ | ⟨_, k, q, tr, hk, _, hh⟩ |
      ⟨sPos, sCap, qPos, qCap, trPos, trCap, kFin, hk, _, hinvPos, hinvCap, hh⟩
    · have hev := hh.eval_of_le hk
      rw [hev.1] at hexit_eq; cases hexit_eq
    · have hev := hh.eval_of_le hk
      rw [hev.1] at hexit_eq; cases hexit_eq
    · have hev := hh.eval_of_le hk
      have htr_eq : r.2 = trPos ++ trCap := hev.2.2
      have hroot_cap : readBuffer sCap (8192 + capValOff 24) 32 = input.commitment := by
        rw [hev.1] at hexit_eq
        by_contra hne_c
        have hbeq : (readBuffer sCap (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))) = false :=
          beq_eq_false_iff_ne.mpr hne_c
        simp only [hbeq, Bool.and_false, Bool.false_eq_true, ite_false] at hexit_eq
        cases hexit_eq
      -- Locate i in sorted positions
      have hmem_sort : i ∈ input.positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨ord, hord_len, hget⟩ := List.mem_iff_getElem.mp hmem_sort
      have hord : ord < input.positions.card := by simpa using hord_len
      have hpos_eq : posAt input.positions ord = i := by
        simp only [posAt, dif_pos hord, hget]
      have hval_eq : valAt input ord = input.values ⟨i, hi⟩ :=
        valAt_eq_of_posAt input ord hord i hi hpos_eq
      let pw := parsePartialWitness (submission.initialState .check input) input.proof.length
        (posRecordOff ord) (posTailOff ord) (posAt input.positions ord) (valAt input ord)
      let w : WitnessPath := {
        index := pw.index
        value := pw.value
        salt := pw.salt
        binSib := fun prev =>
          if prev < 16 then pw.binSib prev
          else readBuffer sCap (8192 + capValOff prev + gapOffset ((i.val >>> prev) ^^^ 1)) 32
      }
      have hw_idx : w.index = i := hpos_eq
      have hw_val : w.value = input.values ⟨i, hi⟩ := hval_eq
      have hw_low : ∀ l ≤ 16,
          w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) l =
          pw.evalLevel (fun x => oracle.compression (x.cast h768.symm)) l :=
        evalLevel_congr_low (fun x => oracle.compression (x.cast h768.symm)) w pw
          rfl rfl rfl (fun prev hp => by simp [w, hp])
      obtain ⟨hpw16, hpw_leaf, hpw_bin⟩ := hinvPos.witnesses ord hord
      have hw16 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 16 =
          readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32 := by
        rw [hw_low 16 (le_refl 16), hpw16, hpos_eq]
      obtain ⟨hroot_w, htr_cap⟩ :=
        check_sound_cap_root h768 oracle input sPos sCap trCap hinvCap i hi w hw_idx hw16
          (fun prev hge => by simp only [w, hge, ite_false])
      refine ⟨w, hw_idx, hw_val, hroot_w.trans hroot_cap, ?_⟩
      intro x hx
      rw [htr_eq]
      let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
      change x ∈ w.pathInputs c96 at hx
      unfold WitnessPath.pathInputs at hx
      rcases List.mem_append.mp hx with hleaf | hbin
      · rw [leafInputs_congr (c := c96) (w1 := w) (w2 := pw) rfl rfl rfl] at hleaf
        exact List.mem_append_left trCap (hpw_leaf x hleaf)
      · obtain ⟨k, hk_mem, rfl⟩ := List.mem_map.mp hbin
        have hk_lt : k < 24 := List.mem_range.mp hk_mem
        by_cases hlo : k < 16
        · have hli_eq : w.levelInput c96 k = pw.levelInput c96 k := by
            unfold WitnessPath.levelInput
            have hev : w.evalLevel c96 k = pw.evalLevel c96 k := hw_low k (by omega)
            rw [hev]
            simp only [w, hlo, ite_true]
          change InTrace h768 oracle (trPos ++ trCap) (w.levelInput c96 k)
          rw [hli_eq]
          exact List.mem_append_left trCap (hpw_bin k hlo)
        · have hd_lt : k - 16 < 8 := by omega
          have hk_eq : 16 + (k - 16) = k := by omega
          change InTrace h768 oracle (trPos ++ trCap) (w.levelInput c96 k)
          rw [← hk_eq]
          exact List.mem_append_right trPos (htr_cap (k - 16) hd_lt)

/-! ### 4. Honest Completeness (`check_honest_accepts`) -/

private theorem flatMap_getElem_at {α β : Type} (f : α → List β) (l : List α) (n j : Nat)
    (hn : n < l.length) (hj : j < (f (l[n]'hn)).length)
    (hbd : ((l.take n).map (fun a => (f a).length)).sum + j < (l.flatMap f).length) :
    (l.flatMap f)[((l.take n).map (fun a => (f a).length)).sum + j]'hbd = (f (l[n]'hn))[j]'hj := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a tl ih =>
    cases n with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.getElem_cons_zero,
        List.flatMap_cons]
      have hj' : j < (f a).length := hj
      exact List.getElem_append_left hj'
    | succ m =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ,
        List.flatMap_cons]
      have hge : (f a).length ≤ (f a).length + (((tl.take m).map (fun x => (f x).length)).sum + j) :=
        Nat.le_add_right _ _
      have hbd' : (f a).length + (((tl.take m).map (fun x => (f x).length)).sum + j) <
          (f a ++ tl.flatMap f).length := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons] at hbd
        omega
      rw [getElem_eq_of_idx (Nat.add_assoc _ _ _) _ hbd', List.getElem_append_right hge]
      have hsub : (f a).length + (((tl.take m).map (fun x => (f x).length)).sum + j) - (f a).length =
          ((tl.take m).map (fun x => (f x).length)).sum + j := Nat.add_sub_cancel_left _ _
      have hbd_tl : ((tl.take m).map (fun x => (f x).length)).sum + j < (tl.flatMap f).length := by
        rw [List.length_append] at hbd'; omega
      rw [getElem_eq_of_idx hsub _ hbd_tl]
      exact ih m (by simp at hn; omega) hj hbd_tl

private theorem bitsToBytes_getElem {w : Nat} (v : BitVec w) (n j : Nat) (_hj : j < n)
    (hbd : j < (bitsToBytes v n).length) :
    (bitsToBytes v n)[j]'hbd = v.extractLsb' (8 * j) 8 := by
  simp [bitsToBytes]

/-! #### Exact Backward 6-Bit Tail Stream Inversion -/

private theorem bytesToNat_eq_sum_getD (bs : List Byte) :
    bytesToNat bs = ∑ j ∈ Finset.range bs.length, (bs.getD j 0#8).toNat * 2 ^ (8 * j) := by
  induction bs using List.reverseRecOn with
  | nil => simp [bytesToNat]
  | append_singleton l b ih =>
    rw [bytesToNat_append_singleton, List.length_append, List.length_singleton,
      Finset.sum_range_succ, ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hjl : j < l.length := Finset.mem_range.mp hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]
    · simp [List.getD_eq_getElem?_getD]

private theorem bitsOf6_extract (tails : List (BitVec 6)) (t : Nat) (ht : t < tails.length) :
    (bitsOf6 tails / 2 ^ (6 * t)) % 64 = (tails[t]'ht).toNat := by
  induction tails generalizing t with
  | nil => simp at ht
  | cons hd tl ih =>
    cases t with
    | zero =>
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, bitsOf6_cons, List.getElem_cons_zero]
      have hlt : hd.toNat < 64 := hd.isLt
      omega
    | succ t' =>
      simp only [bitsOf6_cons, List.getElem_cons_succ]
      have hpow : 2 ^ (6 * (t' + 1)) = 64 * 2 ^ (6 * t') := by
        rw [show 6 * (t' + 1) = 6 + 6 * t' by omega, Nat.pow_add]
      have hlt : hd.toNat < 64 := hd.isLt
      rw [hpow, ← Nat.div_div_eq_div_mul,
        show (hd.toNat + 64 * bitsOf6 tl) / 64 = bitsOf6 tl by omega]
      exact ih t' (by simp at ht; omega)

private theorem backBytesNat_split (s0 : MachineState) (proofLen k K : Nat) (hk : k ≤ K) :
    ∃ Q, backBytesNat s0 proofLen K = backBytesNat s0 proofLen k + 2 ^ (8 * k) * Q := by
  induction hk with
  | refl => exact ⟨0, by simp⟩
  | @step m hm ih =>
    obtain ⟨Q, hQ⟩ := ih
    rw [backBytesNat_succ, hQ]
    have hkm : k ≤ m := hm
    have hpow : 2 ^ (8 * m) = 2 ^ (8 * k) * 2 ^ (8 * (m - k)) := by
      rw [← Nat.pow_add, show 8 * k + 8 * (m - k) = 8 * m by omega]
    refine ⟨Q + (s0.getByte (BitVec.ofNat 64 (11878272992 + (proofLen - 1 - m)))).toNat * 2 ^ (8 * (m - k)), ?_⟩
    rw [hpow]; ring

private theorem backBytesNat_pack6BitsRev (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (fwd : List Byte) (tails : List (BitVec 6))
    (hpf : input.proof = fwd ++ pack6BitsRev tails) :
    backBytesNat (submission.initialState .check input) input.proof.length (tailBytes tails.length) =
      bitsOf6 tails := by
  let s0 := submission.initialState .check input
  let bs := pack6Bits tails
  have hbs_len : bs.length = tailBytes tails.length := pack6Bits_length tails
  have hrev_len : (pack6BitsRev tails).length = tailBytes tails.length := pack6BitsRev_length tails
  have hpf_len : input.proof.length = fwd.length + tailBytes tails.length := by
    rw [hpf, List.length_append, hrev_len]
  rw [← pack6Bits_bytesToNat tails, bytesToNat_eq_sum_getD]
  unfold backBytesNat
  rw [hbs_len]
  apply Finset.sum_congr rfl
  intro j hj
  have hjt : j < tailBytes tails.length := Finset.mem_range.mp hj
  have hidx_lt : input.proof.length - 1 - j < input.proof.length := by omega
  have hb0 := check_initial_proof_byte input hvalid (input.proof.length - 1 - j) hidx_lt
  have hget_pf : input.proof[input.proof.length - 1 - j]'hidx_lt = bs[j]'(by omega) := by
    have hge : fwd.length ≤ input.proof.length - 1 - j := by omega
    have hsub_lt : input.proof.length - 1 - j - fwd.length < (pack6BitsRev tails).length := by omega
    have hsub_eq : input.proof.length - 1 - j - fwd.length = bs.length - 1 - j := by omega
    have h1 : input.proof[input.proof.length - 1 - j]'hidx_lt =
        (fwd ++ pack6BitsRev tails)[input.proof.length - 1 - j]'(by rwa [← hpf]) := by
      simp [hpf]
    rw [h1, List.getElem_append_right hge]
    have hpk_len : (pack6Bits tails).length = bs.length := rfl
    unfold pack6BitsRev
    rw [getElem_eq_of_idx hsub_eq _ (by rw [List.length_reverse, hpk_len]; omega), List.getElem_reverse]
    exact getElem_eq_of_idx (by rw [hpk_len]; omega) _ (by rw [hpk_len]; omega)
  have hgetD : bs.getD j 0#8 = bs[j]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, show j < bs.length by omega]
  rw [hb0, hget_pf, hgetD]

private theorem honest_tailBuf_zero (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (fwd : List Byte) (tails : List (BitVec 6))
    (hpf : input.proof = fwd ++ pack6BitsRev tails) :
    tailBuf (submission.initialState .check input) input.proof.length tails.length = 0 := by
  unfold tailBuf
  rw [backBytesNat_pack6BitsRev input hvalid fwd tails hpf]
  exact Nat.div_eq_of_lt (bitsOf6_lt tails)

private theorem honest_tailAt_eq (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (fwd : List Byte) (tails : List (BitVec 6))
    (hpf : input.proof = fwd ++ pack6BitsRev tails)
    (t : Nat) (ht : t < tails.length) :
    tailAt (submission.initialState .check input) input.proof.length t = tails[t]'ht := by
  let s0 := submission.initialState .check input
  have hK := backBytesNat_pack6BitsRev input hvalid fwd tails hpf
  have hk_le : tailBytes (t + 1) ≤ tailBytes tails.length := tailBytes_mono (by omega)
  obtain ⟨Q, hQ⟩ := backBytesNat_split s0 input.proof.length (tailBytes (t + 1)) (tailBytes tails.length) hk_le
  rw [hK] at hQ
  have hbits : 6 * t + 6 ≤ 8 * tailBytes (t + 1) := by unfold tailBytes; omega
  have hpow : 2 ^ (8 * tailBytes (t + 1)) = 2 ^ (6 * t) * (64 * 2 ^ (8 * tailBytes (t + 1) - (6 * t + 6))) := by
    rw [show 64 = 2 ^ 6 by decide, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; omega
  have hdiv : bitsOf6 tails / 2 ^ (6 * t) =
      backBytesNat s0 input.proof.length (tailBytes (t + 1)) / 2 ^ (6 * t) +
        64 * (2 ^ (8 * tailBytes (t + 1) - (6 * t + 6)) * Q) := by
    rw [hQ, hpow, show 2 ^ (6 * t) * (64 * 2 ^ (8 * tailBytes (t + 1) - (6 * t + 6))) * Q =
      (64 * (2 ^ (8 * tailBytes (t + 1) - (6 * t + 6)) * Q)) * 2 ^ (6 * t) by ring,
      Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
  have hmod : (backBytesNat s0 input.proof.length (tailBytes (t + 1)) / 2 ^ (6 * t)) % 64 = (tails[t]'ht).toNat := by
    have h1 := bitsOf6_extract tails t ht
    rw [hdiv] at h1
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [tailAt, BitVec.toNat_ofNat]
  exact hmod

/-! #### Prefix Length and Element Extraction Lemmas for `referenceProofFwd` & `referenceProofTails` -/

private theorem binPathFwd_prefix_len (nodes : Nat → Nat → Digest) (i : Index) (n : Nat) (hn : n ≤ 16) :
    (((List.range 16).take n).map fun l =>
      (bitsToBytes (nodes l ((i.val >>> l) ^^^ 1)) (levelFwdBytes l)).length).sum =
    if n < 2 then 30 * n else 60 + 29 * (n - 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have htake : (List.range 16).take (k + 1) = (List.range 16).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), bitsToBytes_length]
    unfold levelFwdBytes FIRST_240_LVL FIRST_238_LVL
    split_ifs <;> omega

private theorem binPathTails_prefix_len (nodes : Nat → Nat → Digest) (i : Index) (n : Nat) (hn : n ≤ 14) :
    (((List.range (16 - FIRST_238_LVL)).take n).map fun step =>
      ([tail6 (nodes (FIRST_238_LVL + step) ((i.val >>> (FIRST_238_LVL + step)) ^^^ 1))]).length).sum = n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have htake : (List.range (16 - FIRST_238_LVL)).take (k + 1) =
        (List.range (16 - FIRST_238_LVL)).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by unfold FIRST_238_LVL; simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih (by omega)]
    simp

private theorem recordsFwd_prefix_len (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (n : Nat) (hn : n ≤ positions.card) :
    (((positions.sort (· ≤ ·)).take n).map fun i => (recordFwd nodes salts i).length).sum =
      posRecordOff n := by
  induction n with
  | zero => simp [posRecordOff]
  | succ k ih =>
    have hlt : k < (positions.sort (· ≤ ·)).length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
    rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih (by omega), posRecordOff_succ, recordFwd_length]

private theorem recordsFwd_flatMap_length (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) :
    ((positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts)).length =
      posRecordOff positions.card := by
  rw [List.length_flatMap]
  have h1 := recordsFwd_prefix_len nodes salts positions positions.card (le_refl _)
  have htake_eq : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rwa [htake_eq] at h1

private theorem recordsTails_prefix_len (nodes : Nat → Nat → Digest)
    (positions : Positions) (n : Nat) (hn : n ≤ positions.card) :
    (((positions.sort (· ≤ ·)).take n).map fun i => (recordTails nodes i).length).sum =
      posTailOff n := by
  induction n with
  | zero => simp [posTailOff]
  | succ k ih =>
    have hlt : k < (positions.sort (· ≤ ·)).length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
    rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih (by omega), posTailOff_succ, recordTails_length]

private theorem recordsTails_flatMap_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length =
      posTailOff positions.card := by
  rw [List.length_flatMap]
  have h1 := recordsTails_prefix_len nodes positions positions.card (le_refl _)
  have htake_eq : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rwa [htake_eq] at h1

private theorem referenceProofFwd_length (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) :
    (referenceProofFwd nodes salts positions).length =
      posRecordOff positions.card + 29 * capFrontierCount positions := by
  unfold referenceProofFwd
  rw [List.length_append, recordsFwd_flatMap_length, capFrontierFwd_length]

private theorem referenceProofTails_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    (referenceProofTails nodes positions).length =
      posTailOff positions.card + capFrontierCount positions := by
  unfold referenceProofTails
  rw [List.length_append, recordsTails_flatMap_length, capFrontierTails_length]

private theorem referenceProof_length_nonempty (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) (hne : positions.card ≠ 0) :
    (referenceProof nodes salts positions).length =
      posRecordOff positions.card + 29 * capFrontierCount positions +
      tailBytes (posTailOff positions.card + capFrontierCount positions) := by
  unfold referenceProof
  rw [if_neg hne, List.length_append, referenceProofFwd_length, pack6BitsRev_length,
    referenceProofTails_length]
  rfl

private theorem capFrontierFwd_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (d : Nat) (hd : d ≤ 8) :
    (((List.range 8).take d).map fun step => (capLevelFrontierFwd nodes positions (16 + step)).length).sum =
      29 * capFrontierPrefix positions d := by
  induction d with
  | zero => simp [capFrontierPrefix_zero]
  | succ k ih =>
    have htake : (List.range 8).take (k + 1) = (List.range 8).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), capLevelFrontierFwd_length, capFrontierPrefix_succ, Nat.mul_add]

private theorem capFrontierTails_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (d : Nat) (hd : d ≤ 8) :
    (((List.range 8).take d).map fun step => (capLevelFrontierTails nodes positions (16 + step)).length).sum =
      capFrontierPrefix positions d := by
  induction d with
  | zero => simp [capFrontierPrefix_zero]
  | succ k ih =>
    have htake : (List.range 8).take (k + 1) = (List.range 8).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), capLevelFrontierTails_length, capFrontierPrefix_succ]

private theorem capLevelFwd_pair_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (l n : Nat) (hn : n ≤ levelSize l / 2) :
    (((List.range (levelSize l / 2)).take n).map fun q =>
      (let mL := capMark positions l (2 * q)
       let mR := capMark positions l (2 * q + 1)
       if mL = mR then []
       else if !mL then bitsToBytes (nodes l (2 * q)) 29
       else bitsToBytes (nodes l (2 * q + 1)) 29).length).sum =
      29 * pairFrontierCount positions l n := by
  induction n with
  | zero => simp [pairFrontierCount_zero]
  | succ q ih =>
    have htake : (List.range (levelSize l / 2)).take (q + 1) = (List.range (levelSize l / 2)).take q ++ [q] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), pairFrontierCount_succ, Nat.mul_add]
    dsimp only
    cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp [bitsToBytes]

private theorem capLevelTails_pair_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (l n : Nat) (hn : n ≤ levelSize l / 2) :
    (((List.range (levelSize l / 2)).take n).map fun q =>
      (let mL := capMark positions l (2 * q)
       let mR := capMark positions l (2 * q + 1)
       if mL = mR then []
       else if !mL then [tail6 (nodes l (2 * q))]
       else [tail6 (nodes l (2 * q + 1))]).length).sum =
      pairFrontierCount positions l n := by
  induction n with
  | zero => simp [pairFrontierCount_zero]
  | succ q ih =>
    have htake : (List.range (levelSize l / 2)).take (q + 1) = (List.range (levelSize l / 2)).take q ++ [q] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), pairFrontierCount_succ]
    dsimp only
    cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp

private theorem readBuffer_proof_of_bitsToBytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off n : Nat) (v : BitVec (8 * n))
    (hbd : off + n ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < n), input.proof[off + j]'(by omega) = v.extractLsb' (8 * j) 8) :
    readBuffer (submission.initialState .check input) (11878272992 + off) n = v := by
  have hr := read_serialized_slice (submission.initialState .check input) v (11878272992 + off) 0 n (by
    intro j hj
    simp only [Nat.zero_add]
    have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
    simpa only [Nat.add_assoc] using h1.trans (hbytes j hj))
  simpa using hr

private theorem proofDigest30_of_proof_bytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off : Nat) (d : Digest) (hbd : off + 30 ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < 30), input.proof[off + j]'(by omega) = d.extractLsb' (8 * j) 8) :
    proofDigest30 (submission.initialState .check input) (11878272992 + off) = mask240 d := by
  apply proofDigest30_of_bytes_eq
  intro j hj
  have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
  simpa only [Nat.add_assoc] using h1.trans (hbytes j hj)

private theorem proofDigest238_of_proof_bytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off t : Nat) (d : Digest) (hbd : off + 29 ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < 29), input.proof[off + j]'(by omega) = d.extractLsb' (8 * j) 8)
    (htail : tailAt (submission.initialState .check input) input.proof.length t = tail6 d) :
    proofDigest238 (submission.initialState .check input) input.proof.length (11878272992 + off) t = mask238 d := by
  apply proofDigest238_of_bytes_eq
  · intro j hj
    have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
    simpa only [Nat.add_assoc] using h1.trans (hbytes j hj)
  · exact htail

/-- Extract byte `j` of `recordFwd` for position `ord` inside `referenceProof`. -/
private theorem referenceProof_recordFwd_getElem (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) (hne : positions.card ≠ 0)
    (ord j : Nat) (hord : ord < positions.card) (hj : j < 490)
    (hbd : posRecordOff ord + j < (referenceProof nodes salts positions).length) :
    (referenceProof nodes salts positions)[posRecordOff ord + j]'hbd =
      (recordFwd nodes salts (posAt positions ord))[j]'(by rw [recordFwd_length]; exact hj) := by
  have hrec_len := recordsFwd_flatMap_length nodes salts positions
  have hlt_rec : posRecordOff ord + j < ((positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts)).length := by
    rw [hrec_len]
    have h1 := posRecordOff_mono (show ord + 1 ≤ positions.card by omega)
    rw [posRecordOff_succ] at h1
    omega
  have hlt_fwd : posRecordOff ord + j < (referenceProofFwd nodes salts positions).length := by
    unfold referenceProofFwd; rw [List.length_append]; omega
  simp only [referenceProof, hne, ite_false]
  rw [List.getElem_append_left hlt_fwd]
  unfold referenceProofFwd at hlt_fwd ⊢
  rw [List.getElem_append_left hlt_rec]
  have hpref := recordsFwd_prefix_len nodes salts positions ord (by omega)
  have hord' : ord < (positions.sort (· ≤ ·)).length := by simpa using hord
  have hpos_get : (positions.sort (· ≤ ·))[ord]'hord' = posAt positions ord := by
    simp only [posAt, dif_pos hord]
  have hj' : j < (recordFwd nodes salts ((positions.sort (· ≤ ·))[ord]'hord')).length := by
    rw [hpos_get, recordFwd_length]; exact hj
  have hfm := flatMap_getElem_at (recordFwd nodes salts) (positions.sort (· ≤ ·)) ord j hord' hj'
    (by rwa [hpref])
  simpa only [hpref, hpos_get] using hfm

/-- Extract tail `j` of `recordTails` for position `ord` inside `referenceProofTails`. -/
private theorem referenceProof_recordTails_getElem (nodes : Nat → Nat → Digest)
    (positions : Positions) (ord j : Nat) (hord : ord < positions.card) (hj : j < 14)
    (hbd : posTailOff ord + j < (referenceProofTails nodes positions).length) :
    (referenceProofTails nodes positions)[posTailOff ord + j]'hbd =
      (recordTails nodes (posAt positions ord))[j]'(by rw [recordTails_length]; exact hj) := by
  have hrec_len := recordsTails_flatMap_length nodes positions
  have hlt_rec : posTailOff ord + j < ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length := by
    rw [hrec_len]
    have h1 := posTailOff_mono (show ord + 1 ≤ positions.card by omega)
    rw [posTailOff_succ] at h1
    omega
  unfold referenceProofTails at hbd ⊢
  rw [List.getElem_append_left hlt_rec]
  have hpref := recordsTails_prefix_len nodes positions ord (by omega)
  have hord' : ord < (positions.sort (· ≤ ·)).length := by simpa using hord
  have hpos_get : (positions.sort (· ≤ ·))[ord]'hord' = posAt positions ord := by
    simp only [posAt, dif_pos hord]
  have hj' : j < (recordTails nodes ((positions.sort (· ≤ ·))[ord]'hord')).length := by
    rw [hpos_get, recordTails_length]; exact hj
  have hfm := flatMap_getElem_at (recordTails nodes) (positions.sort (· ≤ ·)) ord j hord' hj'
    (by rwa [hpref])
  simpa only [hpref, hpos_get] using hfm

/-- Extract forward byte `j < 29` of the frontier digest for pair `q` at cap level `16 + d`. -/
private theorem referenceProof_capFwd_getElem (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) (hne : positions.card ≠ 0)
    (d q j : Nat) (hd : d < 8) (hq : q < levelSize (16 + d) / 2) (hj : j < 29)
    (hdiff : capMark positions (16 + d) (2 * q) ≠ capMark positions (16 + d) (2 * q + 1))
    (hbd : posRecordOff positions.card +
        29 * (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q) + j <
      (referenceProof nodes salts positions).length) :
    (referenceProof nodes salts positions)[posRecordOff positions.card +
        29 * (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q) + j]'hbd =
      (nodes (16 + d) (if !capMark positions (16 + d) (2 * q) then 2 * q else 2 * q + 1)).extractLsb' (8 * j) 8 := by
  let l := 16 + d
  have hq' : q < levelSize l / 2 := hq
  have hdiff' : capMark positions l (2 * q) ≠ capMark positions l (2 * q + 1) := hdiff
  have hrec_len := recordsFwd_flatMap_length nodes salts positions
  have hq_lt_f : pairFrontierCount positions l q + 1 ≤ levelFrontierCount positions l := by
    have h1 := pairFrontierCount_mono positions l (show q + 1 ≤ levelSize l / 2 by omega)
    rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff')] at h1
    exact h1
  have hcap_lt : capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions := by
    have h1 := capFrontierPrefix_mono positions (show d + 1 ≤ 8 by omega)
    rw [capFrontierPrefix_succ, capFrontierPrefix_8] at h1
    exact h1
  have hlt_fwd : posRecordOff positions.card +
      29 * (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q) + j <
      (referenceProofFwd nodes salts positions).length := by
    rw [referenceProofFwd_length]; dsimp only [l] at hq_lt_f hcap_lt; omega
  simp only [referenceProof, hne, ite_false]
  rw [List.getElem_append_left hlt_fwd]
  unfold referenceProofFwd at hlt_fwd ⊢
  rw [List.getElem_append_right (by rw [hrec_len]; omega)]
  unfold capFrontierFwd
  have hd_len : d < (List.range 8).length := by simp; omega
  have hget_d : (List.range 8)[d]'hd_len = d := by simp
  have hpref_d := capFrontierFwd_prefix_len nodes positions d (by omega)
  have hlt_lvl : 29 * pairFrontierCount positions l q + j <
      (capLevelFrontierFwd nodes positions (16 + (List.range 8)[d]'hd_len)).length := by
    rw [hget_d, capLevelFrontierFwd_length]
    change 29 * pairFrontierCount positions l q + j < 29 * levelFrontierCount positions l
    omega
  have hfm1_bd : (((List.range 8).take d).map fun step => (capLevelFrontierFwd nodes positions (16 + step)).length).sum +
      (29 * pairFrontierCount positions l q + j) <
      ((List.range 8).flatMap fun step => capLevelFrontierFwd nodes positions (16 + step)).length := by
    rw [hpref_d, List.length_flatMap]
    have h8 := capFrontierFwd_prefix_len nodes positions 8 (le_refl 8)
    rw [show (List.range 8).take 8 = List.range 8 by simp] at h8
    rw [h8, capFrontierPrefix_8]; omega
  have hidx_sub : posRecordOff positions.card +
      29 * (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q) + j -
      ((positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts)).length =
      (((List.range 8).take d).map fun step => (capLevelFrontierFwd nodes positions (16 + step)).length).sum +
      (29 * pairFrontierCount positions l q + j) := by
    rw [hrec_len, hpref_d]; dsimp only [l]; omega
  have hfm1 := flatMap_getElem_at (fun step => capLevelFrontierFwd nodes positions (16 + step))
    (List.range 8) d (29 * pairFrontierCount positions l q + j) hd_len hlt_lvl hfm1_bd
  rw [getElem_eq_of_idx hidx_sub _ hfm1_bd, hfm1]
  have hlt_lvl' : 29 * pairFrontierCount positions l q + j < (capLevelFrontierFwd nodes positions l).length := by
    rw [capLevelFrontierFwd_length]; omega
  have hget_d_lvl :
      (capLevelFrontierFwd nodes positions (16 + (List.range 8)[d]'hd_len))[29 * pairFrontierCount positions l q + j]'hlt_lvl =
      (capLevelFrontierFwd nodes positions l)[29 * pairFrontierCount positions l q + j]'hlt_lvl' := by
    simp only [hget_d, l]
  rw [hget_d_lvl]
  unfold capLevelFrontierFwd at hlt_lvl' ⊢
  have hq_len : q < (List.range (levelSize l / 2)).length := by simp; omega
  have hget_q : (List.range (levelSize l / 2))[q]'hq_len = q := by simp
  have hpref_q := capLevelFwd_pair_prefix_len nodes positions l q (by omega)
  have hpair_len : (have mL := capMark positions l (2 * q)
      have mR := capMark positions l (2 * q + 1)
      if mL = mR then []
      else if !mL then bitsToBytes (nodes l (2 * q)) 29
      else bitsToBytes (nodes l (2 * q + 1)) 29).length = 29 := by
    simp only [hdiff', ite_false]; split <;> simp [bitsToBytes]
  have hfm2_bd : (((List.range (levelSize l / 2)).take q).map fun q0 =>
      (have mL := capMark positions l (2 * q0)
       have mR := capMark positions l (2 * q0 + 1)
       if mL = mR then []
       else if !mL then bitsToBytes (nodes l (2 * q0)) 29
       else bitsToBytes (nodes l (2 * q0 + 1)) 29).length).sum + j <
      ((List.range (levelSize l / 2)).flatMap fun q0 =>
       have mL := capMark positions l (2 * q0)
       have mR := capMark positions l (2 * q0 + 1)
       if mL = mR then []
       else if !mL then bitsToBytes (nodes l (2 * q0)) 29
       else bitsToBytes (nodes l (2 * q0 + 1)) 29).length := by
    rw [hpref_q]; change 29 * pairFrontierCount positions l q + j < (capLevelFrontierFwd nodes positions l).length
    rw [capLevelFrontierFwd_length]; omega
  have hfm2 := flatMap_getElem_at (fun q0 =>
      have mL := capMark positions l (2 * q0)
      have mR := capMark positions l (2 * q0 + 1)
      if mL = mR then []
      else if !mL then bitsToBytes (nodes l (2 * q0)) 29
      else bitsToBytes (nodes l (2 * q0 + 1)) 29)
    (List.range (levelSize l / 2)) q j hq_len (by rw [hget_q, hpair_len]; exact hj) hfm2_bd
  have hidx_q : 29 * pairFrontierCount positions l q + j =
      (((List.range (levelSize l / 2)).take q).map fun q0 =>
        (have mL := capMark positions l (2 * q0)
         have mR := capMark positions l (2 * q0 + 1)
         if mL = mR then []
         else if !mL then bitsToBytes (nodes l (2 * q0)) 29
         else bitsToBytes (nodes l (2 * q0 + 1)) 29).length).sum + j := by
    rw [hpref_q]
  rw [getElem_eq_of_idx hidx_q hlt_lvl' hfm2_bd, hfm2]
  simp only [hget_q, hdiff', ite_false]
  dsimp only [l]
  by_cases hmL : capMark positions (16 + d) (2 * q) = true
  · simp only [hmL, Bool.not_true, Bool.false_eq_true, ite_false]
    exact bitsToBytes_getElem (nodes (16 + d) (2 * q + 1)) 29 j hj _
  · have hmLf : capMark positions (16 + d) (2 * q) = false := Bool.eq_false_iff.mpr hmL
    simp only [hmLf, Bool.not_false, ite_true]
    exact bitsToBytes_getElem (nodes (16 + d) (2 * q)) 29 j hj _

/-- Extract the 6-bit tail of the frontier digest for pair `q` at cap level `16 + d`. -/
private theorem referenceProof_capTails_getElem (nodes : Nat → Nat → Digest)
    (positions : Positions) (d q : Nat) (hd : d < 8) (hq : q < levelSize (16 + d) / 2)
    (hdiff : capMark positions (16 + d) (2 * q) ≠ capMark positions (16 + d) (2 * q + 1))
    (hbd : posTailOff positions.card +
        (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q) <
      (referenceProofTails nodes positions).length) :
    (referenceProofTails nodes positions)[posTailOff positions.card +
        (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q)]'hbd =
      tail6 (nodes (16 + d) (if !capMark positions (16 + d) (2 * q) then 2 * q else 2 * q + 1)) := by
  let l := 16 + d
  have hq' : q < levelSize l / 2 := hq
  have hdiff' : capMark positions l (2 * q) ≠ capMark positions l (2 * q + 1) := hdiff
  have hrec_len := recordsTails_flatMap_length nodes positions
  have hq_lt_f : pairFrontierCount positions l q + 1 ≤ levelFrontierCount positions l := by
    have h1 := pairFrontierCount_mono positions l (show q + 1 ≤ levelSize l / 2 by omega)
    rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff')] at h1
    exact h1
  have hcap_lt : capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions := by
    have h1 := capFrontierPrefix_mono positions (show d + 1 ≤ 8 by omega)
    rw [capFrontierPrefix_succ, capFrontierPrefix_8] at h1
    exact h1
  unfold referenceProofTails at hbd ⊢
  rw [List.getElem_append_right (by rw [hrec_len]; omega)]
  unfold capFrontierTails
  have hd_len : d < (List.range 8).length := by simp; omega
  have hget_d : (List.range 8)[d]'hd_len = d := by simp
  have hpref_d := capFrontierTails_prefix_len nodes positions d (by omega)
  have hlt_lvl : pairFrontierCount positions l q <
      (capLevelFrontierTails nodes positions (16 + (List.range 8)[d]'hd_len)).length := by
    rw [hget_d, capLevelFrontierTails_length]
    change pairFrontierCount positions l q < levelFrontierCount positions l
    omega
  have hfm1_bd : (((List.range 8).take d).map fun step => (capLevelFrontierTails nodes positions (16 + step)).length).sum +
      pairFrontierCount positions l q <
      ((List.range 8).flatMap fun step => capLevelFrontierTails nodes positions (16 + step)).length := by
    rw [hpref_d, List.length_flatMap]
    have h8 := capFrontierTails_prefix_len nodes positions 8 (le_refl 8)
    rw [show (List.range 8).take 8 = List.range 8 by simp] at h8
    rw [h8, capFrontierPrefix_8]; omega
  have hidx_sub : posTailOff positions.card +
      (capFrontierPrefix positions d + pairFrontierCount positions (16 + d) q) -
      ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length =
      (((List.range 8).take d).map fun step => (capLevelFrontierTails nodes positions (16 + step)).length).sum +
      pairFrontierCount positions l q := by
    rw [hrec_len, hpref_d]; dsimp only [l]; omega
  have hfm1 := flatMap_getElem_at (fun step => capLevelFrontierTails nodes positions (16 + step))
    (List.range 8) d (pairFrontierCount positions l q) hd_len hlt_lvl hfm1_bd
  rw [getElem_eq_of_idx hidx_sub _ hfm1_bd, hfm1]
  have hlt_lvl' : pairFrontierCount positions l q < (capLevelFrontierTails nodes positions l).length := by
    rw [capLevelFrontierTails_length]; omega
  have hget_d_lvl :
      (capLevelFrontierTails nodes positions (16 + (List.range 8)[d]'hd_len))[pairFrontierCount positions l q]'hlt_lvl =
      (capLevelFrontierTails nodes positions l)[pairFrontierCount positions l q]'hlt_lvl' := by
    simp only [hget_d, l]
  rw [hget_d_lvl]
  unfold capLevelFrontierTails at hlt_lvl' ⊢
  have hq_len : q < (List.range (levelSize l / 2)).length := by simp; omega
  have hget_q : (List.range (levelSize l / 2))[q]'hq_len = q := by simp
  have hpref_q := capLevelTails_pair_prefix_len nodes positions l q (by omega)
  have hpair_len : (have mL := capMark positions l (2 * q)
      have mR := capMark positions l (2 * q + 1)
      if mL = mR then []
      else if !mL then [tail6 (nodes l (2 * q))]
      else [tail6 (nodes l (2 * q + 1))]).length = 1 := by
    simp only [hdiff', ite_false]; split <;> simp
  have hfm2_bd : (((List.range (levelSize l / 2)).take q).map fun q0 =>
      (have mL := capMark positions l (2 * q0)
       have mR := capMark positions l (2 * q0 + 1)
       if mL = mR then []
       else if !mL then [tail6 (nodes l (2 * q0))]
       else [tail6 (nodes l (2 * q0 + 1))]).length).sum + 0 <
      ((List.range (levelSize l / 2)).flatMap fun q0 =>
       have mL := capMark positions l (2 * q0)
       have mR := capMark positions l (2 * q0 + 1)
       if mL = mR then []
       else if !mL then [tail6 (nodes l (2 * q0))]
       else [tail6 (nodes l (2 * q0 + 1))]).length := by
    rw [hpref_q, Nat.add_zero]; change pairFrontierCount positions l q < (capLevelFrontierTails nodes positions l).length
    rw [capLevelFrontierTails_length]; omega
  have hfm2 := flatMap_getElem_at (fun q0 =>
      have mL := capMark positions l (2 * q0)
      have mR := capMark positions l (2 * q0 + 1)
      if mL = mR then []
      else if !mL then [tail6 (nodes l (2 * q0))]
      else [tail6 (nodes l (2 * q0 + 1))])
    (List.range (levelSize l / 2)) q 0 hq_len (by rw [hget_q, hpair_len]; decide) hfm2_bd
  have hidx_q : pairFrontierCount positions l q =
      (((List.range (levelSize l / 2)).take q).map fun q0 =>
        (have mL := capMark positions l (2 * q0)
         have mR := capMark positions l (2 * q0 + 1)
         if mL = mR then []
         else if !mL then [tail6 (nodes l (2 * q0))]
         else [tail6 (nodes l (2 * q0 + 1))]).length).sum + 0 := by
    rw [hpref_q, Nat.add_zero]
  rw [getElem_eq_of_idx hidx_q hlt_lvl' hfm2_bd, hfm2]
  simp only [hget_q, hdiff', ite_false]
  dsimp only [l]
  by_cases hmL : capMark positions (16 + d) (2 * q) = true
  · simp [hmL]
  · have hmLf : capMark positions (16 + d) (2 * q) = false := Bool.eq_false_iff.mpr hmL
    simp [hmLf]

/-- On an honest `referenceProof`, every parsed per-position witness evaluates to `nodeVal` up to L16. -/
private theorem honest_parsePartialWitness_eval16 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (positions : Positions) (hne : positions.card ≠ 0) (rt : Commitment)
    (ord : Nat) (hord : ord < positions.card) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 msg salts
    let input : CheckInput :=
      ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
    let s0 := submission.initialState .check input
    let i := posAt positions ord
    let pw := parsePartialWitness s0 input.proof.length (posRecordOff ord) (posTailOff ord)
      i (valAt input ord)
    pw.evalLevel c96 16 = nodes 16 (capLeafOf i) := by
  intro c96 nodes input s0 i pw
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  have hpf_eq : input.proof = referenceProofFwd nodes salts positions ++
      pack6BitsRev (referenceProofTails nodes positions) := by
    change referenceProof nodes salts positions = _
    unfold referenceProof; exact if_neg hne
  have hplen := referenceProof_length_nonempty nodes salts positions hne
  have htlen := referenceProofTails_length nodes positions
  let pOff := posRecordOff ord
  let tOff := posTailOff ord
  have hpOff_rec : pOff + 490 ≤ input.proof.length := by
    have h1 := posRecordOff_mono (show ord + 1 ≤ positions.card by omega)
    rw [posRecordOff_succ] at h1
    change pOff + 490 ≤ posRecordOff positions.card at h1
    change pOff + 490 ≤ (referenceProof nodes salts positions).length
    rw [hplen]; omega
  have htOff_rec : tOff + 14 ≤ (referenceProofTails nodes positions).length := by
    have h1 := posTailOff_mono (show ord + 1 ≤ positions.card by omega)
    rw [posTailOff_succ] at h1
    change tOff + 14 ≤ posTailOff positions.card at h1
    rw [htlen]; omega
  have hrec_byte : ∀ off (hoff : off < 490),
      input.proof[pOff + off]'(by omega) =
        (recordFwd nodes salts i)[off]'(by rw [recordFwd_length]; exact hoff) := by
    intro off hoff
    have hbd_ref : posRecordOff ord + off < (referenceProof nodes salts positions).length := by
      change pOff + off < input.proof.length; omega
    exact referenceProof_recordFwd_getElem nodes salts positions hne ord off hord hoff hbd_ref
  -- Value at ord equals msg i
  have hval_msg : valAt input ord = msg i := by
    have hmem : i ∈ positions := posAt_mem positions ord hord
    rw [valAt_eq_of_posAt input ord hord i hmem rfl]
    rfl
  -- Salt matches salts i
  have hsalt_eq : pw.salt = salts i := by
    exact readBuffer_proof_of_bitsToBytes input hvalid pOff 24 (salts i) (by omega) (fun j hj => by
      rw [hrec_byte j (by omega)]
      unfold recordFwd
      rw [List.getElem_append_left (by simp [bitsToBytes_length]; omega)]
      exact bitsToBytes_getElem (salts i) 24 j hj _)
  -- L0 evaluation matches nodes 0 i.val
  have hl0_eq : pw.evalLevel c96 0 = nodes 0 i.val := by
    change maskLevel 0 (leafDigest c96 i pw.salt (valAt input ord)) = _
    rw [hsalt_eq, hval_msg]
    simp only [nodes, nodeVal, nodeValFromLeaves, i.isLt, dite_true]
  -- Shared forward-byte extraction for L0..L15 siblings
  have hbin_fwd_byte : ∀ (l : Nat) (hl : l < 16),
      let sib := (i.val >>> l) ^^^ 1
      let offInBin := if l < 2 then 30 * l else 60 + 29 * (l - 2)
      let nb := levelFwdBytes l
      ∀ j (hj : j < nb),
        input.proof[pOff + 24 + offInBin + j]'(by
          dsimp only [offInBin, nb] at hj ⊢
          unfold levelFwdBytes FIRST_240_LVL FIRST_238_LVL at hj
          split_ifs at hj ⊢ <;> omega) =
          (nodes l sib).extractLsb' (8 * j) 8 := by
    intro l hl sib offInBin nb j hj
    have hnb_bd : offInBin + j < 466 := by
      dsimp only [offInBin, nb] at hj ⊢
      unfold levelFwdBytes FIRST_240_LVL FIRST_238_LVL at hj
      split_ifs at hj ⊢ <;> omega
    have hrb := hrec_byte (24 + offInBin + j) (by omega)
    rw [getElem_eq_of_idx (show pOff + 24 + offInBin + j = pOff + (24 + offInBin + j) by omega) _ (by omega), hrb]
    unfold recordFwd
    rw [List.getElem_append_right (by simp [bitsToBytes_length]; omega)]
    simp only [bitsToBytes_length, show 24 + offInBin + j - 24 = offInBin + j by omega]
    unfold binPathFwd
    have hl_len : l < (List.range 16).length := by simp; omega
    have hget_l : (List.range 16)[l]'hl_len = l := by simp
    have hpref := binPathFwd_prefix_len nodes i l (by omega)
    have hfm_bd : (((List.range 16).take l).map fun k =>
        (bitsToBytes (nodes k ((i.val >>> k) ^^^ 1)) (levelFwdBytes k)).length).sum + j <
        ((List.range 16).flatMap fun k =>
          bitsToBytes (nodes k ((i.val >>> k) ^^^ 1)) (levelFwdBytes k)).length := by
      rw [hpref]; change offInBin + j < (binPathFwd nodes i).length
      rw [binPathFwd_length]; exact hnb_bd
    have hfm := flatMap_getElem_at (fun k => bitsToBytes (nodes k ((i.val >>> k) ^^^ 1)) (levelFwdBytes k))
      (List.range 16) l j hl_len (by rw [hget_l, bitsToBytes_length]; exact hj) hfm_bd
    have hidx_l : offInBin + j =
        (((List.range 16).take l).map fun k =>
          (bitsToBytes (nodes k ((i.val >>> k) ^^^ 1)) (levelFwdBytes k)).length).sum + j := by
      rw [hpref]
    rw [getElem_eq_of_idx hidx_l _ hfm_bd, hfm]
    simp only [hget_l]
    exact bitsToBytes_getElem (nodes l sib) nb j hj _
  -- L0..L15 siblings match nodes l ((i.val >>> l) ^^^ 1)
  have hsib_bin_eq : ∀ l < 16, pw.binSib l = nodes l ((i.val >>> l) ^^^ 1) := by
    intro l hl
    have hsib_lt := shiftRight_xor_one_lt i l (by omega)
    by_cases hlt2 : l < 2
    · have hnb : levelFwdBytes l = 30 := by
        unfold levelFwdBytes FIRST_240_LVL FIRST_238_LVL; rw [if_neg (by omega), if_pos hlt2]
      have hpd := proofDigest30_of_proof_bytes input hvalid (pOff + 24 + 30 * l) (nodes l ((i.val >>> l) ^^^ 1))
        (by omega) (fun j hj => by
          have hb := hbin_fwd_byte l hl j (by rw [hnb]; exact hj)
          simpa only [hlt2, ite_true] using hb)
      have hmask : mask240 (nodes l ((i.val >>> l) ^^^ 1)) = nodes l ((i.val >>> l) ^^^ 1) :=
        nodeValFromLeaves_masked c96 _ l _ (by unfold FIRST_240_LVL; omega) (by omega) hsib_lt
      have hpw_b : pw.binSib l = proofDigest30 s0 (11878272992 + (pOff + 24 + 30 * l)) := by
        simp only [pw, parsePartialWitness, hlt2, ite_true, pOff, Nat.add_assoc]
      rw [hpw_b, hpd, hmask]
    · have hnb : levelFwdBytes l = 29 := by
        unfold levelFwdBytes FIRST_240_LVL FIRST_238_LVL; rw [if_neg (by omega), if_neg (by omega)]
      let step := l - 2
      have hstep_lt : step < 14 := by omega
      have htail_lt : tOff + step < (referenceProofTails nodes positions).length := by omega
      have htail_eq : tailAt s0 input.proof.length (tOff + step) = tail6 (nodes l ((i.val >>> l) ^^^ 1)) := by
        rw [honest_tailAt_eq input hvalid _ _ hpf_eq (tOff + step) htail_lt]
        rw [referenceProof_recordTails_getElem nodes positions ord step hord hstep_lt htail_lt]
        unfold recordTails binPathTails
        have hst_len : step < (List.range (16 - FIRST_238_LVL)).length := by unfold FIRST_238_LVL; simp; omega
        have hget_st : (List.range (16 - FIRST_238_LVL))[step]'hst_len = step := by simp
        have hpref := binPathTails_prefix_len nodes i step (by omega)
        have hfm_bd : (((List.range (16 - FIRST_238_LVL)).take step).map fun st =>
            ([tail6 (nodes (FIRST_238_LVL + st) ((i.val >>> (FIRST_238_LVL + st)) ^^^ 1))]).length).sum + 0 <
            ((List.range (16 - FIRST_238_LVL)).flatMap fun st =>
              [tail6 (nodes (FIRST_238_LVL + st) ((i.val >>> (FIRST_238_LVL + st)) ^^^ 1))]).length := by
          rw [hpref, Nat.add_zero]; change step < (binPathTails nodes i).length
          rw [binPathTails_length]; exact hstep_lt
        have hfm := flatMap_getElem_at (fun st =>
            [tail6 (nodes (FIRST_238_LVL + st) ((i.val >>> (FIRST_238_LVL + st)) ^^^ 1))])
          (List.range (16 - FIRST_238_LVL)) step 0 hst_len (by simp) hfm_bd
        have hidx_st : step =
            (((List.range (16 - FIRST_238_LVL)).take step).map fun st =>
              ([tail6 (nodes (FIRST_238_LVL + st) ((i.val >>> (FIRST_238_LVL + st)) ^^^ 1))]).length).sum + 0 := by
          rw [hpref, Nat.add_zero]
        rw [getElem_eq_of_idx hidx_st _ hfm_bd, hfm]
        simp only [List.getElem_cons_zero, hget_st]
        simp only [FIRST_238_LVL, show 2 + step = l by omega]
      have hpd := proofDigest238_of_proof_bytes input hvalid
        (pOff + 84 + 29 * step) (tOff + step) (nodes l ((i.val >>> l) ^^^ 1))
        (by omega) (fun j hj => by
          have hb := hbin_fwd_byte l hl j (by rw [hnb]; exact hj)
          simpa only [hlt2, ite_false, show pOff + 24 + (60 + 29 * (l - 2)) + j = pOff + 84 + 29 * step + j by omega] using hb)
        htail_eq
      have hmask : mask238 (nodes l ((i.val >>> l) ^^^ 1)) = nodes l ((i.val >>> l) ^^^ 1) :=
        nodeValFromLeaves_masked238 c96 _ l _ (by unfold FIRST_238_LVL; omega) (by omega) hsib_lt
      have hpw_b : pw.binSib l = proofDigest238 s0 input.proof.length
          (11878272992 + (pOff + 84 + 29 * step)) (tOff + step) := by
        simp only [pw, parsePartialWitness, hlt2, ite_false, hl, ite_true, pOff, tOff, step, Nat.add_assoc]
      rw [hpw_b, hpd, hmask]
  -- Induction on l ≤ 16: pw.evalLevel c96 l = nodes l (i.val >>> l)
  have hclimb : ∀ l ≤ 16, i.val >>> l < levelSize l ∧ pw.evalLevel c96 l = nodes l (i.val >>> l) := by
    intro l hl
    induction l with
    | zero =>
      exact ⟨by rw [levelSize_0, Nat.shiftRight_zero]; exact i.isLt, by simpa using hl0_eq⟩
    | succ k ih =>
      obtain ⟨hidx_lt, hev_k⟩ := ih (by omega)
      let idx := i.val >>> k
      let q := idx / 2
      have hidx_next : i.val >>> (k + 1) = q := shiftRight_succ_eq_div2 i.val k
      have hls_even : levelSize k % 2 = 0 := levelSize_even k (by omega)
      have h2q1_lt : 2 * q + 1 < levelSize k := by dsimp only [q, idx] at *; omega
      have hq_lt : q < levelSize (k + 1) := by
        rw [levelSize_step k (by omega)]; dsimp only [q, idx] at *; omega
      refine ⟨by rwa [hidx_next], ?_⟩
      rw [hidx_next]
      change maskLevel (k + 1) (c96 (if idx % 2 = 0 then binaryInput (pw.evalLevel c96 k) (pw.binSib k)
        else binaryInput (pw.binSib k) (pw.evalLevel c96 k))) =
        if 2 * q + 1 < levelSize k then
          maskLevel (k + 1) (c96 (binaryInput (nodes k (2 * q)) (nodes k (2 * q + 1))))
        else 0
      rw [if_pos h2q1_lt, hsib_bin_eq k (by omega), hev_k]
      rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
      · have hqm : q = m := by dsimp only [q]; omega
        have hev : idx % 2 = 0 := by omega
        have h2q : 2 * q = idx := by omega
        have h2q1 : 2 * q + 1 = idx ^^^ 1 := by rw [hm, xor_one_even]; omega
        rw [if_pos hev, h2q1, h2q]
      · have hqm : q = m := by dsimp only [q]; omega
        have hodd : idx % 2 ≠ 0 := by omega
        have h2q1 : 2 * q + 1 = idx := by omega
        have h2q : 2 * q = idx ^^^ 1 := by rw [hm, xor_one_odd]; omega
        rw [if_neg hodd, h2q1, h2q]
  exact (hclimb 16 (le_refl 16)).2

private theorem rootVal_eq_nodeVal24 (c : Comp96) (msg : Message) (salts : Index → Salt192) :
    rootVal c msg salts = nodeVal c msg salts 24 0 := rfl

private theorem check_honest_cap_eq (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (hempty : positions.card ≠ 0) (rt : Commitment)
    (sPos sCap : MachineState) (trPos trCap : CompressionReplies)
    (hinvPos : PosLoopInv h768 oracle
      ⟨rt, positions, msg.restrict positions,
        referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions⟩
      positions.card sPos trPos)
    (hinvCap : CapWalkInv h768 oracle
      ⟨rt, positions, msg.restrict positions,
        referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions⟩
      sPos 8 sCap trCap) :
    ∀ d ≤ 8, ∀ idx < levelSize (16 + d),
      capMark positions (16 + d) idx = true →
      readBuffer sCap (8192 + capValOff (16 + d) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (16 + d) idx := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let nodes := nodeVal c96 msg salts
  let pf := referenceProof nodes salts positions
  let input : CheckInput := ⟨rt, positions, msg.restrict positions, pf⟩
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  have hpf_eq : input.proof = referenceProofFwd nodes salts positions ++
      pack6BitsRev (referenceProofTails nodes positions) := by
    change referenceProof nodes salts positions = _
    unfold referenceProof; exact if_neg hempty
  have hplen := referenceProof_length_nonempty nodes salts positions hempty
  have htlen := referenceProofTails_length nodes positions
  intro d hd
  induction d with
  | zero =>
    intro idx hidx hcm
    rw [levelSize_16] at hidx
    rw [capMark_16, decide_eq_true_eq] at hcm
    obtain ⟨i, hi, hci⟩ := hcm
    have hmem_sort : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
    obtain ⟨ord, hord_len, hget⟩ := List.mem_iff_getElem.mp hmem_sort
    have hord : ord < positions.card := by simpa using hord_len
    have hpos_eq : posAt positions ord = i := by simp only [posAt, dif_pos hord, hget]
    have hw1 := (hinvPos.witnesses ord hord).1
    have hev := honest_parsePartialWitness_eval16 h768 oracle msg salts positions hempty rt ord hord
    have h16 := hinvCap.val16_marked idx hidx (by rw [capMark_16, decide_eq_true_eq]; exact ⟨i, hi, hci⟩)
    rw [h16, ← hci, ← hpos_eq, ← hw1, hev]
  | succ d ih =>
    intro idx hidx hcm
    let l := 16 + d
    have hl1 : 16 ≤ l := by omega
    have hl2 : l < 24 := by omega
    have hls_even : levelSize l % 2 = 0 := levelSize_even l hl2
    have hls_next : levelSize (l + 1) = levelSize l / 2 := levelSize_step l hl2
    rw [show 16 + (d + 1) = l + 1 by omega] at hidx hcm ⊢
    have hq_pair : idx < levelSize l / 2 := by omega
    have h2q1 : 2 * idx + 1 < levelSize l := by omega
    change readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 =
      if 2 * idx + 1 < levelSize l then
        maskLevel (l + 1) (c96 (binaryInput (nodes l (2 * idx)) (nodes l (2 * idx + 1))))
      else 0
    rw [if_pos h2q1]
    obtain ⟨hcap_val, _, hfrL, hfrR⟩ := hinvCap.levels_done d (by omega) idx hq_pair hcm
    have hdL_eq : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32 = nodes l (2 * idx) := by
      cases hmL : capMark positions l (2 * idx) with
      | true => exact ih (by omega) (2 * idx) (by change 2 * idx < levelSize l; omega) hmL
      | false =>
        have hmR : capMark positions l (2 * idx + 1) = true := by
          rw [capMark_succ positions l idx hl1, if_pos h2q1, hmL] at hcm; simpa using hcm
        have hdiff : capMark positions l (2 * idx) ≠ capMark positions l (2 * idx + 1) := by
          rw [hmL, hmR]; decide
        have hfrL' : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32 =
            proofDigest238 (submission.initialState .check input) input.proof.length
              (11878272992 + (posRecordOff positions.card +
                29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx)))
              (posTailOff positions.card +
                (capFrontierPrefix positions d + pairFrontierCount positions l idx)) :=
          hfrL hmL
        rw [hfrL']
        have hf_step : capFrontierPrefix positions d + pairFrontierCount positions l idx + 1 ≤
            capFrontierCount positions := by
          have h1 := pairFrontierCount_mono positions l (show idx + 1 ≤ levelSize l / 2 by omega)
          rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff)] at h1
          have h2 := capFrontierPrefix_mono positions (show d + 1 ≤ 8 by omega)
          rw [capFrontierPrefix_succ, capFrontierPrefix_8] at h2
          change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h2
          omega
        have hpd_bd : posRecordOff positions.card +
            29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + 29 ≤ input.proof.length := by
          change _ + 29 ≤ (referenceProof nodes salts positions).length
          rw [hplen]; omega
        have htd_bd : posTailOff positions.card +
            (capFrontierPrefix positions d + pairFrontierCount positions l idx) <
            (referenceProofTails nodes positions).length := by
          rw [htlen]; omega
        have hmL' : capMark positions (16 + d) (2 * idx) = false := hmL
        have htail_eq : tailAt (submission.initialState .check input) input.proof.length
            (posTailOff positions.card +
              (capFrontierPrefix positions d + pairFrontierCount positions l idx)) =
            tail6 (nodes l (2 * idx)) := by
          rw [honest_tailAt_eq input hvalid _ _ hpf_eq _ htd_bd]
          have ht := referenceProof_capTails_getElem nodes positions d idx (by omega) hq_pair hdiff htd_bd
          simpa only [l, hmL', Bool.not_false, ite_true] using ht
        have hpd := proofDigest238_of_proof_bytes input hvalid
          (posRecordOff positions.card +
            29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))
          (posTailOff positions.card +
            (capFrontierPrefix positions d + pairFrontierCount positions l idx))
          (nodes l (2 * idx)) hpd_bd
          (fun j hj => by
            have h := referenceProof_capFwd_getElem nodes salts positions hempty d idx j
              (by omega) hq_pair hj hdiff (by
                change posRecordOff positions.card +
                  29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + j < input.proof.length
                omega)
            simpa only [l, hmL', Bool.not_false, ite_true] using h) htail_eq
        rw [hpd]
        exact nodeValFromLeaves_masked238 c96 _ l (2 * idx) (by unfold FIRST_238_LVL; omega) (by omega) (by omega)
    have hdR_eq : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32 = nodes l (2 * idx + 1) := by
      cases hmR : capMark positions l (2 * idx + 1) with
      | true => exact ih (by omega) (2 * idx + 1) (by change 2 * idx + 1 < levelSize l; omega) hmR
      | false =>
        have hmL : capMark positions l (2 * idx) = true := by
          rw [capMark_succ positions l idx hl1, if_pos h2q1, hmR] at hcm; simpa using hcm
        have hdiff : capMark positions l (2 * idx) ≠ capMark positions l (2 * idx + 1) := by
          rw [hmL, hmR]; decide
        have hfrR' : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32 =
            proofDigest238 (submission.initialState .check input) input.proof.length
              (11878272992 + (posRecordOff positions.card +
                29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx)))
              (posTailOff positions.card +
                (capFrontierPrefix positions d + pairFrontierCount positions l idx)) :=
          hfrR hmR
        rw [hfrR']
        have hf_step : capFrontierPrefix positions d + pairFrontierCount positions l idx + 1 ≤
            capFrontierCount positions := by
          have h1 := pairFrontierCount_mono positions l (show idx + 1 ≤ levelSize l / 2 by omega)
          rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff)] at h1
          have h2 := capFrontierPrefix_mono positions (show d + 1 ≤ 8 by omega)
          rw [capFrontierPrefix_succ, capFrontierPrefix_8] at h2
          change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h2
          omega
        have hpd_bd : posRecordOff positions.card +
            29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + 29 ≤ input.proof.length := by
          change _ + 29 ≤ (referenceProof nodes salts positions).length
          rw [hplen]; omega
        have htd_bd : posTailOff positions.card +
            (capFrontierPrefix positions d + pairFrontierCount positions l idx) <
            (referenceProofTails nodes positions).length := by
          rw [htlen]; omega
        have hmL' : capMark positions (16 + d) (2 * idx) = true := hmL
        have htail_eq : tailAt (submission.initialState .check input) input.proof.length
            (posTailOff positions.card +
              (capFrontierPrefix positions d + pairFrontierCount positions l idx)) =
            tail6 (nodes l (2 * idx + 1)) := by
          rw [honest_tailAt_eq input hvalid _ _ hpf_eq _ htd_bd]
          have ht := referenceProof_capTails_getElem nodes positions d idx (by omega) hq_pair hdiff htd_bd
          simpa only [l, hmL', Bool.not_true, Bool.false_eq_true, ite_false] using ht
        have hpd := proofDigest238_of_proof_bytes input hvalid
          (posRecordOff positions.card +
            29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))
          (posTailOff positions.card +
            (capFrontierPrefix positions d + pairFrontierCount positions l idx))
          (nodes l (2 * idx + 1)) hpd_bd
          (fun j hj => by
            have h := referenceProof_capFwd_getElem nodes salts positions hempty d idx j
              (by omega) hq_pair hj hdiff (by
                change posRecordOff positions.card +
                  29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + j < input.proof.length
                omega)
            simpa only [l, hmL', Bool.not_true, Bool.false_eq_true, ite_false] using h) htail_eq
        rw [hpd]
        exact nodeValFromLeaves_masked238 c96 _ l (2 * idx + 1) (by unfold FIRST_238_LVL; omega) (by omega) (by omega)
    have hcap_val' : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 =
        if l = 23 then
          c96 (binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32)
            (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32))
        else
          mask238 (c96 (binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32)
            (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32))) := hcap_val
    rw [hcap_val', hdL_eq, hdR_eq, maskLevel_cap_eq l hl1 hl2]

private theorem check_honest_consistent (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (hempty : positions.card ≠ 0) (rt : Commitment) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 msg salts
    let input : CheckInput := ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
    PosConsistent c96 (submission.initialState .check input) input positions.card := by
  intro c96 nodes input
  have hplen := referenceProof_length_nonempty nodes salts positions hempty
  have ht_mono : tailBytes (posTailOff positions.card) ≤
      tailBytes (posTailOff positions.card + capFrontierCount positions) :=
    tailBytes_mono (by omega)
  refine ⟨by change posRecordOff positions.card + tailBytes (posTailOff positions.card) ≤
               (referenceProof nodes salts positions).length
             rw [hplen]; omega, ?_⟩
  intro j1 j2 hj1 hj2 hc_eq
  have h1 := honest_parsePartialWitness_eval16 h768 oracle msg salts positions hempty rt j1 hj1
  have h2 := honest_parsePartialWitness_eval16 h768 oracle msg salts positions hempty rt j2 hj2
  rw [h1, h2, hc_eq]

private theorem check_honest_empty (oracle : Oracle) (msg : Message) (positions : Positions)
    (rt : Commitment) (pf : Proof) (hempty : positions.card = 0) (hpf_nil : pf.length = 0)
    (hvalid : pf.length ≤ submission.sizes.proof) :
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).1 = true ∧
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).2 ≤ CHECK_BUDGET positions.card := by
  let input : CheckInput := ⟨rt, positions, msg.restrict positions, pf⟩
  have hrun : submission.run .check input =
      execute (submission.image .check) (submission.steps .check)
        (submission.initialState .check input) false :=
    submission_run_check_valid submission input hvalid
  change ((oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true) ∧
    ((oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).2 ≤ CHECK_BUDGET positions.card)
  rw [scheme_check_eval_eq, hrun, checkEval_execute_false]
  dsimp only
  have hh := step_prologue_empty oracle input hvalid hempty
  have hev := hh.eval_of_le (show 12 ≤ submission.steps .check by rw [check_steps_eq]; omega)
  refine ⟨?_, ?_⟩
  · rw [hev.1, if_pos hpf_nil]; rfl
  · rw [hev.2.1]; unfold CHECK_BUDGET; omega

private theorem check_honest_nonempty_root (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (hempty : positions.card ≠ 0) (rt : Commitment)
    (hrt : rt = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 24 0)
    (sPos sCap : MachineState) (trPos trCap : CompressionReplies)
    (hinvPos : PosLoopInv h768 oracle
      ⟨rt, positions, msg.restrict positions,
        referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions⟩
      positions.card sPos trPos)
    (hinvCap : CapWalkInv h768 oracle
      ⟨rt, positions, msg.restrict positions,
        referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions⟩
      sPos 8 sCap trCap) :
    readBuffer sCap (8192 + capValOff 24) 32 = rt := by
  have hcap_eq := check_honest_cap_eq h768 oracle msg salts positions hempty rt sPos sCap trPos trCap hinvPos hinvCap
  have hcm24 := capMark_24_eq_true positions (Finset.card_pos.mp (Nat.pos_of_ne_zero hempty))
  have h24 := hcap_eq 8 (le_refl 8) 0 (by change 0 < levelSize 24; rw [levelSize_24]; decide) hcm24
  have h168 : (16 + 8 : Nat) = 24 := rfl
  have hgo0 : gapOffset 0 = 0 := by decide
  rw [h168, hgo0, Nat.add_zero] at h24
  exact h24.trans hrt.symm

private theorem check_honest_accepts_core (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (rt : Commitment) (pf : Proof)
    (hrt : rt = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 24 0)
    (hpf : pf = referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions) :
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).1 = true ∧
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).2 ≤ CHECK_BUDGET positions.card := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let nodes := nodeVal c96 msg salts
  have hvalid : pf.length ≤ submission.sizes.proof := by
    rw [hpf]
    exact referenceProof_length_le_cap nodes salts positions
  by_cases hempty : positions.card = 0
  · have hpf_nil : pf.length = 0 := by
      rw [hpf]; unfold referenceProof; simp [hempty]
    exact check_honest_empty oracle msg positions rt pf hempty hpf_nil hvalid
  · let input : CheckInput := ⟨rt, positions, msg.restrict positions, pf⟩
    have hrun : submission.run .check input =
        execute (submission.image .check) (submission.steps .check)
          (submission.initialState .check input) false :=
      submission_run_check_valid submission input hvalid
    change ((oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true) ∧
      ((oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).2 ≤ CHECK_BUDGET positions.card)
    rw [scheme_check_eval_eq, hrun, checkEval_execute_false]
    dsimp only
    have hplen : pf.length =
        posRecordOff positions.card + 29 * capFrontierCount positions +
        tailBytes (posTailOff positions.card + capFrontierCount positions) := by
      rw [hpf]
      exact referenceProof_length_nonempty nodes salts positions hempty
    have hpf_split : input.proof = referenceProofFwd nodes salts positions ++
        pack6BitsRev (referenceProofTails nodes positions) := by
      change pf = _
      rw [hpf]; unfold referenceProof; exact if_neg hempty
    have hbuf0 : tailBuf (submission.initialState .check input) input.proof.length
        (posTailOff input.positions.card + capFrontierCount input.positions) = 0 := by
      have htlen := referenceProofTails_length nodes positions
      rw [← htlen]
      exact honest_tailBuf_zero input hvalid _ _ hpf_split
    have hcons : PosConsistent c96 (submission.initialState .check input) input positions.card := by
      have h := check_honest_consistent h768 oracle msg salts positions hempty rt
      dsimp only at h
      simpa only [input, hpf, c96, nodes] using h
    rcases check_pipeline_nonempty h768 oracle input hvalid hempty with
      ⟨hnot, _⟩ | ⟨hshort, _⟩ | ⟨sPos, sCap, qPos, qCap, trPos, trCap, kFin, hk, hq, hinvPos, hinvCap, hh⟩
    · exact (hnot hcons).elim
    · change pf.length < posRecordOff positions.card + 29 * capFrontierCount positions +
        tailBytes (posTailOff positions.card + capFrontierCount positions) at hshort
      rw [hplen] at hshort; omega
    · have hinvPos' : PosLoopInv h768 oracle
          ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
          positions.card sPos trPos := by
        simpa only [input, hpf] using hinvPos
      have hinvCap' : CapWalkInv h768 oracle
          ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
          sPos 8 sCap trCap := by
        simpa only [input, hpf] using hinvCap
      have hroot_eq : readBuffer sCap (8192 + capValOff 24) 32 = rt :=
        check_honest_nonempty_root h768 oracle msg salts positions hempty rt hrt sPos sCap trPos trCap hinvPos' hinvCap'
      have hev := hh.eval_of_le hk
      have hlen_eq : posRecordOff input.positions.card + 29 * capFrontierCount input.positions +
          tailBytes (posTailOff input.positions.card + capFrontierCount input.positions) =
          input.proof.length := hplen.symm
      have hcmt_eq : readBuffer sCap (8192 + capValOff 24) 32 = (input.commitment : BitVec (8 * 32)) := hroot_eq
      have hcond : (posRecordOff input.positions.card + 29 * capFrontierCount input.positions +
          tailBytes (posTailOff input.positions.card + capFrontierCount input.positions) ==
          input.proof.length &&
          tailBuf (submission.initialState .check input) input.proof.length
            (posTailOff input.positions.card + capFrontierCount input.positions) == 0 &&
          readBuffer sCap (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))) = true :=
        (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hlen_eq, beq_iff_eq.mpr hbuf0⟩,
          beq_iff_eq.mpr hcmt_eq⟩
      have hcard_eq : input.positions.card = positions.card := rfl
      rw [hcard_eq] at hq
      refine ⟨?_, ?_⟩
      · rw [hev.1, if_pos hcond]; rfl
      · rw [hev.2.1]; unfold CHECK_BUDGET; omega

theorem check_honest_accepts (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let rt := rootVal c96 msg salts
    let pf := referenceProof (nodeVal c96 msg salts) salts positions
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).1 = true ∧
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).2 ≤ CHECK_BUDGET positions.card := by
  intro c96 rt pf
  exact check_honest_accepts_core h768 oracle msg salts positions rt pf (rootVal_eq_nodeVal24 c96 msg salts) rfl

end CommitGolfCandidate
