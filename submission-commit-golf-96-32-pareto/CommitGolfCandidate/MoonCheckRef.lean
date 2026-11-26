import CommitGolfCandidate.MoonCheckExec
import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! End-to-end verification of the submitted `check` image:
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
    (hx24 : s1.getReg .x24 = BitVec.ofNat 64 6733261056)
    (hx8  : s1.getReg .x8  = BitVec.ofNat 64 6867478784)
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
    simp only [posMarked14_zero, Bool.false_eq_true, ite_false]
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
    let pTotal := posRecordOff input.positions input.positions.card + 29 * capFrontierCount input.positions
    let tTotal := posTailOff input.positions input.positions.card + capFrontierCount input.positions
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
      CapWalkInv h768 oracle input sPos 9 sCap trCap ∧
      HaltsWith oracle s0 kFin (qPos + qCap)
        (if pTotal + tailBytes tTotal == input.proof.length &&
            tailBuf s0 input.proof.length tTotal == 0 &&
            readBuffer sCap (8192 + capValOff 23) 32 == (input.commitment : BitVec (8 * 32))
         then Exit.success else Exit.failure)
        (trPos ++ trCap)) := by
  intro s0 c96 pTotal tTotal
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hsteps_bd : 20 + 3715 * input.positions.card + 110000 + 25 ≤ submission.steps .check := by
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
      have hpc364 : sCap.pc = pcWord 364 := by simpa only [ite_true] using hinvCap.pc
      have hcur_fin : ProofCursor s0 input.proof.length pTotal tTotal sCap := by
        simpa only [capFrontierPrefix_9, pTotal, tTotal] using hinvCap.cursor
      have hepi := step_epilogue oracle input hvalid pTotal tTotal sCap hpc364
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
      have hev := hh.eval_of_le (show 12 ≤ submission.steps .check by rw [check_steps_eq]; decide)
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

private theorem nodeVal_succ_of_ge2 (c : Comp96) (msg : Message) (salts : Index → Salt192)
    (l idx : Nat) (hl : 2 ≤ l) :
    nodeVal c msg salts (l + 1) idx =
      if 2 * idx + 1 < levelSize l then
        maskLevel (l + 1)
          (c (binaryInput (nodeVal c msg salts l (2 * idx)) (nodeVal c msg salts l (2 * idx + 1))))
      else if 2 * idx < levelSize l then nodeVal c msg salts l (2 * idx) else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
  rfl

private theorem maskLevel_cap_eq (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23) (d : Digest) :
    maskLevel (l + 1) d = if l = 22 then d else mask238 d := by
  unfold maskLevel
  by_cases h22 : l = 22
  · simp [h22]
  · have h1 : ¬ (l + 1 < 5 ∨ l + 1 = 23) := by omega
    have h2 : ¬ (l + 1 < 9) := by omega
    simp only [h1, h2, h22, ite_false]

private theorem getElem_eq_of_idx {α : Type} {l : List α} {i1 i2 : Nat} (h : i1 = i2)
    (h1 : i1 < l.length) (h2 : i2 < l.length) : l[i1]'h1 = l[i2]'h2 := by
  subst h; rfl

private theorem evalLevel_congr_low (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt)
    (hs0 : w1.l0Sib0 = w2.l0Sib0) (hs1 : w1.l0Sib1 = w2.l0Sib1)
    (hs10 : w1.l1Sib0 = w2.l1Sib0) (hs11 : w1.l1Sib1 = w2.l1Sib1)
    (hbin : ∀ prev, 2 ≤ prev → prev < 14 → w1.binSib prev = w2.binSib prev) :
    ∀ l ≤ 14, w1.evalLevel c l = w2.evalLevel c l := by
  intro l hl
  induction l with
  | zero => simp [WitnessPath.evalLevel, hidx, hval, hsalt]
  | succ k ih =>
    cases k with
    | zero =>
      simp [WitnessPath.evalLevel, WitnessPath.evalL1, WitnessPath.l0Input, hidx, hval, hsalt, hs0, hs1]
    | succ k' =>
      cases k' with
      | zero =>
        simp [WitnessPath.evalLevel, WitnessPath.evalL2, WitnessPath.l1Input,
          WitnessPath.evalL1, WitnessPath.l0Input, hidx, hval, hsalt, hs0, hs1, hs10, hs11]
      | succ m =>
        have hih := ih (by omega)
        have hsb := hbin (m + 2) (by omega) (by omega)
        simp only [WitnessPath.evalLevel, hidx, hih, hsb]

private theorem check_sound_cap_climb (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) (sPos sCap : MachineState) (trCap : CompressionReplies)
    (hinvCap : CapWalkInv h768 oracle input sPos 9 sCap trCap)
    (i : Index) (hi : i ∈ input.positions) (w : WitnessPath)
    (hw_idx : w.index = i)
    (hw14 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 14 =
      readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32)
    (hbin_cap : ∀ prev, ¬ (prev < 14) →
      w.binSib prev = readBuffer sCap (8192 + capValOff prev + gapOffset ((((i.val / 3) / 3) >>> (prev - 2)) ^^^ 1)) 32) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∀ d ≤ 9,
      let idx := ((i.val / 3) / 3) >>> (12 + d)
      idx < levelSize (14 + d) ∧
      capMark input.positions (14 + d) idx = true ∧
      w.evalLevel c96 (14 + d) = readBuffer sCap (8192 + capValOff (14 + d) + gapOffset idx) 32 ∧
      ∀ d' < d, ∀ x ∈ w.levelInput c96 (14 + d'), InTrace h768 oracle trCap x := by
  intro c96 d hd
  induction d with
  | zero =>
    refine ⟨by rw [levelSize_14]; exact capLeafOf_lt i,
      by rw [capMark_14, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩,
      ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    have hc_lt : capLeafOf i < 456 := capLeafOf_lt i
    have hcm14 : capMark input.positions 14 (capLeafOf i) = true := by
      rw [capMark_14, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩
    have h14 := hinvCap.val14_marked (capLeafOf i) hc_lt hcm14
    simpa only [Nat.add_zero, show ((i.val / 3) / 3) >>> 12 = capLeafOf i from rfl] using
      hw14.trans h14.symm
  | succ d ih =>
    obtain ⟨hidx_lt, hcm_d, heval_d, htr_d⟩ := ih (by omega)
    let l := 14 + d
    let idx := ((i.val / 3) / 3) >>> (12 + d)
    let q := idx / 2
    have hidx_lt' : idx < levelSize l := hidx_lt
    have hcm_d' : capMark input.positions l idx = true := hcm_d
    have heval_d' : w.evalLevel c96 l = readBuffer sCap (8192 + capValOff l + gapOffset idx) 32 := heval_d
    have hidx_next : ((i.val / 3) / 3) >>> (12 + (d + 1)) = q :=
      shiftRight_succ_eq_div2 ((i.val / 3) / 3) (12 + d)
    have hq_lt : q < levelSize (l + 1) := by
      rw [levelSize_step l (by omega)]; dsimp only [q]; omega
    have heval_unfold : w.evalLevel c96 (l + 1) =
        if (idx ^^^ 1) < levelSize l then
          let inp := if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
                     else binaryInput (w.binSib l) (w.evalLevel c96 l)
          maskLevel (l + 1) (c96 inp)
        else w.evalLevel c96 l := by
      rw [evalLevel_succ_of_ge2 c96 w l (by omega)]
      simp only [hw_idx, show l - 2 = 12 + d by omega, idx]
    have hlinp_unfold : w.levelInput c96 l =
        if (idx ^^^ 1) < levelSize l then
          [if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
           else binaryInput (w.binSib l) (w.evalLevel c96 l)]
        else [] := by
      unfold WitnessPath.levelInput
      simp only [hw_idx, show l - 2 = 12 + d by omega, idx]
    by_cases hpair : (idx ^^^ 1) < levelSize l
    · have h2q1_lt : 2 * q + 1 < levelSize l := by
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · have hqm : q = m := by dsimp only [q]; omega
          rw [hm, xor_one_even] at hpair; omega
        · have hqm : q = m := by dsimp only [q]; omega
          omega
      have hq_pairs : q < levelSize l / 2 := by omega
      have hcm_next : capMark input.positions (l + 1) q = true := by
        simp only [capMark_succ input.positions l q (by omega), h2q1_lt, ite_true]
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · have hqm : q = m := by dsimp only [q]; omega
          have : 2 * q = idx := by omega
          rw [this, hcm_d']; rfl
        · have hqm : q = m := by dsimp only [q]; omega
          have : 2 * q + 1 = idx := by omega
          rw [this, hcm_d', Bool.or_true]
      obtain ⟨hcap_val, hcap_tr, _, _⟩ :=
        (hinvCap.levels_done d (by omega)).1 q hq_pairs hcm_next
      have hnot14 : ¬ (l < 14) := by omega
      have hsib_eq : w.binSib l = readBuffer sCap (8192 + capValOff l + gapOffset (idx ^^^ 1)) 32 := by
        simpa only [show l - 2 = 12 + d by omega] using hbin_cap l hnot14
      have hinp_eq : (if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
          else binaryInput (w.binSib l) (w.evalLevel c96 l)) =
          binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * q)) 32)
            (readBuffer sCap (8192 + capValOff l + gapOffset (2 * q + 1)) 32) := by
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · have hqm : q = m := by dsimp only [q]; omega
          have hev_i : idx % 2 = 0 := by omega
          have h2q : 2 * q = idx := by omega
          have h2q1 : 2 * q + 1 = idx ^^^ 1 := by rw [hm, xor_one_even]; omega
          simp only [hev_i, ite_true, heval_d', hsib_eq]; rw [h2q1, h2q]
        · have hqm : q = m := by dsimp only [q]; omega
          have hodd_i : idx % 2 ≠ 0 := by omega
          have h2q1 : 2 * q + 1 = idx := by omega
          have h2q : 2 * q = idx ^^^ 1 := by rw [hm, xor_one_odd]; omega
          simp only [hodd_i, ite_false, heval_d', hsib_eq]; rw [h2q1, h2q]
      refine ⟨by simpa only [hidx_next, show 14 + (d + 1) = l + 1 by omega] using hq_lt,
        by simpa only [hidx_next, show 14 + (d + 1) = l + 1 by omega] using hcm_next, ?_, ?_⟩
      · simp only [hidx_next, show 14 + (d + 1) = l + 1 by omega, heval_unfold, hpair, ite_true, hinp_eq]
        rw [maskLevel_cap_eq l (by omega) (by omega)]
        exact hcap_val.symm
      · intro d' hd' x hx
        by_cases hlt : d' < d
        · exact htr_d d' hlt x hx
        · have : d' = d := by omega
          subst this
          change x ∈ w.levelInput c96 l at hx
          simp only [hlinp_unfold, hpair, ite_true, hinp_eq, List.mem_singleton] at hx
          subst hx; exact hcap_tr
    · -- Odd promoted node: idx = 2 * q, levelSize l = 2 * q + 1
      have hodd_lvl : levelSize l % 2 = 1 := by
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · rw [hm, xor_one_even] at hpair; omega
        · rw [hm, xor_one_odd] at hpair; omega
      have hq_eq : q = levelSize l / 2 := by
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · rw [hm, xor_one_even] at hpair; dsimp only [q]; omega
        · rw [hm, xor_one_odd] at hpair; dsimp only [q]; omega
      have hidx_eq_2q : idx = 2 * q := by
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · dsimp only [q]; omega
        · rw [hm, xor_one_odd] at hpair; omega
      have hcm_2p : capMark input.positions l (2 * (levelSize l / 2)) = true := by
        rwa [← hq_eq, ← hidx_eq_2q]
      have hcm_next : capMark input.positions (l + 1) q = true := by
        simp only [capMark_succ input.positions l q (by omega),
          show ¬ (2 * q + 1 < levelSize l) by omega, show 2 * q < levelSize l by omega,
          ite_false, ite_true]
        rw [← hidx_eq_2q, hcm_d']
      have hprom : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset (levelSize l / 2)) 32 =
          readBuffer sCap (8192 + capValOff l + gapOffset (2 * (levelSize l / 2))) 32 :=
        (hinvCap.levels_done d (by omega)).2 hodd_lvl hcm_2p
      refine ⟨by simpa only [hidx_next, show 14 + (d + 1) = l + 1 by omega] using hq_lt,
        by simpa only [hidx_next, show 14 + (d + 1) = l + 1 by omega] using hcm_next, ?_, ?_⟩
      · simp only [hidx_next, show 14 + (d + 1) = l + 1 by omega, heval_unfold, hpair, ite_false]
        rw [heval_d', hidx_eq_2q, hq_eq, ← hprom]
      · intro d' hd' x hx
        by_cases hlt : d' < d
        · exact htr_d d' hlt x hx
        · have : d' = d := by omega
          subst this
          change x ∈ w.levelInput c96 l at hx
          simp only [hlinp_unfold, hpair, ite_false] at hx
          cases hx

private theorem evalRoot_eq_evalLevel23 (c : Comp96) (w : WitnessPath) :
    w.evalRoot c = w.evalLevel c 23 := rfl

private theorem leafInputs_congr {c : Comp96} {w1 w2 : WitnessPath}
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt) :
    w1.leafInputs c = w2.leafInputs c := by
  unfold WitnessPath.leafInputs; rw [hidx, hval, hsalt]

private theorem l0Input_congr {c : Comp96} {w1 w2 : WitnessPath}
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt)
    (hs0 : w1.l0Sib0 = w2.l0Sib0) (hs1 : w1.l0Sib1 = w2.l0Sib1) :
    w1.l0Input c = w2.l0Input c := by
  unfold WitnessPath.l0Input; rw [hidx, hval, hsalt, hs0, hs1]

private theorem l1Input_congr {c : Comp96} {w1 w2 : WitnessPath}
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt)
    (hs0 : w1.l0Sib0 = w2.l0Sib0) (hs1 : w1.l0Sib1 = w2.l0Sib1)
    (hs10 : w1.l1Sib0 = w2.l1Sib0) (hs11 : w1.l1Sib1 = w2.l1Sib1) :
    w1.l1Input c = w2.l1Input c := by
  unfold WitnessPath.l1Input WitnessPath.evalL1 WitnessPath.l0Input
  rw [hidx, hval, hsalt, hs0, hs1, hs10, hs11]

private theorem check_sound_cap_root (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) (sPos sCap : MachineState) (trCap : CompressionReplies)
    (hinvCap : CapWalkInv h768 oracle input sPos 9 sCap trCap)
    (i : Index) (hi : i ∈ input.positions) (w : WitnessPath)
    (hw_idx : w.index = i)
    (hw14 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 14 =
      readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32)
    (hbin_cap : ∀ prev, ¬ (prev < 14) →
      w.binSib prev = readBuffer sCap (8192 + capValOff prev + gapOffset ((((i.val / 3) / 3) >>> (prev - 2)) ^^^ 1)) 32) :
    w.evalRoot (fun x => oracle.compression (x.cast h768.symm)) =
      readBuffer sCap (8192 + capValOff 23) 32 ∧
    ∀ d' < 9, ∀ x ∈ w.levelInput (fun x => oracle.compression (x.cast h768.symm)) (14 + d'),
      InTrace h768 oracle trCap x := by
  obtain ⟨hidx23_lt, _, heval23, htr_cap⟩ :=
    check_sound_cap_climb h768 oracle input sPos sCap trCap hinvCap i hi w hw_idx hw14 hbin_cap 9 (le_refl 9)
  have h149 : (14 + 9 : Nat) = 23 := rfl
  have h129 : (12 + 9 : Nat) = 21 := rfl
  rw [h149, h129] at hidx23_lt heval23
  have hidx23_zero : ((i.val / 3) / 3) >>> 21 = 0 := by
    rw [levelSize_23] at hidx23_lt; omega
  have hgo0 : gapOffset 0 = 0 := by decide
  rw [hidx23_zero, hgo0, Nat.add_zero] at heval23
  exact ⟨(evalRoot_eq_evalLevel23 _ w).trans heval23, htr_cap⟩

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
      have hroot_cap : readBuffer sCap (8192 + capValOff 23) 32 = input.commitment := by
        rw [hev.1] at hexit_eq
        by_contra hne_c
        have hbeq : (readBuffer sCap (8192 + capValOff 23) 32 == (input.commitment : BitVec (8 * 32))) = false :=
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
        (posRecordOff input.positions ord) (posTailOff input.positions ord)
        (posAt input.positions ord) (valAt input ord)
      let w : WitnessPath := {
        index := pw.index
        value := pw.value
        salt := pw.salt
        l0Sib0 := pw.l0Sib0
        l0Sib1 := pw.l0Sib1
        l1Sib0 := pw.l1Sib0
        l1Sib1 := pw.l1Sib1
        binSib := fun prev =>
          if prev < 14 then pw.binSib prev
          else readBuffer sCap (8192 + capValOff prev + gapOffset ((((i.val / 3) / 3) >>> (prev - 2)) ^^^ 1)) 32
      }
      have hw_idx : w.index = i := hpos_eq
      have hw_val : w.value = input.values ⟨i, hi⟩ := hval_eq
      have hw_low : ∀ l ≤ 14,
          w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) l =
          pw.evalLevel (fun x => oracle.compression (x.cast h768.symm)) l :=
        evalLevel_congr_low (fun x => oracle.compression (x.cast h768.symm)) w pw
          rfl rfl rfl rfl rfl rfl rfl (fun prev _ hp => by simp [w, hp])
      obtain ⟨hpw14, hpw_leaf, hpw_l0, hpw_l1, hpw_bin⟩ := hinvPos.witnesses ord hord
      have hw14 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 14 =
          readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32 := by
        rw [hw_low 14 (le_refl 14), hpw14, hpos_eq]
      obtain ⟨hroot_w, htr_cap⟩ :=
        check_sound_cap_root h768 oracle input sPos sCap trCap hinvCap i hi w hw_idx hw14
          (fun prev hge => by simp only [w, hge, ite_false])
      refine ⟨w, hw_idx, hw_val, hroot_w.trans hroot_cap, ?_⟩
      intro x hx
      rw [htr_eq]
      let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
      change x ∈ w.pathInputs c96 at hx
      unfold WitnessPath.pathInputs at hx
      rcases List.mem_append.mp hx with h123 | h4
      · rcases List.mem_append.mp h123 with h12 | hl1
        · rcases List.mem_append.mp h12 with hleaf | hl0
          · rw [leafInputs_congr (c := c96) (w1 := w) (w2 := pw) rfl rfl rfl] at hleaf
            exact List.mem_append_left trCap (hpw_leaf x hleaf)
          · by_cases hfull : w.index.val / 3 = FULL_TRIPLETS_0
            · simp [hfull] at hl0
            · simp only [hfull, ite_false, List.mem_singleton] at hl0
              subst hl0
              have hl0_eq : w.l0Input c96 = pw.l0Input c96 :=
                l0Input_congr (c := c96) (w1 := w) (w2 := pw) rfl rfl rfl rfl rfl
              change InTrace h768 oracle (trPos ++ trCap) (w.l0Input c96)
              rw [hl0_eq]
              exact List.mem_append_left trCap (hpw_l0 hfull)
        · by_cases hfull1 : (w.index.val / 3) / 3 = FULL_TRIPLETS_1
          · simp [hfull1] at hl1
          · simp only [hfull1, ite_false, List.mem_singleton] at hl1
            subst hl1
            have hl1_eq : w.l1Input c96 = pw.l1Input c96 :=
              l1Input_congr (c := c96) (w1 := w) (w2 := pw) rfl rfl rfl rfl rfl rfl rfl
            change InTrace h768 oracle (trPos ++ trCap) (w.l1Input c96)
            rw [hl1_eq]
            exact List.mem_append_left trCap (hpw_l1 hfull1)
      · obtain ⟨k, hk_mem, hxk⟩ := List.mem_flatMap.mp h4
        have hk_lt : k < 21 := List.mem_range.mp hk_mem
        by_cases hlo : k + 2 ≤ 13
        · have hli_eq : w.levelInput c96 (k + 2) = pw.levelInput c96 (k + 2) := by
            unfold WitnessPath.levelInput
            have hwl : w.evalLevel c96 (k + 2) = pw.evalLevel c96 (k + 2) := hw_low (k + 2) (by omega)
            rw [hwl]
            simp only [w, show k + 2 < 14 by omega, ite_true]
          rw [hli_eq] at hxk
          exact List.mem_append_left trCap (hpw_bin (k + 2) (by omega) hlo x hxk)
        · have hd_lt : k + 2 - 14 < 9 := by omega
          have hk_eq : 14 + (k + 2 - 14) = k + 2 := by omega
          rw [← hk_eq] at hxk
          exact List.mem_append_right trPos (htr_cap (k + 2 - 14) hd_lt x hxk)

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
    refine ⟨Q + (s0.getByte (BitVec.ofNat 64 (11162446080 + (proofLen - 1 - m)))).toNat * 2 ^ (8 * (m - k)), ?_⟩
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

private theorem l0SiblingsProof_length (nodes : Nat → Nat → Digest) (i : Index) :
    (l0SiblingsProof nodes i).length = l0Bytes i := by
  unfold l0SiblingsProof l0Bytes
  dsimp only
  split_ifs <;> simp [bitsToBytes]

private theorem l1SiblingsProof_length (nodes : Nat → Nat → Digest) (i : Index) :
    (l1SiblingsProof nodes i).length = l1Bytes i := by
  unfold l1SiblingsProof l1Bytes
  dsimp only
  split_ifs <;> simp [bitsToBytes]

private theorem binPathFwd_prefix_len (nodes : Nat → Nat → Digest) (g1 n : Nat) (hn : n ≤ 12) :
    (((List.range 12).take n).map fun step =>
      (if ((g1 >>> step) ^^^ 1) < levelSize (2 + step)
       then bitsToBytes (nodes (2 + step) ((g1 >>> step) ^^^ 1))
         (if 2 + step < 5 then 32 else if 2 + step < 9 then 30 else 29)
       else []).length).sum =
    binPathOff g1 n := by
  induction n with
  | zero => simp [binPathOff]
  | succ k ih =>
    have htake : (List.range 12).take (k + 1) = (List.range 12).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih (by omega)]
    simp only [binPathOff, binStepBytes]
    by_cases hlt : ((g1 >>> k) ^^^ 1) < levelSize (2 + k)
    · simp [hlt, bitsToBytes_length]
    · simp [hlt]

private theorem binPathFwd_length (nodes : Nat → Nat → Digest) (g1 : Nat) :
    (binPathFwd nodes g1).length = binPathOff g1 12 := by
  unfold binPathFwd
  rw [List.length_flatMap]
  simpa using binPathFwd_prefix_len nodes g1 12 (le_refl 12)

private theorem binPathTails_prefix_len (nodes : Nat → Nat → Digest) (g1 n : Nat) (hn : n ≤ 5) :
    (((List.range 5).take n).map fun step =>
      (if ((g1 >>> (step + 7)) ^^^ 1) < levelSize (9 + step)
       then [tail6 (nodes (9 + step) ((g1 >>> (step + 7)) ^^^ 1))]
       else []).length).sum =
    binTailOff g1 n := by
  induction n with
  | zero => simp [binTailOff]
  | succ k ih =>
    have htake : (List.range 5).take (k + 1) = (List.range 5).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih (by omega)]
    simp only [binTailOff, binStepTails]
    by_cases hlt : ((g1 >>> (k + 7)) ^^^ 1) < levelSize (9 + k)
    · simp [hlt]
    · simp [hlt]

private theorem binPathTails_length (nodes : Nat → Nat → Digest) (g1 : Nat) :
    (binPathTails nodes g1).length = binTailOff g1 5 := by
  unfold binPathTails
  rw [List.length_flatMap]
  simpa using binPathTails_prefix_len nodes g1 5 (le_refl 5)

private theorem recordFwd_length (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) :
    (recordFwd nodes salts i).length = recordLen i := by
  unfold recordFwd recordLen
  simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length, l1SiblingsProof_length,
    binPathFwd_length]

private theorem recordTails_length (nodes : Nat → Nat → Digest) (i : Index) :
    (recordTails nodes i).length = recordTailCount i :=
  binPathTails_length nodes ((i.val / 3) / 3)

private theorem recordsFwd_prefix_len (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (n : Nat) (hn : n ≤ positions.card) :
    (((positions.sort (· ≤ ·)).take n).map fun i => (recordFwd nodes salts i).length).sum =
      posRecordOff positions n := by
  induction n with
  | zero => simp [posRecordOff]
  | succ k ih =>
    have hlt : k < (positions.sort (· ≤ ·)).length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
    rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih (by omega), posRecordOff_succ, recordFwd_length]
    congr 1
    simp only [posAt, dif_pos (show k < positions.card by omega)]

private theorem recordsFwd_flatMap_length (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) :
    ((positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts)).length =
      posRecordOff positions positions.card := by
  rw [List.length_flatMap]
  have h1 := recordsFwd_prefix_len nodes salts positions positions.card (le_refl _)
  have htake_eq : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rwa [htake_eq] at h1

private theorem recordsTails_prefix_len (nodes : Nat → Nat → Digest)
    (positions : Positions) (n : Nat) (hn : n ≤ positions.card) :
    (((positions.sort (· ≤ ·)).take n).map fun i => (recordTails nodes i).length).sum =
      posTailOff positions n := by
  induction n with
  | zero => simp [posTailOff]
  | succ k ih =>
    have hlt : k < (positions.sort (· ≤ ·)).length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
    rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih (by omega), posTailOff_succ, recordTails_length]
    congr 1
    simp only [posAt, dif_pos (show k < positions.card by omega)]

private theorem recordsTails_flatMap_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length =
      posTailOff positions positions.card := by
  rw [List.length_flatMap]
  have h1 := recordsTails_prefix_len nodes positions positions.card (le_refl _)
  have htake_eq : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rwa [htake_eq] at h1

private theorem referenceProofFwd_length (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) :
    (referenceProofFwd nodes salts positions).length =
      posRecordOff positions positions.card + 29 * capFrontierCount positions := by
  unfold referenceProofFwd
  rw [List.length_append, recordsFwd_flatMap_length, capFrontierFwd_length]

private theorem referenceProofTails_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    (referenceProofTails nodes positions).length =
      posTailOff positions positions.card + capFrontierCount positions := by
  unfold referenceProofTails
  rw [List.length_append, recordsTails_flatMap_length, capFrontierTails_length]

private theorem referenceProof_length_nonempty (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) (hne : positions.card ≠ 0) :
    (referenceProof nodes salts positions).length =
      posRecordOff positions positions.card + 29 * capFrontierCount positions +
      tailBytes (posTailOff positions positions.card + capFrontierCount positions) := by
  unfold referenceProof
  simp only [hne, ite_false]; rw [List.length_append, referenceProofFwd_length, pack6BitsRev_length,
    referenceProofTails_length]
  rfl

private theorem capFrontierFwd_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (d : Nat) (hd : d ≤ 9) :
    (((List.range 9).take d).map fun step => (capLevelFrontierFwd nodes positions (14 + step)).length).sum =
      29 * capFrontierPrefix positions d := by
  induction d with
  | zero => simp [capFrontierPrefix_zero]
  | succ k ih =>
    have htake : (List.range 9).take (k + 1) = (List.range 9).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), capLevelFrontierFwd_length, capFrontierPrefix_succ, Nat.mul_add]

private theorem capFrontierTails_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (d : Nat) (hd : d ≤ 9) :
    (((List.range 9).take d).map fun step => (capLevelFrontierTails nodes positions (14 + step)).length).sum =
      capFrontierPrefix positions d := by
  induction d with
  | zero => simp [capFrontierPrefix_zero]
  | succ k ih =>
    have htake : (List.range 9).take (k + 1) = (List.range 9).take k ++ [k] := by
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
    readBuffer (submission.initialState .check input) (11162446080 + off) n = v := by
  have hr := read_serialized_slice (submission.initialState .check input) v (11162446080 + off) 0 n (by
    intro j hj
    simp only [Nat.zero_add]
    have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
    simpa only [Nat.add_assoc] using h1.trans (hbytes j hj))
  simpa using hr

private theorem proofDigest30_of_proof_bytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off : Nat) (d : Digest) (hbd : off + 30 ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < 30), input.proof[off + j]'(by omega) = d.extractLsb' (8 * j) 8) :
    proofDigest30 (submission.initialState .check input) (11162446080 + off) = mask240 d := by
  apply proofDigest30_of_bytes_eq
  intro j hj
  have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
  simpa only [Nat.add_assoc] using h1.trans (hbytes j hj)

private theorem proofDigest238_of_proof_bytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off t : Nat) (d : Digest) (hbd : off + 29 ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < 29), input.proof[off + j]'(by omega) = d.extractLsb' (8 * j) 8)
    (htail : tailAt (submission.initialState .check input) input.proof.length t = tail6 d) :
    proofDigest238 (submission.initialState .check input) input.proof.length (11162446080 + off) t = mask238 d := by
  apply proofDigest238_of_bytes_eq
  · intro j hj
    have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
    simpa only [Nat.add_assoc] using h1.trans (hbytes j hj)
  · exact htail

/-- Extract byte `j` of `recordFwd` for position `ord` inside `referenceProof`. -/
private theorem referenceProof_recordFwd_getElem (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) (hne : positions.card ≠ 0)
    (ord j : Nat) (hord : ord < positions.card) (hj : j < recordLen (posAt positions ord))
    (hbd : posRecordOff positions ord + j < (referenceProof nodes salts positions).length) :
    (referenceProof nodes salts positions)[posRecordOff positions ord + j]'hbd =
      (recordFwd nodes salts (posAt positions ord))[j]'(by rw [recordFwd_length]; exact hj) := by
  have hrec_len := recordsFwd_flatMap_length nodes salts positions
  have hlt_rec : posRecordOff positions ord + j < ((positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts)).length := by
    rw [hrec_len]
    have h1 := posRecordOff_mono positions (show ord + 1 ≤ positions.card by omega)
    rw [posRecordOff_succ] at h1
    omega
  have hlt_fwd : posRecordOff positions ord + j < (referenceProofFwd nodes salts positions).length := by
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
    (positions : Positions) (ord j : Nat) (hord : ord < positions.card)
    (hj : j < recordTailCount (posAt positions ord))
    (hbd : posTailOff positions ord + j < (referenceProofTails nodes positions).length) :
    (referenceProofTails nodes positions)[posTailOff positions ord + j]'hbd =
      (recordTails nodes (posAt positions ord))[j]'(by rw [recordTails_length]; exact hj) := by
  have hrec_len := recordsTails_flatMap_length nodes positions
  have hlt_rec : posTailOff positions ord + j < ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length := by
    rw [hrec_len]
    have h1 := posTailOff_mono positions (show ord + 1 ≤ positions.card by omega)
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

/-- Extract forward byte `j < 29` of the frontier digest for pair `q` at cap level `14 + d`. -/
private theorem referenceProof_capFwd_getElem (nodes : Nat → Nat → Digest)
    (salts : Index → Salt192) (positions : Positions) (hne : positions.card ≠ 0)
    (d q j : Nat) (hd : d < 9) (hq : q < levelSize (14 + d) / 2) (hj : j < 29)
    (hdiff : capMark positions (14 + d) (2 * q) ≠ capMark positions (14 + d) (2 * q + 1))
    (hbd : posRecordOff positions positions.card +
        29 * (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q) + j <
      (referenceProof nodes salts positions).length) :
    (referenceProof nodes salts positions)[posRecordOff positions positions.card +
        29 * (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q) + j]'hbd =
      (nodes (14 + d) (if !capMark positions (14 + d) (2 * q) then 2 * q else 2 * q + 1)).extractLsb' (8 * j) 8 := by
  let l := 14 + d
  have hq' : q < levelSize l / 2 := hq
  have hdiff' : capMark positions l (2 * q) ≠ capMark positions l (2 * q + 1) := hdiff
  have hrec_len := recordsFwd_flatMap_length nodes salts positions
  have hq_lt_f : pairFrontierCount positions l q + 1 ≤ levelFrontierCount positions l := by
    have h1 := pairFrontierCount_mono positions l (show q + 1 ≤ levelSize l / 2 by omega)
    simp only [pairFrontierCount_full, pairFrontierCount_succ, bne_iff_ne.mpr hdiff', ite_true] at h1
    exact h1
  have hcap_lt : capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions := by
    have h1 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
    rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h1
    exact h1
  have hlt_fwd : posRecordOff positions positions.card +
      29 * (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q) + j <
      (referenceProofFwd nodes salts positions).length := by
    rw [referenceProofFwd_length]; dsimp only [l] at hq_lt_f hcap_lt; omega
  simp only [referenceProof, hne, ite_false]
  rw [List.getElem_append_left hlt_fwd]
  unfold referenceProofFwd at hlt_fwd ⊢
  rw [List.getElem_append_right (by rw [hrec_len]; omega)]
  unfold capFrontierFwd
  have hd_len : d < (List.range 9).length := by simp; omega
  have hget_d : (List.range 9)[d]'hd_len = d := by simp
  have hpref_d := capFrontierFwd_prefix_len nodes positions d (by omega)
  have hlt_lvl : 29 * pairFrontierCount positions l q + j <
      (capLevelFrontierFwd nodes positions (14 + (List.range 9)[d]'hd_len)).length := by
    rw [hget_d, capLevelFrontierFwd_length]
    change 29 * pairFrontierCount positions l q + j < 29 * levelFrontierCount positions l
    omega
  have hfm1_bd : (((List.range 9).take d).map fun step => (capLevelFrontierFwd nodes positions (14 + step)).length).sum +
      (29 * pairFrontierCount positions l q + j) <
      ((List.range 9).flatMap fun step => capLevelFrontierFwd nodes positions (14 + step)).length := by
    rw [hpref_d, List.length_flatMap]
    have h9 := capFrontierFwd_prefix_len nodes positions 9 (le_refl 9)
    rw [show (List.range 9).take 9 = List.range 9 by simp] at h9
    rw [h9, capFrontierPrefix_9]; omega
  have hidx_sub : posRecordOff positions positions.card +
      29 * (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q) + j -
      ((positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts)).length =
      (((List.range 9).take d).map fun step => (capLevelFrontierFwd nodes positions (14 + step)).length).sum +
      (29 * pairFrontierCount positions l q + j) := by
    rw [hrec_len, hpref_d]; dsimp only [l]; omega
  have hfm1 := flatMap_getElem_at (fun step => capLevelFrontierFwd nodes positions (14 + step))
    (List.range 9) d (29 * pairFrontierCount positions l q + j) hd_len hlt_lvl hfm1_bd
  rw [getElem_eq_of_idx hidx_sub _ hfm1_bd, hfm1]
  have hlt_lvl' : 29 * pairFrontierCount positions l q + j < (capLevelFrontierFwd nodes positions l).length := by
    rw [capLevelFrontierFwd_length]; omega
  have hget_d_lvl :
      (capLevelFrontierFwd nodes positions (14 + (List.range 9)[d]'hd_len))[29 * pairFrontierCount positions l q + j]'hlt_lvl =
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
  by_cases hmL : capMark positions (14 + d) (2 * q) = true
  · simp only [hmL, Bool.not_true, Bool.false_eq_true, ite_false]
    exact bitsToBytes_getElem (nodes (14 + d) (2 * q + 1)) 29 j hj _
  · have hmLf : capMark positions (14 + d) (2 * q) = false := Bool.eq_false_iff.mpr hmL
    simp only [hmLf, Bool.not_false, ite_true]
    exact bitsToBytes_getElem (nodes (14 + d) (2 * q)) 29 j hj _

/-- Extract the 6-bit tail of the frontier digest for pair `q` at cap level `14 + d`. -/
private theorem referenceProof_capTails_getElem (nodes : Nat → Nat → Digest)
    (positions : Positions) (d q : Nat) (hd : d < 9) (hq : q < levelSize (14 + d) / 2)
    (hdiff : capMark positions (14 + d) (2 * q) ≠ capMark positions (14 + d) (2 * q + 1))
    (hbd : posTailOff positions positions.card +
        (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q) <
      (referenceProofTails nodes positions).length) :
    (referenceProofTails nodes positions)[posTailOff positions positions.card +
        (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q)]'hbd =
      tail6 (nodes (14 + d) (if !capMark positions (14 + d) (2 * q) then 2 * q else 2 * q + 1)) := by
  let l := 14 + d
  have hq' : q < levelSize l / 2 := hq
  have hdiff' : capMark positions l (2 * q) ≠ capMark positions l (2 * q + 1) := hdiff
  have hrec_len := recordsTails_flatMap_length nodes positions
  have hq_lt_f : pairFrontierCount positions l q + 1 ≤ levelFrontierCount positions l := by
    have h1 := pairFrontierCount_mono positions l (show q + 1 ≤ levelSize l / 2 by omega)
    simp only [pairFrontierCount_full, pairFrontierCount_succ, bne_iff_ne.mpr hdiff', ite_true] at h1
    exact h1
  have hcap_lt : capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions := by
    have h1 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
    rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h1
    exact h1
  unfold referenceProofTails at hbd ⊢
  rw [List.getElem_append_right (by rw [hrec_len]; omega)]
  unfold capFrontierTails
  have hd_len : d < (List.range 9).length := by simp; omega
  have hget_d : (List.range 9)[d]'hd_len = d := by simp
  have hpref_d := capFrontierTails_prefix_len nodes positions d (by omega)
  have hlt_lvl : pairFrontierCount positions l q <
      (capLevelFrontierTails nodes positions (14 + (List.range 9)[d]'hd_len)).length := by
    rw [hget_d, capLevelFrontierTails_length]
    change pairFrontierCount positions l q < levelFrontierCount positions l
    omega
  have hfm1_bd : (((List.range 9).take d).map fun step => (capLevelFrontierTails nodes positions (14 + step)).length).sum +
      pairFrontierCount positions l q <
      ((List.range 9).flatMap fun step => capLevelFrontierTails nodes positions (14 + step)).length := by
    rw [hpref_d, List.length_flatMap]
    have h9 := capFrontierTails_prefix_len nodes positions 9 (le_refl 9)
    rw [show (List.range 9).take 9 = List.range 9 by simp] at h9
    rw [h9, capFrontierPrefix_9]; omega
  have hidx_sub : posTailOff positions positions.card +
      (capFrontierPrefix positions d + pairFrontierCount positions (14 + d) q) -
      ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length =
      (((List.range 9).take d).map fun step => (capLevelFrontierTails nodes positions (14 + step)).length).sum +
      pairFrontierCount positions l q := by
    rw [hrec_len, hpref_d]; dsimp only [l]; omega
  have hfm1 := flatMap_getElem_at (fun step => capLevelFrontierTails nodes positions (14 + step))
    (List.range 9) d (pairFrontierCount positions l q) hd_len hlt_lvl hfm1_bd
  rw [getElem_eq_of_idx hidx_sub _ hfm1_bd, hfm1]
  have hlt_lvl' : pairFrontierCount positions l q < (capLevelFrontierTails nodes positions l).length := by
    rw [capLevelFrontierTails_length]; omega
  have hget_d_lvl :
      (capLevelFrontierTails nodes positions (14 + (List.range 9)[d]'hd_len))[pairFrontierCount positions l q]'hlt_lvl =
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
  by_cases hmL : capMark positions (14 + d) (2 * q) = true
  · simp [hmL]
  · have hmLf : capMark positions (14 + d) (2 * q) = false := Bool.eq_false_iff.mpr hmL
    simp [hmLf]

/-- On an honest `referenceProof`, every parsed per-position witness evaluates to `nodeVal` up to L14. -/
private theorem honest_parsePartialWitness_eval14 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (positions : Positions) (hne : positions.card ≠ 0) (rt : Commitment)
    (ord : Nat) (hord : ord < positions.card) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 msg salts
    let input : CheckInput :=
      ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
    let s0 := submission.initialState .check input
    let i := posAt positions ord
    let pw := parsePartialWitness s0 input.proof.length (posRecordOff positions ord) (posTailOff positions ord)
      i (valAt input ord)
    pw.evalLevel c96 14 = nodes 14 (capLeafOf i) := by
  intro c96 nodes input s0 i pw
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  have hpf_eq : input.proof = referenceProofFwd nodes salts positions ++
      pack6BitsRev (referenceProofTails nodes positions) := by
    change referenceProof nodes salts positions = _
    unfold referenceProof; simp only [hne, ite_false]
  have hplen := referenceProof_length_nonempty nodes salts positions hne
  have htlen := referenceProofTails_length nodes positions
  let pOff := posRecordOff positions ord
  let tOff := posTailOff positions ord
  have hpOff_rec : pOff + recordLen i ≤ input.proof.length := by
    have h1 := posRecordOff_mono positions (show ord + 1 ≤ positions.card by omega)
    rw [posRecordOff_succ] at h1
    change pOff + recordLen i ≤ posRecordOff positions positions.card at h1
    change pOff + recordLen i ≤ (referenceProof nodes salts positions).length
    rw [hplen]; omega
  have htOff_rec : tOff + recordTailCount i ≤ (referenceProofTails nodes positions).length := by
    have h1 := posTailOff_mono positions (show ord + 1 ≤ positions.card by omega)
    rw [posTailOff_succ] at h1
    change tOff + recordTailCount i ≤ posTailOff positions positions.card at h1
    rw [htlen]; omega
  let g0 := i.val / 3
  let g1 := g0 / 3
  have hrec_eq : recordLen i = 24 + l0Bytes i + l1Bytes i + binPathOff g1 12 := rfl
  have hi_lt : i.val < 16777216 := i.isLt
  have hg0_le : g0 ≤ FULL_TRIPLETS_0 := by rw [full_triplets_0_eq]; omega
  have hg1_le : g1 ≤ FULL_TRIPLETS_1 := by rw [full_triplets_1_eq]; omega
  have hrec_byte : ∀ off (hoff : off < recordLen i),
      input.proof[pOff + off]'(by omega) =
        (recordFwd nodes salts i)[off]'(by rw [recordFwd_length]; exact hoff) := by
    intro off hoff
    have hbd_ref : posRecordOff positions ord + off < (referenceProof nodes salts positions).length := by
      change pOff + off < input.proof.length; omega
    exact referenceProof_recordFwd_getElem nodes salts positions hne ord off hord hoff hbd_ref
  -- Value at ord equals msg i
  have hval_msg : valAt input ord = msg i := by
    have hmem : i ∈ positions := posAt_mem positions ord hord
    rw [valAt_eq_of_posAt input ord hord i hmem rfl]
    rfl
  -- Salt matches salts i
  have hsalt_eq : pw.salt = salts i := by
    have h := readBuffer_proof_of_bitsToBytes input hvalid pOff 24 (salts i)
      (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
        rw [hrec_byte j (by unfold recordLen; omega)]
        unfold recordFwd
        rw [List.getElem_append_left (by simp [bitsToBytes_length]; omega),
          List.getElem_append_left (by simp [bitsToBytes_length]; omega),
          List.getElem_append_left (by simp [bitsToBytes_length]; omega)]
        exact bitsToBytes_getElem (salts i) 24 j hj _)
    exact h
  -- L0 evaluation matches nodes 1 g0
  have hleaf_eq : leafDigest c96 pw.index pw.salt pw.value = nodes 0 i.val := by
    have hpwi : pw.index = i := rfl
    have hpwv : pw.value = msg i := hval_msg
    rw [hpwi, hsalt_eq, hpwv]
    simp only [nodes, nodeVal, nodeValFromLeaves, i.isLt, dite_true]
  have hl1_eq : pw.evalLevel c96 1 = nodes 1 g0 := by
    change pw.evalL1 c96 = nodeValFromLeaves c96 (fun idx => leafDigest c96 idx (salts idx) (msg idx)) 1 g0
    unfold WitnessPath.evalL1 nodeValFromLeaves
    by_cases hfull : g0 = FULL_TRIPLETS_0
    · have h3f : 3 * FULL_TRIPLETS_0 = i.val := by rw [full_triplets_0_eq] at hfull ⊢; omega
      simp only [show pw.index.val / 3 = FULL_TRIPLETS_0 from hfull, hfull, ite_true,
        show ¬ (FULL_TRIPLETS_0 < FULL_TRIPLETS_0) from Nat.lt_irrefl _, ite_false, h3f]
      exact hleaf_eq
    · have hlt_f : g0 < FULL_TRIPLETS_0 := by omega
      have hl0_64 : l0Bytes i = 64 := by unfold l0Bytes; simp [show i.val / 3 ≠ FULL_TRIPLETS_0 from hfull]
      simp only [show pw.index.val / 3 ≠ FULL_TRIPLETS_0 from hfull, ite_false, hlt_f, ite_true]
      congr 1
      have hread_sib : ∀ (d0 d1 : Digest),
          l0SiblingsProof nodes i = bitsToBytes d0 32 ++ bitsToBytes d1 32 →
          pw.l0Sib0 = d0 ∧ pw.l0Sib1 = d1 := by
        intro d0 d1 hl0_eq
        constructor
        · have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 24) 32 d0
            (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
              have hrb := hrec_byte (24 + j) (by unfold recordLen; omega)
              rw [getElem_eq_of_idx (show pOff + 24 + j = pOff + (24 + j) by omega) _ (by omega), hrb]
              unfold recordFwd
              rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_right (by simp [bitsToBytes_length])]
              simp only [bitsToBytes_length, show 24 + j - 24 = j by omega, hl0_eq]
              rw [List.getElem_append_left (by simp [bitsToBytes_length]; omega)]
              exact bitsToBytes_getElem d0 32 j hj _)
          simpa [pw, parsePartialWitness, show i.val / 3 ≠ FULL_TRIPLETS_0 from hfull, Nat.add_assoc] using h
        · have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 56) 32 d1
            (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
              have hrb := hrec_byte (56 + j) (by unfold recordLen; omega)
              rw [getElem_eq_of_idx (show pOff + 56 + j = pOff + (56 + j) by omega) _ (by omega), hrb]
              unfold recordFwd
              rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_right (by simp [bitsToBytes_length]; omega)]
              simp only [bitsToBytes_length, show 56 + j - 24 = 32 + j by omega, hl0_eq]
              rw [List.getElem_append_right (by simp [bitsToBytes_length])]
              simp only [bitsToBytes_length, show 32 + j - 32 = j by omega]
              exact bitsToBytes_getElem d1 32 j hj _)
          simpa [pw, parsePartialWitness, show i.val / 3 ≠ FULL_TRIPLETS_0 from hfull, Nat.add_assoc] using h
      have hrem_cases : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hrem_cases with hr0 | hr1 | hr2
      · have hi0 : 3 * g0 = i.val := by omega
        have hl0_eq : l0SiblingsProof nodes i = bitsToBytes (nodes 0 (3 * g0 + 1)) 32 ++ bitsToBytes (nodes 0 (3 * g0 + 2)) 32 := by
          unfold l0SiblingsProof; simp [show i.val / 3 ≠ FULL_TRIPLETS_0 from hfull, hr0, g0]
        obtain ⟨hs0, hs1⟩ := hread_sib _ _ hl0_eq
        simp only [WitnessPath.l0Input, show pw.index.val % 3 = 0 from hr0, ite_true, hleaf_eq, hs0, hs1, hi0]
        rfl
      · have hi1 : 3 * g0 + 1 = i.val := by omega
        have hl0_eq : l0SiblingsProof nodes i = bitsToBytes (nodes 0 (3 * g0)) 32 ++ bitsToBytes (nodes 0 (3 * g0 + 2)) 32 := by
          unfold l0SiblingsProof; simp [show i.val / 3 ≠ FULL_TRIPLETS_0 from hfull, hr1, g0]
        obtain ⟨hs0, hs1⟩ := hread_sib _ _ hl0_eq
        simp only [WitnessPath.l0Input, show pw.index.val % 3 = 1 from hr1,
          show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, hleaf_eq, hs0, hs1, hi1]
        rfl
      · have hi2 : 3 * g0 + 2 = i.val := by omega
        have hl0_eq : l0SiblingsProof nodes i = bitsToBytes (nodes 0 (3 * g0)) 32 ++ bitsToBytes (nodes 0 (3 * g0 + 1)) 32 := by
          unfold l0SiblingsProof; simp [show i.val / 3 ≠ FULL_TRIPLETS_0 from hfull, hr2, g0]
        obtain ⟨hs0, hs1⟩ := hread_sib _ _ hl0_eq
        simp only [WitnessPath.l0Input, show pw.index.val % 3 = 2 from hr2,
          show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false, hleaf_eq, hs0, hs1, hi2]
        rfl
  -- L1 evaluation matches nodes 2 g1
  have hl2_eq : pw.evalLevel c96 2 = nodes 2 g1 := by
    change pw.evalL2 c96 = nodeValFromLeaves c96 (fun idx => leafDigest c96 idx (salts idx) (msg idx)) 2 g1
    unfold WitnessPath.evalL2 nodeValFromLeaves
    by_cases hfull1 : g1 = FULL_TRIPLETS_1
    · have h3f1 : 3 * FULL_TRIPLETS_1 = g0 := by
        rw [full_triplets_1_eq] at hfull1 ⊢; rw [full_triplets_0_eq] at hg0_le; omega
      simp only [show (pw.index.val / 3) / 3 = FULL_TRIPLETS_1 from hfull1, hfull1, ite_true,
        show ¬ (FULL_TRIPLETS_1 < FULL_TRIPLETS_1) from Nat.lt_irrefl _, ite_false, h3f1]
      exact hl1_eq
    · have hlt_f1 : g1 < FULL_TRIPLETS_1 := by omega
      have hl1_64 : l1Bytes i = 64 := by unfold l1Bytes; simp [show (i.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1]
      simp only [show (pw.index.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1, ite_false, hlt_f1, ite_true]
      congr 1
      have hread_sib1 : ∀ (d0 d1 : Digest),
          l1SiblingsProof nodes i = bitsToBytes d0 32 ++ bitsToBytes d1 32 →
          pw.l1Sib0 = d0 ∧ pw.l1Sib1 = d1 := by
        intro d0 d1 hl1_s_eq
        constructor
        · have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 24 + l0Bytes i) 32 d0
            (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
              have hrb := hrec_byte (24 + l0Bytes i + j) (by unfold recordLen; omega)
              rw [getElem_eq_of_idx (show pOff + 24 + l0Bytes i + j = pOff + (24 + l0Bytes i + j) by omega) _ (by omega), hrb]
              unfold recordFwd
              rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, l1SiblingsProof_length, hl1_64]; omega),
                List.getElem_append_right (by simp [bitsToBytes_length, l0SiblingsProof_length])]
              simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length,
                show 24 + l0Bytes i + j - (24 + l0Bytes i) = j by omega, hl1_s_eq]
              rw [List.getElem_append_left (by simp [bitsToBytes_length]; omega)]
              exact bitsToBytes_getElem d0 32 j hj _)
          simpa [pw, parsePartialWitness, show (i.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1, Nat.add_assoc] using h
        · have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 24 + l0Bytes i + 32) 32 d1
            (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
              have hrb := hrec_byte (24 + l0Bytes i + 32 + j) (by unfold recordLen; omega)
              rw [getElem_eq_of_idx (show pOff + 24 + l0Bytes i + 32 + j = pOff + (24 + l0Bytes i + 32 + j) by omega) _ (by omega), hrb]
              unfold recordFwd
              rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, l1SiblingsProof_length, hl1_64]; omega),
                List.getElem_append_right (by simp [bitsToBytes_length, l0SiblingsProof_length]; omega)]
              simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length,
                show 24 + l0Bytes i + 32 + j - (24 + l0Bytes i) = 32 + j by omega, hl1_s_eq]
              rw [List.getElem_append_right (by simp [bitsToBytes_length])]
              simp only [bitsToBytes_length, show 32 + j - 32 = j by omega]
              exact bitsToBytes_getElem d1 32 j hj _)
          simpa [pw, parsePartialWitness, show (i.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1, Nat.add_assoc] using h
      have hrem1_cases : g0 % 3 = 0 ∨ g0 % 3 = 1 ∨ g0 % 3 = 2 := by omega
      rcases hrem1_cases with hr0 | hr1 | hr2
      · have hg0_0 : 3 * g1 = g0 := by omega
        have hl1_s_eq : l1SiblingsProof nodes i = bitsToBytes (nodes 1 (3 * g1 + 1)) 32 ++ bitsToBytes (nodes 1 (3 * g1 + 2)) 32 := by
          unfold l1SiblingsProof; simp [show (i.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1, hr0, g0, g1]
        obtain ⟨hs0, hs1⟩ := hread_sib1 _ _ hl1_s_eq
        simp only [WitnessPath.l1Input, show (pw.index.val / 3) % 3 = 0 from hr0, ite_true,
          show pw.evalL1 c96 = nodes 1 g0 from hl1_eq, hs0, hs1, hg0_0]
        rfl
      · have hg0_1 : 3 * g1 + 1 = g0 := by omega
        have hl1_s_eq : l1SiblingsProof nodes i = bitsToBytes (nodes 1 (3 * g1)) 32 ++ bitsToBytes (nodes 1 (3 * g1 + 2)) 32 := by
          unfold l1SiblingsProof; simp [show (i.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1, hr1, g0, g1]
        obtain ⟨hs0, hs1⟩ := hread_sib1 _ _ hl1_s_eq
        simp only [WitnessPath.l1Input, show (pw.index.val / 3) % 3 = 1 from hr1,
          show (1 : Nat) ≠ 0 by decide, ite_false, ite_true,
          show pw.evalL1 c96 = nodes 1 g0 from hl1_eq, hs0, hs1, hg0_1]
        rfl
      · have hg0_2 : 3 * g1 + 2 = g0 := by omega
        have hl1_s_eq : l1SiblingsProof nodes i = bitsToBytes (nodes 1 (3 * g1)) 32 ++ bitsToBytes (nodes 1 (3 * g1 + 1)) 32 := by
          unfold l1SiblingsProof; simp [show (i.val / 3) / 3 ≠ FULL_TRIPLETS_1 from hfull1, hr2, g0, g1]
        obtain ⟨hs0, hs1⟩ := hread_sib1 _ _ hl1_s_eq
        simp only [WitnessPath.l1Input, show (pw.index.val / 3) % 3 = 2 from hr2,
          show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false,
          show pw.evalL1 c96 = nodes 1 g0 from hl1_eq, hs0, hs1, hg0_2]
        rfl
  -- Shared forward-byte extraction for L2..L13 siblings
  have hbin_fwd_byte : ∀ step < 12,
      let l := 2 + step
      let sib := (g1 >>> step) ^^^ 1
      let nb := if l < 5 then 32 else if l < 9 then 30 else 29
      sib < levelSize l →
      ∃ hbin_le : binPathOff g1 step + nb ≤ binPathOff g1 12,
      ∀ j (hj : j < nb),
        input.proof[pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step + j]'(by rw [hrec_eq] at hpOff_rec; omega) =
          (nodes l sib).extractLsb' (8 * j) 8 := by
    intro step hstep l sib nb hsib_lt
    have hsib_lt' : ((g1 >>> step) ^^^ 1) < levelSize (2 + step) := hsib_lt
    have hstep_b : binStepBytes g1 step = nb := by unfold binStepBytes; simp only [hsib_lt', ite_true, nb, l]
    have hbin_le : binPathOff g1 step + nb ≤ binPathOff g1 12 := by
      have h1 : binPathOff g1 (step + 1) ≤ binPathOff g1 12 := by
        have hm : ∀ a b, a ≤ b → binPathOff g1 a ≤ binPathOff g1 b := by
          intro a b hab; induction hab with
          | refl => exact le_refl _
          | step _ ih => simp only [binPathOff]; omega
        exact hm (step + 1) 12 (by omega)
      simp only [binPathOff] at h1; rw [hstep_b] at h1; exact h1
    refine ⟨hbin_le, fun j hj => ?_⟩
    have hrb := hrec_byte (24 + l0Bytes i + l1Bytes i + binPathOff g1 step + j) (by rw [hrec_eq]; omega)
    rw [getElem_eq_of_idx (show pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step + j =
        pOff + (24 + l0Bytes i + l1Bytes i + binPathOff g1 step + j) by omega) _ (by rw [hrec_eq] at hpOff_rec; omega), hrb]
    unfold recordFwd
    rw [List.getElem_append_right (by simp [List.length_append, bitsToBytes_length, l0SiblingsProof_length, l1SiblingsProof_length]; omega)]
    simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length, l1SiblingsProof_length,
      show 24 + l0Bytes i + l1Bytes i + binPathOff g1 step + j - (24 + l0Bytes i + l1Bytes i) = binPathOff g1 step + j by omega]
    unfold binPathFwd
    have hst_len : step < (List.range 12).length := by simp; omega
    have hget_st : (List.range 12)[step]'hst_len = step := by simp
    have hpref := binPathFwd_prefix_len nodes g1 step (by omega)
    have hfm_bd : (((List.range 12).take step).map fun st =>
        (if ((g1 >>> st) ^^^ 1) < levelSize (2 + st)
         then bitsToBytes (nodes (2 + st) ((g1 >>> st) ^^^ 1))
           (if 2 + st < 5 then 32 else if 2 + st < 9 then 30 else 29) else []).length).sum + j <
        ((List.range 12).flatMap fun st =>
         if ((g1 >>> st) ^^^ 1) < levelSize (2 + st)
         then bitsToBytes (nodes (2 + st) ((g1 >>> st) ^^^ 1))
           (if 2 + st < 5 then 32 else if 2 + st < 9 then 30 else 29) else []).length := by
      rw [hpref]; change binPathOff g1 step + j < (binPathFwd nodes g1).length
      rw [binPathFwd_length]; omega
    have hfm := flatMap_getElem_at (fun st =>
        if ((g1 >>> st) ^^^ 1) < levelSize (2 + st)
        then bitsToBytes (nodes (2 + st) ((g1 >>> st) ^^^ 1))
          (if 2 + st < 5 then 32 else if 2 + st < 9 then 30 else 29) else [])
      (List.range 12) step j hst_len
      (by simp only [hget_st, hsib_lt', ite_true, bitsToBytes_length]; exact hj) hfm_bd
    have hidx_st : binPathOff g1 step + j =
        (((List.range 12).take step).map fun st =>
          (if ((g1 >>> st) ^^^ 1) < levelSize (2 + st)
           then bitsToBytes (nodes (2 + st) ((g1 >>> st) ^^^ 1))
             (if 2 + st < 5 then 32 else if 2 + st < 9 then 30 else 29) else []).length).sum + j := by
      rw [hpref]
    rw [getElem_eq_of_idx hidx_st _ hfm_bd, hfm]
    simp only [hget_st, hsib_lt', ite_true]
    exact bitsToBytes_getElem (nodes l sib) nb j hj _
  -- L2..L13 siblings match nodes (2 + step) ((g1 >>> step) ^^^ 1)
  have hsib_bin_eq : ∀ step < 12,
      let l := 2 + step
      let sib := (g1 >>> step) ^^^ 1
      sib < levelSize l → pw.binSib l = nodes l sib := by
    intro step hstep l sib hsib_lt
    obtain ⟨hbin_le, hbytes⟩ := hbin_fwd_byte step hstep hsib_lt
    by_cases hlt5 : l < 5
    · have hnb : (if l < 5 then 32 else if l < 9 then 30 else 29) = 32 := by simp [hlt5]
      rw [hnb] at hbin_le
      have hrb := readBuffer_proof_of_bitsToBytes input hvalid
        (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) 32 (nodes l sib)
        (by rw [hrec_eq] at hpOff_rec; omega)
        (fun j hj => by simpa only [hnb] using hbytes j (by rw [hnb]; exact hj))
      have hpw_b : pw.binSib l =
          readBuffer s0 (11162446080 + pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) 32 := by
        dsimp only [pw, parsePartialWitness, pOff, g1, g0]
        simp only [show 2 ≤ l ∧ l ≤ 4 by omega, and_self, ite_true, show l - 2 = step by omega]
      rw [hpw_b, show 11162446080 + pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step =
          11162446080 + (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) by omega, hrb]
    · by_cases hlt9 : l < 9
      · have hnb : (if l < 5 then 32 else if l < 9 then 30 else 29) = 30 := by simp [hlt5, hlt9]
        rw [hnb] at hbin_le
        have hpd := proofDigest30_of_proof_bytes input hvalid
          (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) (nodes l sib)
          (by rw [hrec_eq] at hpOff_rec; omega)
          (fun j hj => by simpa only [hnb] using hbytes j (by rw [hnb]; exact hj))
        have hmask : mask240 (nodes l sib) = nodes l sib :=
          nodeValFromLeaves_masked c96 _ l sib (by omega) (by omega) hsib_lt
        have hpw_b : pw.binSib l =
            proofDigest30 s0 (11162446080 + pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) := by
          dsimp only [pw, parsePartialWitness, pOff, g1, g0]
          simp only [show ¬ (2 ≤ l ∧ l ≤ 4) by omega, show 5 ≤ l ∧ l ≤ 8 by omega,
            and_self, ite_false, ite_true, show l - 2 = step by omega]
        rw [hpw_b, show 11162446080 + pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step =
            11162446080 + (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) by omega, hpd, hmask]
      · have hnb : (if l < 5 then 32 else if l < 9 then 30 else 29) = 29 := by simp [hlt5, hlt9]
        rw [hnb] at hbin_le
        let step' := step - 7
        have hstep'_lt : step' < 5 := by omega
        have h9_eq : 9 + step' = l := by omega
        have hsib_lt' : ((g1 >>> (step' + 7)) ^^^ 1) < levelSize (9 + step') := by
          simpa only [show step' + 7 = step by omega, h9_eq] using hsib_lt
        have ht_le : binTailOff g1 step' + 1 ≤ binTailOff g1 5 := by
          have hm : ∀ a b, a ≤ b → binTailOff g1 a ≤ binTailOff g1 b := by
            intro a b hab; induction hab with
            | refl => exact le_refl _
            | step _ ih => simp only [binTailOff]; omega
          have h1 := hm (step' + 1) 5 (by omega)
          simp only [binTailOff, binStepTails, hsib_lt', ite_true] at h1
          exact h1
        have htail_lt : tOff + binTailOff g1 step' < (referenceProofTails nodes positions).length := by
          have : recordTailCount i = binTailOff g1 5 := rfl
          omega
        have htail_eq : tailAt s0 input.proof.length (tOff + binTailOff g1 step') = tail6 (nodes l sib) := by
          rw [honest_tailAt_eq input hvalid _ _ hpf_eq (tOff + binTailOff g1 step') htail_lt]
          rw [referenceProof_recordTails_getElem nodes positions ord (binTailOff g1 step') hord
            (by change binTailOff g1 step' < binTailOff g1 5; omega) htail_lt]
          unfold recordTails binPathTails
          have hst_len : step' < (List.range 5).length := by simp; omega
          have hget_st : (List.range 5)[step']'hst_len = step' := by simp
          have hpref := binPathTails_prefix_len nodes g1 step' (by omega)
          have hfm_bd : (((List.range 5).take step').map fun st =>
              (if ((g1 >>> (st + 7)) ^^^ 1) < levelSize (9 + st)
               then [tail6 (nodes (9 + st) ((g1 >>> (st + 7)) ^^^ 1))] else []).length).sum + 0 <
              ((List.range 5).flatMap fun st =>
               if ((g1 >>> (st + 7)) ^^^ 1) < levelSize (9 + st)
               then [tail6 (nodes (9 + st) ((g1 >>> (st + 7)) ^^^ 1))] else []).length := by
            rw [hpref, Nat.add_zero]; change binTailOff g1 step' < (binPathTails nodes g1).length
            rw [binPathTails_length]; omega
          have hfm := flatMap_getElem_at (fun st =>
              if ((g1 >>> (st + 7)) ^^^ 1) < levelSize (9 + st)
              then [tail6 (nodes (9 + st) ((g1 >>> (st + 7)) ^^^ 1))] else [])
            (List.range 5) step' 0 hst_len (by simp only [hget_st, hsib_lt', ite_true, List.length_singleton]; decide) hfm_bd
          have hidx_st : binTailOff g1 step' =
              (((List.range 5).take step').map fun st =>
                (if ((g1 >>> (st + 7)) ^^^ 1) < levelSize (9 + st)
                 then [tail6 (nodes (9 + st) ((g1 >>> (st + 7)) ^^^ 1))] else []).length).sum + 0 := by
            rw [hpref, Nat.add_zero]
          rw [getElem_eq_of_idx hidx_st _ hfm_bd, hfm]
          have h0 : ∀ (n : Nat) (hn : ((g1 >>> (n + 7)) ^^^ 1) < levelSize (9 + n))
              (h0lt : 0 < (if ((g1 >>> (n + 7)) ^^^ 1) < levelSize (9 + n)
                           then [tail6 (nodes (9 + n) ((g1 >>> (n + 7)) ^^^ 1))] else []).length),
              (if ((g1 >>> (n + 7)) ^^^ 1) < levelSize (9 + n)
               then [tail6 (nodes (9 + n) ((g1 >>> (n + 7)) ^^^ 1))] else [])[0]'h0lt =
                tail6 (nodes (9 + n) ((g1 >>> (n + 7)) ^^^ 1)) := by
            intro n hn h0lt; simp [hn]
          rw [h0 _ (by rw [hget_st]; exact hsib_lt'), hget_st, h9_eq, show step' + 7 = step by omega]
        have hpd := proofDigest238_of_proof_bytes input hvalid
          (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) (tOff + binTailOff g1 step') (nodes l sib)
          (by rw [hrec_eq] at hpOff_rec; omega)
          (fun j hj => by simpa only [hnb] using hbytes j (by rw [hnb]; exact hj)) htail_eq
        have hmask : mask238 (nodes l sib) = nodes l sib :=
          nodeValFromLeaves_masked238 c96 _ l sib (by omega) (by omega) hsib_lt
        have hpw_b : pw.binSib l = proofDigest238 s0 input.proof.length
            (11162446080 + pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) (tOff + binTailOff g1 step') := by
          dsimp only [pw, parsePartialWitness, pOff, tOff, g1, g0]
          simp only [show ¬ (2 ≤ l ∧ l ≤ 4) by omega, show ¬ (5 ≤ l ∧ l ≤ 8) by omega,
            show 9 ≤ l ∧ l ≤ 13 by omega, and_self, ite_false, ite_true,
            show l - 2 = step by omega, show l - 9 = step' by omega]
        rw [hpw_b, show 11162446080 + pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step =
            11162446080 + (pOff + 24 + l0Bytes i + l1Bytes i + binPathOff g1 step) by omega, hpd, hmask]
  -- Induction on m = 0..12: pw.evalLevel c96 (2 + m) = nodes (2 + m) (g1 >>> m)
  have hclimb : ∀ m ≤ 12, g1 >>> m < levelSize (2 + m) ∧ pw.evalLevel c96 (2 + m) = nodes (2 + m) (g1 >>> m) := by
    intro m hm
    induction m with
    | zero =>
      exact ⟨by rw [levelSize_2]; rw [full_triplets_1_eq] at hg1_le; simp; omega,
        by simpa using hl2_eq⟩
    | succ k ih =>
      obtain ⟨hidx_lt, hev_k⟩ := ih (by omega)
      let prev := 2 + k
      let idx := g1 >>> k
      let q := idx / 2
      have hidx_lt' : idx < levelSize prev := hidx_lt
      have hev_k' : pw.evalLevel c96 prev = nodes prev idx := hev_k
      have hidx_next : g1 >>> (k + 1) = q := shiftRight_succ_eq_div2 g1 k
      have hq_lt : q < levelSize (prev + 1) := by
        rw [levelSize_step prev (by omega)]; dsimp only [q]; omega
      have hpw_unfold : pw.evalLevel c96 (prev + 1) =
          if (idx ^^^ 1) < levelSize prev then
            let inp := if idx % 2 = 0 then binaryInput (pw.evalLevel c96 prev) (pw.binSib prev)
                       else binaryInput (pw.binSib prev) (pw.evalLevel c96 prev)
            maskLevel (prev + 1) (c96 inp)
          else pw.evalLevel c96 prev := by
        rw [evalLevel_succ_of_ge2 c96 pw prev (by omega)]
        simp only [show prev - 2 = k by omega, show (pw.index.val / 3) / 3 = g1 from rfl, idx]
      have hnd_unfold : nodes (prev + 1) q =
          if 2 * q + 1 < levelSize prev then
            maskLevel (prev + 1) (c96 (binaryInput (nodes prev (2 * q)) (nodes prev (2 * q + 1))))
          else if 2 * q < levelSize prev then nodes prev (2 * q) else 0 := by
        dsimp only [nodes]
        exact nodeVal_succ_of_ge2 c96 msg salts prev q (by omega)
      refine ⟨by simpa only [hidx_next, show 2 + (k + 1) = prev + 1 by omega] using hq_lt, ?_⟩
      simp only [hidx_next, show 2 + (k + 1) = prev + 1 by omega, hpw_unfold, hnd_unfold]
      by_cases hpair : (idx ^^^ 1) < levelSize prev
      · have h2q1_lt : 2 * q + 1 < levelSize prev := by
          rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
          · rw [hm, xor_one_even] at hpair; dsimp only [q]; omega
          · dsimp only [q]; omega
        simp only [hpair, h2q1_lt, ite_true]
        have hsib_eq : pw.binSib prev = nodes prev (idx ^^^ 1) :=
          hsib_bin_eq k (by omega) hpair
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · have hev : idx % 2 = 0 := by omega
          have h2q : 2 * q = idx := by dsimp only [q]; omega
          have h2q1 : 2 * q + 1 = idx ^^^ 1 := by rw [hm, xor_one_even]; dsimp only [q]; omega
          simp only [hev, ite_true, hev_k', hsib_eq]; rw [h2q1, h2q]
        · have hodd : idx % 2 ≠ 0 := by omega
          have h2q1 : 2 * q + 1 = idx := by dsimp only [q]; omega
          have h2q : 2 * q = idx ^^^ 1 := by rw [hm, xor_one_odd]; dsimp only [q]; omega
          simp only [hodd, ite_false, hev_k', hsib_eq]; rw [h2q1, h2q]
      · have hnot2q1 : ¬ (2 * q + 1 < levelSize prev) := by
          rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
          · rw [hm, xor_one_even] at hpair; dsimp only [q]; omega
          · rw [hm, xor_one_odd] at hpair; dsimp only [q]; omega
        have h2q_eq : 2 * q = idx := by
          rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
          · dsimp only [q]; omega
          · rw [hm, xor_one_odd] at hpair; omega
        simp only [hpair, hnot2q1, show 2 * q < levelSize prev by omega, ite_false, ite_true]
        rw [h2q_eq, hev_k']
  exact (hclimb 12 (le_refl 12)).2

private theorem rootVal_eq_nodeVal23 (c : Comp96) (msg : Message) (salts : Index → Salt192) :
    rootVal c msg salts = nodeVal c msg salts 23 0 := rfl

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
      sPos 9 sCap trCap) :
    ∀ d ≤ 9, ∀ idx < levelSize (14 + d),
      capMark positions (14 + d) idx = true →
      readBuffer sCap (8192 + capValOff (14 + d) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (14 + d) idx := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let nodes := nodeVal c96 msg salts
  let pf := referenceProof nodes salts positions
  let input : CheckInput := ⟨rt, positions, msg.restrict positions, pf⟩
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  have hpf_eq : input.proof = referenceProofFwd nodes salts positions ++
      pack6BitsRev (referenceProofTails nodes positions) := by
    change referenceProof nodes salts positions = _
    unfold referenceProof; simp only [hempty, ite_false]
  have hplen := referenceProof_length_nonempty nodes salts positions hempty
  have htlen := referenceProofTails_length nodes positions
  intro d hd
  induction d with
  | zero =>
    intro idx hidx hcm
    rw [levelSize_14] at hidx
    rw [capMark_14, decide_eq_true_eq] at hcm
    obtain ⟨i, hi, hci⟩ := hcm
    have hmem_sort : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
    obtain ⟨ord, hord_len, hget⟩ := List.mem_iff_getElem.mp hmem_sort
    have hord : ord < positions.card := by simpa using hord_len
    have hpos_eq : posAt positions ord = i := by simp only [posAt, dif_pos hord, hget]
    have hw1 := (hinvPos.witnesses ord hord).1
    have hev := honest_parsePartialWitness_eval14 h768 oracle msg salts positions hempty rt ord hord
    have h15 := hinvCap.val14_marked idx hidx (by rw [capMark_14, decide_eq_true_eq]; exact ⟨i, hi, hci⟩)
    rw [h15, ← hci, ← hpos_eq, ← hw1, hev]
  | succ d ih =>
    intro idx hidx hcm
    let l := 14 + d
    have hl1 : 14 ≤ l := by omega
    have hl2 : l < 23 := by omega
    have hls_next : levelSize (l + 1) = levelSize l / 2 + levelSize l % 2 := by
      rw [levelSize_step l (by omega)]; omega
    rw [show 14 + (d + 1) = l + 1 by omega] at hidx hcm ⊢
    change readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (l + 1) idx
    rw [nodeVal_succ_of_ge2 c96 msg salts l idx (by omega)]
    change readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 =
      if 2 * idx + 1 < levelSize l then
        maskLevel (l + 1) (c96 (binaryInput (nodes l (2 * idx)) (nodes l (2 * idx + 1))))
      else if 2 * idx < levelSize l then nodes l (2 * idx) else 0
    by_cases hq_pair : idx < levelSize l / 2
    · have h2q1 : 2 * idx + 1 < levelSize l := by omega
      simp only [h2q1, ite_true]
      obtain ⟨hcap_val, _, hfrL, hfrR⟩ := (hinvCap.levels_done d (by omega)).1 idx hq_pair hcm
      have hdL_eq : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32 = nodes l (2 * idx) := by
        cases hmL : capMark positions l (2 * idx) with
        | true => exact ih (by omega) (2 * idx) (by change 2 * idx < levelSize l; omega) hmL
        | false =>
          have hmR : capMark positions l (2 * idx + 1) = true := by
            simp only [capMark_succ positions l idx hl1, h2q1, ite_true, hmL] at hcm; simpa using hcm
          have hdiff : capMark positions l (2 * idx) ≠ capMark positions l (2 * idx + 1) := by
            rw [hmL, hmR]; decide
          have hfrL' : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32 =
              proofDigest238 (submission.initialState .check input) input.proof.length
                (11162446080 + (posRecordOff positions positions.card +
                  29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx)))
                (posTailOff positions positions.card +
                  (capFrontierPrefix positions d + pairFrontierCount positions l idx)) :=
            hfrL hmL
          rw [hfrL']
          have hf_step : capFrontierPrefix positions d + pairFrontierCount positions l idx + 1 ≤
              capFrontierCount positions := by
            have h1 := pairFrontierCount_mono positions l (show idx + 1 ≤ levelSize l / 2 by omega)
            simp only [pairFrontierCount_full, pairFrontierCount_succ, bne_iff_ne.mpr hdiff, ite_true] at h1
            have h2 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
            rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h2
            change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h2
            omega
          have hpd_bd : posRecordOff positions positions.card +
              29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + 29 ≤ input.proof.length := by
            change _ + 29 ≤ (referenceProof nodes salts positions).length
            rw [hplen]; omega
          have htd_bd : posTailOff positions positions.card +
              (capFrontierPrefix positions d + pairFrontierCount positions l idx) <
              (referenceProofTails nodes positions).length := by
            rw [htlen]; omega
          have hmL' : capMark positions (14 + d) (2 * idx) = false := hmL
          have htail_eq : tailAt (submission.initialState .check input) input.proof.length
              (posTailOff positions positions.card +
                (capFrontierPrefix positions d + pairFrontierCount positions l idx)) =
              tail6 (nodes l (2 * idx)) := by
            rw [honest_tailAt_eq input hvalid _ _ hpf_eq _ htd_bd]
            have ht := referenceProof_capTails_getElem nodes positions d idx (by omega) hq_pair hdiff htd_bd
            simpa only [l, hmL', Bool.not_false, ite_true] using ht
          have hpd := proofDigest238_of_proof_bytes input hvalid
            (posRecordOff positions positions.card +
              29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))
            (posTailOff positions positions.card +
              (capFrontierPrefix positions d + pairFrontierCount positions l idx))
            (nodes l (2 * idx)) hpd_bd
            (fun j hj => by
              have h := referenceProof_capFwd_getElem nodes salts positions hempty d idx j
                (by omega) hq_pair hj hdiff (by
                  change posRecordOff positions positions.card +
                    29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + j < input.proof.length
                  omega)
              simpa only [l, hmL', Bool.not_false, ite_true] using h) htail_eq
          rw [hpd]
          exact nodeValFromLeaves_masked238 c96 _ l (2 * idx) (by omega) (by omega) (by omega)
      have hdR_eq : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32 = nodes l (2 * idx + 1) := by
        cases hmR : capMark positions l (2 * idx + 1) with
        | true => exact ih (by omega) (2 * idx + 1) (by change 2 * idx + 1 < levelSize l; omega) hmR
        | false =>
          have hmL : capMark positions l (2 * idx) = true := by
            simp only [capMark_succ positions l idx hl1, h2q1, ite_true, hmR] at hcm; simpa using hcm
          have hdiff : capMark positions l (2 * idx) ≠ capMark positions l (2 * idx + 1) := by
            rw [hmL, hmR]; decide
          have hfrR' : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32 =
              proofDigest238 (submission.initialState .check input) input.proof.length
                (11162446080 + (posRecordOff positions positions.card +
                  29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx)))
                (posTailOff positions positions.card +
                  (capFrontierPrefix positions d + pairFrontierCount positions l idx)) :=
            hfrR hmR
          rw [hfrR']
          have hf_step : capFrontierPrefix positions d + pairFrontierCount positions l idx + 1 ≤
              capFrontierCount positions := by
            have h1 := pairFrontierCount_mono positions l (show idx + 1 ≤ levelSize l / 2 by omega)
            simp only [pairFrontierCount_full, pairFrontierCount_succ, bne_iff_ne.mpr hdiff, ite_true] at h1
            have h2 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
            rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h2
            change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h2
            omega
          have hpd_bd : posRecordOff positions positions.card +
              29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + 29 ≤ input.proof.length := by
            change _ + 29 ≤ (referenceProof nodes salts positions).length
            rw [hplen]; omega
          have htd_bd : posTailOff positions positions.card +
              (capFrontierPrefix positions d + pairFrontierCount positions l idx) <
              (referenceProofTails nodes positions).length := by
            rw [htlen]; omega
          have hmL' : capMark positions (14 + d) (2 * idx) = true := hmL
          have htail_eq : tailAt (submission.initialState .check input) input.proof.length
              (posTailOff positions positions.card +
                (capFrontierPrefix positions d + pairFrontierCount positions l idx)) =
              tail6 (nodes l (2 * idx + 1)) := by
            rw [honest_tailAt_eq input hvalid _ _ hpf_eq _ htd_bd]
            have ht := referenceProof_capTails_getElem nodes positions d idx (by omega) hq_pair hdiff htd_bd
            simpa only [l, hmL', Bool.not_true, Bool.false_eq_true, ite_false] using ht
          have hpd := proofDigest238_of_proof_bytes input hvalid
            (posRecordOff positions positions.card +
              29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))
            (posTailOff positions positions.card +
              (capFrontierPrefix positions d + pairFrontierCount positions l idx))
            (nodes l (2 * idx + 1)) hpd_bd
            (fun j hj => by
              have h := referenceProof_capFwd_getElem nodes salts positions hempty d idx j
                (by omega) hq_pair hj hdiff (by
                  change posRecordOff positions positions.card +
                    29 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + j < input.proof.length
                  omega)
              simpa only [l, hmL', Bool.not_true, Bool.false_eq_true, ite_false] using h) htail_eq
          rw [hpd]
          exact nodeValFromLeaves_masked238 c96 _ l (2 * idx + 1) (by omega) (by omega) (by omega)
      have hcap_val' : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 =
          if l = 22 then
            c96 (binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32)
              (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32))
          else
            mask238 (c96 (binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32)
              (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32))) := hcap_val
      rw [hcap_val', hdL_eq, hdR_eq, maskLevel_cap_eq l hl1 hl2]
    · -- Odd promoted tail
      have hodd : levelSize l % 2 = 1 := by omega
      have hidx_eq : idx = levelSize l / 2 := by omega
      have hnot2q1 : ¬ (2 * idx + 1 < levelSize l) := by omega
      have h2q : 2 * idx < levelSize l := by omega
      have hcm_l : capMark positions l (2 * (levelSize l / 2)) = true := by
        simp only [capMark_succ positions l idx hl1, hnot2q1, h2q, ite_false, ite_true] at hcm
        rw [hidx_eq] at hcm
        exact hcm
      have hprom : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset (levelSize l / 2)) 32 =
          readBuffer sCap (8192 + capValOff l + gapOffset (2 * (levelSize l / 2))) 32 :=
        (hinvCap.levels_done d (by omega)).2 hodd hcm_l
      simp only [hnot2q1, h2q, ite_false, ite_true]
      rw [hidx_eq, hprom]
      exact ih (by omega) (2 * (levelSize l / 2)) (by change 2 * (levelSize l / 2) < levelSize l; omega) hcm_l

private theorem check_honest_consistent (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (hempty : positions.card ≠ 0) (rt : Commitment) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 msg salts
    let input : CheckInput := ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
    PosConsistent c96 (submission.initialState .check input) input positions.card := by
  intro c96 nodes input
  have hplen := referenceProof_length_nonempty nodes salts positions hempty
  have ht_mono : tailBytes (posTailOff positions positions.card) ≤
      tailBytes (posTailOff positions positions.card + capFrontierCount positions) :=
    tailBytes_mono (by omega)
  refine ⟨by change posRecordOff positions positions.card + tailBytes (posTailOff positions positions.card) ≤
               (referenceProof nodes salts positions).length
             rw [hplen]; omega, ?_⟩
  intro j1 j2 hj1 hj2 hc_eq
  have h1 := honest_parsePartialWitness_eval14 h768 oracle msg salts positions hempty rt j1 hj1
  have h2 := honest_parsePartialWitness_eval14 h768 oracle msg salts positions hempty rt j2 hj2
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
  · simp only [hev.1, show input.proof.length = 0 from hpf_nil, ite_true]; rfl
  · rw [hev.2.1]; unfold CHECK_BUDGET; omega

private theorem check_honest_nonempty_root (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (hempty : positions.card ≠ 0) (rt : Commitment)
    (hrt : rt = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 23 0)
    (sPos sCap : MachineState) (trPos trCap : CompressionReplies)
    (hinvPos : PosLoopInv h768 oracle
      ⟨rt, positions, msg.restrict positions,
        referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions⟩
      positions.card sPos trPos)
    (hinvCap : CapWalkInv h768 oracle
      ⟨rt, positions, msg.restrict positions,
        referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts) salts positions⟩
      sPos 9 sCap trCap) :
    readBuffer sCap (8192 + capValOff 23) 32 = rt := by
  have hcap_eq := check_honest_cap_eq h768 oracle msg salts positions hempty rt sPos sCap trPos trCap hinvPos hinvCap
  have hcm24 := capMark_23_eq_true positions (Finset.card_pos.mp (Nat.pos_of_ne_zero hempty))
  have h24 := hcap_eq 9 (le_refl 9) 0 (by change 0 < levelSize 23; rw [levelSize_23]; decide) hcm24
  have h149 : (14 + 9 : Nat) = 23 := rfl
  have hgo0 : gapOffset 0 = 0 := by decide
  rw [h149, hgo0, Nat.add_zero] at h24
  exact h24.trans hrt.symm

private theorem check_honest_accepts_core (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions)
    (rt : Commitment) (pf : Proof)
    (hrt : rt = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 23 0)
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
        posRecordOff positions positions.card + 29 * capFrontierCount positions +
        tailBytes (posTailOff positions positions.card + capFrontierCount positions) := by
      rw [hpf]
      exact referenceProof_length_nonempty nodes salts positions hempty
    have hpf_split : input.proof = referenceProofFwd nodes salts positions ++
        pack6BitsRev (referenceProofTails nodes positions) := by
      change pf = _
      rw [hpf]; unfold referenceProof; simp only [hempty, ite_false]; rfl
    have hbuf0 : tailBuf (submission.initialState .check input) input.proof.length
        (posTailOff input.positions input.positions.card + capFrontierCount input.positions) = 0 := by
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
    · change pf.length < posRecordOff positions positions.card + 29 * capFrontierCount positions +
        tailBytes (posTailOff positions positions.card + capFrontierCount positions) at hshort
      rw [hplen] at hshort; omega
    · have hinvPos' : PosLoopInv h768 oracle
          ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
          positions.card sPos trPos := by
        simpa only [input, hpf] using hinvPos
      have hinvCap' : CapWalkInv h768 oracle
          ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
          sPos 9 sCap trCap := by
        simpa only [input, hpf] using hinvCap
      have hroot_eq : readBuffer sCap (8192 + capValOff 23) 32 = rt :=
        check_honest_nonempty_root h768 oracle msg salts positions hempty rt hrt sPos sCap trPos trCap hinvPos' hinvCap'
      have hev := hh.eval_of_le hk
      have hlen_eq : posRecordOff input.positions input.positions.card + 29 * capFrontierCount input.positions +
          tailBytes (posTailOff input.positions input.positions.card + capFrontierCount input.positions) =
          input.proof.length := hplen.symm
      have hcmt_eq : readBuffer sCap (8192 + capValOff 23) 32 = (input.commitment : BitVec (8 * 32)) := hroot_eq
      have hcond : (posRecordOff input.positions input.positions.card + 29 * capFrontierCount input.positions +
          tailBytes (posTailOff input.positions input.positions.card + capFrontierCount input.positions) ==
          input.proof.length &&
          tailBuf (submission.initialState .check input) input.proof.length
            (posTailOff input.positions input.positions.card + capFrontierCount input.positions) == 0 &&
          readBuffer sCap (8192 + capValOff 23) 32 == (input.commitment : BitVec (8 * 32))) = true :=
        (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hlen_eq, beq_iff_eq.mpr hbuf0⟩,
          beq_iff_eq.mpr hcmt_eq⟩
      have hcard_eq : input.positions.card = positions.card := rfl
      rw [hcard_eq] at hq
      refine ⟨?_, ?_⟩
      · simp only [hev.1, hcond, ite_true]; rfl
      · rw [hev.2.1]; unfold CHECK_BUDGET; omega

theorem check_honest_accepts (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (positions : Positions) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let rt := rootVal c96 msg salts
    let pf := referenceProof (nodeVal c96 msg salts) salts positions
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).1 = true ∧
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).2 ≤ CHECK_BUDGET positions.card := by
  intro c96 rt pf
  exact check_honest_accepts_core h768 oracle msg salts positions rt pf (rootVal_eq_nodeVal23 c96 msg salts) rfl

end CommitGolfCandidate
