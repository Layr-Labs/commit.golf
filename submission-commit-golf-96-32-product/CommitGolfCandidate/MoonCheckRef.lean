import CommitGolfCandidate.MoonCheckExec
import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! End-to-end verification of the submitted `check` image:
- `check_run_termination`: universal termination on all inputs within step fuel and `28 * k` oracle calls.
- `check_honest_accepts`: perfect completeness and `CHECK_BUDGET` bound on `referenceProof`.
- `check_sound`: `CheckSound h768` witness-path and compression-trace extraction for adaptive 240-bit binding. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Initial Invariant and Master Pipeline Composition -/

private theorem check_steps_eq : submission.steps .check = 68719476736 := rfl

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
    (s1 : MachineState) (hpc1 : s1.pc = pcWord 17)
    (hmem1 : s1.mem = (submission.initialState .check input).mem)
    (hfix1 : CheckFixedRegs s1 input.proof.length)
    (hx24 : s1.getReg .x24 = BitVec.ofNat 64 5637149760)
    (hx8  : s1.getReg .x8  = BitVec.ofNat 64 5771367488)
    (hx25 : s1.getReg .x25 = BitVec.ofNat 64 10066334784)
    (hx27 : s1.getReg .x27 = BitVec.ofNat 64 input.positions.card) :
    PosLoopInv h768 oracle input 0 s1 [] := by
  have hbyte0 : ∀ a < 4294971392, s1.getByte (BitVec.ofNat 64 a) = 0#8 := fun a ha => by
    simp only [MachineState.getByte, MachineState.getMem, hmem1]
    exact check_initial_zero_low input a ha
  refine ⟨hfix1, MemEqOutside.of_mem_eq hmem1 0 4294971392,
    by simp [Nat.ne_of_lt (Nat.pos_of_ne_zero hne), hpc1],
    by simpa using hx24, by simpa using hx8,
    by simpa [posRecordOff] using hx25, by simpa using hx27,
    by simp [posRecordOff], ?_, ?_, ?_, ?_, ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  · intro c hc
    rw [posMarked15_zero, if_neg (by decide)]
    exact hbyte0 (4096 + c) (by omega)
  · intro a ha1 ha2
    exact hbyte0 a (by omega)
  · intro c hc _ b hb
    exact hbyte0 (8192 + gapOffset c + b) (by unfold gapOffset; omega)
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
    let pTotal := posRecordOff input.positions input.positions.card + 30 * capFrontierCount input.positions
    (¬ PosConsistent c96 s0 input input.positions.card ∧
      ∃ k q tr, k ≤ submission.steps .check ∧ q ≤ 28 * input.positions.card ∧
        HaltsWith oracle s0 k q .failure tr) ∨
    (input.proof.length < pTotal ∧
      ∃ k q tr, k ≤ submission.steps .check ∧ q ≤ 28 * input.positions.card ∧
        HaltsWith oracle s0 k q .failure tr) ∨
    (∃ sPos sCap qPos qCap trPos trCap kFin,
      kFin ≤ submission.steps .check ∧
      qPos + qCap ≤ 28 * input.positions.card ∧
      PosLoopInv h768 oracle input input.positions.card sPos trPos ∧
      CapWalkInv h768 oracle input sPos 9 sCap trCap ∧
      HaltsWith oracle s0 kFin (qPos + qCap)
        (if pTotal == input.proof.length &&
            readBuffer sCap (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
         then Exit.success else Exit.failure)
        (trPos ++ trCap)) := by
  intro s0 c96 pTotal
  have hcard_bd : input.positions.card ≤ 16777216 := by
    have h : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    unfold LENGTH LOG_LENGTH at h; omega
  have hsteps_bd : 15 + 1100 * input.positions.card + 30000 + 25 ≤ submission.steps .check := by
    rw [check_steps_eq]; omega
  obtain ⟨s1, hs1, hpc1, hmem1, hfix1, hx24, hx8, hx25, hx27⟩ :=
    step_prologue_nonempty oracle input hne
  have hinit := posLoopInv_init h768 oracle input hne s1 hpc1 hmem1 hfix1 hx24 hx8 hx25 hx27
  have hpos := step_pos_loop h768 oracle input hvalid hne s1 hinit
  cases hpos with
  | rejected kPos qPos trPos hnot hkPos hqPos hhPos =>
    left
    refine ⟨hnot, 15 + kPos, qPos, trPos, by omega, by omega, ?_⟩
    simpa using hs1.halt hhPos
  | continued sPos kPos qPos trPos hkPos hqPos hsPos hpPos =>
    obtain ⟨hqPos_le, hinvPos⟩ := hpPos
    have hcap := step_cap_walk h768 oracle input hvalid sPos trPos hinvPos
    cases hcap with
    | rejected kCap qCap trCap hshort hkCap hqCap hhCap =>
      right; left
      refine ⟨hshort, 15 + kPos + kCap, qPos + qCap, trPos ++ trCap, by omega, by omega, ?_⟩
      simpa [Nat.add_assoc] using (hs1.trans hsPos).halt hhCap
    | continued sCap kCap qCap trCap hkCap hqCap hsCap hpCap =>
      obtain ⟨hqCap_le, hinvCap⟩ := hpCap
      have hpc318 : sCap.pc = pcWord 318 := by have := hinvCap.pc; rwa [if_pos rfl] at this
      have hx25_fin : sCap.getReg .x25 = BitVec.ofNat 64 (10066334784 + pTotal) := by
        simpa only [capFrontierPrefix_9, pTotal] using hinvCap.x25
      have hple_fin : pTotal ≤ input.proof.length := by
        simpa only [capFrontierPrefix_9, pTotal] using hinvCap.poff_le
      have hepi := step_epilogue oracle input hvalid pTotal hple_fin sCap hpc318
        hinvCap.fixed hinvCap.high hx25_fin
      right; right
      refine ⟨sPos, sCap, qPos, qCap, trPos, trCap, 15 + kPos + kCap + 25,
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

private theorem evalLevel_succ_of_ge1 (c : Comp96) (w : WitnessPath) (l : Nat) (hl : 1 ≤ l) :
    w.evalLevel c (l + 1) =
      let cur := w.evalLevel c l
      let idx := (w.index.val / 3) >>> (l - 1)
      if (idx ^^^ 1) < levelSize l then
        let inp := if idx % 2 = 0 then binaryInput cur (w.binSib l)
                   else binaryInput (w.binSib l) cur
        let raw := c inp
        if l + 1 = 24 then raw else mask240 raw
      else cur := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rfl

private theorem nodeVal_succ_of_ge1 (c : Comp96) (msg : Message) (salts : Index → Salt128)
    (l idx : Nat) (hl : 1 ≤ l) :
    nodeVal c msg salts (l + 1) idx =
      if 2 * idx + 1 < levelSize l then
        let raw := c (binaryInput (nodeVal c msg salts l (2 * idx)) (nodeVal c msg salts l (2 * idx + 1)))
        if l + 1 = 24 then raw else mask240 raw
      else if 2 * idx < levelSize l then nodeVal c msg salts l (2 * idx) else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rfl

private theorem getElem_eq_of_idx {α : Type} {l : List α} {i1 i2 : Nat} (h : i1 = i2)
    (h1 : i1 < l.length) (h2 : i2 < l.length) : l[i1]'h1 = l[i2]'h2 := by
  subst h; rfl

private theorem evalLevel_congr_low (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt)
    (hs0 : w1.l0Sib0 = w2.l0Sib0) (hs1 : w1.l0Sib1 = w2.l0Sib1)
    (hbin : ∀ prev, 1 ≤ prev → prev < 15 → w1.binSib prev = w2.binSib prev) :
    ∀ l ≤ 15, w1.evalLevel c l = w2.evalLevel c l := by
  intro l hl
  induction l with
  | zero => simp [WitnessPath.evalLevel, hidx, hval, hsalt]
  | succ k ih =>
    cases k with
    | zero =>
      simp [WitnessPath.evalLevel, WitnessPath.evalL1, WitnessPath.l0Input, hidx, hval, hsalt, hs0, hs1]
    | succ m =>
      have hih := ih (by omega)
      have hsb := hbin (m + 1) (by omega) (by omega)
      simp only [WitnessPath.evalLevel, hidx, hih, hsb]

private theorem check_sound_cap_climb (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) (sPos sCap : MachineState) (trCap : CompressionReplies)
    (hinvCap : CapWalkInv h768 oracle input sPos 9 sCap trCap)
    (i : Index) (hi : i ∈ input.positions) (w : WitnessPath)
    (hw_idx : w.index = i)
    (hw15 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 15 =
      readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32)
    (hbin_cap : ∀ prev, ¬ (prev < 15) →
      w.binSib prev = readBuffer sCap (8192 + capValOff prev + gapOffset (((i.val / 3) >>> (prev - 1)) ^^^ 1)) 32) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∀ d ≤ 9,
      let idx := (i.val / 3) >>> (14 + d)
      idx < levelSize (15 + d) ∧
      capMark input.positions (15 + d) idx = true ∧
      w.evalLevel c96 (15 + d) = readBuffer sCap (8192 + capValOff (15 + d) + gapOffset idx) 32 ∧
      ∀ d' < d, ∀ x ∈ w.levelInput c96 (15 + d'), InTrace h768 oracle trCap x := by
  intro c96 d hd
  induction d with
  | zero =>
    refine ⟨by rw [levelSize_15]; exact capLeafOf_lt i,
      by rw [capMark_15, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩,
      ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    have hc_lt : capLeafOf i < 342 := capLeafOf_lt i
    have hcm15 : capMark input.positions 15 (capLeafOf i) = true := by
      rw [capMark_15, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩
    have h15 := hinvCap.val15_marked (capLeafOf i) hc_lt hcm15
    simpa only [Nat.add_zero, show (i.val / 3) >>> 14 = capLeafOf i from rfl] using
      hw15.trans h15.symm
  | succ d ih =>
    obtain ⟨hidx_lt, hcm_d, heval_d, htr_d⟩ := ih (by omega)
    let l := 15 + d
    let idx := (i.val / 3) >>> (14 + d)
    let q := idx / 2
    have hidx_lt' : idx < levelSize l := hidx_lt
    have hcm_d' : capMark input.positions l idx = true := hcm_d
    have heval_d' : w.evalLevel c96 l = readBuffer sCap (8192 + capValOff l + gapOffset idx) 32 := heval_d
    have hidx_next : (i.val / 3) >>> (14 + (d + 1)) = q :=
      shiftRight_succ_eq_div2 (i.val / 3) (14 + d)
    have hq_lt : q < levelSize (l + 1) := by
      rw [levelSize_step l (by omega)]; dsimp only [q]; omega
    have heval_unfold : w.evalLevel c96 (l + 1) =
        if (idx ^^^ 1) < levelSize l then
          let inp := if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
                     else binaryInput (w.binSib l) (w.evalLevel c96 l)
          let raw := c96 inp
          if l + 1 = 24 then raw else mask240 raw
        else w.evalLevel c96 l := by
      rw [evalLevel_succ_of_ge1 c96 w l (by omega)]
      simp only [hw_idx, show l - 1 = 14 + d by omega, idx]
    have hlinp_unfold : w.levelInput c96 l =
        if (idx ^^^ 1) < levelSize l then
          [if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
           else binaryInput (w.binSib l) (w.evalLevel c96 l)]
        else [] := by
      unfold WitnessPath.levelInput
      simp only [hw_idx, show l - 1 = 14 + d by omega, idx]
    by_cases hpair : (idx ^^^ 1) < levelSize l
    · have h2q1_lt : 2 * q + 1 < levelSize l := by
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · have hqm : q = m := by dsimp only [q]; omega
          rw [hm, xor_one_even] at hpair; omega
        · have hqm : q = m := by dsimp only [q]; omega
          omega
      have hq_pairs : q < levelSize l / 2 := by omega
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
        (hinvCap.levels_done d (by omega)).1 q hq_pairs hcm_next
      have hnot15 : ¬ (l < 15) := by omega
      have hsib_eq : w.binSib l = readBuffer sCap (8192 + capValOff l + gapOffset (idx ^^^ 1)) 32 := by
        simpa only [show l - 1 = 14 + d by omega] using hbin_cap l hnot15
      have hinp_eq : (if idx % 2 = 0 then binaryInput (w.evalLevel c96 l) (w.binSib l)
          else binaryInput (w.binSib l) (w.evalLevel c96 l)) =
          binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * q)) 32)
            (readBuffer sCap (8192 + capValOff l + gapOffset (2 * q + 1)) 32) := by
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
      refine ⟨by simpa only [hidx_next, show 15 + (d + 1) = l + 1 by omega] using hq_lt,
        by simpa only [hidx_next, show 15 + (d + 1) = l + 1 by omega] using hcm_next, ?_, ?_⟩
      · simp only [hidx_next, show 15 + (d + 1) = l + 1 by omega, heval_unfold, hpair, ite_true,
          hinp_eq, show (l + 1 = 24) ↔ (l = 23) by omega]
        exact hcap_val.symm
      · intro d' hd' x hx
        by_cases hlt : d' < d
        · exact htr_d d' hlt x hx
        · have : d' = d := by omega
          subst this
          change x ∈ w.levelInput c96 l at hx
          rw [hlinp_unfold, if_pos hpair, hinp_eq, List.mem_singleton] at hx
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
        rw [capMark_succ input.positions l q (by omega), if_neg (by omega), if_pos (by omega),
          ← hidx_eq_2q, hcm_d']
      have hprom : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset (levelSize l / 2)) 32 =
          readBuffer sCap (8192 + capValOff l + gapOffset (2 * (levelSize l / 2))) 32 :=
        (hinvCap.levels_done d (by omega)).2 hodd_lvl hcm_2p
      refine ⟨by simpa only [hidx_next, show 15 + (d + 1) = l + 1 by omega] using hq_lt,
        by simpa only [hidx_next, show 15 + (d + 1) = l + 1 by omega] using hcm_next, ?_, ?_⟩
      · simp only [hidx_next, show 15 + (d + 1) = l + 1 by omega, heval_unfold, hpair, ite_false]
        rw [heval_d', hidx_eq_2q, hq_eq, ← hprom]
      · intro d' hd' x hx
        by_cases hlt : d' < d
        · exact htr_d d' hlt x hx
        · have : d' = d := by omega
          subst this
          change x ∈ w.levelInput c96 l at hx
          rw [hlinp_unfold, if_neg hpair] at hx
          cases hx

private theorem evalRoot_eq_evalLevel24 (c : Comp96) (w : WitnessPath) :
    w.evalRoot c = w.evalLevel c 24 := rfl

private theorem leafInputs_congr {c : Comp96} {w1 w2 : WitnessPath}
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt) :
    w1.leafInputs c = w2.leafInputs c := by
  unfold WitnessPath.leafInputs; rw [hidx, hval, hsalt]

private theorem l0Input_congr {c : Comp96} {w1 w2 : WitnessPath}
    (hidx : w1.index = w2.index) (hval : w1.value = w2.value) (hsalt : w1.salt = w2.salt)
    (hs0 : w1.l0Sib0 = w2.l0Sib0) (hs1 : w1.l0Sib1 = w2.l0Sib1) :
    w1.l0Input c = w2.l0Input c := by
  unfold WitnessPath.l0Input; rw [hidx, hval, hsalt, hs0, hs1]

private theorem check_sound_cap_root (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) (sPos sCap : MachineState) (trCap : CompressionReplies)
    (hinvCap : CapWalkInv h768 oracle input sPos 9 sCap trCap)
    (i : Index) (hi : i ∈ input.positions) (w : WitnessPath)
    (hw_idx : w.index = i)
    (hw15 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 15 =
      readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32)
    (hbin_cap : ∀ prev, ¬ (prev < 15) →
      w.binSib prev = readBuffer sCap (8192 + capValOff prev + gapOffset (((i.val / 3) >>> (prev - 1)) ^^^ 1)) 32) :
    w.evalRoot (fun x => oracle.compression (x.cast h768.symm)) =
      readBuffer sCap (8192 + capValOff 24) 32 ∧
    ∀ d' < 9, ∀ x ∈ w.levelInput (fun x => oracle.compression (x.cast h768.symm)) (15 + d'),
      InTrace h768 oracle trCap x := by
  obtain ⟨hidx24_lt, _, heval24, htr_cap⟩ :=
    check_sound_cap_climb h768 oracle input sPos sCap trCap hinvCap i hi w hw_idx hw15 hbin_cap 9 (le_refl 9)
  have h159 : (15 + 9 : Nat) = 24 := rfl
  have h149 : (14 + 9 : Nat) = 23 := rfl
  rw [h159, h149] at hidx24_lt heval24
  have hidx24_zero : (i.val / 3) >>> 23 = 0 := by
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
      let pw := parsePartialWitness (submission.initialState .check input) (posRecordOff input.positions ord)
        (posAt input.positions ord) (valAt input ord)
      let w : WitnessPath := {
        index := pw.index
        value := pw.value
        salt := pw.salt
        l0Sib0 := pw.l0Sib0
        l0Sib1 := pw.l0Sib1
        binSib := fun prev =>
          if prev < 15 then pw.binSib prev
          else readBuffer sCap (8192 + capValOff prev + gapOffset (((i.val / 3) >>> (prev - 1)) ^^^ 1)) 32
      }
      have hw_idx : w.index = i := hpos_eq
      have hw_val : w.value = input.values ⟨i, hi⟩ := hval_eq
      have hw_low : ∀ l ≤ 15,
          w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) l =
          pw.evalLevel (fun x => oracle.compression (x.cast h768.symm)) l :=
        evalLevel_congr_low (fun x => oracle.compression (x.cast h768.symm)) w pw
          rfl rfl rfl rfl rfl (fun prev _ hp => by simp [w, hp])
      obtain ⟨hpw15, hpw_leaf, hpw_l0, hpw_bin⟩ := hinvPos.witnesses ord hord
      have hw15 : w.evalLevel (fun x => oracle.compression (x.cast h768.symm)) 15 =
          readBuffer sPos (8192 + gapOffset (capLeafOf i)) 32 := by
        rw [hw_low 15 (le_refl 15), hpw15, hpos_eq]
      obtain ⟨hroot_w, htr_cap⟩ :=
        check_sound_cap_root h768 oracle input sPos sCap trCap hinvCap i hi w hw_idx hw15
          (fun prev hge => by simp only [w, hge, ite_false])
      refine ⟨w, hw_idx, hw_val, hroot_w.trans hroot_cap, ?_⟩
      intro x hx
      rw [htr_eq]
      let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
      change x ∈ w.pathInputs c96 at hx
      unfold WitnessPath.pathInputs at hx
      rcases List.mem_append.mp hx with h12 | h3
      · rcases List.mem_append.mp h12 with hleaf | hl0
        · rw [leafInputs_congr (c := c96) (w1 := w) (w2 := pw) rfl rfl rfl] at hleaf
          exact List.mem_append_left trCap (hpw_leaf x hleaf)
        · by_cases hfull : w.index.val / 3 = FULL_TRIPLETS
          · simp [hfull] at hl0
          · simp only [hfull, ite_false, List.mem_singleton] at hl0
            subst hl0
            have hl0_eq : w.l0Input c96 = pw.l0Input c96 :=
              l0Input_congr (c := c96) (w1 := w) (w2 := pw) rfl rfl rfl rfl rfl
            change InTrace h768 oracle (trPos ++ trCap) (w.l0Input c96)
            rw [hl0_eq]
            exact List.mem_append_left trCap (hpw_l0 hfull)
      · obtain ⟨k, hk_mem, hxk⟩ := List.mem_flatMap.mp h3
        have hk_lt : k < 23 := List.mem_range.mp hk_mem
        by_cases hlo : k + 1 ≤ 14
        · have hli_eq : w.levelInput c96 (k + 1) = pw.levelInput c96 (k + 1) := by
            unfold WitnessPath.levelInput
            have hwl : w.evalLevel c96 (k + 1) = pw.evalLevel c96 (k + 1) := hw_low (k + 1) (by omega)
            rw [hwl]
            simp only [w, show k + 1 < 15 by omega, ite_true]
          rw [hli_eq] at hxk
          exact List.mem_append_left trCap (hpw_bin (k + 1) (by omega) hlo x hxk)
        · have hd_lt : k + 1 - 15 < 9 := by omega
          have hk_eq : 15 + (k + 1 - 15) = k + 1 := by omega
          rw [← hk_eq] at hxk
          exact List.mem_append_right trPos (htr_cap (k + 1 - 15) hd_lt x hxk)

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

private theorem l0SiblingsProof_length (nodes : Nat → Nat → Digest) (i : Index) :
    (l0SiblingsProof nodes i).length = l0Bytes i := by
  unfold l0SiblingsProof l0Bytes
  dsimp only
  split_ifs <;> simp [bitsToBytes]

private theorem binPathProof_prefix_len (nodes : Nat → Nat → Digest) (g n : Nat) (hn : n ≤ 13) :
    (((List.range 13).take n).map fun step =>
      (if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
       then bitsToBytes (nodes (2 + step) ((g >>> (step + 1)) ^^^ 1)) 30 else []).length).sum =
    binPathOff g n := by
  induction n with
  | zero => simp [binPathOff]
  | succ k ih =>
    have htake : (List.range 13).take (k + 1) = (List.range 13).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih (by omega)]
    simp only [binPathOff, binStepBytes]
    by_cases hlt : ((g >>> (k + 1)) ^^^ 1) < levelSize (2 + k)
    · simp [hlt, bitsToBytes_length]
    · simp [hlt]

private theorem binPathProof_length (nodes : Nat → Nat → Digest) (g : Nat) :
    (binPathProof nodes g).length = binPathOff g 13 := by
  unfold binPathProof
  rw [List.length_flatMap]
  simpa using binPathProof_prefix_len nodes g 13 (le_refl 13)

private theorem recordProof_length (nodes : Nat → Nat → Digest) (salts : Index → Salt128) (i : Index) :
    (recordProof nodes salts i).length = recordLen i := by
  unfold recordProof recordLen
  simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length, binPathProof_length]

private theorem records_prefix_len (nodes : Nat → Nat → Digest) (salts : Index → Salt128)
    (positions : Positions) (n : Nat) (hn : n ≤ positions.card) :
    (((positions.sort (· ≤ ·)).take n).map fun i => (recordProof nodes salts i).length).sum =
      posRecordOff positions n := by
  induction n with
  | zero => simp [posRecordOff]
  | succ k ih =>
    have hlt : k < (positions.sort (· ≤ ·)).length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
    rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih (by omega), posRecordOff_succ, recordProof_length]
    congr 1
    simp only [posAt, dif_pos (show k < positions.card by omega)]

private theorem records_flatMap_length (nodes : Nat → Nat → Digest)
    (salts : Index → Salt128) (positions : Positions) :
    ((positions.sort (· ≤ ·)).flatMap (recordProof nodes salts)).length =
      posRecordOff positions positions.card := by
  rw [List.length_flatMap]
  have h1 := records_prefix_len nodes salts positions positions.card (le_refl _)
  have htake_eq : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rwa [htake_eq] at h1

private theorem referenceProof_length_nonempty (nodes : Nat → Nat → Digest)
    (salts : Index → Salt128) (positions : Positions) (hne : positions.card ≠ 0) :
    (referenceProof nodes salts positions).length =
      posRecordOff positions positions.card + 30 * capFrontierCount positions := by
  unfold referenceProof
  rw [if_neg hne, List.length_append, records_flatMap_length, capFrontierProof_length]

private theorem capFrontier_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (d : Nat) (hd : d ≤ 9) :
    (((List.range 9).take d).map fun step => (capLevelFrontierProof nodes positions (15 + step)).length).sum =
      30 * capFrontierPrefix positions d := by
  induction d with
  | zero => simp [capFrontierPrefix_zero]
  | succ k ih =>
    have htake : (List.range 9).take (k + 1) = (List.range 9).take k ++ [k] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [List.getElem_range]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih (by omega), capLevelFrontierProof_length, capFrontierPrefix_succ, Nat.mul_add]

private theorem capLevel_pair_prefix_len (nodes : Nat → Nat → Digest) (positions : Positions)
    (l n : Nat) (hn : n ≤ levelSize l / 2) :
    (((List.range (levelSize l / 2)).take n).map fun q =>
      (let mL := capMark positions l (2 * q)
       let mR := capMark positions l (2 * q + 1)
       if mL = mR then []
       else if !mL then bitsToBytes (nodes l (2 * q)) 30
       else bitsToBytes (nodes l (2 * q + 1)) 30).length).sum =
      30 * pairFrontierCount positions l n := by
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

private theorem readBuffer_proof_of_bitsToBytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off n : Nat) (v : BitVec (8 * n))
    (hbd : off + n ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < n), input.proof[off + j]'(by omega) = v.extractLsb' (8 * j) 8) :
    readBuffer (submission.initialState .check input) (10066334784 + off) n = v := by
  have hr := read_serialized_slice (submission.initialState .check input) v (10066334784 + off) 0 n (by
    intro j hj
    simp only [Nat.zero_add]
    have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
    simpa only [Nat.add_assoc] using h1.trans (hbytes j hj))
  simpa using hr

private theorem proofDigest30_of_proof_bytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (off : Nat) (d : Digest) (hbd : off + 30 ≤ input.proof.length)
    (hbytes : ∀ j (hj : j < 30), input.proof[off + j]'(by omega) = d.extractLsb' (8 * j) 8) :
    proofDigest30 (submission.initialState .check input) (10066334784 + off) = mask240 d := by
  apply proofDigest30_of_bytes_eq
  intro j hj
  have h1 := check_initial_proof_byte input hvalid (off + j) (by omega)
  simpa only [Nat.add_assoc] using h1.trans (hbytes j hj)

/-- Extract byte `j` of `recordProof` for position `ord` inside `referenceProof`. -/
private theorem referenceProof_record_getElem (nodes : Nat → Nat → Digest)
    (salts : Index → Salt128) (positions : Positions) (hne : positions.card ≠ 0)
    (ord j : Nat) (hord : ord < positions.card) (hj : j < recordLen (posAt positions ord))
    (hbd : posRecordOff positions ord + j < (referenceProof nodes salts positions).length) :
    (referenceProof nodes salts positions)[posRecordOff positions ord + j]'hbd =
      (recordProof nodes salts (posAt positions ord))[j]'(by rw [recordProof_length]; exact hj) := by
  have hrec_len := records_flatMap_length nodes salts positions
  have hlt_rec : posRecordOff positions ord + j < ((positions.sort (· ≤ ·)).flatMap (recordProof nodes salts)).length := by
    rw [hrec_len]
    have h1 := posRecordOff_mono positions (show ord + 1 ≤ positions.card by omega)
    rw [posRecordOff_succ] at h1
    omega
  simp only [referenceProof, hne, ite_false]
  rw [List.getElem_append_left hlt_rec]
  have hpref := records_prefix_len nodes salts positions ord (by omega)
  have hord' : ord < (positions.sort (· ≤ ·)).length := by simpa using hord
  have hpos_get : (positions.sort (· ≤ ·))[ord]'hord' = posAt positions ord := by
    simp only [posAt, dif_pos hord]
  have hj' : j < (recordProof nodes salts ((positions.sort (· ≤ ·))[ord]'hord')).length := by
    rw [hpos_get, recordProof_length]; exact hj
  have hfm := flatMap_getElem_at (recordProof nodes salts) (positions.sort (· ≤ ·)) ord j hord' hj'
    (by rwa [hpref])
  simpa only [hpref, hpos_get] using hfm

/-- Extract byte `j < 30` of the frontier digest for pair `q` at cap level `15 + d` inside `referenceProof`. -/
private theorem referenceProof_cap_getElem (nodes : Nat → Nat → Digest)
    (salts : Index → Salt128) (positions : Positions) (hne : positions.card ≠ 0)
    (d q j : Nat) (hd : d < 9) (hq : q < levelSize (15 + d) / 2) (hj : j < 30)
    (hdiff : capMark positions (15 + d) (2 * q) ≠ capMark positions (15 + d) (2 * q + 1))
    (hbd : posRecordOff positions positions.card +
        30 * (capFrontierPrefix positions d + pairFrontierCount positions (15 + d) q) + j <
      (referenceProof nodes salts positions).length) :
    (referenceProof nodes salts positions)[posRecordOff positions positions.card +
        30 * (capFrontierPrefix positions d + pairFrontierCount positions (15 + d) q) + j]'hbd =
      (nodes (15 + d) (if !capMark positions (15 + d) (2 * q) then 2 * q else 2 * q + 1)).extractLsb' (8 * j) 8 := by
  let l := 15 + d
  have hq' : q < levelSize l / 2 := hq
  have hdiff' : capMark positions l (2 * q) ≠ capMark positions l (2 * q + 1) := hdiff
  have hrec_len := records_flatMap_length nodes salts positions
  simp only [referenceProof, hne, ite_false]
  rw [List.getElem_append_right (by rw [hrec_len]; omega)]
  unfold capFrontierProof
  have hd_len : d < (List.range 9).length := by simp; omega
  have hget_d : (List.range 9)[d]'hd_len = d := by simp
  have hpref_d := capFrontier_prefix_len nodes positions d (by omega)
  have hq_lt_f : pairFrontierCount positions l q + 1 ≤ levelFrontierCount positions l := by
    have h1 := pairFrontierCount_mono positions l (show q + 1 ≤ levelSize l / 2 by omega)
    rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff')] at h1
    exact h1
  have hlt_lvl : 30 * pairFrontierCount positions l q + j <
      (capLevelFrontierProof nodes positions (15 + (List.range 9)[d]'hd_len)).length := by
    rw [hget_d, capLevelFrontierProof_length]
    change 30 * pairFrontierCount positions l q + j < 30 * levelFrontierCount positions l
    omega
  have hfm1_bd : (((List.range 9).take d).map fun step => (capLevelFrontierProof nodes positions (15 + step)).length).sum +
      (30 * pairFrontierCount positions l q + j) <
      ((List.range 9).flatMap fun step => capLevelFrontierProof nodes positions (15 + step)).length := by
    rw [hpref_d, List.length_flatMap]
    have h9 := capFrontier_prefix_len nodes positions 9 (le_refl 9)
    rw [show (List.range 9).take 9 = List.range 9 by simp] at h9
    rw [h9, capFrontierPrefix_9]
    have h1 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
    rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h1
    change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h1
    omega
  have hidx_sub : posRecordOff positions positions.card +
      30 * (capFrontierPrefix positions d + pairFrontierCount positions (15 + d) q) + j -
      ((positions.sort (· ≤ ·)).flatMap (recordProof nodes salts)).length =
      (((List.range 9).take d).map fun step => (capLevelFrontierProof nodes positions (15 + step)).length).sum +
      (30 * pairFrontierCount positions l q + j) := by
    rw [hrec_len, hpref_d]; dsimp only [l]; omega
  have hfm1 := flatMap_getElem_at (fun step => capLevelFrontierProof nodes positions (15 + step))
    (List.range 9) d (30 * pairFrontierCount positions l q + j) hd_len hlt_lvl hfm1_bd
  rw [getElem_eq_of_idx hidx_sub _ hfm1_bd, hfm1]
  have hlt_lvl' : 30 * pairFrontierCount positions l q + j < (capLevelFrontierProof nodes positions l).length := by
    rw [capLevelFrontierProof_length]; omega
  have hget_d_lvl :
      (capLevelFrontierProof nodes positions (15 + (List.range 9)[d]'hd_len))[30 * pairFrontierCount positions l q + j]'hlt_lvl =
      (capLevelFrontierProof nodes positions l)[30 * pairFrontierCount positions l q + j]'hlt_lvl' := by
    simp only [hget_d, l]
  rw [hget_d_lvl]
  unfold capLevelFrontierProof at hlt_lvl' ⊢
  have hq_len : q < (List.range (levelSize l / 2)).length := by simp; omega
  have hget_q : (List.range (levelSize l / 2))[q]'hq_len = q := by simp
  have hpref_q := capLevel_pair_prefix_len nodes positions l q (by omega)
  have hpair_len : (have mL := capMark positions l (2 * q)
      have mR := capMark positions l (2 * q + 1)
      if mL = mR then []
      else if !mL then bitsToBytes (nodes l (2 * q)) 30
      else bitsToBytes (nodes l (2 * q + 1)) 30).length = 30 := by
    simp only [hdiff', ite_false]; split <;> simp [bitsToBytes]
  have hfm2_bd : (((List.range (levelSize l / 2)).take q).map fun q0 =>
      (have mL := capMark positions l (2 * q0)
       have mR := capMark positions l (2 * q0 + 1)
       if mL = mR then []
       else if !mL then bitsToBytes (nodes l (2 * q0)) 30
       else bitsToBytes (nodes l (2 * q0 + 1)) 30).length).sum + j <
      ((List.range (levelSize l / 2)).flatMap fun q0 =>
       have mL := capMark positions l (2 * q0)
       have mR := capMark positions l (2 * q0 + 1)
       if mL = mR then []
       else if !mL then bitsToBytes (nodes l (2 * q0)) 30
       else bitsToBytes (nodes l (2 * q0 + 1)) 30).length := by
    rw [hpref_q]; change 30 * pairFrontierCount positions l q + j < (capLevelFrontierProof nodes positions l).length
    rw [capLevelFrontierProof_length]; omega
  have hfm2 := flatMap_getElem_at (fun q0 =>
      have mL := capMark positions l (2 * q0)
      have mR := capMark positions l (2 * q0 + 1)
      if mL = mR then []
      else if !mL then bitsToBytes (nodes l (2 * q0)) 30
      else bitsToBytes (nodes l (2 * q0 + 1)) 30)
    (List.range (levelSize l / 2)) q j hq_len (by rw [hget_q, hpair_len]; exact hj) hfm2_bd
  have hidx_q : 30 * pairFrontierCount positions l q + j =
      (((List.range (levelSize l / 2)).take q).map fun q0 =>
        (have mL := capMark positions l (2 * q0)
         have mR := capMark positions l (2 * q0 + 1)
         if mL = mR then []
         else if !mL then bitsToBytes (nodes l (2 * q0)) 30
         else bitsToBytes (nodes l (2 * q0 + 1)) 30).length).sum + j := by
    rw [hpref_q]
  rw [getElem_eq_of_idx hidx_q hlt_lvl' hfm2_bd, hfm2]
  simp only [hget_q, hdiff', ite_false]
  dsimp only [l]
  by_cases hmL : capMark positions (15 + d) (2 * q) = true
  · simp only [hmL, Bool.not_true, Bool.false_eq_true, ite_false]
    exact bitsToBytes_getElem (nodes (15 + d) (2 * q + 1)) 30 j hj _
  · have hmLf : capMark positions (15 + d) (2 * q) = false := Bool.eq_false_iff.mpr hmL
    simp only [hmLf, Bool.not_false, ite_true]
    exact bitsToBytes_getElem (nodes (15 + d) (2 * q)) 30 j hj _

/-- On an honest `referenceProof`, every parsed per-position witness evaluates to `nodeVal` up to L15. -/
private theorem honest_parsePartialWitness_eval15 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (positions : Positions) (hne : positions.card ≠ 0) (rt : Commitment)
    (ord : Nat) (hord : ord < positions.card) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 msg salts
    let input : CheckInput :=
      ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
    let s0 := submission.initialState .check input
    let i := posAt positions ord
    let pw := parsePartialWitness s0 (posRecordOff positions ord) i (valAt input ord)
    pw.evalLevel c96 15 = nodes 15 (capLeafOf i) := by
  intro c96 nodes input s0 i pw
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  have hplen := referenceProof_length_nonempty nodes salts positions hne
  let pOff := posRecordOff positions ord
  have hpOff_rec : pOff + recordLen i ≤ input.proof.length := by
    have h1 := posRecordOff_mono positions (show ord + 1 ≤ positions.card by omega)
    rw [posRecordOff_succ] at h1
    change pOff + recordLen i ≤ posRecordOff positions positions.card at h1
    change pOff + recordLen i ≤ (referenceProof nodes salts positions).length
    rw [hplen]; omega
  let g := i.val / 3
  have hrec_eq : recordLen i = 16 + l0Bytes i + 32 + binPathOff g 13 := rfl
  have hi_lt : i.val < 16777216 := i.isLt
  have hg_le : g ≤ FULL_TRIPLETS := by rw [full_triplets_eq]; omega
  have hrec_byte : ∀ off (hoff : off < recordLen i),
      input.proof[pOff + off]'(by omega) =
        (recordProof nodes salts i)[off]'(by rw [recordProof_length]; exact hoff) := by
    intro off hoff
    have hbd_ref : posRecordOff positions ord + off < (referenceProof nodes salts positions).length := by
      change pOff + off < input.proof.length; omega
    exact referenceProof_record_getElem nodes salts positions hne ord off hord hoff hbd_ref
  -- Value at ord equals msg i
  have hval_msg : valAt input ord = msg i := by
    have hmem : i ∈ positions := posAt_mem positions ord hord
    rw [valAt_eq_of_posAt input ord hord i hmem rfl]
    rfl
  -- Salt matches salts i
  have hsalt_eq : pw.salt = salts i := by
    have h := readBuffer_proof_of_bitsToBytes input hvalid pOff 16 (salts i)
      (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
        rw [hrec_byte j (by unfold recordLen; omega)]
        unfold recordProof
        rw [List.getElem_append_left (by simp [bitsToBytes_length]; omega),
          List.getElem_append_left (by simp [bitsToBytes_length]; omega),
          List.getElem_append_left (by simp [bitsToBytes_length]; omega)]
        exact bitsToBytes_getElem (salts i) 16 j hj _)
    exact h
  -- L0 evaluation matches nodes 1 g
  have hleaf_eq : leafDigest c96 pw.index pw.salt pw.value = nodes 0 i.val := by
    have hpwi : pw.index = i := rfl
    have hpwv : pw.value = msg i := hval_msg
    rw [hpwi, hsalt_eq, hpwv]
    simp only [nodes, nodeVal, nodeValFromLeaves, i.isLt, dite_true]
  have hl1_eq : pw.evalLevel c96 1 = nodes 1 g := by
    change pw.evalL1 c96 = nodeValFromLeaves c96 (fun idx => leafDigest c96 idx (salts idx) (msg idx)) 1 g
    unfold WitnessPath.evalL1 nodeValFromLeaves
    by_cases hfull : g = FULL_TRIPLETS
    · have h3f : 3 * FULL_TRIPLETS = i.val := by rw [full_triplets_eq] at hfull ⊢; omega
      simp only [show pw.index.val / 3 = FULL_TRIPLETS from hfull, hfull, ite_true,
        show ¬ (FULL_TRIPLETS < FULL_TRIPLETS) from Nat.lt_irrefl _, ite_false, h3f]
      exact hleaf_eq
    · have hlt_f : g < FULL_TRIPLETS := by omega
      have hl0_64 : l0Bytes i = 64 := by unfold l0Bytes; simp [show i.val / 3 ≠ FULL_TRIPLETS from hfull]
      simp only [show pw.index.val / 3 ≠ FULL_TRIPLETS from hfull, ite_false, hlt_f, ite_true]
      congr 1
      have hread_sib : ∀ (d0 d1 : Digest),
          l0SiblingsProof nodes i = bitsToBytes d0 32 ++ bitsToBytes d1 32 →
          pw.l0Sib0 = d0 ∧ pw.l0Sib1 = d1 := by
        intro d0 d1 hl0_eq
        constructor
        · have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 16) 32 d0
            (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
              have hrb := hrec_byte (16 + j) (by unfold recordLen; omega)
              rw [getElem_eq_of_idx (show pOff + 16 + j = pOff + (16 + j) by omega) _ (by omega), hrb]
              unfold recordProof
              rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_right (by simp [bitsToBytes_length])]
              simp only [bitsToBytes_length, show 16 + j - 16 = j by omega, hl0_eq]
              rw [List.getElem_append_left (by simp [bitsToBytes_length]; omega)]
              exact bitsToBytes_getElem d0 32 j hj _)
          simpa [pw, parsePartialWitness, show i.val / 3 ≠ FULL_TRIPLETS from hfull, Nat.add_assoc] using h
        · have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 48) 32 d1
            (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
              have hrb := hrec_byte (48 + j) (by unfold recordLen; omega)
              rw [getElem_eq_of_idx (show pOff + 48 + j = pOff + (48 + j) by omega) _ (by omega), hrb]
              unfold recordProof
              rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length, hl0_64]; omega),
                List.getElem_append_right (by simp [bitsToBytes_length]; omega)]
              simp only [bitsToBytes_length, show 48 + j - 16 = 32 + j by omega, hl0_eq]
              rw [List.getElem_append_right (by simp [bitsToBytes_length])]
              simp only [bitsToBytes_length, show 32 + j - 32 = j by omega]
              exact bitsToBytes_getElem d1 32 j hj _)
          simpa [pw, parsePartialWitness, show i.val / 3 ≠ FULL_TRIPLETS from hfull, Nat.add_assoc] using h
      have hrem_cases : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hrem_cases with hr0 | hr1 | hr2
      · have hi0 : 3 * g = i.val := by omega
        have hl0_eq : l0SiblingsProof nodes i = bitsToBytes (nodes 0 (3 * g + 1)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32 := by
          unfold l0SiblingsProof; simp [show i.val / 3 ≠ FULL_TRIPLETS from hfull, hr0, g]
        obtain ⟨hs0, hs1⟩ := hread_sib _ _ hl0_eq
        simp only [WitnessPath.l0Input, show pw.index.val % 3 = 0 from hr0, ite_true, hleaf_eq, hs0, hs1, hi0]
        rfl
      · have hi1 : 3 * g + 1 = i.val := by omega
        have hl0_eq : l0SiblingsProof nodes i = bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32 := by
          unfold l0SiblingsProof; simp [show i.val / 3 ≠ FULL_TRIPLETS from hfull, hr1, g]
        obtain ⟨hs0, hs1⟩ := hread_sib _ _ hl0_eq
        simp only [WitnessPath.l0Input, show pw.index.val % 3 = 1 from hr1,
          show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, hleaf_eq, hs0, hs1, hi1]
        rfl
      · have hi2 : 3 * g + 2 = i.val := by omega
        have hl0_eq : l0SiblingsProof nodes i = bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 1)) 32 := by
          unfold l0SiblingsProof; simp [show i.val / 3 ≠ FULL_TRIPLETS from hfull, hr2, g]
        obtain ⟨hs0, hs1⟩ := hread_sib _ _ hl0_eq
        simp only [WitnessPath.l0Input, show pw.index.val % 3 = 2 from hr2,
          show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false, hleaf_eq, hs0, hs1, hi2]
        rfl
  -- L1 sibling matches nodes 1 (g ^^^ 1)
  have hsib1_eq : pw.binSib 1 = nodes 1 (g ^^^ 1) := by
    have h := readBuffer_proof_of_bitsToBytes input hvalid (pOff + 16 + l0Bytes i) 32 (nodes 1 (g ^^^ 1))
      (by unfold recordLen at hpOff_rec; omega) (fun j hj => by
        have hrb := hrec_byte (16 + l0Bytes i + j) (by unfold recordLen; omega)
        rw [getElem_eq_of_idx (show pOff + 16 + l0Bytes i + j = pOff + (16 + l0Bytes i + j) by omega) _ (by omega), hrb]
        unfold recordProof
        rw [List.getElem_append_left (by simp [bitsToBytes_length, l0SiblingsProof_length]; omega),
          List.getElem_append_right (by simp [bitsToBytes_length, l0SiblingsProof_length])]
        simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length,
          show 16 + l0Bytes i + j - (16 + l0Bytes i) = j by omega]
        exact bitsToBytes_getElem (nodes 1 (g ^^^ 1)) 32 j hj _)
    simpa [pw, parsePartialWitness, Nat.add_assoc] using h
  -- L2..L14 siblings match nodes (2 + step) ((g >>> (step + 1)) ^^^ 1)
  have hsib_bin_eq : ∀ step < 13,
      let l := 2 + step
      let sib := (g >>> (step + 1)) ^^^ 1
      sib < levelSize l → pw.binSib l = nodes l sib := by
    intro step hstep l sib hsib_lt
    have hsib_lt' : ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step) := hsib_lt
    have hstep_b : binStepBytes g step = 30 := by unfold binStepBytes; exact if_pos hsib_lt'
    have hbin_le : binPathOff g step + 30 ≤ binPathOff g 13 := by
      have h1 : binPathOff g (step + 1) ≤ binPathOff g 13 := by
        have hm : ∀ a b, a ≤ b → binPathOff g a ≤ binPathOff g b := by
          intro a b hab; induction hab with
          | refl => exact le_refl _
          | step _ ih => simp only [binPathOff]; omega
        exact hm (step + 1) 13 (by omega)
      simp only [binPathOff] at h1; rw [hstep_b] at h1; exact h1
    have hpd := proofDigest30_of_proof_bytes input hvalid
      (pOff + 16 + l0Bytes i + 32 + binPathOff g step) (nodes l sib)
      (by rw [hrec_eq] at hpOff_rec; omega) (fun j hj => by
        have hrb := hrec_byte (16 + l0Bytes i + 32 + binPathOff g step + j) (by rw [hrec_eq]; omega)
        rw [getElem_eq_of_idx (show pOff + 16 + l0Bytes i + 32 + binPathOff g step + j =
            pOff + (16 + l0Bytes i + 32 + binPathOff g step + j) by omega) _ (by rw [hrec_eq] at hpOff_rec; omega), hrb]
        unfold recordProof
        rw [List.getElem_append_right (by simp [List.length_append, bitsToBytes_length, l0SiblingsProof_length]; omega)]
        simp only [List.length_append, bitsToBytes_length, l0SiblingsProof_length,
          show 16 + l0Bytes i + 32 + binPathOff g step + j - (16 + l0Bytes i + 32) = binPathOff g step + j by omega]
        unfold binPathProof
        have hst_len : step < (List.range 13).length := by simp; omega
        have hget_st : (List.range 13)[step]'hst_len = step := by simp
        have hpref := binPathProof_prefix_len nodes g step (by omega)
        have hfm_bd : (((List.range 13).take step).map fun st =>
            (if ((g >>> (st + 1)) ^^^ 1) < levelSize (2 + st)
             then bitsToBytes (nodes (2 + st) ((g >>> (st + 1)) ^^^ 1)) 30 else []).length).sum + j <
            ((List.range 13).flatMap fun st =>
             if ((g >>> (st + 1)) ^^^ 1) < levelSize (2 + st)
             then bitsToBytes (nodes (2 + st) ((g >>> (st + 1)) ^^^ 1)) 30 else []).length := by
          rw [hpref]; change binPathOff g step + j < (binPathProof nodes g).length
          rw [binPathProof_length]; omega
        have hfm := flatMap_getElem_at (fun st =>
            if ((g >>> (st + 1)) ^^^ 1) < levelSize (2 + st)
            then bitsToBytes (nodes (2 + st) ((g >>> (st + 1)) ^^^ 1)) 30 else [])
          (List.range 13) step j hst_len
          (by rw [hget_st, if_pos hsib_lt', bitsToBytes_length]; exact hj) hfm_bd
        have hidx_st : binPathOff g step + j =
            (((List.range 13).take step).map fun st =>
              (if ((g >>> (st + 1)) ^^^ 1) < levelSize (2 + st)
               then bitsToBytes (nodes (2 + st) ((g >>> (st + 1)) ^^^ 1)) 30 else []).length).sum + j := by
          rw [hpref]
        rw [getElem_eq_of_idx hidx_st _ hfm_bd, hfm]
        simp only [hget_st, hsib_lt', ite_true]
        exact bitsToBytes_getElem (nodes l sib) 30 j hj _)
    have hmask : mask240 (nodes l sib) = nodes l sib :=
      nodeValFromLeaves_masked c96 _ l sib (by omega) (by omega) hsib_lt
    have hpw_b : pw.binSib l = proofDigest30 s0 (10066334784 + pOff + 16 + l0Bytes i + 32 + binPathOff g step) := by
      dsimp only [pw, parsePartialWitness, pOff, g]
      rw [if_neg (by omega), if_pos (by omega), show l - 2 = step by omega]
    rw [hpw_b, show 10066334784 + pOff + 16 + l0Bytes i + 32 + binPathOff g step =
        10066334784 + (pOff + 16 + l0Bytes i + 32 + binPathOff g step) by omega, hpd, hmask]
  -- Induction on m = 0..14: pw.evalLevel c96 (1 + m) = nodes (1 + m) (g >>> m)
  have hclimb : ∀ m ≤ 14, g >>> m < levelSize (1 + m) ∧ pw.evalLevel c96 (1 + m) = nodes (1 + m) (g >>> m) := by
    intro m hm
    induction m with
    | zero =>
      exact ⟨by rw [levelSize_1]; rw [full_triplets_eq] at hg_le; simp; omega,
        by simpa using hl1_eq⟩
    | succ k ih =>
      obtain ⟨hidx_lt, hev_k⟩ := ih (by omega)
      let prev := 1 + k
      let idx := g >>> k
      let q := idx / 2
      have hidx_lt' : idx < levelSize prev := hidx_lt
      have hev_k' : pw.evalLevel c96 prev = nodes prev idx := hev_k
      have hidx_next : g >>> (k + 1) = q := shiftRight_succ_eq_div2 g k
      have hq_lt : q < levelSize (prev + 1) := by
        rw [levelSize_step prev (by omega)]; dsimp only [q]; omega
      have hpw_unfold : pw.evalLevel c96 (prev + 1) =
          if (idx ^^^ 1) < levelSize prev then
            let inp := if idx % 2 = 0 then binaryInput (pw.evalLevel c96 prev) (pw.binSib prev)
                       else binaryInput (pw.binSib prev) (pw.evalLevel c96 prev)
            mask240 (c96 inp)
          else pw.evalLevel c96 prev := by
        rw [evalLevel_succ_of_ge1 c96 pw prev (by omega)]
        simp only [show prev + 1 ≠ 24 by omega, ite_false, show prev - 1 = k by omega,
          show pw.index.val / 3 = g from rfl, idx]
      have hnd_unfold : nodes (prev + 1) q =
          if 2 * q + 1 < levelSize prev then
            mask240 (c96 (binaryInput (nodes prev (2 * q)) (nodes prev (2 * q + 1))))
          else if 2 * q < levelSize prev then nodes prev (2 * q) else 0 := by
        dsimp only [nodes]
        rw [nodeVal_succ_of_ge1 c96 msg salts prev q (by omega)]
        simp only [show prev + 1 ≠ 24 by omega, ite_false]
      refine ⟨by simpa only [hidx_next, show 1 + (k + 1) = prev + 1 by omega] using hq_lt, ?_⟩
      simp only [hidx_next, show 1 + (k + 1) = prev + 1 by omega, hpw_unfold, hnd_unfold]
      by_cases hpair : (idx ^^^ 1) < levelSize prev
      · have h2q1_lt : 2 * q + 1 < levelSize prev := by
          rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
          · rw [hm, xor_one_even] at hpair; dsimp only [q]; omega
          · dsimp only [q]; omega
        rw [if_pos hpair, if_pos h2q1_lt]
        have hsib_eq : pw.binSib prev = nodes prev (idx ^^^ 1) := by
          cases k with
          | zero => simpa [prev, idx] using hsib1_eq
          | succ k' =>
            have hprev_eq : prev = 2 + k' := by dsimp only [prev]; omega
            have hidx_eq : idx = g >>> (k' + 1) := rfl
            have hpair' : (g >>> (k' + 1)) ^^^ 1 < levelSize (2 + k') := by
              rw [← hprev_eq, ← hidx_eq]; exact hpair
            simpa only [hprev_eq, hidx_eq] using hsib_bin_eq k' (by omega) hpair'
        rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
        · have hev : idx % 2 = 0 := by omega
          have h2q : 2 * q = idx := by dsimp only [q]; omega
          have h2q1 : 2 * q + 1 = idx ^^^ 1 := by rw [hm, xor_one_even]; dsimp only [q]; omega
          rw [if_pos hev, hev_k', hsib_eq, h2q1, h2q]
        · have hodd : idx % 2 ≠ 0 := by omega
          have h2q1 : 2 * q + 1 = idx := by dsimp only [q]; omega
          have h2q : 2 * q = idx ^^^ 1 := by rw [hm, xor_one_odd]; dsimp only [q]; omega
          rw [if_neg hodd, hev_k', hsib_eq, h2q1, h2q]
      · have hnot2q1 : ¬ (2 * q + 1 < levelSize prev) := by
          rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
          · rw [hm, xor_one_even] at hpair; dsimp only [q]; omega
          · rw [hm, xor_one_odd] at hpair; dsimp only [q]; omega
        have h2q_eq : 2 * q = idx := by
          rcases Nat.even_or_odd' idx with ⟨m, hm | hm⟩
          · dsimp only [q]; omega
          · rw [hm, xor_one_odd] at hpair; omega
        rw [if_neg hpair, if_neg hnot2q1, if_pos (by omega), h2q_eq, hev_k']
  exact (hclimb 14 (le_refl 14)).2

private theorem rootVal_eq_nodeVal24 (c : Comp96) (msg : Message) (salts : Index → Salt128) :
    rootVal c msg salts = nodeVal c msg salts 24 0 := rfl

private theorem check_honest_cap_eq (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128) (positions : Positions)
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
    ∀ d ≤ 9, ∀ idx < levelSize (15 + d),
      capMark positions (15 + d) idx = true →
      readBuffer sCap (8192 + capValOff (15 + d) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (15 + d) idx := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let nodes := nodeVal c96 msg salts
  let pf := referenceProof nodes salts positions
  let input : CheckInput := ⟨rt, positions, msg.restrict positions, pf⟩
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  have hplen := referenceProof_length_nonempty nodes salts positions hempty
  intro d hd
  induction d with
  | zero =>
    intro idx hidx hcm
    rw [levelSize_15] at hidx
    rw [capMark_15, decide_eq_true_eq] at hcm
    obtain ⟨i, hi, hci⟩ := hcm
    have hmem_sort : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
    obtain ⟨ord, hord_len, hget⟩ := List.mem_iff_getElem.mp hmem_sort
    have hord : ord < positions.card := by simpa using hord_len
    have hpos_eq : posAt positions ord = i := by simp only [posAt, dif_pos hord, hget]
    have hw1 := (hinvPos.witnesses ord hord).1
    have hev := honest_parsePartialWitness_eval15 h768 oracle msg salts positions hempty rt ord hord
    have h15 := hinvCap.val15_marked idx hidx (by rw [capMark_15, decide_eq_true_eq]; exact ⟨i, hi, hci⟩)
    rw [h15, ← hci, ← hpos_eq, ← hw1, hev]
  | succ d ih =>
    intro idx hidx hcm
    let l := 15 + d
    have hl1 : 15 ≤ l := by omega
    have hl2 : l < 24 := by omega
    have hls_next : levelSize (l + 1) = levelSize l / 2 + levelSize l % 2 := by
      rw [levelSize_step l (by omega)]; omega
    rw [show 15 + (d + 1) = l + 1 by omega] at hidx hcm ⊢
    change readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (l + 1) idx
    rw [nodeVal_succ_of_ge1 c96 msg salts l idx (by omega)]
    change readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 =
      if 2 * idx + 1 < levelSize l then
        if l + 1 = 24 then c96 (binaryInput (nodes l (2 * idx)) (nodes l (2 * idx + 1)))
        else mask240 (c96 (binaryInput (nodes l (2 * idx)) (nodes l (2 * idx + 1))))
      else if 2 * idx < levelSize l then nodes l (2 * idx) else 0
    by_cases hq_pair : idx < levelSize l / 2
    · have h2q1 : 2 * idx + 1 < levelSize l := by omega
      rw [if_pos h2q1]
      obtain ⟨hcap_val, _, hfrL, hfrR⟩ := (hinvCap.levels_done d (by omega)).1 idx hq_pair hcm
      have hdL_eq : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32 = nodes l (2 * idx) := by
        cases hmL : capMark positions l (2 * idx) with
        | true => exact ih (by omega) (2 * idx) (by change 2 * idx < levelSize l; omega) hmL
        | false =>
          have hmR : capMark positions l (2 * idx + 1) = true := by
            rw [capMark_succ positions l idx hl1, if_pos h2q1, hmL] at hcm; simpa using hcm
          have hdiff : capMark positions l (2 * idx) ≠ capMark positions l (2 * idx + 1) := by
            rw [hmL, hmR]; decide
          have hfrL' : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32 =
              proofDigest30 (submission.initialState .check input)
                (10066334784 + (posRecordOff positions positions.card +
                  30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))) :=
            hfrL hmL
          rw [hfrL']
          have hpd_bd : posRecordOff positions positions.card +
              30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + 30 ≤ input.proof.length := by
            change _ + 30 ≤ (referenceProof nodes salts positions).length
            rw [hplen]
            have h1 := pairFrontierCount_mono positions l (show idx + 1 ≤ levelSize l / 2 by omega)
            rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff)] at h1
            have h2 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
            rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h2
            change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h2
            omega
          have hmL' : capMark positions (15 + d) (2 * idx) = false := hmL
          have hpd := proofDigest30_of_proof_bytes input hvalid
            (posRecordOff positions positions.card +
              30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))
            (nodes l (2 * idx)) hpd_bd
            (fun j hj => by
              have h := referenceProof_cap_getElem nodes salts positions hempty d idx j
                (by omega) hq_pair hj hdiff (by
                  change posRecordOff positions positions.card +
                    30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + j < input.proof.length
                  omega)
              simpa only [l, hmL', Bool.not_false, ite_true] using h)
          rw [hpd]
          exact nodeValFromLeaves_masked c96 _ l (2 * idx) (by omega) (by omega) (by omega)
      have hdR_eq : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32 = nodes l (2 * idx + 1) := by
        cases hmR : capMark positions l (2 * idx + 1) with
        | true => exact ih (by omega) (2 * idx + 1) (by change 2 * idx + 1 < levelSize l; omega) hmR
        | false =>
          have hmL : capMark positions l (2 * idx) = true := by
            rw [capMark_succ positions l idx hl1, if_pos h2q1, hmR] at hcm; simpa using hcm
          have hdiff : capMark positions l (2 * idx) ≠ capMark positions l (2 * idx + 1) := by
            rw [hmL, hmR]; decide
          have hfrR' : readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32 =
              proofDigest30 (submission.initialState .check input)
                (10066334784 + (posRecordOff positions positions.card +
                  30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))) :=
            hfrR hmR
          rw [hfrR']
          have hpd_bd : posRecordOff positions positions.card +
              30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + 30 ≤ input.proof.length := by
            change _ + 30 ≤ (referenceProof nodes salts positions).length
            rw [hplen]
            have h1 := pairFrontierCount_mono positions l (show idx + 1 ≤ levelSize l / 2 by omega)
            rw [pairFrontierCount_full, pairFrontierCount_succ, if_pos (bne_iff_ne.mpr hdiff)] at h1
            have h2 := capFrontierPrefix_mono positions (show d + 1 ≤ 9 by omega)
            rw [capFrontierPrefix_succ, capFrontierPrefix_9] at h2
            change capFrontierPrefix positions d + levelFrontierCount positions l ≤ capFrontierCount positions at h2
            omega
          have hmL' : capMark positions (15 + d) (2 * idx) = true := hmL
          have hpd := proofDigest30_of_proof_bytes input hvalid
            (posRecordOff positions positions.card +
              30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx))
            (nodes l (2 * idx + 1)) hpd_bd
            (fun j hj => by
              have h := referenceProof_cap_getElem nodes salts positions hempty d idx j
                (by omega) hq_pair hj hdiff (by
                  change posRecordOff positions positions.card +
                    30 * (capFrontierPrefix positions d + pairFrontierCount positions l idx) + j < input.proof.length
                  omega)
              simpa only [l, hmL', Bool.not_true, Bool.false_eq_true, ite_false] using h)
          rw [hpd]
          exact nodeValFromLeaves_masked c96 _ l (2 * idx + 1) (by omega) (by omega) (by omega)
      have hcap_val' : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset idx) 32 =
          if l = 23 then
            c96 (binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32)
              (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32))
          else
            mask240 (c96 (binaryInput (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx)) 32)
              (readBuffer sCap (8192 + capValOff l + gapOffset (2 * idx + 1)) 32))) := hcap_val
      rw [hcap_val', hdL_eq, hdR_eq]
      simp only [show (l = 23) ↔ (l + 1 = 24) by omega]
    · -- Odd promoted tail
      have hodd : levelSize l % 2 = 1 := by omega
      have hidx_eq : idx = levelSize l / 2 := by omega
      have hnot2q1 : ¬ (2 * idx + 1 < levelSize l) := by omega
      have h2q : 2 * idx < levelSize l := by omega
      have hcm_l : capMark positions l (2 * (levelSize l / 2)) = true := by
        rw [capMark_succ positions l idx hl1, if_neg hnot2q1, if_pos h2q, hidx_eq] at hcm
        exact hcm
      have hprom : readBuffer sCap (8192 + capValOff (l + 1) + gapOffset (levelSize l / 2)) 32 =
          readBuffer sCap (8192 + capValOff l + gapOffset (2 * (levelSize l / 2))) 32 :=
        (hinvCap.levels_done d (by omega)).2 hodd hcm_l
      rw [if_neg hnot2q1, if_pos h2q, hidx_eq, hprom]
      exact ih (by omega) (2 * (levelSize l / 2)) (by change 2 * (levelSize l / 2) < levelSize l; omega) hcm_l

private theorem check_honest_consistent (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128) (positions : Positions)
    (hempty : positions.card ≠ 0) (rt : Commitment) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 msg salts
    let input : CheckInput := ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
    PosConsistent c96 (submission.initialState .check input) input positions.card := by
  intro c96 nodes input
  have hplen := referenceProof_length_nonempty nodes salts positions hempty
  refine ⟨by change posRecordOff positions positions.card ≤ (referenceProof nodes salts positions).length
             rw [hplen]; omega, ?_⟩
  intro j1 j2 hj1 hj2 hc_eq
  have h1 := honest_parsePartialWitness_eval15 h768 oracle msg salts positions hempty rt j1 hj1
  have h2 := honest_parsePartialWitness_eval15 h768 oracle msg salts positions hempty rt j2 hj2
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
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128) (positions : Positions)
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
      sPos 9 sCap trCap) :
    readBuffer sCap (8192 + capValOff 24) 32 = rt := by
  have hcap_eq := check_honest_cap_eq h768 oracle msg salts positions hempty rt sPos sCap trPos trCap hinvPos hinvCap
  have hcm24 := capMark_24_eq_true positions (Finset.card_pos.mp (Nat.pos_of_ne_zero hempty))
  have h24 := hcap_eq 9 (le_refl 9) 0 (by change 0 < levelSize 24; rw [levelSize_24]; decide) hcm24
  have h159 : (15 + 9 : Nat) = 24 := rfl
  have hgo0 : gapOffset 0 = 0 := by decide
  rw [h159, hgo0, Nat.add_zero] at h24
  exact h24.trans hrt.symm

private theorem check_honest_accepts_core (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128) (positions : Positions)
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
    have hplen : pf.length = posRecordOff positions positions.card + 30 * capFrontierCount positions := by
      rw [hpf]
      exact referenceProof_length_nonempty nodes salts positions hempty
    have hcons : PosConsistent c96 (submission.initialState .check input) input positions.card := by
      have h := check_honest_consistent h768 oracle msg salts positions hempty rt
      dsimp only at h
      simpa only [input, hpf, c96, nodes] using h
    rcases check_pipeline_nonempty h768 oracle input hvalid hempty with
      ⟨hnot, _⟩ | ⟨hshort, _⟩ | ⟨sPos, sCap, qPos, qCap, trPos, trCap, kFin, hk, hq, hinvPos, hinvCap, hh⟩
    · exact (hnot hcons).elim
    · change pf.length < posRecordOff positions positions.card + 30 * capFrontierCount positions at hshort
      rw [hplen] at hshort; omega
    · have hinvPos' : PosLoopInv h768 oracle
          ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
          positions.card sPos trPos := by
        simpa only [input, hpf] using hinvPos
      have hinvCap' : CapWalkInv h768 oracle
          ⟨rt, positions, msg.restrict positions, referenceProof nodes salts positions⟩
          sPos 9 sCap trCap := by
        simpa only [input, hpf] using hinvCap
      have hroot_eq : readBuffer sCap (8192 + capValOff 24) 32 = rt :=
        check_honest_nonempty_root h768 oracle msg salts positions hempty rt hrt sPos sCap trPos trCap hinvPos' hinvCap'
      have hev := hh.eval_of_le hk
      have hlen_eq : posRecordOff input.positions input.positions.card + 30 * capFrontierCount input.positions =
          input.proof.length := hplen.symm
      have hcmt_eq : readBuffer sCap (8192 + capValOff 24) 32 = (input.commitment : BitVec (8 * 32)) := hroot_eq
      have hcond : (posRecordOff input.positions input.positions.card + 30 * capFrontierCount input.positions ==
          input.proof.length &&
          readBuffer sCap (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))) = true :=
        (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hlen_eq, beq_iff_eq.mpr hcmt_eq⟩
      have hcard_eq : input.positions.card = positions.card := rfl
      rw [hcard_eq] at hq
      refine ⟨?_, ?_⟩
      · rw [hev.1, if_pos hcond]; rfl
      · rw [hev.2.1]; unfold CHECK_BUDGET; omega

theorem check_honest_accepts (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128) (positions : Positions) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let rt := rootVal c96 msg salts
    let pf := referenceProof (nodeVal c96 msg salts) salts positions
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).1 = true ∧
    (oracle.eval (submission.scheme.check rt positions (msg.restrict positions) pf)).2 ≤ CHECK_BUDGET positions.card := by
  intro c96 rt pf
  exact check_honest_accepts_core h768 oracle msg salts positions rt pf (rootVal_eq_nodeVal24 c96 msg salts) rfl

end CommitGolfCandidate
