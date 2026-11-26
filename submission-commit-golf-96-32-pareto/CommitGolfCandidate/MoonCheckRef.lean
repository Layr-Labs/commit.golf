import CommitGolfCandidate.MoonCheckCap

/-! End-to-end verification of the 269-word pure 3-ary `check` image:
- `check_run_termination`: universal termination on all inputs within fuel and `≤ 20 * k` oracle calls.
- `check_sound`: `CheckSound h768` witness-path and compression-trace extraction for 256-bit binding.
- `check_honest_accepts`: perfect completeness and `CHECK_BUDGET` bound on `referenceProof`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Initial Invariant and Master Non-Empty Pipeline -/

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
    (s1 : MachineState) (hpc1 : s1.pc = kPcAt 29)
    (hmem1 : s1.mem = (submission.initialState .check input).mem)
    (hfix1 : CheckFixedRegs input s1)
    (hx9 : s1.getReg .x9 = BitVec.ofNat 64 6643781664)
    (hx19 : s1.getReg .x19 = BitVec.ofNat 64 6777999392)
    (hx20 : s1.getReg .x20 = BitVec.ofNat 64 11072966688) :
    PosLoopInv h768 oracle input 0 s1 [] := by
  have hbyte0 : ∀ a < 4294971392, s1.getByte (BitVec.ofNat 64 a) = 0#8 := fun a ha => by
    simp only [MachineState.getByte, MachineState.getMem, hmem1]
    exact check_initial_zero_low input a ha
  refine ⟨hfix1, MemEqOutside.of_mem_eq hmem1 0 4294971392,
    by simp [Ne.symm hne, hpc1],
    by simpa using hx9, by simpa using hx19, by simpa [posRecordOff] using hx20,
    Nat.zero_le _, ?_, ?_, ?_, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  · intro c hc
    rw [posMarked_zero]
    exact hbyte0 (4096 + c) (by omega)
  · intro u hu1 hu2
    exact hbyte0 (4096 + u) (by omega)
  · intro a ha1 ha2
    exact hbyte0 a (by omega)

private theorem check_pipeline_nonempty (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let baseOff := posRecordOff input.positions input.positions.card
    let capEnd := baseOff + 32 * capFrontierCount input.positions
    (¬ PosConsistent c96 s0 input input.positions.card ∧
      ∃ k q tr, k ≤ submission.steps .check ∧ q ≤ 20 * input.positions.card ∧
        HaltsWith oracle s0 k q .failure tr) ∨
    (input.proof.length < capEnd ∧
      ∃ k q tr, k ≤ submission.steps .check ∧ q ≤ 20 * input.positions.card ∧
        HaltsWith oracle s0 k q .failure tr) ∨
    (∃ sPos sCap qPos qCap trPos trCap kFin,
      kFin ≤ submission.steps .check ∧
      qPos + qCap ≤ 20 * input.positions.card ∧
      PosLoopInv h768 oracle input input.positions.card sPos trPos ∧
      CapDoneInv h768 oracle input baseOff sPos sCap trCap ∧
      HaltsWith oracle s0 kFin (qPos + qCap)
        (if capEnd == input.proof.length &&
            readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))
         then Exit.success else Exit.failure)
        (trPos ++ trCap)) := by
  intro s0 c96 baseOff capEnd
  have hcard_bd := k_card_le input.positions
  have hne_fin : input.positions.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  have hcap_calls_le := capMarkedInternalCount_le_6_mul_card input.positions
  have hsteps_bd : 25 + 520 * input.positions.card + 8000 + 20 ≤ submission.steps .check := by
    rw [check_steps_eq]; omega
  obtain ⟨s1, hs1, hpc1, hmem1, hfix1, hx9, hx19, hx20⟩ := check_prologue_nonempty oracle input hne
  have hinit := posLoopInv_init h768 oracle input hne s1 hpc1 hmem1 hfix1 hx9 hx19 hx20
  have hpos := check_pos_loop h768 oracle input hvalid hne s1 hinit
  cases hpos with
  | rejected kPos qPos trPos hnot hkPos hqPos hhPos =>
    left
    refine ⟨hnot, 25 + kPos, qPos, trPos, by omega, by omega, ?_⟩
    simpa using hs1.halt hhPos
  | continued sPos kPos qPos trPos hkPos hqPos hsPos hinvPos =>
    have hcap := check_cap_walk h768 oracle input hvalid hne_fin sPos trPos hinvPos
    cases hcap with
    | rejected kCap qCap trCap hshort hkCap hqCap hhCap =>
      right; left
      refine ⟨hshort, 25 + kPos + kCap, qPos + qCap, trPos ++ trCap, by omega, by omega, ?_⟩
      simpa [Nat.add_assoc] using (hs1.trans hsPos).halt hhCap
    | continued sCap kCap qCap trCap hkCap hqCap hsCap hdone =>
      obtain ⟨kEpi, hkEpi, hepi⟩ := check_epilogue h768 oracle input hvalid hdone
      right; right
      refine ⟨sPos, sCap, qPos, qCap, trPos, trCap, 25 + kPos + kCap + kEpi,
        by omega, by omega, hinvPos, hdone, ?_⟩
      simpa [Nat.add_assoc] using ((hs1.trans hsPos).trans hsCap).halt hepi

/-! ### 2. Universal Termination (`check_run_termination`) -/

theorem check_run_termination (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (input : CheckInput) :
    ∃ exec : Execution,
      oracle.run (submission.run .check input) = pure (exec, exec.oracleCalls) ∧
      exec.exit ≠ .unfinished ∧
      exec.oracleCalls ≤ 20 * input.positions.card := by
  by_cases hvalid : input.proof.length ≤ submission.sizes.proof
  · rw [submission_run_check_valid submission input hvalid, oracle_run_execute_false]
    let r := detExec oracle (submission.image .check) (submission.steps .check)
      (submission.initialState .check input)
    refine ⟨r.1, rfl, ?_⟩
    by_cases hempty : input.positions.card = 0
    · have hh := check_prologue_empty oracle input hvalid hempty
      have hev := hh.eval_of_le (show 5 ≤ submission.steps .check by rw [check_steps_eq]; omega)
      exact ⟨by rw [hev.1]; split <;> decide, by rw [hev.2.1]; omega⟩
    · rcases check_pipeline_nonempty h768 oracle input hvalid hempty with
        ⟨_, k, q, tr, hk, hq, hh⟩ | ⟨_, k, q, tr, hk, hq, hh⟩ |
        ⟨_, _, qPos, qCap, _, _, kFin, hk, hq, _, _, hh⟩
      · have hev := hh.eval_of_le hk
        exact ⟨by rw [hev.1]; decide, by rw [hev.2.1]; exact hq⟩
      · have hev := hh.eval_of_le hk
        exact ⟨by rw [hev.1]; decide, by rw [hev.2.1]; exact hq⟩
      · have hev := hh.eval_of_le hk
        exact ⟨by rw [hev.1]; split <;> decide, by rw [hev.2.1]; exact hq⟩
  · rw [submission_run_check_invalid submission input hvalid, oracle_run_pure]
    exact ⟨⟨.failure, initialMachine, 0, 0⟩, rfl, by decide, Nat.zero_le _⟩

/-! ### 3. Soundness (`check_sound : CheckSound h768`) -/

private theorem valAt_eq_of_posAt (input : CheckInput) (ord : Nat)
    (hord : ord < input.positions.card) (i : Index) (hi : i ∈ input.positions)
    (hpos : posAt input.positions ord = i) :
    valAt input ord = input.values ⟨i, hi⟩ := by
  unfold valAt
  simp only [hord, ↓reduceDIte]
  congr 1
  apply Subtype.ext
  apply Fin.ext
  rw [sorted_value_index input.positions ord hord, ← posAt_val input.positions ord, hpos]

private theorem witness_climb_low (c : Comp96) (s0 : MachineState) (w : WitnessPath) :
    ∀ steps v off cur,
      v < CAP_LEAF_LO → climbStepsFrom v = steps →
      (∀ u, v ≤ u → u < CAP_LEAF_LO → w.sibOf u = climbSibOf s0 v off u) →
      w.evalFrom c v cur = w.evalFrom c (climbEndFrom v) (evalClimb c s0 v off cur) ∧
      w.inputsFrom c v cur =
        climbInputs c s0 v off cur ++ w.inputsFrom c (climbEndFrom v) (evalClimb c s0 v off cur) := by
  intro steps
  induction steps with
  | zero =>
    intro v _ _ hv hcs; rw [climbStepsFrom_of_lt hv] at hcs; omega
  | succ k ih =>
    intro v off cur hv hcs hsib
    have hcl := capLeafLo_eq
    have hrn := rootNode_eq
    have hlen : LENGTH = 16777216 := by decide
    have hv_lt_root : v < ROOT_NODE := by omega
    have hpar_gt : v < parentNode v := by unfold parentNode; omega
    have hsib_v : w.sibOf v =
        (readBuffer s0 (11072966688 + off) 32, readBuffer s0 (11072966688 + off + 32) 32) := by
      rw [hsib v le_rfl hv, climbSibOf_self s0 hv]
    have hcs_par : climbStepsFrom (parentNode v) = k := by
      rw [climbStepsFrom_of_lt hv] at hcs; omega
    rw [w.evalFrom_lt c hv_lt_root, w.inputsFrom_lt c hv_lt_root,
      climbEndFrom_of_lt hv, evalClimb_of_lt c s0 hv, climbInputs_of_lt c s0 hv, hsib_v]
    by_cases hpar : parentNode v < CAP_LEAF_LO
    · have hsib_par : ∀ u, parentNode v ≤ u → u < CAP_LEAF_LO →
          w.sibOf u = climbSibOf s0 (parentNode v) (off + 64) u := fun u hu1 hu2 => by
        rw [hsib u (by omega) hu2, climbSibOf_step s0 hv (by omega)]
      obtain ⟨he, hi⟩ := ih (parentNode v) (off + 64)
        (c (stepInput v cur (readBuffer s0 (11072966688 + off) 32,
                             readBuffer s0 (11072966688 + off + 32) 32)))
        hpar hcs_par hsib_par
      exact ⟨he, by dsimp only; rw [hi, List.cons_append]⟩
    · dsimp only
      rw [climbEndFrom_of_ge (by omega), evalClimb_of_ge c s0 (by omega),
        climbInputs_of_ge c s0 (by omega)]
      simp

private theorem witness_climb_cap (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) {baseOff : Nat} {sPos sCap : MachineState} {trCap : CompressionReplies}
    (hdone : CapDoneInv h768 oracle input baseOff sPos sCap trCap) (w : WitnessPath)
    (hsib_cap : ∀ u < 428,
      let valCap (k : Nat) := readBuffer sCap (8192 + 32 * k) 32
      w.sibOf (CAP_LEAF_LO + u) =
        if u < 426 then
          let t := 3 * (u / 3)
          if u % 3 = 0 then (valCap (t + 1), valCap (t + 2))
          else if u % 3 = 1 then (valCap t, valCap (t + 2))
          else (valCap t, valCap (t + 1))
        else if u = 426 then (valCap 427, 0)
        else (valCap 426, 0)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let valCap (k : Nat) := readBuffer sCap (8192 + 32 * k) 32
    ∀ d u, u ≤ 428 → 428 - u ≤ d → capMark input.positions u = true →
      w.evalFrom c96 (CAP_LEAF_LO + u) (valCap u) = valCap 428 ∧
      ∀ x ∈ w.inputsFrom c96 (CAP_LEAF_LO + u) (valCap u), InTrace h768 oracle trCap x := by
  intro c96 valCap d
  have hcl := capLeafLo_eq
  have hrn := rootNode_eq
  have hqc := queueCalls_eq
  have hlen : LENGTH = 16777216 := by decide
  induction d with
  | zero =>
    intro u hu hd _
    have hu428 : u = 428 := by omega
    subst hu428
    have hge : ROOT_NODE ≤ CAP_LEAF_LO + 428 := by omega
    rw [w.evalFrom_ge c96 hge, w.inputsFrom_ge c96 hge]
    exact ⟨rfl, fun _ h => by simp at h⟩
  | succ k ih =>
    intro u hu hd hmu
    by_cases h428 : u = 428
    · subst h428
      have hge : ROOT_NODE ≤ CAP_LEAF_LO + 428 := by omega
      rw [w.evalFrom_ge c96 hge, w.inputsFrom_ge c96 hge]
      exact ⟨rfl, fun _ h => by simp at h⟩
    · have hv_lt : CAP_LEAF_LO + u < ROOT_NODE := by omega
      rw [w.evalFrom_lt c96 hv_lt, w.inputsFrom_lt c96 hv_lt]
      by_cases h426 : u < 426
      · let j := u / 3
        have hj : j < 142 := by omega
        have hpar_eq : parentNode (CAP_LEAF_LO + u) = CAP_LEAF_LO + (286 + j) := by
          unfold parentNode; dsimp only [j]; omega
        have hmark_par : capMark input.positions (286 + j) = true := by
          have := capMark_parent_true input.positions (by omega) hmu
          simpa only [capParent, j] using this
        have hstep_eq : stepInput (CAP_LEAF_LO + u) (valCap u) (w.sibOf (CAP_LEAF_LO + u)) =
            ternaryInput (valCap (3 * j)) (valCap (3 * j + 1)) (valCap (3 * j + 2)) := by
          rw [hsib_cap u (by omega)]
          simp only [h426, ite_true]
          unfold stepInput
          have hnot_last : ¬ ((CAP_LEAF_LO + u) / 3 = QUEUE_CALLS - 1) := by omega
          have hmod_eq : (CAP_LEAF_LO + u) % 3 = u % 3 := by omega
          simp only [hnot_last, ite_false, hmod_eq]
          have hmod : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
          rcases hmod with hr | hr | hr
          · have hu0 : u = 3 * j := by dsimp only [j]; omega
            simp only [hr, ite_true]
            have hvu : valCap u = valCap (3 * j) := congrArg valCap hu0
            rw [hvu]
          · have hu1 : u = 3 * j + 1 := by dsimp only [j]; omega
            simp only [hr, show (1 : Nat) ≠ 0 by omega, ite_false, ite_true]
            have hvu : valCap u = valCap (3 * j + 1) := congrArg valCap hu1
            rw [hvu]
          · have hu2 : u = 3 * j + 2 := by dsimp only [j]; omega
            simp only [hr, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false]
            have hvu : valCap u = valCap (3 * j + 2) := congrArg valCap hu2
            rw [hvu]
        obtain ⟨hval_par, htr_par, _, _, _⟩ := hdone.val_internal j hj hmark_par
        change valCap (286 + j) =
          c96 (ternaryInput (valCap (3 * j)) (valCap (3 * j + 1)) (valCap (3 * j + 2))) at hval_par
        rw [hpar_eq, hstep_eq, ← hval_par]
        obtain ⟨he, htr⟩ := ih (286 + j) (by omega) (by omega) hmark_par
        refine ⟨he, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | htail
        · exact htr_par
        · exact htr x htail
      · have hpar_eq : parentNode (CAP_LEAF_LO + u) = CAP_LEAF_LO + 428 := by
          unfold parentNode; omega
        have hstep_eq : stepInput (CAP_LEAF_LO + u) (valCap u) (w.sibOf (CAP_LEAF_LO + u)) =
            ternaryInput (valCap 426) (valCap 427) 0#256 := by
          rw [hsib_cap u (by omega)]
          simp only [h426, ite_false]
          unfold stepInput
          have hlast : (CAP_LEAF_LO + u) / 3 = QUEUE_CALLS - 1 := by omega
          simp only [hlast, ite_true]
          have hcases : u = 426 ∨ u = 427 := by omega
          rcases hcases with rfl | rfl
          · have hm0 : (CAP_LEAF_LO + 426) % 3 = 0 := by rw [hcl]
            simp only [hm0, ite_true]; rfl
          · have hm1 : (CAP_LEAF_LO + 427) % 3 = 1 := by rw [hcl]
            simp only [show (427 : Nat) ≠ 426 by omega, hm1, show (1 : Nat) ≠ 0 by omega, ite_false]; rfl
        obtain ⟨hval_rt, htr_rt, _, _⟩ := hdone.val_root
        change valCap 428 = c96 (ternaryInput (valCap 426) (valCap 427) 0#256) at hval_rt
        rw [hpar_eq, hstep_eq, ← hval_rt]
        have hge : ROOT_NODE ≤ CAP_LEAF_LO + 428 := by omega
        rw [w.evalFrom_ge c96 hge, w.inputsFrom_ge c96 hge]
        refine ⟨rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hnil
        · exact htr_rt
        · simp at hnil

theorem check_sound (h768 : COMPRESSION_INPUT_LENGTH = 768) : CheckSound h768 := by
  intro oracle input hacc
  have hvalid : input.proof.length ≤ submission.sizes.proof := by
    by_contra hnot
    rw [scheme_check_eval_eq, submission_run_check_invalid submission input hnot, checkEval_pure] at hacc
    cases hacc
  rw [scheme_check_eval_eq, submission_run_check_valid submission input hvalid,
    checkEval_execute_false] at hacc
  let s0 := submission.initialState .check input
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  generalize hr : detExec oracle (submission.image .check) (submission.steps .check)
    (submission.initialState .check input) = r at hacc
  rcases r with ⟨e, tr⟩
  have hexit_suc : e.exit = .success := by
    simpa only [beq_iff_eq] using hacc
  refine ⟨e, tr, ?_, ?_⟩
  · rw [submission_run_check_valid submission input hvalid, fixedOracleRun_trace_execute_false]
    exact congrArg pure hr
  · intro i hi
    have hne : input.positions.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, hi⟩)
    rcases check_pipeline_nonempty h768 oracle input hvalid hne with
      ⟨_, k, q, tr', hk, _, hh⟩ | ⟨_, k, q, tr', hk, _, hh⟩ |
      ⟨sPos, sCap, qPos, qCap, trPos, trCap, kFin, hk, _, hinvPos, hdone, hh⟩
    · have hev := hh.eval_of_le hk; dsimp only at hev; rw [hr] at hev; rw [hev.1] at hexit_suc; cases hexit_suc
    · have hev := hh.eval_of_le hk; dsimp only at hev; rw [hr] at hev; rw [hev.1] at hexit_suc; cases hexit_suc
    · have hev := hh.eval_of_le hk
      dsimp only at hev
      rw [hr] at hev
      have htr_eq : tr = trPos ++ trCap := hev.2.2
      have hcond_eq : (posRecordOff input.positions input.positions.card +
          32 * capFrontierCount input.positions == input.proof.length &&
          readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))) = true := by
        by_contra hc
        have hcf : (posRecordOff input.positions input.positions.card +
            32 * capFrontierCount input.positions == input.proof.length &&
            readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))) = false :=
          Bool.eq_false_iff.mpr hc
        have he1 := hev.1; rw [hcf] at he1; rw [he1] at hexit_suc; cases hexit_suc
      have hroot_eq : readBuffer sCap (8192 + 32 * 428) 32 = input.commitment := by
        have h2 := (Bool.and_eq_true _ _).mp hcond_eq
        exact eq_of_beq h2.2
      have hmem : i ∈ input.positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨ord, hord_len, hget⟩ := List.getElem_of_mem hmem
      have hord : ord < input.positions.card := by simpa using hord_len
      have hpos_ord : posAt input.positions ord = i := by
        unfold posAt; simp only [hord, ↓reduceDIte]; exact hget
      have hval_ord : valAt input ord = input.values ⟨i, hi⟩ :=
        valAt_eq_of_posAt input ord hord i hi hpos_ord
      let off := posRecordOff input.positions ord
      let valCap (k : Nat) := readBuffer sCap (8192 + 32 * k) 32
      let w : WitnessPath := {
        index := i
        value := input.values ⟨i, hi⟩
        salt := readBuffer s0 (11072966688 + off) 24
        sibOf := fun v =>
          if v < CAP_LEAF_LO then climbSibOf s0 i.val (off + 24) v
          else
            let u := v - CAP_LEAF_LO
            if u < 426 then
              let t := 3 * (u / 3)
              if u % 3 = 0 then (valCap (t + 1), valCap (t + 2))
              else if u % 3 = 1 then (valCap t, valCap (t + 2))
              else (valCap t, valCap (t + 1))
            else if u = 426 then (valCap 427, 0)
            else (valCap 426, 0)
      }
      have hi_lt : i.val < CAP_LEAF_LO := by
        have h1 : i.val < 16777216 := i.isLt; rw [capLeafLo_eq]; omega
      obtain ⟨hd_pos, hleaf_tr, hclimb_tr⟩ := hinvPos.pos_done ord hord
      change readBuffer sPos (8192 + 32 * capLeafOf (posAt input.positions ord)) 32 =
        posCapDigest c96 s0 input ord at hd_pos
      change ∀ x ∈ leafInputsOf c96 (posAt input.positions ord)
          (readBuffer s0 (11072966688 + posRecordOff input.positions ord) 24) (valAt input ord),
        InTrace h768 oracle trPos x at hleaf_tr
      change ∀ x ∈ climbInputs c96 s0 (posAt input.positions ord).val
          (posRecordOff input.positions ord + 24)
          (leafDigest c96 (posAt input.positions ord)
            (readBuffer s0 (11072966688 + posRecordOff input.positions ord) 24) (valAt input ord)),
        InTrace h768 oracle trPos x at hclimb_tr
      rw [hpos_ord] at hd_pos
      rw [hpos_ord, hval_ord] at hleaf_tr hclimb_tr
      have hc_lt : capLeafOf i < 286 := by rw [← capLeaves_eq]; exact capLeafOf_lt i
      have hmark_c : capMark input.positions (capLeafOf i) = true := by
        rw [capMark_leaf input.positions _ hc_lt, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩
      have hcap_leaf_eq : valCap (capLeafOf i) = posCapDigest c96 s0 input ord :=
        (hdone.val_leaf_marked (capLeafOf i) hc_lt hmark_c).trans hd_pos
      have hpd_unfold : posCapDigest c96 s0 input ord =
          evalClimb c96 s0 i.val (off + 24) (leafDigest c96 i w.salt w.value) := by
        unfold posCapDigest; dsimp only; rw [hpos_ord, hval_ord]
      obtain ⟨he_low, hi_low⟩ := witness_climb_low c96 s0 w (climbStepsFrom i.val) i.val (off + 24)
        (leafDigest c96 i w.salt w.value) hi_lt rfl (fun u _ hu => by dsimp only [w]; simp only [hu, ite_true])
      obtain ⟨he_cap, hi_cap⟩ := witness_climb_cap h768 oracle input hdone w
        (fun u hu => by
          dsimp only [w]
          simp only [show ¬ (CAP_LEAF_LO + u < CAP_LEAF_LO) by omega, ite_false, Nat.add_sub_cancel_left]
          rfl)
        428 (capLeafOf i) (by omega) (by omega) hmark_c
      refine ⟨w, rfl, rfl, ?_, ?_⟩
      · unfold WitnessPath.evalRoot
        change w.evalFrom c96 i.val (leafDigest c96 i w.salt w.value) = input.commitment
        rw [he_low, climbEndFrom_eq_capLeafOf i, ← hpd_unfold, ← hcap_leaf_eq, he_cap]
        exact hroot_eq
      · intro x hx
        unfold WitnessPath.pathInputs at hx
        rw [htr_eq]
        rcases List.mem_append.mp hx with hlf | hclm
        · exact (hleaf_tr x hlf).append_left
        · change x ∈ w.inputsFrom c96 i.val (leafDigest c96 i w.salt w.value) at hclm
          rw [hi_low] at hclm
          rcases List.mem_append.mp hclm with hlow | hup
          · exact (hclimb_tr x hlow).append_left
          · rw [climbEndFrom_eq_capLeafOf i, ← hpd_unfold, ← hcap_leaf_eq] at hup
            exact (hi_cap x hup).append_right

/-! ### 4. Honest Proof Slicing, Completeness, and Query Budget (`check_honest_accepts`) -/

private structure ListSlice (l : List Byte) (off : Nat) (sub : List Byte) : Prop where
  bound  : off + sub.length ≤ l.length
  get_eq : ∀ j (hj : j < sub.length), l[off + j]'(by omega) = sub[j]'hj

private theorem listSlice_self (l : List Byte) : ListSlice l 0 l :=
  ⟨by omega, fun j _ => by simp⟩

private theorem listSlice_append_left (l1 l2 : List Byte) {off : Nat} {sub : List Byte}
    (h : ListSlice l1 off sub) : ListSlice (l1 ++ l2) off sub :=
  ⟨by have hb := h.bound; rw [List.length_append]; omega,
   fun j hj => by
     have hb := h.bound
     rw [List.getElem_append_left (by omega : off + j < l1.length)]
     exact h.get_eq j hj⟩

private theorem listSlice_append_right (l1 l2 : List Byte) {off : Nat} {sub : List Byte}
    (h : ListSlice l2 off sub) : ListSlice (l1 ++ l2) (l1.length + off) sub :=
  ⟨by have hb := h.bound; rw [List.length_append]; omega,
   fun j hj => by
     rw [List.getElem_append_right (by omega : l1.length ≤ l1.length + off + j)]
     have heq : l1.length + off + j - l1.length = off + j := by omega
     simp only [heq]; exact h.get_eq j hj⟩

private theorem listSlice_split_left {l a b : List Byte} {off : Nat}
    (h : ListSlice l off (a ++ b)) : ListSlice l off a :=
  ⟨by have hb := h.bound; rw [List.length_append] at hb; omega,
   fun j hj => by
     have hg := h.get_eq j (by rw [List.length_append]; omega)
     rwa [List.getElem_append_left hj] at hg⟩

private theorem listSlice_split_right {l a b : List Byte} {off : Nat}
    (h : ListSlice l off (a ++ b)) : ListSlice l (off + a.length) b :=
  ⟨by have hb := h.bound; rw [List.length_append] at hb; omega,
   fun j hj => by
     have hg := h.get_eq (a.length + j) (by rw [List.length_append]; omega)
     have hidx : off + (a.length + j) = off + a.length + j := by omega
     rw [List.getElem_append_right (by omega : a.length ≤ a.length + j)] at hg
     simpa only [hidx, Nat.add_sub_cancel_left] using hg⟩

private theorem readBuffer_of_listSlice_bitsToBytes (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    {off n : Nat} {v : BitVec (8 * n)}
    (h : ListSlice input.proof off (bitsToBytes v n)) :
    readBuffer (submission.initialState .check input) (11072966688 + off) n = v := by
  have hlen : (bitsToBytes v n).length = n := bitsToBytes_length v n
  have hbound : off + n ≤ input.proof.length := by have hb := h.bound; omega
  have hb := read_serialized_slice (submission.initialState .check input) v (11072966688 + off) 0 n (by
    intro j hj
    simp only [Nat.zero_add, Nat.add_assoc]
    rw [check_initial_proof_byte input hvalid (off + j) (by omega), h.get_eq j (by omega)]
    simp [bitsToBytes])
  simpa using hb

private theorem take_flatMap_recordProof_length (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    ∀ n ≤ positions.card,
      (((positions.sort (· ≤ ·)).take n).flatMap (recordProof nodes salts)).length =
        posRecordOff positions n := by
  intro n hn
  induction n with
  | zero => simp [posRecordOff]
  | succ k ih =>
    have hk_lt : k < (positions.sort (· ≤ ·)).length := by rw [Finset.length_sort]; omega
    rw [List.take_succ_eq_append_getElem hk_lt, List.flatMap_append, List.flatMap_singleton,
      List.length_append, ih (by omega), posRecordOff]
    unfold recordProof posAt
    simp only [show k < positions.card by omega, ↓reduceDIte]
    rw [List.length_append, bitsToBytes_length, climbProofFrom_length]

private theorem recordProof_slice_in_ref (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (hne : positions.card ≠ 0) (ord : Nat) (hord : ord < positions.card) :
    ListSlice (referenceProof nodes salts positions) (posRecordOff positions ord)
      (recordProof nodes salts (posAt positions ord)) := by
  have hord_len : ord < (positions.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hord
  let l := positions.sort (· ≤ ·)
  have hsplit : l = l.take ord ++ [l[ord]'hord_len] ++ l.drop (ord + 1) := by
    have h2 : l.drop ord = l[ord]'hord_len :: l.drop (ord + 1) := List.drop_eq_getElem_cons hord_len
    rw [List.append_assoc, List.singleton_append, ← h2, List.take_append_drop]
  have href : referenceProof nodes salts positions =
      (l.take ord).flatMap (recordProof nodes salts) ++
      (recordProof nodes salts (posAt positions ord) ++
       ((l.drop (ord + 1)).flatMap (recordProof nodes salts) ++
        capFrontierProof nodes positions)) := by
    unfold referenceProof
    simp only [hne, ite_false]
    conv_lhs => rw [show positions.sort (· ≤ ·) = l from rfl, hsplit]
    simp only [List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    have hpa : posAt positions ord = l[ord]'hord_len := by unfold posAt; simp only [hord, ↓reduceDIte]; rfl
    rw [hpa]
  rw [href]
  have hlen : ((l.take ord).flatMap (recordProof nodes salts)).length = posRecordOff positions ord :=
    take_flatMap_recordProof_length nodes salts positions ord (by omega)
  have hinner := listSlice_append_left (recordProof nodes salts (posAt positions ord))
    ((l.drop (ord + 1)).flatMap (recordProof nodes salts) ++ capFrontierProof nodes positions)
    (listSlice_self _)
  simpa only [hlen, Nat.add_zero] using
    listSlice_append_right ((l.take ord).flatMap (recordProof nodes salts)) _ hinner

private theorem honest_evalClimb (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (message : Message) (salts : Index → Salt192) (positions : Positions) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let nodes := nodeVal c96 message salts
    let input : CheckInput := ⟨rootVal c96 message salts, positions, message.restrict positions,
      referenceProof nodes salts positions⟩
    let s0 := submission.initialState .check input
    ∀ steps v off,
      v < CAP_LEAF_LO → climbStepsFrom v = steps →
      ListSlice input.proof off (climbProofFrom nodes v) →
      evalClimb c96 s0 v off (nodes v) = nodes (climbEndFrom v) := by
  intro c96 nodes input s0 steps
  have hvalid : input.proof.length ≤ submission.sizes.proof := referenceProof_length_le_cap nodes salts positions
  have hcl := capLeafLo_eq
  have hqc := queueCalls_eq
  have hlen : LENGTH = 16777216 := by decide
  induction steps with
  | zero =>
    intro v _ hv hcs; rw [climbStepsFrom_of_lt hv] at hcs; omega
  | succ k ih =>
    intro v off hv hcs hsl
    rw [climbProofFrom_of_lt nodes hv] at hsl
    have hsl_sib := listSlice_split_left hsl
    have hsl_rest := listSlice_split_right hsl
    rw [stepSiblingsProof_length] at hsl_rest
    have hnot_last : ¬ (v / 3 = QUEUE_CALLS - 1) := by omega
    have hstep_eq : stepInput v (nodes v)
        (readBuffer s0 (11072966688 + off) 32, readBuffer s0 (11072966688 + off + 32) 32) =
        ternaryInput (nodes (3 * (v / 3))) (nodes (3 * (v / 3) + 1)) (nodes (3 * (v / 3) + 2)) := by
      unfold stepSiblingsProof at hsl_sib
      unfold stepInput
      simp only [hnot_last, ite_false]
      have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hr | hr | hr
      · simp only [hr, ite_true] at hsl_sib ⊢
        have hv0 : v = 3 * (v / 3) := by omega
        have hs0 := readBuffer_of_listSlice_bitsToBytes input hvalid (n := 32)
          (v := (nodes (3 * (v / 3) + 1) : BitVec (8 * 32))) (listSlice_split_left hsl_sib)
        have hs1 := readBuffer_of_listSlice_bitsToBytes input hvalid (n := 32)
          (v := (nodes (3 * (v / 3) + 2) : BitVec (8 * 32)))
          (by simpa only [bitsToBytes_length] using listSlice_split_right hsl_sib)
        rw [hs0, Nat.add_assoc, hs1, congrArg nodes hv0]
      · simp only [hr, show (1 : Nat) ≠ 0 by omega, ite_false, ite_true] at hsl_sib ⊢
        have hv1 : v = 3 * (v / 3) + 1 := by omega
        have hs0 := readBuffer_of_listSlice_bitsToBytes input hvalid (n := 32)
          (v := (nodes (3 * (v / 3)) : BitVec (8 * 32))) (listSlice_split_left hsl_sib)
        have hs1 := readBuffer_of_listSlice_bitsToBytes input hvalid (n := 32)
          (v := (nodes (3 * (v / 3) + 2) : BitVec (8 * 32)))
          (by simpa only [bitsToBytes_length] using listSlice_split_right hsl_sib)
        rw [hs0, Nat.add_assoc, hs1, congrArg nodes hv1]
      · simp only [hr, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false] at hsl_sib ⊢
        have hv2 : v = 3 * (v / 3) + 2 := by omega
        have hs0 := readBuffer_of_listSlice_bitsToBytes input hvalid (n := 32)
          (v := (nodes (3 * (v / 3)) : BitVec (8 * 32))) (listSlice_split_left hsl_sib)
        have hs1 := readBuffer_of_listSlice_bitsToBytes input hvalid (n := 32)
          (v := (nodes (3 * (v / 3) + 1) : BitVec (8 * 32)))
          (by simpa only [bitsToBytes_length] using listSlice_split_right hsl_sib)
        rw [hs0, Nat.add_assoc, hs1, congrArg nodes hv2]
    have hpar_node : c96 (ternaryInput (nodes (3 * (v / 3))) (nodes (3 * (v / 3) + 1)) (nodes (3 * (v / 3) + 2))) =
        nodes (parentNode v) := by
      unfold nodes nodeVal parentNode
      exact (nodeValFromLeaves_internal c96 _ (v / 3) (by omega)).symm
    rw [evalClimb_of_lt c96 s0 hv, climbEndFrom_of_lt hv, hstep_eq, hpar_node]
    have hcs_par : climbStepsFrom (parentNode v) = k := by rw [climbStepsFrom_of_lt hv] at hcs; omega
    by_cases hpar : parentNode v < CAP_LEAF_LO
    · exact ih (parentNode v) (off + 64) hpar hcs_par hsl_rest
    · rw [evalClimb_of_ge c96 s0 (by omega), climbEndFrom_of_ge (by omega)]

private theorem capNodeFrontier_slice_in_ref (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (hne : positions.card ≠ 0) (j : Nat) (hj : j < 143) :
    ListSlice (referenceProof nodes salts positions)
      (posRecordOff positions positions.card + 32 * capFrontierCountPrefix positions j)
      (capNodeFrontierProof nodes positions j) := by
  have hrec_len : ((positions.sort (· ≤ ·)).flatMap (recordProof nodes salts)).length =
      posRecordOff positions positions.card := by
    have h := take_flatMap_recordProof_length nodes salts positions positions.card le_rfl
    have htake : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) :=
      List.take_of_length_le (by simp)
    rwa [htake] at h
  have hcap_slice : ListSlice (capFrontierProof nodes positions)
      (32 * capFrontierCountPrefix positions j) (capNodeFrontierProof nodes positions j) := by
    have hsplit : List.range 143 = List.range j ++ [j] ++ (List.range (143 - (j + 1))).map (j + 1 + ·) := by
      apply List.ext_getElem
      · simp; omega
      · intro k hk1 hk2
        simp only [List.getElem_range]
        by_cases hlt : k < j
        · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega), List.getElem_range]
        · by_cases heq : k = j
          · subst heq
            rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
            simp
          · rw [List.getElem_append_right (by simp; omega)]
            simp; omega
    have hpref_len : ((List.range j).flatMap (capNodeFrontierProof nodes positions)).length =
        32 * capFrontierCountPrefix positions j := by
      clear hj hsplit
      induction j with
      | zero => simp [capFrontierCountPrefix_zero]
      | succ m ihm =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append, ihm,
          capNodeFrontierProof_length, capFrontierCountPrefix_succ, Nat.mul_add]
    unfold capFrontierProof
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    have hinner := listSlice_append_left (capNodeFrontierProof nodes positions j)
      (((List.range (143 - (j + 1))).map (j + 1 + ·)).flatMap (capNodeFrontierProof nodes positions))
      (listSlice_self _)
    simpa only [hpref_len, Nat.add_zero] using
      listSlice_append_right ((List.range j).flatMap (capNodeFrontierProof nodes positions)) _ hinner
  unfold referenceProof
  simp only [hne, ite_false]
  simpa only [hrec_len] using
    listSlice_append_right ((positions.sort (· ≤ ·)).flatMap (recordProof nodes salts))
      (capFrontierProof nodes positions) hcap_slice

theorem check_honest_accepts (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (salts : Index → Salt192)
    (positions : Positions) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let ev := oracle.eval (submission.scheme.check
      (rootVal c96 message salts) positions (message.restrict positions)
      (referenceProof (nodeVal c96 message salts) salts positions))
    ev.1 = true ∧ ev.2 ≤ CHECK_BUDGET positions.card := by
  intro c96
  let nodes := nodeVal c96 message salts
  let input : CheckInput := ⟨rootVal c96 message salts, positions, message.restrict positions,
    referenceProof nodes salts positions⟩
  let s0 := submission.initialState .check input
  have hvalid : input.proof.length ≤ submission.sizes.proof :=
    referenceProof_length_le_cap nodes salts positions
  dsimp only
  rw [scheme_check_eval_eq oracle input, submission_run_check_valid submission input hvalid,
    checkEval_execute_false]
  generalize hr : detExec oracle (submission.image .check) (submission.steps .check)
    (submission.initialState .check input) = r
  rcases r with ⟨e, tr⟩
  have hinp_pos : input.positions = positions := rfl
  by_cases hempty : positions.card = 0
  · have hpf_nil : input.proof.length = 0 := by simp [input, referenceProof, hempty]
    have hh := check_prologue_empty oracle input hvalid hempty
    have hev := hh.eval_of_le (show 5 ≤ submission.steps .check by rw [check_steps_eq]; omega)
    dsimp only at hev; rw [hr] at hev
    rw [hev.1, hev.2.1]
    simp only [hpf_nil, ↓reduceIte]
    exact ⟨rfl, Nat.zero_le _⟩
  · have hne : positions.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
    have hrec_len : ((positions.sort (· ≤ ·)).flatMap (recordProof nodes salts)).length =
        posRecordOff positions positions.card := by
      have h := take_flatMap_recordProof_length nodes salts positions positions.card le_rfl
      have htake : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) :=
        List.take_of_length_le (by simp)
      rwa [htake] at h
    have hpf_len : input.proof.length =
        posRecordOff positions positions.card + 32 * capFrontierCount positions := by
      change (referenceProof nodes salts positions).length = _
      unfold referenceProof
      simp only [hempty, ite_false, List.length_append, hrec_len, capFrontierProof_length]
    have hpos_dig : ∀ ord < positions.card,
        posCapDigest c96 s0 input ord = nodes (CAP_LEAF_LO + capLeafOf (posAt positions ord)) := by
      intro ord hord
      have hsl := recordProof_slice_in_ref nodes salts positions hempty ord hord
      unfold recordProof at hsl
      have hs_sl := listSlice_split_left hsl
      have hc_sl := listSlice_split_right hsl
      rw [bitsToBytes_length] at hc_sl
      have hsalt_eq : readBuffer s0 (11072966688 + posRecordOff positions ord) 24 =
          salts (posAt positions ord) :=
        readBuffer_of_listSlice_bitsToBytes input hvalid hs_sl
      have hval_eq : valAt input ord = message (posAt positions ord) := by
        have hmem : posAt positions ord ∈ positions := by
          unfold posAt; simp only [hord, ↓reduceDIte]
          exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _)
        exact valAt_eq_of_posAt input ord hord (posAt positions ord) hmem rfl
      have hleaf_eq : leafDigest c96 (posAt positions ord) (salts (posAt positions ord))
          (message (posAt positions ord)) = nodes (posAt positions ord).val := by
        unfold nodes nodeVal
        rw [nodeValFromLeaves_leaf c96 _ (posAt positions ord).val (posAt positions ord).isLt]
      have hi_lt : (posAt positions ord).val < CAP_LEAF_LO := by
        have h1 : (posAt positions ord).val < 16777216 := (posAt positions ord).isLt
        rw [capLeafLo_eq]; omega
      unfold posCapDigest
      dsimp only
      rw [hinp_pos, hsalt_eq, hval_eq, hleaf_eq,
        honest_evalClimb h768 oracle message salts positions (climbStepsFrom (posAt positions ord).val)
          (posAt positions ord).val (posRecordOff positions ord + 24) hi_lt rfl hc_sl,
        climbEndFrom_eq_capLeafOf]
    have hcon : PosConsistent c96 s0 input positions.card :=
      ⟨by rw [hinp_pos]; omega, fun a ha b hb heq => by rw [hpos_dig a ha, hpos_dig b hb, heq]⟩
    have hpipe := check_pipeline_nonempty h768 oracle input hvalid hempty
    rw [hinp_pos] at hpipe
    rcases hpipe with
      ⟨hnot, _⟩ | ⟨hshort, _⟩ |
      ⟨sPos, sCap, qPos, qCap, trPos, trCap, kFin, hk, hq, hinvPos, hdone, hh⟩
    · exact (hnot hcon).elim
    · omega
    · -- Prove every marked cap node u < 429 holds nodes (CAP_LEAF_LO + u) in sCap
      let baseOff := posRecordOff positions positions.card
      have hchild_proof : ∀ j < 142, capMark positions (286 + j) = true →
          (capMark positions (3 * j) = false →
            readBuffer s0 (11072966688 + capChildOff positions baseOff j 0) 32 = nodes (CAP_LEAF_LO + 3 * j)) ∧
          (capMark positions (3 * j + 1) = false →
            readBuffer s0 (11072966688 + capChildOff positions baseOff j 1) 32 = nodes (CAP_LEAF_LO + 3 * j + 1)) ∧
          (capMark positions (3 * j + 2) = false →
            readBuffer s0 (11072966688 + capChildOff positions baseOff j 2) 32 = nodes (CAP_LEAF_LO + 3 * j + 2)) := by
        intro j hj hmj
        have hsl := capNodeFrontier_slice_in_ref nodes salts positions hempty j (by omega)
        unfold capNodeFrontierProof at hsl
        simp only [hj, ite_true, hmj] at hsl
        refine ⟨fun hm0 => ?_, fun hm1 => ?_, fun hm2 => ?_⟩
        · have hsl0 := listSlice_split_left (listSlice_split_left hsl)
          simp only [hm0, Bool.not_false, ite_true] at hsl0
          have hco : capChildOff positions baseOff j 0 = baseOff + 32 * capFrontierCountPrefix positions j := by
            unfold capChildOff; simp only [hj, ite_true]
          rw [hco]
          exact readBuffer_of_listSlice_bitsToBytes input hvalid hsl0
        · have hsl1 := listSlice_split_right (listSlice_split_left hsl)
          simp only [hm1, Bool.not_false, ite_true] at hsl1
          have hl0 : (if (!capMark positions (3 * j)) = true then bitsToBytes (nodes (CAP_LEAF_LO + 3 * j)) 32 else []).length =
              if !capMark positions (3 * j) then 32 else 0 := by
            cases capMark positions (3 * j) <;> simp [bitsToBytes]
          rw [hl0] at hsl1
          have hco : capChildOff positions baseOff j 1 =
              baseOff + 32 * capFrontierCountPrefix positions j + (if !capMark positions (3 * j) then 32 else 0) := by
            unfold capChildOff; simp only [hj, show (1 : Nat) ≠ 0 by omega, ite_false, ite_true]
          rw [hco]
          exact readBuffer_of_listSlice_bitsToBytes input hvalid hsl1
        · have hsl2 := listSlice_split_right hsl
          simp only [hm2, Bool.not_false, ite_true] at hsl2
          have hl01 : ((if (!capMark positions (3 * j)) = true then bitsToBytes (nodes (CAP_LEAF_LO + 3 * j)) 32 else []) ++
              (if (!capMark positions (3 * j + 1)) = true then bitsToBytes (nodes (CAP_LEAF_LO + 3 * j + 1)) 32 else [])).length =
              (if !capMark positions (3 * j) then 32 else 0) + (if !capMark positions (3 * j + 1) then 32 else 0) := by
            rw [List.length_append]
            cases capMark positions (3 * j) <;> cases capMark positions (3 * j + 1) <;> simp [bitsToBytes]
          rw [hl01] at hsl2
          have hco : capChildOff positions baseOff j 2 =
              baseOff + 32 * capFrontierCountPrefix positions j +
              (if !capMark positions (3 * j) then 32 else 0) +
              (if !capMark positions (3 * j + 1) then 32 else 0) := by
            unfold capChildOff; simp only [hj, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false, ite_true]
          rw [hco, Nat.add_assoc]
          exact readBuffer_of_listSlice_bitsToBytes input hvalid (by simpa only [Nat.add_assoc] using hsl2)
      have hroot_proof :
          (capMark positions 426 = false →
            readBuffer s0 (11072966688 + capChildOff positions baseOff 142 0) 32 = nodes (CAP_LEAF_LO + 426)) ∧
          (capMark positions 427 = false →
            readBuffer s0 (11072966688 + capChildOff positions baseOff 142 1) 32 = nodes (CAP_LEAF_LO + 427)) := by
        have h428 := capMark_428_eq_true positions hne
        have hsl := capNodeFrontier_slice_in_ref nodes salts positions hempty 142 (by omega)
        unfold capNodeFrontierProof at hsl
        simp only [show ¬ (142 < 142) by omega, ite_false, ite_true, h428] at hsl
        refine ⟨fun hm0 => ?_, fun hm1 => ?_⟩
        · have hsl0 := listSlice_split_left hsl
          simp only [hm0, Bool.not_false, ite_true] at hsl0
          have hco : capChildOff positions baseOff 142 0 = baseOff + 32 * capFrontierCountPrefix positions 142 := by
            unfold capChildOff; simp only [show ¬ (142 < 142) by omega, ite_false, ite_true]
          rw [hco]
          exact readBuffer_of_listSlice_bitsToBytes input hvalid hsl0
        · have hsl1 := listSlice_split_right hsl
          simp only [hm1, Bool.not_false, ite_true] at hsl1
          have hl0 : (if (!capMark positions 426) = true then bitsToBytes (nodes (CAP_LEAF_LO + 426)) 32 else []).length =
              if !capMark positions 426 then 32 else 0 := by
            cases capMark positions 426 <;> simp [bitsToBytes]
          rw [hl0] at hsl1
          have hco : capChildOff positions baseOff 142 1 =
              baseOff + 32 * capFrontierCountPrefix positions 142 + (if !capMark positions 426 then 32 else 0) := by
            unfold capChildOff; simp only [show ¬ (142 < 142) by omega, show (1 : Nat) ≠ 0 by omega, ite_false]
          rw [hco]
          exact readBuffer_of_listSlice_bitsToBytes input hvalid hsl1
      have hall_cap : ∀ u < 428, capMark positions u = true →
          readBuffer sCap (8192 + 32 * u) 32 = nodes (CAP_LEAF_LO + u) := by
        intro u
        induction u using Nat.strong_induction_on with
        | h u ih =>
          intro hu hmu
          by_cases h286 : u < 286
          · rw [hdone.val_leaf_marked u h286 hmu]
            rw [capMark_leaf positions u h286, decide_eq_true_eq] at hmu
            obtain ⟨i, hi, heqc⟩ := hmu
            have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
            obtain ⟨ord, hord_len, hget⟩ := List.getElem_of_mem hmem
            have hord : ord < positions.card := by simpa using hord_len
            have hpa : posAt positions ord = i := by unfold posAt; simp only [hord, ↓reduceDIte]; exact hget
            have hd := (hinvPos.pos_done ord hord).1
            rw [hpa, heqc] at hd
            rw [hd, hpos_dig ord hord, hpa, heqc]
          · obtain ⟨j, rfl⟩ : ∃ j, u = 286 + j := ⟨u - 286, by omega⟩
            have hj : j < 142 := by omega
            obtain ⟨hval, _, hc0, hc1, hc2⟩ := hdone.val_internal j hj hmu
            obtain ⟨hp0, hp1, hp2⟩ := hchild_proof j hj hmu
            have hd0 : readBuffer sCap (8192 + 32 * (3 * j)) 32 = nodes (CAP_LEAF_LO + 3 * j) := by
              cases h : capMark positions (3 * j) with
              | true => exact ih (3 * j) (by omega) (by omega) h
              | false => rw [hc0 h, hp0 h]
            have hd1 : readBuffer sCap (8192 + 32 * (3 * j + 1)) 32 = nodes (CAP_LEAF_LO + 3 * j + 1) := by
              cases h : capMark positions (3 * j + 1) with
              | true => exact ih (3 * j + 1) (by omega) (by omega) h
              | false => rw [hc1 h, hp1 h]
            have hd2 : readBuffer sCap (8192 + 32 * (3 * j + 2)) 32 = nodes (CAP_LEAF_LO + 3 * j + 2) := by
              cases h : capMark positions (3 * j + 2) with
              | true => exact ih (3 * j + 2) (by omega) (by omega) h
              | false => rw [hc2 h, hp2 h]
            rw [hval, hd0, hd1, hd2]
            have hstart : CAP_LEAF_LO + (286 + j) = CAP_START + j := by
              have := capLeafLo_eq; have := capStart_eq; omega
            rw [hstart]
            exact (nodeValFromLeaves_capInternal c96 _ j hj).symm
      let comm : BitVec (8 * 32) := input.commitment
      have hroot_val : readBuffer sCap (8192 + 32 * 428) 32 = comm := by
        obtain ⟨hval, _, hc0, hc1⟩ := hdone.val_root
        have hd0 : readBuffer sCap (8192 + 32 * 426) 32 = nodes 25165821 := by
          have ha : CAP_LEAF_LO + 426 = 25165821 := by rw [capLeafLo_eq]
          rw [← ha]
          cases h : capMark positions 426 with
          | true => exact hall_cap 426 (by omega) h
          | false => rw [hc0 h, hroot_proof.1 h]
        have hd1 : readBuffer sCap (8192 + 32 * 427) 32 = nodes 25165822 := by
          have ha : CAP_LEAF_LO + 427 = 25165822 := by rw [capLeafLo_eq]
          rw [← ha]
          cases h : capMark positions 427 with
          | true => exact hall_cap 427 (by omega) h
          | false => rw [hc1 h, hroot_proof.2 h]
        rw [hval, hd0, hd1]
        exact (nodeValFromLeaves_root c96 _).symm
      have hev := hh.eval_of_le hk
      dsimp only at hev; rw [hr] at hev
      have hbeq_root : (comm == comm) = true := beq_self_eq_true comm
      have hcond_t : (posRecordOff positions positions.card + 32 * capFrontierCount positions ==
          input.proof.length &&
          readBuffer sCap (8192 + 32 * 428) 32 == comm) = true := by
        rw [← hpf_len, hroot_val, hbeq_root, beq_self_eq_true, Bool.and_self]
      have hev_exit : e.exit = .success := by
        have h1 := hev.1
        change e.exit = (if (posRecordOff positions positions.card + 32 * capFrontierCount positions ==
            input.proof.length &&
            readBuffer sCap (8192 + 32 * 428) 32 == comm) = true
          then Exit.success else Exit.failure) at h1
        rw [hcond_t] at h1
        exact h1
      rw [hev_exit, hev.2.1]
      refine ⟨rfl, ?_⟩
      unfold CHECK_BUDGET
      omega

end CommitGolfCandidate
