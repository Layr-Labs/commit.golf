import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! Deterministic symbolic execution infrastructure for the submitted `check` image (`checkInstr`,
words `0..358`):
- Equivalence between coin-free `execute` and the pure deterministic evaluator `detExec` under
  `Oracle.run`, `Oracle.eval`, and `fixedOracleRun (traceCompressionReplies _)`.
- Compositional step/halt/phase combinators with byte-level memory frames and `ChainScratchZero`.
- Variable-bit backward tail stream (`ProofCursor`, `proofDigestVar`), `step_readVarDigest`,
  and domain-separated iterated chain/mask subroutine `step_hashLevelNode`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Pure Deterministic Evaluator and Bridges -/

/-- Pure deterministic evaluator matching `execute image steps state false` together with the
exact list of compression `(input, answer)` replies in execution order. -/
def detExec (oracle : Oracle) (image : Image) :
    Nat → MachineState → Execution × CompressionReplies
  | 0, state => ({ exit := .unfinished, state := state, cycles := 0, oracleCalls := 0 }, [])
  | steps + 1, state =>
    match fetch image state with
    | none => ({ exit := .failure, state := state, cycles := 0, oracleCalls := 0 }, [])
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 then
        match oracleInput state with
        | none => ({ exit := .failure, state := state, cycles := 1, oracleCalls := 0 }, [])
        | some input =>
          match input with
          | .inl x =>
            let answer := oracle.compression x
            let r := detExec oracle image steps (writeBits state (state.getReg .x12) answer)
            (r.1.charge COMPRESSION_CYCLES 1, (x, answer) :: r.2)
          | .inr pq =>
            let answer := oracle.answer (m := Id) (.inr pq)
            let r := detExec oracle image steps
              (writeOracleAnswer state (state.getReg .x12) (.inr pq) answer)
            (r.1.charge PERMUTATION_CYCLES 1, r.2)
      else if state.getReg .x5 = 1 then
        ({ exit := if state.getReg .x10 = 0 then .success else .failure,
           state := state, cycles := 1, oracleCalls := 0 }, [])
      else
        ({ exit := .failure, state := state, cycles := 1, oracleCalls := 0 }, [])
    | some instruction =>
      match ordinaryStep state instruction with
      | none => ({ exit := .failure, state := state, cycles := 1, oracleCalls := 0 }, [])
      | some next =>
        let r := detExec oracle image steps next
        (r.1.charge (instructionCycles instruction) 0, r.2)

theorem detExec_succ_none (oracle : Oracle) (image : Image) (steps : Nat) (state : MachineState)
    (hfetch : fetch image state = none) :
    detExec oracle image (steps + 1) state =
      ({ exit := .failure, state := state, cycles := 0, oracleCalls := 0 }, []) := by
  simp only [detExec, hfetch]

theorem detExec_succ_ecall (oracle : Oracle) (image : Image) (steps : Nat) (state : MachineState)
    (hfetch : fetch image state = some (.base .ECALL)) :
    detExec oracle image (steps + 1) state =
      if state.getReg .x5 = 0 then
        match oracleInput state with
        | none => ({ exit := .failure, state := state, cycles := 1, oracleCalls := 0 }, [])
        | some (.inl x) =>
          let answer := oracle.compression x
          let r := detExec oracle image steps (writeBits state (state.getReg .x12) answer)
          (r.1.charge COMPRESSION_CYCLES 1, (x, answer) :: r.2)
        | some (.inr pq) =>
          let answer := oracle.answer (m := Id) (.inr pq)
          let r := detExec oracle image steps
            (writeOracleAnswer state (state.getReg .x12) (.inr pq) answer)
          (r.1.charge PERMUTATION_CYCLES 1, r.2)
      else if state.getReg .x5 = 1 then
        ({ exit := if state.getReg .x10 = 0 then .success else .failure,
           state := state, cycles := 1, oracleCalls := 0 }, [])
      else
        ({ exit := .failure, state := state, cycles := 1, oracleCalls := 0 }, []) := by
  simp only [detExec, hfetch]
  split
  · cases oracleInput state with
    | none => rfl
    | some q => cases q <;> rfl
  · rfl

theorem detExec_succ_other (oracle : Oracle) (image : Image) (steps : Nat) (state : MachineState)
    (instr : Instruction) (hne : instr ≠ .base .ECALL)
    (hfetch : fetch image state = some instr) :
    detExec oracle image (steps + 1) state =
      match ordinaryStep state instr with
      | none => ({ exit := .failure, state := state, cycles := 1, oracleCalls := 0 }, [])
      | some next =>
        let r := detExec oracle image steps next
        (r.1.charge (instructionCycles instr) 0, r.2) := by
  cases instr with
  | base inst =>
    cases inst with
    | ECALL => exact (hne rfl).elim
    | _ => simp only [detExec, hfetch]
  | word _ _ _ _ => simp only [detExec, hfetch]
  | sraiw _ _ _ => simp only [detExec, hfetch]

theorem detExec_trace_nil_of_zero_calls (oracle : Oracle) (image : Image) (steps : Nat)
    (state : MachineState) (hz : (detExec oracle image steps state).1.oracleCalls = 0) :
    (detExec oracle image steps state).2 = [] := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
    cases hfetch : fetch image state with
    | none => rw [detExec_succ_none oracle image steps state hfetch]
    | some instr =>
      by_cases he : instr = .base .ECALL
      · subst he
        rw [detExec_succ_ecall oracle image steps state hfetch] at hz ⊢
        by_cases hx5 : state.getReg .x5 = 0
        · simp only [hx5, ite_true] at hz ⊢
          cases hin : oracleInput state with
          | none => simp only [hin]; rfl
          | some q =>
            cases q with
            | inl x => simp [hin, Execution.charge] at hz
            | inr pq => simp [hin, Execution.charge] at hz
        · simp only [hx5, ite_false]
          by_cases hx51 : state.getReg .x5 = 1 <;> (simp only [hx51, ite_true, ite_false]; rfl)
      · rw [detExec_succ_other oracle image steps state instr he hfetch] at hz ⊢
        cases hstep : ordinaryStep state instr with
        | none => simp [hstep]
        | some next =>
          simp only [hstep, Execution.charge, Nat.zero_add] at hz ⊢
          exact ih next hz

private theorem execute_succ_other (image : Image) (steps : Nat) (state : MachineState)
    (instr : Instruction) (hne : instr ≠ .base .ECALL)
    (hfetch : fetch image state = some instr) :
    execute image (steps + 1) state false =
      match ordinaryStep state instr with
      | none => pure { exit := .failure, state := state, cycles := 1, oracleCalls := 0 }
      | some next => do
          let result ← execute image steps next false
          return result.charge (instructionCycles instr) 0 := by
  cases hstep : ordinaryStep state instr with
  | some next =>
    exact execute_ordinary_step image instr state next steps false hfetch hstep
  | none =>
    cases instr with
    | base inst =>
      cases inst <;> first | exact (hne rfl).elim | simp only [execute, hfetch, hstep]
    | word _ _ _ _ => simp only [execute, hfetch, hstep]
    | sraiw _ _ _ => simp only [execute, hfetch, hstep]

/-- Coin-free execution under `oracle.run` agrees with `detExec`. -/
theorem oracle_run_execute_false (oracle : Oracle) (image : Image) (steps : Nat)
    (state : MachineState) :
    oracle.run (execute image steps state false) =
      pure ((detExec oracle image steps state).1, (detExec oracle image steps state).1.oracleCalls) := by
  induction steps generalizing state with
  | zero =>
    simp only [execute, detExec, oracle_run_pure]
  | succ steps ih =>
    cases hfetch : fetch image state with
    | none =>
      simp only [execute, detExec, hfetch, oracle_run_pure]
    | some instr =>
      by_cases he : instr = .base .ECALL
      · subst he
        rw [detExec_succ_ecall oracle image steps state hfetch]
        simp only [execute, hfetch, Bool.false_and, Bool.false_eq_true, ite_false]
        by_cases hx5 : state.getReg .x5 = 0
        · simp only [hx5, ite_true]
          cases hin : oracleInput state with
          | none => simp only [oracle_run_pure]
          | some input =>
            cases input with
            | inl x =>
              rw [oracle_run_public_bind]
              change (do
                let (result, calls) ← oracle.run
                  ((execute image steps (writeBits state (state.getReg .x12) (oracle.compression x)) false) >>=
                    fun result => pure (result.charge COMPRESSION_CYCLES 1))
                return (result, 1 + calls)) = _
              rw [oracle_run_bind, ih]
              simp only [pure_bind, oracle_run_pure, Nat.add_zero, Execution.charge]
            | inr pq =>
              rw [oracle_run_public_bind]
              change (do
                let (result, calls) ← oracle.run
                  ((execute image steps
                    (writeOracleAnswer state (state.getReg .x12) (.inr pq) (oracle.answer (m := Id) (.inr pq))) false) >>=
                    fun result => pure (result.charge PERMUTATION_CYCLES 1))
                return (result, 1 + calls)) = _
              rw [oracle_run_bind, ih]
              simp only [pure_bind, oracle_run_pure, Nat.add_zero, Execution.charge]
        · simp only [hx5, ite_false]
          by_cases hx51 : state.getReg .x5 = 1 <;> simp only [hx51, ite_true, ite_false, oracle_run_pure]
      · rw [execute_succ_other image steps state instr he hfetch,
          detExec_succ_other oracle image steps state instr he hfetch]
        cases hstep : ordinaryStep state instr with
        | none => simp only [oracle_run_pure]
        | some next =>
          rw [oracle_run_bind, ih next]
          simp only [pure_bind, oracle_run_pure, Nat.add_zero, Execution.charge, Nat.zero_add]

/-- Deterministic check-handler evaluation of a `World` computation. -/
def checkEval (oracle : Oracle) {α : Type} (computation : OracleComp World α) : α × Nat :=
  oracle.eval (simulateQ checkHandler computation)

theorem checkEval_pure (oracle : Oracle) {α : Type} (v : α) :
    checkEval oracle (pure v) = (v, 0) := by
  simp [checkEval, Oracle.eval]
  rfl

theorem checkEval_bind (oracle : Oracle) {α β : Type} (c : OracleComp World α)
    (k : α → OracleComp World β) :
    checkEval oracle (c >>= k) =
      let (v, n1) := checkEval oracle c
      let (r, n2) := checkEval oracle (k v)
      (r, n1 + n2) := by
  simp only [checkEval, Oracle.eval, simulateQ_bind, WriterT.run_bind]
  rfl

theorem checkEval_public_bind (oracle : Oracle) {α : Type} (q : PublicSpec.Domain)
    (k : PublicSpec.Range q → OracleComp World α) :
    checkEval oracle ((World.query (.inr q) : OracleComp World _) >>= k) =
      let (r, n) := checkEval oracle (k (oracle.answer (m := Id) q))
      (r, 1 + n) := by
  rw [checkEval_bind]
  have hq : checkEval oracle (World.query (.inr q) : OracleComp World _) =
      (oracle.answer (m := Id) q, 1) := by
    simp [checkEval, Oracle.eval, checkHandler, QueryImpl.withAddCost, QueryImpl.withCost]
    rfl
  rw [hq]

theorem checkEval_execute_false (oracle : Oracle) (image : Image) (steps : Nat)
    (state : MachineState) :
    checkEval oracle (execute image steps state false) =
      ((detExec oracle image steps state).1, (detExec oracle image steps state).1.oracleCalls) := by
  induction steps generalizing state with
  | zero =>
    simp only [execute, detExec, checkEval_pure]
  | succ steps ih =>
    cases hfetch : fetch image state with
    | none =>
      simp only [execute, detExec, hfetch, checkEval_pure]
    | some instr =>
      by_cases he : instr = .base .ECALL
      · subst he
        rw [detExec_succ_ecall oracle image steps state hfetch]
        simp only [execute, hfetch, Bool.false_and, Bool.false_eq_true, ite_false]
        by_cases hx5 : state.getReg .x5 = 0
        · simp only [hx5, ite_true]
          cases hin : oracleInput state with
          | none => simp only [checkEval_pure]
          | some input =>
            cases input with
            | inl x =>
              rw [checkEval_public_bind]
              change (match checkEval oracle
                ((execute image steps (writeBits state (state.getReg .x12) (oracle.compression x)) false) >>=
                  fun result => pure (result.charge COMPRESSION_CYCLES 1)) with
                | (r, n) => (r, 1 + n)) = _
              rw [checkEval_bind, ih]
              simp only [checkEval_pure, Nat.add_zero, Execution.charge]
            | inr pq =>
              rw [checkEval_public_bind]
              change (match checkEval oracle
                ((execute image steps
                  (writeOracleAnswer state (state.getReg .x12) (.inr pq) (oracle.answer (m := Id) (.inr pq))) false) >>=
                  fun result => pure (result.charge PERMUTATION_CYCLES 1)) with
                | (r, n) => (r, 1 + n)) = _
              rw [checkEval_bind, ih]
              simp only [checkEval_pure, Nat.add_zero, Execution.charge]
        · simp only [hx5, ite_false]
          by_cases hx51 : state.getReg .x5 = 1 <;> simp only [hx51, ite_true, ite_false, checkEval_pure]
      · rw [execute_succ_other image steps state instr he hfetch,
          detExec_succ_other oracle image steps state instr he hfetch]
        cases hstep : ordinaryStep state instr with
        | none => simp only [checkEval_pure]
        | some next =>
          rw [checkEval_bind, ih next]
          simp only [checkEval_pure, Nat.add_zero, Execution.charge, Nat.zero_add]

theorem scheme_check_eval_eq (oracle : Oracle) (input : CheckInput) :
    oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof) =
      ((checkEval oracle (submission.run .check input)).1.exit == .success,
       (checkEval oracle (submission.run .check input)).2) := by
  simp only [Submission.scheme, Oracle.eval, simulateQ_map, WriterT.run_map]
  rfl

private theorem traceReplies_bind_pure {α β : Type} (c : OracleComp World α) (f : α → β) :
    traceCompressionReplies (c >>= fun x => pure (f x)) =
      (fun p => (f p.1, p.2)) <$> traceCompressionReplies c := by
  induction c using OracleComp.inductionOn with
  | pure v =>
    simp only [pure_bind, map_pure]
    rfl
  | query_bind q next ih =>
    rw [bind_assoc]
    rcases q with coins | (input | permQuery)
    · change ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
        traceCompressionReplies (next answer >>= fun x => pure (f x))) =
        (fun p => (f p.1, p.2)) <$>
          ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer))
      rw [map_bind]
      apply bind_congr; intro answer
      exact ih answer
    · change ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
        traceCompressionReplies (next answer >>= fun x => pure (f x)) >>= fun p =>
          pure (p.1, (input, answer) :: p.2)) =
        (fun p => (f p.1, p.2)) <$>
          ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer) >>= fun p =>
              pure (p.1, (input, answer) :: p.2))
      rw [map_bind]
      apply bind_congr; intro answer
      rw [ih answer, bind_map_left, map_bind]
      apply bind_congr; rintro ⟨v, t⟩
      simp
    · change ((liftM (World.query (.inr (.inr permQuery))) : OracleComp World _) >>= fun answer =>
        traceCompressionReplies (next answer >>= fun x => pure (f x))) =
        (fun p => (f p.1, p.2)) <$>
          ((liftM (World.query (.inr (.inr permQuery))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer))
      rw [map_bind]
      apply bind_congr; intro answer
      exact ih answer

/-- Coin-free execution under `fixedOracleRun oracle (traceCompressionReplies _)` agrees with `detExec`. -/
theorem fixedOracleRun_trace_execute_false (oracle : Oracle) (image : Image) (steps : Nat)
    (state : MachineState) :
    fixedOracleRun oracle (traceCompressionReplies (execute image steps state false)) =
      pure (detExec oracle image steps state) := by
  induction steps generalizing state with
  | zero =>
    change fixedOracleRun oracle
      (pure (({ exit := .unfinished, state := state, cycles := 0, oracleCalls := 0 } : Execution),
        ([] : CompressionReplies))) = _
    exact fixed_oracle_run_pure oracle _
  | succ steps ih =>
    cases hfetch : fetch image state with
    | none =>
      simp only [execute, detExec, hfetch]
      change fixedOracleRun oracle
        (pure (({ exit := .failure, state := state, cycles := 0, oracleCalls := 0 } : Execution),
          ([] : CompressionReplies))) = _
      exact fixed_oracle_run_pure oracle _
    | some instr =>
      by_cases he : instr = .base .ECALL
      · subst he
        rw [detExec_succ_ecall oracle image steps state hfetch]
        simp only [execute, hfetch, Bool.false_and, Bool.false_eq_true, ite_false]
        by_cases hx5 : state.getReg .x5 = 0
        · simp only [hx5, ite_true]
          cases hin : oracleInput state with
          | none =>
            change fixedOracleRun oracle (pure _) = _
            exact fixed_oracle_run_pure oracle _
          | some input =>
            cases input with
            | inl x =>
              change fixedOracleRun oracle
                ((liftM (World.query (.inr (.inl x))) : OracleComp World _) >>= fun answer =>
                  traceCompressionReplies
                    ((execute image steps (writeBits state (state.getReg .x12) answer) false) >>=
                      fun result => pure (result.charge COMPRESSION_CYCLES 1)) >>= fun p =>
                    pure (p.1, (x, answer) :: p.2)) = _
              rw [fixed_oracle_run_public, traceReplies_bind_pure, fixed_oracle_run_bind,
                fixed_oracle_run_map]
              change (((fun p : Execution × CompressionReplies => (p.1.charge COMPRESSION_CYCLES 1, p.2)) <$>
                fixedOracleRun oracle
                  (traceCompressionReplies (execute image steps
                    (writeBits state (state.getReg .x12) (oracle.compression x)) false))) >>=
                fun p => fixedOracleRun oracle (pure (p.1, (x, oracle.compression x) :: p.2))) = _
              rw [ih, map_pure, pure_bind, fixed_oracle_run_pure]
              rfl
            | inr pq =>
              change fixedOracleRun oracle
                ((liftM (World.query (.inr (.inr pq))) : OracleComp World _) >>= fun answer =>
                  traceCompressionReplies
                    ((execute image steps (writeOracleAnswer state (state.getReg .x12) (.inr pq) answer) false) >>=
                      fun result => pure (result.charge PERMUTATION_CYCLES 1))) = _
              rw [fixed_oracle_run_public, traceReplies_bind_pure, fixed_oracle_run_map, ih, map_pure]
              rfl
        · simp only [hx5, ite_false]
          by_cases hx51 : state.getReg .x5 = 1
          · simp only [hx51, ite_true]
            change fixedOracleRun oracle (pure _) = _
            exact fixed_oracle_run_pure oracle _
          · simp only [hx51, ite_false]
            change fixedOracleRun oracle (pure _) = _
            exact fixed_oracle_run_pure oracle _
      · rw [execute_succ_other image steps state instr he hfetch,
          detExec_succ_other oracle image steps state instr he hfetch]
        cases hstep : ordinaryStep state instr with
        | none =>
          change fixedOracleRun oracle (pure _) = _
          exact fixed_oracle_run_pure oracle _
        | some next =>
          rw [traceReplies_bind_pure, fixed_oracle_run_map, ih next, map_pure]

/-! ### 2. `StepsTo`, `HaltsWith`, `PhaseOutcome`, BitVec and Memory-Frame Helpers -/

/-- Exact multi-step transition of `detExec` on the check image (ignoring cycles). -/
def StepsTo (oracle : Oracle) (s1 s2 : MachineState) (steps calls : Nat)
    (tr : CompressionReplies) : Prop :=
  ∀ extra,
    let r1 := detExec oracle (submission.image .check) (steps + extra) s1
    let r2 := detExec oracle (submission.image .check) extra s2
    r1.1.exit = r2.1.exit ∧
    r1.1.state = r2.1.state ∧
    r1.1.oracleCalls = calls + r2.1.oracleCalls ∧
    r1.2 = tr ++ r2.2

/-- Halting execution of `detExec` on the check image within `steps` instructions. -/
def HaltsWith (oracle : Oracle) (s : MachineState) (steps calls : Nat)
    (exit : Exit) (tr : CompressionReplies) : Prop :=
  exit ≠ .unfinished ∧
  ∀ extra,
    let r := detExec oracle (submission.image .check) (steps + extra) s
    r.1.exit = exit ∧ r.1.oracleCalls = calls ∧ r.2 = tr

/-- Either early rejection (guarded by `CanReject`) or successful continuation to a state
satisfying `P`. -/
inductive PhaseOutcome (oracle : Oracle) (s : MachineState) (maxSteps maxCalls : Nat)
    (CanReject : Prop) (P : MachineState → Nat → CompressionReplies → Prop) : Prop where
  | rejected (k q : Nat) (tr : CompressionReplies) :
      CanReject → k ≤ maxSteps → q ≤ maxCalls → HaltsWith oracle s k q .failure tr →
      PhaseOutcome oracle s maxSteps maxCalls CanReject P
  | continued (s' : MachineState) (k q : Nat) (tr : CompressionReplies) :
      k ≤ maxSteps → q ≤ maxCalls → StepsTo oracle s s' k q tr → P s' q tr →
      PhaseOutcome oracle s maxSteps maxCalls CanReject P

theorem StepsTo.refl (oracle : Oracle) (s : MachineState) :
    StepsTo oracle s s 0 0 [] := by
  intro extra
  simp

theorem StepsTo.trans {oracle : Oracle} {s1 s2 s3 : MachineState}
    {k1 k2 q1 q2 : Nat} {t1 t2 : CompressionReplies}
    (h1 : StepsTo oracle s1 s2 k1 q1 t1) (h2 : StepsTo oracle s2 s3 k2 q2 t2) :
    StepsTo oracle s1 s3 (k1 + k2) (q1 + q2) (t1 ++ t2) := by
  intro extra
  have a := h1 (k2 + extra)
  have b := h2 extra
  rw [show k1 + k2 + extra = k1 + (k2 + extra) by omega]
  refine ⟨a.1.trans b.1, a.2.1.trans b.2.1, ?_, ?_⟩
  · rw [a.2.2.1, b.2.2.1]; omega
  · rw [a.2.2.2, b.2.2.2, List.append_assoc]

theorem StepsTo.eq_of {oracle : Oracle} {s1 s2 s2' : MachineState}
    {k k' q q' : Nat} {t t' : CompressionReplies}
    (h : StepsTo oracle s1 s2 k q t)
    (hs : s2 = s2') (hk : k = k') (hq : q = q') (ht : t = t') :
    StepsTo oracle s1 s2' k' q' t' := by
  subst hs; subst hk; subst hq; subst ht; exact h

theorem StepsTo.halt {oracle : Oracle} {s1 s2 : MachineState}
    {k1 k2 q1 q2 : Nat} {ex : Exit} {t1 t2 : CompressionReplies}
    (h1 : StepsTo oracle s1 s2 k1 q1 t1) (h2 : HaltsWith oracle s2 k2 q2 ex t2) :
    HaltsWith oracle s1 (k1 + k2) (q1 + q2) ex (t1 ++ t2) := by
  refine ⟨h2.1, fun extra => ?_⟩
  have a := h1 (k2 + extra)
  have b := h2.2 extra
  rw [show k1 + k2 + extra = k1 + (k2 + extra) by omega]
  exact ⟨a.1.trans b.1, by rw [a.2.2.1, b.2.1], by rw [a.2.2.2, b.2.2]⟩

theorem HaltsWith.mono {oracle : Oracle} {s : MachineState}
    {k1 k2 q : Nat} {ex : Exit} {tr : CompressionReplies}
    (h : HaltsWith oracle s k1 q ex tr) (hle : k1 ≤ k2) :
    HaltsWith oracle s k2 q ex tr := by
  refine ⟨h.1, fun extra => ?_⟩
  have a := h.2 ((k2 - k1) + extra)
  simpa only [show k1 + (k2 - k1 + extra) = k2 + extra by omega] using a

theorem HaltsWith.eval_of_le {oracle : Oracle} {s : MachineState}
    {k N q : Nat} {ex : Exit} {tr : CompressionReplies}
    (h : HaltsWith oracle s k q ex tr) (hle : k ≤ N) :
    let r := detExec oracle (submission.image .check) N s
    r.1.exit = ex ∧ r.1.oracleCalls = q ∧ r.2 = tr := by
  have a := h.2 (N - k)
  simpa only [show k + (N - k) = N by omega] using a

theorem PhaseOutcome.bind {oracle : Oracle} {s1 : MachineState}
    {K1 K2 Q1 Q2 : Nat} {R1 R2 R : Prop}
    {P1 P2 : MachineState → Nat → CompressionReplies → Prop}
    (h1 : PhaseOutcome oracle s1 K1 Q1 R1 P1)
    (hR1 : R1 → R) (hR2 : R2 → R)
    (h2 : ∀ s2 q1 tr1, P1 s2 q1 tr1 →
      PhaseOutcome oracle s2 K2 Q2 R2 (fun s3 q2 tr2 => P2 s3 (q1 + q2) (tr1 ++ tr2))) :
    PhaseOutcome oracle s1 (K1 + K2) (Q1 + Q2) R P2 := by
  cases h1 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected k q tr (hR1 hr) (by omega) (by omega) hh
  | continued s2 k1 q1 tr1 hk1 hq1 hs1 hp1 =>
    cases h2 s2 q1 tr1 hp1 with
    | rejected k2 q2 tr2 hr2 hk2 hq2 hh2 =>
      exact .rejected (k1 + k2) (q1 + q2) (tr1 ++ tr2) (hR2 hr2) (by omega) (by omega) (hs1.halt hh2)
    | continued s3 k2 q2 tr2 hk2 hq2 hs2 hp2 =>
      exact .continued s3 (k1 + k2) (q1 + q2) (tr1 ++ tr2) (by omega) (by omega) (hs1.trans hs2) hp2

theorem PhaseOutcome.bind_dep {oracle : Oracle} {s1 : MachineState}
    {K1 K2 Q1 Q2 : Nat} {R1 R : Prop}
    {P1 P2 : MachineState → Nat → CompressionReplies → Prop}
    (h1 : PhaseOutcome oracle s1 K1 Q1 R1 P1)
    (hR1 : R1 → R)
    (h2 : ∀ s2 q1 tr1, P1 s2 q1 tr1 →
      PhaseOutcome oracle s2 K2 Q2 R (fun s3 q2 tr2 => P2 s3 (q1 + q2) (tr1 ++ tr2))) :
    PhaseOutcome oracle s1 (K1 + K2) (Q1 + Q2) R P2 := by
  cases h1 with
  | rejected k q tr hr hk hq hh =>
    exact .rejected k q tr (hR1 hr) (by omega) (by omega) hh
  | continued s2 k1 q1 tr1 hk1 hq1 hs1 hp1 =>
    cases h2 s2 q1 tr1 hp1 with
    | rejected k2 q2 tr2 hr2 hk2 hq2 hh2 =>
      exact .rejected (k1 + k2) (q1 + q2) (tr1 ++ tr2) hr2 (by omega) (by omega) (hs1.halt hh2)
    | continued s3 k2 q2 tr2 hk2 hq2 hs2 hp2 =>
      exact .continued s3 (k1 + k2) (q1 + q2) (tr1 ++ tr2) (by omega) (by omega) (hs1.trans hs2) hp2

theorem PhaseOutcome.weaken {oracle : Oracle} {s : MachineState}
    {K1 K2 Q1 Q2 : Nat} {R1 R2 : Prop}
    {P1 P2 : MachineState → Nat → CompressionReplies → Prop}
    (h : PhaseOutcome oracle s K1 Q1 R1 P1)
    (hK : K1 ≤ K2) (hQ : Q1 ≤ Q2) (hR : R1 → R2)
    (hP : ∀ s' q tr, P1 s' q tr → P2 s' q tr) :
    PhaseOutcome oracle s K2 Q2 R2 P2 := by
  cases h with
  | rejected k q tr hr hk hq hh =>
    exact .rejected k q tr (hR hr) (by omega) (by omega) hh
  | continued s' k q tr hk hq hs hp =>
    exact .continued s' k q tr (by omega) (by omega) hs (hP s' q tr hp)

theorem StepsTo.prepend_pure {oracle : Oracle} {s1 s2 : MachineState}
    {k1 K2 Q2 : Nat} {R : Prop}
    {P : MachineState → Nat → CompressionReplies → Prop}
    (h1 : StepsTo oracle s1 s2 k1 0 [])
    (h2 : PhaseOutcome oracle s2 K2 Q2 R P) :
    PhaseOutcome oracle s1 (k1 + K2) Q2 R P := by
  cases h2 with
  | rejected k2 q2 tr2 hr hk2 hq2 hh2 =>
    exact .rejected (k1 + k2) q2 tr2 hr (by omega) hq2 (by simpa using h1.halt hh2)
  | continued s3 k2 q2 tr2 hk2 hq2 hs2 hp2 =>
    exact .continued s3 (k1 + k2) q2 tr2 (by omega) hq2 (by simpa using h1.trans hs2) hp2

theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0#64 := rfl

/-! #### BitVec and Address Helpers -/

def pcWord (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

theorem mem_setPC (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl

theorem mem_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem toNat_ofNat64 (a : Nat) (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem signExtend12_ofNat_lt2048 (n : Nat) (hn : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  unfold signExtend12
  apply BitVec.eq_of_toNat_eq
  have hmod12 : n % 2 ^ 12 = n := Nat.mod_eq_of_lt (by omega)
  have hmod64 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmsb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, hmod12]
    exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, if_neg (by rw [hmsb]; decide), Nat.add_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, hmod12, hmod64, toNat_ofNat64 n (by omega)]

theorem signExtend13_ofNat_lt4096 (n : Nat) (hn : n < 4096) :
    signExtend13 (BitVec.ofNat 13 n) = BitVec.ofNat 64 n := by
  unfold signExtend13
  apply BitVec.eq_of_toNat_eq
  have hmod13 : n % 2 ^ 13 = n := Nat.mod_eq_of_lt (by omega)
  have hmod64 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmsb : (BitVec.ofNat 13 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, hmod13]
    exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, if_neg (by rw [hmsb]; decide), Nat.add_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, hmod13, hmod64, toNat_ofNat64 n (by omega)]

theorem signExtend21_ofNat_lt (n : Nat) (hn : n < 2 ^ 20) :
    signExtend21 (BitVec.ofNat 21 n) = BitVec.ofNat 64 n := by
  unfold signExtend21
  apply BitVec.eq_of_toNat_eq
  have hmod21 : n % 2 ^ 21 = n := Nat.mod_eq_of_lt (by omega)
  have hmod64 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmsb : (BitVec.ofNat 21 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, hmod21]
    exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, if_neg (by rw [hmsb]; decide), Nat.add_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, hmod21, hmod64, toNat_ofNat64 n (by omega)]

theorem se12_0 : signExtend12 0#12 = 0#64 := by decide
theorem se12_1 : signExtend12 1#12 = 1#64 := by decide
theorem se12_8 : signExtend12 8#12 = 8#64 := by decide
theorem se12_16 : signExtend12 16#12 = 16#64 := by decide
theorem se12_24 : signExtend12 24#12 = 24#64 := by decide
theorem se12_28 : signExtend12 28#12 = 28#64 := by decide
theorem se12_32 : signExtend12 32#12 = 32#64 := by decide
theorem se12_40 : signExtend12 40#12 = 40#64 := by decide
theorem se12_48 : signExtend12 48#12 = 48#64 := by decide
theorem se12_56 : signExtend12 56#12 = 56#64 := by decide
theorem se12_64 : signExtend12 64#12 = 64#64 := by decide
theorem se12_72 : signExtend12 72#12 = 72#64 := by decide
theorem se12_80 : signExtend12 80#12 = 80#64 := by decide
theorem se12_96 : signExtend12 96#12 = 96#64 := by decide
theorem se12_112 : signExtend12 112#12 = 112#64 := by decide
theorem se12_120 : signExtend12 120#12 = 120#64 := by decide
theorem se12_160 : signExtend12 160#12 = 160#64 := by decide
theorem se12_168 : signExtend12 168#12 = 168#64 := by decide
theorem se12_255 : signExtend12 255#12 = 255#64 := by decide
theorem se12_256 : signExtend12 256#12 = BitVec.ofNat 64 256 := signExtend12_ofNat_lt2048 256 (by decide)
theorem se12_320 : signExtend12 320#12 = BitVec.ofNat 64 320 := signExtend12_ofNat_lt2048 320 (by decide)
theorem se12_512 : signExtend12 512#12 = BitVec.ofNat 64 512 := signExtend12_ofNat_lt2048 512 (by decide)
theorem se12_560 : signExtend12 560#12 = BitVec.ofNat 64 560 := signExtend12_ofNat_lt2048 560 (by decide)
theorem se12_960 : signExtend12 960#12 = BitVec.ofNat 64 960 := signExtend12_ofNat_lt2048 960 (by decide)
theorem se12_984 : signExtend12 984#12 = BitVec.ofNat 64 984 := signExtend12_ofNat_lt2048 984 (by decide)
theorem se12_4095 : signExtend12 4095#12 = (-1#64 : Word) := by decide
theorem se12_4095_allOnes : signExtend12 4095#12 = BitVec.allOnes 64 := by decide

theorem bv64_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bv64_sub (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat64 a ha, toNat_ofNat64 b (by omega), toNat_ofNat64 (a - b) (by omega)]
  omega

theorem bv64_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  rw [se12_4095, ← bv64_add n 1]
  change BitVec.ofNat 64 n + 1#64 + (-1#64 : Word) = BitVec.ofNat 64 n
  rw [BitVec.add_assoc, show (1#64 : Word) + (-1#64 : Word) = 0#64 by decide, BitVec.add_zero]

theorem bv64_and_255 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& 255#64 = BitVec.ofNat 64 (a % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat64 a ha, toNat_ofNat64 (a % 256) (by omega),
    show (255#64 : Word).toNat = 255 by decide]
  change a &&& (2 ^ 8 - 1) = a % 2 ^ 8
  exact Nat.and_two_pow_sub_one_eq_mod a 8

theorem bv64_and_pow_sub1 (a k : Nat) (ha : a < 2 ^ 64) (hk : k < 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (a % 2 ^ k) := by
  have hpow : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide : 1 < 2) hk
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat64 a ha, toNat_ofNat64 (2 ^ k - 1) (by omega),
    toNat_ofNat64 (a % 2 ^ k) (Nat.lt_trans (Nat.mod_lt a hpos) hpow)]
  exact Nat.and_two_pow_sub_one_eq_mod a k

theorem bv64_or_shift_eq_add (a b k : Nat) (ha : a < 2 ^ k) (hsum : a + b * 2 ^ k < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 (b * 2 ^ k)) = BitVec.ofNat 64 (a + b * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, toNat_ofNat64 a (by omega), toNat_ofNat64 (b * 2 ^ k) (by omega),
    toNat_ofNat64 (a + b * 2 ^ k) hsum, Nat.or_comm, ← Nat.shiftLeft_eq b k,
    ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem truncate8_zeroExtend64 (b : Byte) :
    (b.zeroExtend 64).truncate 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hlt : b.toNat < 2 ^ 8 := b.isLt
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt hlt]

theorem truncate8_ofNat64 (n : Nat) (hn : n < 256) :
    (BitVec.ofNat 64 n).truncate 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn]

theorem pcWord_sub_20 (base : Nat) :
    pcWord (base + 5) + signExtend13 8172#13 = pcWord base := by
  have hse : signExtend13 8172#13 = (-20#64 : Word) := by decide
  rw [hse]
  unfold pcWord
  rw [show 0x1000 + 4 * (base + 5) = (0x1000 + 4 * base) + 20 by omega, ← bv64_add]
  change BitVec.ofNat 64 (0x1000 + 4 * base) + 20#64 + (-20#64 : Word) = _
  rw [BitVec.add_assoc, show (20#64 : Word) + (-20#64 : Word) = 0#64 by decide, BitVec.add_zero]

theorem bv64_shl (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha]

theorem bv64_shr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt ha]
  have hlt : a / 2 ^ k < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  rw [Nat.mod_eq_of_lt hlt]

theorem bv64_and_one (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& 1#64 = BitVec.ofNat 64 (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat64 a ha, toNat_ofNat64 (a % 2) (by omega),
    show (1#64 : Word).toNat = 1 by decide]
  change a &&& (2 ^ 1 - 1) = a % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod a 1

theorem bv64_xor_one (a : Nat) (ha : a < 2 ^ 63) :
    BitVec.ofNat 64 a ^^^ 1#64 = BitVec.ofNat 64 (a ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  have hx : a ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' a with ⟨q, rfl | rfl⟩
    · rw [xor_one_even]; omega
    · rw [xor_one_odd]; omega
  rw [BitVec.toNat_xor, toNat_ofNat64 a (by omega), toNat_ofNat64 (a ^^^ 1) hx,
    show (1#64 : Word).toNat = 1 by decide]

theorem bv64_ult_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  unfold BitVec.ult
  rw [toNat_ofNat64 a ha, toNat_ofNat64 b hb]

theorem bv64_eq_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rwa [toNat_ofNat64 a ha, toNat_ofNat64 b hb] at hn
  · intro h; rw [h]

theorem bv64_beq_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff, bv64_eq_iff a b ha hb]

theorem bv64_bne_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, decide_eq_true_iff, ne_eq, bv64_eq_iff a b ha hb]

@[local simp] theorem pcWord_add_four (idx : Nat) :
    pcWord idx + (4 : Word) = pcWord (idx + 1) := by
  unfold pcWord
  change BitVec.ofNat 64 (0x1000 + 4 * idx) + BitVec.ofNat 64 4 = _
  rw [bv64_add]
  congr 1 <;> omega

@[local simp] theorem pcWord_add_four_bv (idx : Nat) :
    pcWord idx + 4#64 = pcWord (idx + 1) :=
  pcWord_add_four idx

theorem readBuffer_congr2 (s1 s2 : MachineState) (a1 a2 n : Nat)
    (h : ∀ j < n, s1.getByte (BitVec.ofNat 64 (a1 + j)) = s2.getByte (BitVec.ofNat 64 (a2 + j))) :
    readBuffer s1 a1 n = readBuffer s2 a2 n := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem signExtend12_ofNat_lt256 (n : Fin 256) :
    signExtend12 (BitVec.ofNat 12 n.val) = BitVec.ofNat 64 n.val :=
  signExtend12_ofNat_lt2048 n.val (by omega)

theorem and_not_one_of_even (n : Nat) (heven : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  have hlow : BitVec.ofNat 64 n &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (n % 2 ^ 64) &&& (2 ^ 1 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hor : (BitVec.ofNat 64 n &&& ~~~1#64) ||| (BitVec.ofNat 64 n &&& 1#64) = BitVec.ofNat 64 n := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases (1#64 : Word)[i] <;> simp
  simpa only [hlow, BitVec.or_zero] using hor

theorem jalr_pcWord (retIdx : Nat) (hsmall : 0x1000 + 4 * retIdx < 2 ^ 64) :
    (pcWord retIdx + signExtend12 (0#12)) &&& ~~~1#64 = pcWord retIdx := by
  rw [se12_0, BitVec.add_zero]
  exact and_not_one_of_even (0x1000 + 4 * retIdx) (by omega)

theorem rangeValid_ofNat (addr n : Nat) (hn : addr + n ≤ MEMORY_BYTES) :
    rangeValid (BitVec.ofNat 64 addr) n = true := by
  unfold rangeValid MEMORY_BYTES at *
  rw [toNat_ofNat64 addr (by omega)]
  exact decide_eq_true hn

theorem accessValid_ofNat (addr w : Nat) (hn : addr + w ≤ MEMORY_BYTES) (ha : addr % w = 0) :
    accessValid (BitVec.ofNat 64 addr) w = true := by
  unfold accessValid
  rw [rangeValid_ofNat addr w hn, Bool.true_and]
  unfold MEMORY_BYTES at hn
  rw [toNat_ofNat64 addr (by omega)]
  exact decide_eq_true ha

theorem bool_byte_zeroExtend (b : Bool) :
    ((if b then (1#8 : Byte) else 0#8).zeroExtend 64) = if b then 1#64 else 0#64 := by
  cases b <;> decide

theorem bool_word_or (b1 b2 : Bool) :
    ((if b1 then (1#64 : Word) else 0#64) ||| (if b2 then 1#64 else 0#64)) =
      if (b1 || b2) then 1#64 else 0#64 := by
  cases b1 <;> cases b2 <;> decide

/-! #### `levelMetaOC` Bit-Field Extraction Lemmas (`l ∈ 2..24`) -/

theorem levelMetaOC_bodyBytes (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    BitVec.ofNat 64 (levelMetaOC l) &&& 255#64 = BitVec.ofNat 64 (levelBodyBytes l) := by
  interval_cases l <;> decide

theorem levelMetaOC_tailBits (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    (BitVec.ofNat 64 (levelMetaOC l) >>> 8) &&& 255#64 = BitVec.ofNat 64 (levelTailBits l) := by
  interval_cases l <;> decide

theorem levelMetaOC_chain (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    (BitVec.ofNat 64 (levelMetaOC l) >>> 16) &&& 255#64 = BitVec.ofNat 64 (levelChain l) := by
  interval_cases l <;> decide

theorem levelMetaOC_shift (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    (BitVec.ofNat 64 (levelMetaOC l) >>> 24) &&& 255#64 = BitVec.ofNat 64 (levelShift l) := by
  interval_cases l <;> decide

theorem levelMetaOC_tagStart (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    BitVec.ofNat 64 (levelMetaOC l) >>> 32 = BitVec.ofNat 64 (levelTagStart l) := by
  interval_cases l <;> decide

theorem levelBodyBytes_bounds (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 23) :
    28 ≤ levelBodyBytes l ∧ levelBodyBytes l ≤ 30 ∧
    levelBodyBytes l + (if levelTailBits l = 0 then 0 else 1) ≤ 30 := by
  interval_cases l <;> decide

theorem levelChain_bounds (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    1 ≤ levelChain l ∧ levelChain l ≤ 16 := by
  interval_cases l <;> decide

theorem levelShift_lt64 (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) :
    levelShift l < 64 := by
  interval_cases l <;> decide

theorem levelTagStart_of_gt1 (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) (hc : levelChain l ≠ 1) :
    2 ≤ levelChain l ∧ levelTagStart l = 256 * l + 1 := by
  interval_cases l <;> first | exact (hc rfl).elim | decide

/-! #### Byte-Level Memory Frame Helpers & `ChainScratchZero` -/

/-- `s2` agrees with `s1` on every byte address outside `[lo, hi)`. -/
def MemEqOutside (s1 s2 : MachineState) (lo hi : Nat) : Prop :=
  ∀ a : Nat, a < 2 ^ 64 → (a < lo ∨ hi ≤ a) →
    s2.getByte (BitVec.ofNat 64 a) = s1.getByte (BitVec.ofNat 64 a)

/-- All read-only input buffers and embedded data (`addr ≥ 4294971392`) are preserved. -/
abbrev HighMemPreserved (s0 s : MachineState) : Prop :=
  MemEqOutside s0 s 0 4294971392

/-- The constant-zero regions of `SCRATCH_CHAIN = 512..608`: middle 32B `[544, 576)` and top 24B `[584, 608)`. -/
def ChainScratchZero (s : MachineState) : Prop :=
  (∀ a, 544 ≤ a → a < 576 → s.getByte (BitVec.ofNat 64 a) = 0#8) ∧
  (∀ a, 584 ≤ a → a < 608 → s.getByte (BitVec.ofNat 64 a) = 0#8)

theorem MemEqOutside.refl (s : MachineState) (lo hi : Nat) : MemEqOutside s s lo hi :=
  fun _ _ _ => rfl

theorem MemEqOutside.of_mem_eq {s1 s2 : MachineState} (h : s2.mem = s1.mem) (lo hi : Nat) :
    MemEqOutside s1 s2 lo hi := by
  intro a _ _
  simp only [MachineState.getByte, MachineState.getMem, h]

theorem MemEqOutside.trans {s1 s2 s3 : MachineState} {lo hi : Nat}
    (h1 : MemEqOutside s1 s2 lo hi) (h2 : MemEqOutside s2 s3 lo hi) :
    MemEqOutside s1 s3 lo hi :=
  fun a ha hout => (h2 a ha hout).trans (h1 a ha hout)

theorem MemEqOutside.mono {s1 s2 : MachineState} {lo1 hi1 lo2 hi2 : Nat}
    (h : MemEqOutside s1 s2 lo1 hi1) (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2) :
    MemEqOutside s1 s2 lo2 hi2 :=
  fun a ha hout => h a ha (by omega)

theorem MemEqOutside.readBuffer_eq {s1 s2 : MachineState} {lo hi addr n : Nat}
    (h : MemEqOutside s1 s2 lo hi) (hbound : addr + n ≤ 2 ^ 64)
    (hdisj : addr + n ≤ lo ∨ hi ≤ addr) :
    readBuffer s2 addr n = readBuffer s1 addr n := by
  apply readBuffer_congr2
  intro j hj
  exact h (addr + j) (by omega) (by omega)

theorem MemEqOutside.getMem_eq {s1 s2 : MachineState} {lo hi addr : Nat}
    (h : MemEqOutside s1 s2 lo hi) (halign : addr % 8 = 0) (hbound : addr + 8 ≤ 2 ^ 64)
    (hdisj : addr + 8 ≤ lo ∨ hi ≤ addr) :
    s2.getMem (BitVec.ofNat 64 addr) = s1.getMem (BitVec.ofNat 64 addr) := by
  rw [← readBuffer_word s2 addr halign, ← readBuffer_word s1 addr halign]
  exact h.readBuffer_eq hbound hdisj

theorem ChainScratchZero.of_mem_eq {s1 s2 : MachineState} (h : ChainScratchZero s1)
    (hm : s2.mem = s1.mem) : ChainScratchZero s2 :=
  ⟨fun a h1 h2 => by simp only [MachineState.getByte, MachineState.getMem, hm]; exact h.1 a h1 h2,
   fun a h1 h2 => by simp only [MachineState.getByte, MachineState.getMem, hm]; exact h.2 a h1 h2⟩

theorem ChainScratchZero.of_outside {s1 s2 : MachineState} {lo hi : Nat}
    (h : ChainScratchZero s1) (hout : MemEqOutside s1 s2 lo hi)
    (hd1 : hi ≤ 544 ∨ 576 ≤ lo) (hd2 : hi ≤ 584 ∨ 608 ≤ lo) :
    ChainScratchZero s2 :=
  ⟨fun a h1 h2 => (hout a (by omega) (by omega)).trans (h.1 a h1 h2),
   fun a h1 h2 => (hout a (by omega) (by omega)).trans (h.2 a h1 h2)⟩

theorem ChainScratchZero.mid_zero {s : MachineState} (h : ChainScratchZero s) :
    readBuffer s 544 32 = 0 :=
  readBuffer_zero_of_bytes s 544 32 (fun j hj => h.1 (544 + j) (by omega) (by omega))

theorem ChainScratchZero.hi_zero {s : MachineState} (h : ChainScratchZero s) :
    readBuffer s 584 24 = 0 :=
  readBuffer_zero_of_bytes s 584 24 (fun j hj => h.2 (584 + j) (by omega) (by omega))

theorem MemEqOutside_setMem (s : MachineState) (addr : Nat) (val : Word)
    (halign : addr % 8 = 0) (hbound : addr + 8 ≤ 2 ^ 64) :
    MemEqOutside s (s.setMem (BitVec.ofNat 64 addr) val) addr (addr + 8) :=
  fun a ha hout => setMem_getByte_ofNat s addr a val halign hbound ha hout

theorem MemEqOutside_setByte (s : MachineState) (addr : Nat) (b : Byte)
    (hbound : addr < 2 ^ 64) :
    MemEqOutside s (s.setByte (BitVec.ofNat 64 addr) b) addr (addr + 1) := by
  intro a ha hout
  rw [set_byte_read]
  have hne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 addr := by
    rw [ne_eq, bv64_eq_iff a addr ha hbound]; omega
  rw [if_neg hne]

theorem MemEqOutside_writeBits_digest (s : MachineState) (addr : Nat) (d : Digest)
    (hbound : addr + 32 ≤ 2 ^ 64) :
    MemEqOutside s (writeBits s (BitVec.ofNat 64 addr) d) addr (addr + 32) := by
  intro a ha hout
  apply write_bits_byte_outside s (BitVec.ofNat 64 addr) (BitVec.ofNat 64 a) d
  intro i hi heq
  rw [bv64_add, bv64_eq_iff a (addr + i) ha (by omega)] at heq
  omega

private theorem extractByte_replaceWord32_hi_zero_lo (w : Word) (k : Nat) (hk : k < 4) :
    extractByte (replaceWord32 w 1 0#32) k = extractByte w k := by
  interval_cases k <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;>
    simp [extractByte, replaceWord32]

private theorem extractByte_replaceWord32_hi_zero_hi (w : Word) (k : Nat) (hk1 : 4 ≤ k) (hk2 : k < 8) :
    extractByte (replaceWord32 w 1 0#32) k = 0#8 := by
  interval_cases k <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;>
    simp [extractByte, replaceWord32]

/-- `SW dst, x0, 28` (for `dst % 8 = 0`) zeroes bytes `[dst+28..dst+32)` and preserves all other bytes. -/
theorem setWord32_zero_hi_inside (s : MachineState) (dst j : Nat)
    (halign : dst % 8 = 0) (hj1 : 28 ≤ j) (hj2 : j < 32) :
    (s.setWord32 (BitVec.ofNat 64 (dst + 28)) 0#32).getByte (BitVec.ofNat 64 (dst + j)) = 0#8 := by
  have hal28 : alignToDword (BitVec.ofNat 64 (dst + 28)) = BitVec.ofNat 64 (dst + 24) := by
    rw [show dst + 28 = (dst + 24) + 4 by omega]
    exact alignToDword_ofNat_eq (dst + 24) 4 (by omega) (by omega)
  have hbo28 : byteOffset (BitVec.ofNat 64 (dst + 28)) = 4 := by
    unfold byteOffset; rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((dst + 28) % 2 ^ 64) &&& (2 ^ 3 - 1) = 4
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
  have halj : alignToDword (BitVec.ofNat 64 (dst + j)) = BitVec.ofNat 64 (dst + 24) := by
    rw [show dst + j = (dst + 24) + (j - 24) by omega]
    exact alignToDword_ofNat_eq (dst + 24) (j - 24) (by omega) (by omega)
  have hboj : byteOffset (BitVec.ofNat 64 (dst + j)) = j - 24 := by
    unfold byteOffset; rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((dst + j) % 2 ^ 64) &&& (2 ^ 3 - 1) = j - 24
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
  simp only [MachineState.setWord32, MachineState.getByte, hal28, hbo28, halj, hboj,
    MachineState.getMem_setMem_eq]
  exact extractByte_replaceWord32_hi_zero_hi _ (j - 24) (by omega) (by omega)

theorem MemEqOutside_setWord32_zero_hi (s : MachineState) (dst : Nat)
    (halign : dst % 8 = 0) (hbound : dst + 32 ≤ 2 ^ 64) :
    MemEqOutside s (s.setWord32 (BitVec.ofNat 64 (dst + 28)) 0#32) (dst + 28) (dst + 32) := by
  intro a ha hout
  have hal28 : alignToDword (BitVec.ofNat 64 (dst + 28)) = BitVec.ofNat 64 (dst + 24) := by
    rw [show dst + 28 = (dst + 24) + 4 by omega]
    exact alignToDword_ofNat_eq (dst + 24) 4 (by omega) (by omega)
  have hbo28 : byteOffset (BitVec.ofNat 64 (dst + 28)) = 4 := by
    unfold byteOffset; rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((dst + 28) % 2 ^ 64) &&& (2 ^ 3 - 1) = 4
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
  have hala : alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (8 * (a / 8)) := by
    have h := alignToDword_ofNat_eq (8 * (a / 8)) (a % 8) (by omega) (by omega)
    simpa only [show 8 * (a / 8) + a % 8 = a by omega] using h
  have hboa : byteOffset (BitVec.ofNat 64 a) = a % 8 := by
    unfold byteOffset; rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (a % 2 ^ 64) &&& (2 ^ 3 - 1) = a % 8
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]
  simp only [MachineState.setWord32, MachineState.getByte, hal28, hbo28, hala]
  by_cases hdw : 8 * (a / 8) = dst + 24
  · rw [hdw, MachineState.getMem_setMem_eq, hboa]
    exact extractByte_replaceWord32_hi_zero_lo _ (a % 8) (by omega)
  · have hne : BitVec.ofNat 64 (8 * (a / 8)) ≠ BitVec.ofNat 64 (dst + 24) := by
      rw [ne_eq, bv64_eq_iff _ _ (by omega) (by omega)]; exact hdw
    rw [MachineState.getMem_setMem_ne hne]

/-! #### Variable-Bit Backward Tail Stream and Two-End Proof Cursor -/

/-- Exact number of backward tail bytes read after consuming `b` total tail bits. -/
def tailBytesBits (b : Nat) : Nat := (b + 7) / 8

/-- Exact number of pending tail bits remaining in `x4` (`cCnt ∈ [0..7]`) after `b` total tail bits. -/
def tailCntBits (b : Nat) : Nat := 8 * tailBytesBits b - b

/-- Little-endian integer value of the first `k` backward bytes read from the end of `proof`. -/
def backBytesNat (s0 : MachineState) (proofLen k : Nat) : Nat :=
  ∑ j ∈ Finset.range k,
    (s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - j)))).toNat * 2 ^ (8 * j)

/-- Exact pending bit-buffer value in `x3` (`cBuf < 2 ^ tailCntBits b`) after `b` total tail bits. -/
def tailBufBits (s0 : MachineState) (proofLen b : Nat) : Nat :=
  backBytesNat s0 proofLen (tailBytesBits b) / 2 ^ b

/-- Exact `tb`-bit tail (`tb < 8`) popped starting at bit offset `b` from the backward tail stream. -/
def tailBitsAt (s0 : MachineState) (proofLen b tb : Nat) : Byte :=
  BitVec.ofNat 8 ((backBytesNat s0 proofLen (tailBytesBits (b + tb)) / 2 ^ b) % 2 ^ tb)

/-- Variable-width digest assembled from `levelBodyBytes l` forward bytes at `fwdAddr`
and (when `levelTailBits l > 0`) `levelTailBits l` tail bits at bit offset `bitOff`. -/
def proofDigestVar (s0 : MachineState) (proofLen fwdAddr bitOff l : Nat) : Digest :=
  let m := levelBodyBytes l
  let tb := levelTailBits l
  BitVec.ofNat (8 * 32)
    (∑ j ∈ Finset.range 32,
      (if j < m then s0.getByte (BitVec.ofNat 64 (fwdAddr + j))
       else if j = m ∧ tb ≠ 0 then tailBitsAt s0 proofLen bitOff tb
       else 0#8).toNat * 2 ^ (8 * j))

theorem tailBytesBits_zero : tailBytesBits 0 = 0 := rfl
theorem tailCntBits_zero : tailCntBits 0 = 0 := rfl

theorem tailCntBits_lt8 (b : Nat) : tailCntBits b < 8 := by
  unfold tailCntBits tailBytesBits; omega

theorem tailBytesBits_le_bits (b : Nat) : b ≤ 8 * tailBytesBits b := by
  unfold tailBytesBits; omega

theorem tailBytesBits_mono {a b : Nat} (h : a ≤ b) : tailBytesBits a ≤ tailBytesBits b := by
  unfold tailBytesBits; omega

theorem tailBytesBits_add_ge (b tb : Nat) (h : tb ≤ tailCntBits b) :
    tailBytesBits (b + tb) = tailBytesBits b ∧ tailCntBits (b + tb) = tailCntBits b - tb := by
  unfold tailCntBits tailBytesBits at *; omega

theorem tailBytesBits_add_lt (b tb : Nat) (hlt : tailCntBits b < tb) (htb : tb < 8) :
    tailBytesBits (b + tb) = tailBytesBits b + 1 ∧ tailCntBits (b + tb) = tailCntBits b + 8 - tb := by
  unfold tailCntBits tailBytesBits at *; omega

theorem backBytesNat_zero (s0 : MachineState) (proofLen : Nat) :
    backBytesNat s0 proofLen 0 = 0 := by
  simp [backBytesNat]

theorem backBytesNat_succ (s0 : MachineState) (proofLen k : Nat) :
    backBytesNat s0 proofLen (k + 1) =
      backBytesNat s0 proofLen k +
        (s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - k)))).toNat * 2 ^ (8 * k) :=
  Finset.sum_range_succ _ k

theorem backBytesNat_lt (s0 : MachineState) (proofLen k : Nat) :
    backBytesNat s0 proofLen k < 2 ^ (8 * k) := by
  induction k with
  | zero => simp [backBytesNat]
  | succ k ih =>
    rw [backBytesNat_succ, Nat.mul_succ, Nat.pow_add]
    have hb : (s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - k)))).toNat ≤ 255 := by
      have := (s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - k)))).isLt; omega
    have hm := Nat.mul_le_mul_right (2 ^ (8 * k)) hb
    have h256 : 2 ^ 8 = 256 := by decide
    rw [h256]
    omega

theorem tailBufBits_zero (s0 : MachineState) (proofLen : Nat) :
    tailBufBits s0 proofLen 0 = 0 := by
  simp [tailBufBits, tailBytesBits_zero, backBytesNat_zero]

theorem tailBufBits_lt (s0 : MachineState) (proofLen b : Nat) :
    tailBufBits s0 proofLen b < 2 ^ tailCntBits b := by
  unfold tailBufBits
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]
  have hle := tailBytesBits_le_bits b
  have hpow : 2 ^ tailCntBits b * 2 ^ b = 2 ^ (8 * tailBytesBits b) := by
    rw [← Nat.pow_add]; congr 1; unfold tailCntBits; omega
  rw [hpow]
  exact backBytesNat_lt s0 proofLen (tailBytesBits b)

theorem tailBufBits_lt256 (s0 : MachineState) (proofLen b : Nat) :
    tailBufBits s0 proofLen b < 256 := by
  have h1 := tailBufBits_lt s0 proofLen b
  have h2 := tailCntBits_lt8 b
  have h3 : 2 ^ tailCntBits b ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 2 ^ 7 = 128 := by decide
  omega

theorem tailStepBits_lt (s0 : MachineState) (proofLen b tb : Nat)
    (hlt : tailCntBits b < tb) (htb : tb < 8) :
    tailBufBits s0 proofLen b +
      (s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits b)))).toNat *
        2 ^ tailCntBits b =
      backBytesNat s0 proofLen (tailBytesBits (b + tb)) / 2 ^ b := by
  have hs := (tailBytesBits_add_lt b tb hlt htb).1
  rw [hs, backBytesNat_succ]
  have hle := tailBytesBits_le_bits b
  have hpow : 2 ^ (8 * tailBytesBits b) = 2 ^ tailCntBits b * 2 ^ b := by
    rw [← Nat.pow_add]; congr 1; unfold tailCntBits; omega
  rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
  rfl

theorem tailStepBits_div (s0 : MachineState) (proofLen b tb : Nat) :
    (backBytesNat s0 proofLen (tailBytesBits (b + tb)) / 2 ^ b) / 2 ^ tb =
      tailBufBits s0 proofLen (b + tb) := by
  unfold tailBufBits
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem tailStepBits_lt32768 (s0 : MachineState) (proofLen b tb : Nat) (htb : tb < 8) :
    backBytesNat s0 proofLen (tailBytesBits (b + tb)) / 2 ^ b < 32768 := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]
  have h1 := backBytesNat_lt s0 proofLen (tailBytesBits (b + tb))
  have hbits : 8 * tailBytesBits (b + tb) ≤ b + 15 := by unfold tailBytesBits; omega
  have h2 : 2 ^ (8 * tailBytesBits (b + tb)) ≤ 2 ^ (b + 15) := Nat.pow_le_pow_right (by decide) hbits
  have h3 : 2 ^ (b + 15) = 32768 * 2 ^ b := by rw [Nat.add_comm, Nat.pow_add]
  omega

theorem proofDigestVar_eq_readBuffer (s s0 : MachineState) (proofLen dst src bitOff l : Nat)
    (hlo : ∀ j < levelBodyBytes l, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (src + j)))
    (hpart : levelTailBits l ≠ 0 →
      s.getByte (BitVec.ofNat 64 (dst + levelBodyBytes l)) = tailBitsAt s0 proofLen bitOff (levelTailBits l))
    (hhi : ∀ j, levelBodyBytes l + (if levelTailBits l = 0 then 0 else 1) ≤ j → j < 32 →
      s.getByte (BitVec.ofNat 64 (dst + j)) = 0#8) :
    readBuffer s dst 32 = proofDigestVar s0 proofLen src bitOff l := by
  unfold readBuffer proofDigestVar
  dsimp only
  apply congrArg (BitVec.ofNat (8 * 32))
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < 32 := Finset.mem_range.mp hj
  by_cases hlt : j < levelBodyBytes l
  · simp only [hlt, ite_true, hlo j hlt]
  · simp only [hlt, ite_false]
    by_cases hp : j = levelBodyBytes l ∧ levelTailBits l ≠ 0
    · rw [if_pos hp, hp.1, hpart hp.2]
    · rw [if_neg hp]
      have hge : levelBodyBytes l + (if levelTailBits l = 0 then 0 else 1) ≤ j := by
        split_ifs with htb <;> omega
      rw [hhi j hge hj']

theorem proofDigestVar_of_bytes_eq (s0 : MachineState) (proofLen src bitOff l : Nat)
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23) (d : Digest)
    (hlo : ∀ j < levelBodyBytes l, s0.getByte (BitVec.ofNat 64 (src + j)) = d.extractLsb' (8 * j) 8)
    (htail : levelTailBits l ≠ 0 →
      tailBitsAt s0 proofLen bitOff (levelTailBits l) =
        BitVec.ofNat 8 (d.extractLsb' (8 * levelBodyBytes l) (levelTailBits l)).toNat) :
    proofDigestVar s0 proofLen src bitOff l = maskLevel l d := by
  have hw_le : levelWidth l ≤ 256 := levelWidth_le_256 l
  have hbyte : ∀ j < 32,
      (if j < levelBodyBytes l then s0.getByte (BitVec.ofNat 64 (src + j))
       else if j = levelBodyBytes l ∧ levelTailBits l ≠ 0 then tailBitsAt s0 proofLen bitOff (levelTailBits l)
       else 0#8) = (maskLevel l d).extractLsb' (8 * j) 8 := by
    intro j hj
    unfold maskLevel
    by_cases hlt : j < levelBodyBytes l
    · rw [if_pos hlt, hlo j hlt]
      exact (maskWidth_byte_lt (levelWidth l) d j hlt).symm
    · rw [if_neg hlt]
      by_cases hp : j = levelBodyBytes l ∧ levelTailBits l ≠ 0
      · rw [if_pos hp, htail hp.2, hp.1]
        exact (maskWidth_byte_partial (levelWidth l) hw_le d).symm
      · rw [if_neg hp]
        have hge : (levelWidth l + 7) / 8 ≤ j := by
          unfold levelBodyBytes at hlt hp
          unfold levelTailBits at hp
          omega
        exact (maskWidth_byte_gt (levelWidth l) d j hge).symm
  unfold proofDigestVar
  dsimp only
  have hsum : ∑ j ∈ Finset.range 32,
        (if j < levelBodyBytes l then s0.getByte (BitVec.ofNat 64 (src + j))
         else if j = levelBodyBytes l ∧ levelTailBits l ≠ 0 then tailBitsAt s0 proofLen bitOff (levelTailBits l)
         else 0#8).toNat * 2 ^ (8 * j) =
      ∑ j ∈ Finset.range 32, ((maskLevel l d).extractLsb' (8 * j) 8).toNat * 2 ^ (8 * j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbyte j (Finset.mem_range.mp hj)]
  rw [hsum]
  have hrec : ∀ (v : BitVec 256),
      BitVec.ofNat (8 * 32) (∑ j ∈ Finset.range 32, (v.extractLsb' (8 * j) 8).toNat * 2 ^ (8 * j)) = v := by
    intro v
    have hmem : ∀ j < 32,
        (writeBits initialMachine 0#64 v).getByte (BitVec.ofNat 64 (0 + j)) = v.extractLsb' (8 * j) 8 := by
      intro j hj
      simpa [Nat.zero_add] using write_bits_byte initialMachine 0#64 v j (by omega) (by decide)
    have hr := read_serialized_slice (writeBits initialMachine 0#64 v) v 0 0 32 (by simpa using hmem)
    rw [readBuffer_congr2 _ _ 0 0 32 (fun _ _ => rfl)] at hr
    unfold readBuffer at hr
    have hsum' : ∑ j ∈ Finset.range 32,
        ((writeBits initialMachine 0#64 v).getByte (BitVec.ofNat 64 (0 + j))).toNat * 2 ^ (8 * j) =
        ∑ j ∈ Finset.range 32, (v.extractLsb' (8 * j) 8).toNat * 2 ^ (8 * j) := by
      apply Finset.sum_congr rfl; intro j hj; rw [hmem j (Finset.mem_range.mp hj)]
    rw [hsum'] at hr
    simpa using hr
  exact hrec (maskLevel l d)

/-- Registers kept constant throughout the per-position loop, cap walk, and epilogue. -/
structure CheckFixedRegs (s : MachineState) : Prop where
  x2  : s.getReg .x2  = BitVec.ofNat 64 68719475728
  x5  : s.getReg .x5  = 0#64
  x11 : s.getReg .x11 = 96#64
  x13 : s.getReg .x13 = 0#64
  x18 : s.getReg .x18 = 4096#64
  x19 : s.getReg .x19 = 8192#64
  x21 : s.getReg .x21 = 256#64
  x26 : s.getReg .x26 = BitVec.ofNat 64 4294971392

def isFixedReg (r : Reg) : Bool :=
  r == .x2 || r == .x5 || r == .x11 || r == .x13 ||
  r == .x18 || r == .x19 || r == .x21 || r == .x26

theorem CheckFixedRegs.of_agree {s1 s2 : MachineState}
    (h : CheckFixedRegs s1)
    (heq : ∀ r : Reg, isFixedReg r = true → s2.getReg r = s1.getReg r) :
    CheckFixedRegs s2 :=
  ⟨(heq .x2 rfl).trans h.x2, (heq .x5 rfl).trans h.x5,
   (heq .x11 rfl).trans h.x11, (heq .x13 rfl).trans h.x13,
   (heq .x18 rfl).trans h.x18, (heq .x19 rfl).trans h.x19,
   (heq .x21 rfl).trans h.x21, (heq .x26 rfl).trans h.x26⟩

theorem isFixedReg_ne_of_false {r r' : Reg} (h : isFixedReg r = true) (hf : isFixedReg r' = false) :
    r ≠ r' := by
  intro heq; subst heq; rw [h] at hf; cases hf

/-- Two-end proof cursor invariant for forward byte offset `pLo` and consumed tail bits `bitOff`. -/
structure ProofCursor (s0 : MachineState) (proofLen pLo bitOff : Nat) (s : MachineState) : Prop where
  le  : pLo + tailBytesBits bitOff ≤ proofLen
  x25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + pLo)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits bitOff))
  x3  : s.getReg .x3  = BitVec.ofNat 64 (tailBufBits s0 proofLen bitOff)
  x4  : s.getReg .x4  = BitVec.ofNat 64 (tailCntBits bitOff)

def isCursorReg (r : Reg) : Bool :=
  r == .x25 || r == .x31 || r == .x3 || r == .x4

theorem ProofCursor.of_agree {s0 s1 s2 : MachineState} {proofLen pLo bitOff : Nat}
    (h : ProofCursor s0 proofLen pLo bitOff s1)
    (heq : ∀ r : Reg, isCursorReg r = true → s2.getReg r = s1.getReg r) :
    ProofCursor s0 proofLen pLo bitOff s2 :=
  ⟨h.le, (heq .x25 rfl).trans h.x25, (heq .x31 rfl).trans h.x31,
   (heq .x3 rfl).trans h.x3, (heq .x4 rfl).trans h.x4⟩

theorem isCursorReg_ne_of_false {r r' : Reg} (h : isCursorReg r = true) (hf : isCursorReg r' = false) :
    r ≠ r' := by
  intro heq; subst heq; rw [h] at hf; cases hf

/-! ### 3. Single-Instruction and Reusable Block Execution Lemmas -/

theorem step_ordinary (oracle : Oracle) (s : MachineState) (idx : Nat) (instr : Instr)
    (hhi : idx < 359) (hpc : s.pc = pcWord idx)
    (hinstr : checkInstr idx = .base instr)
    (hne : Instruction.base instr ≠ .base .ECALL)
    (hstep : ordinaryStep s (.base instr) = some (execInstrBr s instr)) :
    StepsTo oracle s (execInstrBr s instr) 1 0 [] := by
  intro extra
  have hfetch : fetch (submission.image .check) s = some (.base instr) := by
    rw [check_fetch s idx hhi hpc, hinstr]
  have hdet := detExec_succ_other oracle (submission.image .check) extra s (.base instr) hne hfetch
  rw [show 1 + extra = extra + 1 by omega, hdet, hstep]
  simp [Execution.charge]

private theorem readBuffer_toNat_congr (s : MachineState) (src : Nat) {n1 n2 : Nat} (h : n1 = n2) :
    (readBuffer s src n1).toNat = (readBuffer s src n2).toNat := by
  subst h; rfl

private theorem ofNat_toNat_cast {n m : Nat} (h : n = m) (v : BitVec n) :
    BitVec.ofNat m v.toNat = v.cast h := by
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_cast]
  exact Nat.mod_eq_of_lt v.isLt

theorem step_ecall_compress (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (s : MachineState) (idx src dst : Nat)
    (hhi : idx < 359) (hpc : s.pc = pcWord idx)
    (hinstr : checkInstr idx = .base .ECALL)
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src) (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 96 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES) :
    StepsTo oracle s
      (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 96).cast h768.symm))) 1 1
      [((readBuffer s src 96).cast h768.symm, oracle.compression ((readBuffer s src 96).cast h768.symm))] := by
  intro extra
  have hfetch : fetch (submission.image .check) s = some (.base .ECALL) := by
    rw [check_fetch s idx hhi hpc, hinstr]
  have hsrc_lt : src < 2 ^ 64 := by unfold MEMORY_BYTES at hsrc_bd; omega
  have hdst_lt : dst < 2 ^ 64 := by unfold MEMORY_BYTES at hdst_bd; omega
  have hor : oracleInput s = some (.inl ((readBuffer s src 96).cast h768.symm)) := by
    unfold oracleInput
    dsimp only
    have hk : (s.getReg .x13).toNat = 0 := by rw [hx13]; rfl
    have h11 : (s.getReg .x11).toNat = 96 := by rw [hx11]; rfl
    have h10 : (s.getReg .x10).toNat = src := by
      rw [hx10, toNat_ofNat64 src hsrc_lt]
    have h12 : (s.getReg .x12).toNat = dst := by
      rw [hx12, toNat_ofNat64 dst hdst_lt]
    have hib : (COMPRESSION_INPUT_LENGTH + 7) / 8 = 96 := by rw [h768]
    have hib_full :
        (((if (s.getReg .x13).toNat = 0 then COMPRESSION_INPUT_LENGTH else PERMUTATION_WIDTH) + 7) / 8) = 96 := by
      rw [hk]; simp only [ite_true]; exact hib
    have hob : (COMPRESSION_OUTPUT_LENGTH + 7) / 8 = 32 := by rfl
    have hr1 : rangeValid (s.getReg .x10) 96 = true := by rw [hx10]; exact rangeValid_ofNat src 96 hsrc_bd
    have hr2 : rangeValid (s.getReg .x12) 32 = true := by rw [hx12]; exact rangeValid_ofNat dst 32 hdst_bd
    simp only [hk, ite_true, h10]
    rw [readBuffer_toNat_congr s src hib_full]
    simp only [hib, hob, h11, h12, hsrc_al, hdst_al, hr1, hr2, Nat.zero_le, and_self, ite_true]
    exact congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => (some (Sum.inl x) : Option PublicSpec.Domain))
      (ofNat_toNat_cast (show 8 * 96 = COMPRESSION_INPUT_LENGTH by rw [h768]) (readBuffer s src 96))
  have hx5_0 : s.getReg .x5 = 0 := hx5
  have hdet := detExec_succ_ecall oracle (submission.image .check) extra s hfetch
  rw [show 1 + extra = extra + 1 by omega, hdet]
  simp only [hx5_0, ite_true, hor, hx12, Execution.charge, List.cons_append, List.nil_append]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega

theorem halt_accept (oracle : Oracle) (s : MachineState) (hpc : s.pc = pcWord 284) :
    HaltsWith oracle s 3 0 .success [] := by
  refine ⟨by decide, fun extra => ?_⟩
  have s1 : StepsTo oracle s (execInstrBr s (.ADDI .x5 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle s 284 (.ADDI .x5 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let st1 := execInstrBr s (.ADDI .x5 .x0 1#12)
  have hpc1 : st1.pc = pcWord 285 := by
    simp only [st1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have s2 : StepsTo oracle st1 (execInstrBr st1 (.ADDI .x10 .x0 0#12)) 1 0 [] :=
    step_ordinary oracle st1 285 (.ADDI .x10 .x0 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let st2 := execInstrBr st1 (.ADDI .x10 .x0 0#12)
  have hpc2 : st2.pc = pcWord 286 := by
    simp only [st2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have s12 : StepsTo oracle s st2 2 0 [] := by simpa using s1.trans s2
  have h2 := s12 (extra + 1)
  rw [show 3 + extra = 2 + (extra + 1) by omega]
  have hfetch3 : fetch (submission.image .check) st2 = some (.base .ECALL) := by
    rw [check_fetch st2 286 (by decide) hpc2]; rfl
  have hx5 : st2.getReg .x5 = 1#64 := by
    simp only [st2, st1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hx10 : st2.getReg .x10 = 0#64 := by
    simp only [st2, st1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hx5_ne0 : st2.getReg .x5 ≠ 0 := by rw [hx5]; decide
  have hx5_eq1 : st2.getReg .x5 = 1 := by rw [hx5]; decide
  have hx10_eq0 : st2.getReg .x10 = 0 := by rw [hx10]; decide
  have hdet := detExec_succ_ecall oracle (submission.image .check) extra st2 hfetch3
  rw [hdet] at h2
  simp only [hx5_ne0, ite_false, hx5_eq1, ite_true, hx10_eq0,
    Nat.zero_add, List.nil_append] at h2
  exact ⟨h2.1, h2.2.2.1, h2.2.2.2⟩

theorem halt_reject (oracle : Oracle) (s : MachineState) (hpc : s.pc = pcWord 287) :
    HaltsWith oracle s 3 0 .failure [] := by
  refine ⟨by decide, fun extra => ?_⟩
  have s1 : StepsTo oracle s (execInstrBr s (.ADDI .x5 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle s 287 (.ADDI .x5 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let st1 := execInstrBr s (.ADDI .x5 .x0 1#12)
  have hpc1 : st1.pc = pcWord 288 := by
    simp only [st1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have s2 : StepsTo oracle st1 (execInstrBr st1 (.ADDI .x10 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle st1 288 (.ADDI .x10 .x0 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let st2 := execInstrBr st1 (.ADDI .x10 .x0 1#12)
  have hpc2 : st2.pc = pcWord 289 := by
    simp only [st2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have s12 : StepsTo oracle s st2 2 0 [] := by simpa using s1.trans s2
  have h2 := s12 (extra + 1)
  rw [show 3 + extra = 2 + (extra + 1) by omega]
  have hfetch3 : fetch (submission.image .check) st2 = some (.base .ECALL) := by
    rw [check_fetch st2 289 (by decide) hpc2]; rfl
  have hx5 : st2.getReg .x5 = 1#64 := by
    simp only [st2, st1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hx10 : st2.getReg .x10 = 1#64 := by
    simp only [st2, st1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  have hx5_ne0 : st2.getReg .x5 ≠ 0 := by rw [hx5]; decide
  have hx5_eq1 : st2.getReg .x5 = 1 := by rw [hx5]; decide
  have hx10_ne0 : st2.getReg .x10 ≠ 0 := by rw [hx10]; decide
  have hdet := detExec_succ_ecall oracle (submission.image .check) extra st2 hfetch3
  rw [hdet] at h2
  simp only [hx5_ne0, ite_false, hx5_eq1, ite_true, hx10_ne0,
    Nat.zero_add, List.nil_append] at h2
  exact ⟨h2.1, h2.2.2.1, h2.2.2.2⟩

/-! #### Reusable Block Steppers (`copyBytes`, `readVarDigest`, `hashLevelNode`) -/

/-- First 2 instructions of byte-copy loop (`LBU rTmp, 0(x25); SB x12, rTmp, 0`). -/
private theorem step_byte_copy_mem (oracle : Oracle) (base : Nat) (rTmp : Reg)
    (ht0 : rTmp ≠ .x0) (ht12 : rTmp ≠ .x12)
    (hhi : base + 2 ≤ 359)
    (hc0 : checkInstr base = .base (.LBU rTmp .x25 0#12))
    (hc1 : checkInstr (base + 1) = .base (.SB .x12 rTmp 0#12))
    (s : MachineState) (src dst : Nat)
    (hpc : s.pc = pcWord base)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_bd : src + 1 ≤ MEMORY_BYTES) (hdst_bd : dst + 1 ≤ MEMORY_BYTES) :
    ∃ s', StepsTo oracle s s' 2 0 [] ∧
      s'.pc = pcWord (base + 2) ∧
      (∀ r : Reg, r ≠ rTmp → s'.getReg r = s.getReg r) ∧
      s'.getByte (BitVec.ofNat 64 dst) = s.getByte (BitVec.ofNat 64 src) ∧
      MemEqOutside s s' dst (dst + 1) := by
  have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
  have ha0 : s.getReg .x25 + signExtend12 0#12 = BitVec.ofNat 64 src := by
    rw [hsrc, se12_0, BitVec.add_zero]
  have hv0 : memoryArgumentsValid s (.LBU rTmp .x25 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha0]
    exact accessValid_ofNat src 1 (by omega) (by omega)
  have hst0 := step_ordinary oracle s base (.LBU rTmp .x25 0#12) (by omega) hpc hc0 (by intro h; cases h)
    (by simp [ordinaryStep, hv0])
  let s1 := execInstrBr s (.LBU rTmp .x25 0#12)
  have hpc1 : s1.pc = pcWord (base + 1) := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have htmp1 : s1.getReg rTmp = (s.getByte (BitVec.ofNat 64 src)).zeroExtend 64 := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha0]
    exact MachineState.getReg_setReg_eq ht0
  have hreg1 : ∀ r, r ≠ rTmp → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha1 : s1.getReg .x12 + signExtend12 0#12 = BitVec.ofNat 64 dst := by
    rw [hreg1 .x12 ht12.symm, hdst, se12_0, BitVec.add_zero]
  have hv1 : memoryArgumentsValid s1 (.SB .x12 rTmp 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha1]
    exact accessValid_ofNat dst 1 (by omega) (by omega)
  have hst1 := step_ordinary oracle s1 (base + 1) (.SB .x12 rTmp 0#12) (by omega) hpc1 hc1 (by intro h; cases h)
    (by simp [ordinaryStep, hv1])
  let s2 := execInstrBr s1 (.SB .x12 rTmp 0#12)
  have hpc2 : s2.pc = pcWord (base + 2) := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hreg2 : ∀ r, r ≠ rTmp → s2.getReg r = s.getReg r := fun r hr => by
    have : s2.getReg r = s1.getReg r := by
      simp [s2, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    exact this.trans (hreg1 r hr)
  have hs2_byte : ∀ q : Word, s2.getByte q =
      (s.setByte (BitVec.ofNat 64 dst) (s.getByte (BitVec.ofNat 64 src))).getByte q := by
    intro q
    simp only [s2, execInstrBr, ha1, htmp1, truncate8_zeroExtend64,
      MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, mem_setPC, hmem1]
  refine ⟨s2, (hst0.trans hst1).eq_of rfl (by decide) (by decide) (by simp), hpc2, hreg2, ?_, ?_⟩
  · rw [hs2_byte, set_byte_read]; simp
  · intro a ha hout
    rw [hs2_byte]
    exact MemEqOutside_setByte s dst _ (by omega) a ha hout

/-- Next 3 instructions of byte-copy loop (`ADDI x25, 1; ADDI x12, 1; ADDI rCnt, -1`). -/
private theorem step_byte_copy_inc (oracle : Oracle) (base : Nat) (rCnt : Reg)
    (hr0 : rCnt ≠ .x0) (hr12 : rCnt ≠ .x12) (hr25 : rCnt ≠ .x25)
    (hhi : base + 5 ≤ 359)
    (hc2 : checkInstr (base + 2) = .base (.ADDI .x25 .x25 1#12))
    (hc3 : checkInstr (base + 3) = .base (.ADDI .x12 .x12 1#12))
    (hc4 : checkInstr (base + 4) = .base (.ADDI rCnt rCnt 4095#12))
    (s : MachineState) (src dst k : Nat)
    (hpc : s.pc = pcWord (base + 2))
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hcnt : s.getReg rCnt = BitVec.ofNat 64 (k + 1)) :
    ∃ s', StepsTo oracle s s' 3 0 [] ∧
      s'.pc = pcWord (base + 5) ∧
      s'.getReg .x25 = BitVec.ofNat 64 (src + 1) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (dst + 1) ∧
      s'.getReg rCnt = BitVec.ofNat 64 k ∧
      (∀ r : Reg, r ≠ .x12 → r ≠ .x25 → r ≠ rCnt → s'.getReg r = s.getReg r) ∧
      s'.mem = s.mem := by
  have hst2 := step_ordinary oracle s (base + 2) (.ADDI .x25 .x25 1#12) (by omega) hpc hc2 (by intro h; cases h) rfl
  let s3 := execInstrBr s (.ADDI .x25 .x25 1#12)
  have hpc3 : s3.pc = pcWord (base + 3) := by simp only [s3, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst3 := step_ordinary oracle s3 (base + 3) (.ADDI .x12 .x12 1#12) (by omega) hpc3 hc3 (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.ADDI .x12 .x12 1#12)
  have hpc4 : s4.pc = pcWord (base + 4) := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hst4 := step_ordinary oracle s4 (base + 4) (.ADDI rCnt rCnt 4095#12) (by omega) hpc4 hc4 (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.ADDI rCnt rCnt 4095#12)
  have hpc5 : s5.pc = pcWord (base + 5) := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simp [s5, s4, s3, execInstrBr, mem_setPC, mem_setReg]
  have hx25_5 : s5.getReg .x25 = BitVec.ofNat 64 (src + 1) := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr25, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x25), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hsrc, se12_1]
    exact bv64_add src 1
  have hx12_5 : s5.getReg .x12 = BitVec.ofNat 64 (dst + 1) := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr12, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x12),
      hdst, se12_1]
    exact bv64_add dst 1
  have hcnt_5 : s5.getReg rCnt = BitVec.ofNat 64 k := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq hr0,
      MachineState.getReg_setReg_ne _ _ _ _ hr12.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ hr25.symm, hcnt]
    exact bv64_add_neg1 k
  have hreg5 : ∀ r, r ≠ .x12 → r ≠ .x25 → r ≠ rCnt → s5.getReg r = s.getReg r :=
    fun r h12 h25 hrc => by
      simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hrc.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h25.symm]
  exact ⟨s5, ((hst2.trans hst3).trans hst4).eq_of rfl (by decide) (by decide) (by simp),
    hpc5, hx25_5, hx12_5, hcnt_5, hreg5, hmem5⟩

private theorem ordinaryStep_BNE_base (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    ordinaryStep st (.base (.BNE r1 r2 off)) = some (execInstrBr st (.BNE r1 r2 off)) := rfl

private theorem execInstrBr_BNE_mem_base (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    (execInstrBr st (.BNE r1 r2 off)).mem = st.mem := by
  simp only [execInstrBr]; split <;> rfl

private theorem execInstrBr_BNE_getReg_base (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr st (.BNE r1 r2 off)).getReg r = st.getReg r := by
  simp only [execInstrBr]; split <;> simp only [MachineState.getReg_setPC]

private theorem execInstrBr_BNE_pc_false_base (st : MachineState) (r1 r2 : Reg) (off : BitVec 13)
    (h : (st.getReg r1 != st.getReg r2) = false) :
    (execInstrBr st (.BNE r1 r2 off)).pc = st.pc + (4 : Word) := by
  simp only [execInstrBr, h, Bool.false_eq_true, ite_false, MachineState.setPC]

private theorem execInstrBr_BNE_pc_true_base (st : MachineState) (r1 r2 : Reg) (off : BitVec 13)
    (h : (st.getReg r1 != st.getReg r2) = true) :
    (execInstrBr st (.BNE r1 r2 off)).pc = st.pc + signExtend13 off := by
  simp only [execInstrBr, h, ite_true, MachineState.setPC]

private theorem step_byte_copy_bne (oracle : Oracle) (base : Nat) (rCnt : Reg)
    (hhi : base + 6 ≤ 359)
    (hc5 : checkInstr (base + 5) = .base (.BNE rCnt .x0 8172#13))
    (s5 : MachineState) (k : Nat) (hk : k < 2 ^ 64)
    (hpc5 : s5.pc = pcWord (base + 5))
    (hcnt5 : s5.getReg rCnt = BitVec.ofNat 64 k) :
    ∃ s6, StepsTo oracle s5 s6 1 0 [] ∧
      s6.pc = (if k = 0 then pcWord (base + 6) else pcWord base) ∧
      (∀ r, s6.getReg r = s5.getReg r) ∧
      s6.mem = s5.mem := by
  have hst5 := step_ordinary oracle s5 (base + 5) (.BNE rCnt .x0 8172#13) (by omega) hpc5 hc5
    (by intro h; cases h) (ordinaryStep_BNE_base s5 rCnt .x0 8172#13)
  refine ⟨execInstrBr s5 (.BNE rCnt .x0 8172#13), hst5, ?_,
    execInstrBr_BNE_getReg_base s5 rCnt .x0 8172#13,
    execInstrBr_BNE_mem_base s5 rCnt .x0 8172#13⟩
  cases k with
  | zero =>
    have hne_f : (s5.getReg rCnt != s5.getReg .x0) = false := by
      rw [hcnt5, getReg_x0]
      exact (bv64_bne_eq 0 0 (by omega) (by omega)).trans (by decide)
    rw [ite_eq_left_iff.mpr (fun hn => (hn rfl).elim),
      execInstrBr_BNE_pc_false_base s5 rCnt .x0 8172#13 hne_f, hpc5, pcWord_add_four]
  | succ m =>
    have hne_b : (s5.getReg rCnt != s5.getReg .x0) = true := by
      rw [hcnt5, getReg_x0]
      exact (bv64_bne_eq (m + 1) 0 (by omega) (by omega)).trans (decide_eq_true (by omega))
    rw [ite_eq_right_iff.mpr (fun h => (Nat.succ_ne_zero m h).elim),
      execInstrBr_BNE_pc_true_base s5 rCnt .x0 8172#13 hne_b, hpc5, pcWord_sub_20]

/-- Generic `n`-byte copy loop parameterized by temporary register `rTmp` and counter `rCnt`. -/
theorem step_byte_copy_loop (oracle : Oracle) (base : Nat) (rTmp rCnt : Reg)
    (ht0 : rTmp ≠ .x0) (ht12 : rTmp ≠ .x12) (ht25 : rTmp ≠ .x25)
    (hr0 : rCnt ≠ .x0) (hrTmp : rCnt ≠ rTmp) (hr12 : rCnt ≠ .x12) (hr25 : rCnt ≠ .x25)
    (hhi : base + 6 ≤ 359)
    (hc0 : checkInstr base = .base (.LBU rTmp .x25 0#12))
    (hc1 : checkInstr (base + 1) = .base (.SB .x12 rTmp 0#12))
    (hc2 : checkInstr (base + 2) = .base (.ADDI .x25 .x25 1#12))
    (hc3 : checkInstr (base + 3) = .base (.ADDI .x12 .x12 1#12))
    (hc4 : checkInstr (base + 4) = .base (.ADDI rCnt rCnt 4095#12))
    (hc5 : checkInstr (base + 5) = .base (.BNE rCnt .x0 8172#13))
    (n : Nat) (hn : 0 < n) (hn_lt : n < 2 ^ 64)
    (s : MachineState) (src dst : Nat)
    (hpc : s.pc = pcWord base)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hcnt : s.getReg rCnt = BitVec.ofNat 64 n)
    (hsrc_bd : src + n ≤ MEMORY_BYTES) (hdst_bd : dst + n ≤ MEMORY_BYTES)
    (hdisj : dst + n ≤ src ∨ src + n ≤ dst) :
    ∃ s', StepsTo oracle s s' (6 * n) 0 [] ∧
      s'.pc = pcWord (base + 6) ∧
      s'.getReg .x25 = BitVec.ofNat 64 (src + n) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (dst + n) ∧
      s'.getReg rCnt = 0#64 ∧
      (∀ r : Reg, r ≠ rTmp → r ≠ .x12 → r ≠ .x25 → r ≠ rCnt → s'.getReg r = s.getReg r) ∧
      (∀ j < n, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + n) := by
  have hmb : MEMORY_BYTES = 2 ^ 36 := rfl
  induction n generalizing s src dst with
  | zero => omega
  | succ k ih =>
    obtain ⟨s2, hs2, hpc2, hreg2, hcopy2, hout2⟩ :=
      step_byte_copy_mem oracle base rTmp ht0 ht12 (by omega) hc0 hc1 s src dst hpc hsrc hdst (by omega) (by omega)
    obtain ⟨s5, hs5, hpc5, hx25_5, hx12_5, hcnt_5, hreg5, hmem5⟩ :=
      step_byte_copy_inc oracle base rCnt hr0 hr12 hr25 (by omega) hc2 hc3 hc4 s2 src dst k hpc2
        ((hreg2 .x25 ht25.symm).trans hsrc) ((hreg2 .x12 ht12.symm).trans hdst)
        ((hreg2 rCnt hrTmp).trans hcnt)
    obtain ⟨s6, hst5, hpc6_if, hreg6, hmem6'⟩ :=
      step_byte_copy_bne oracle base rCnt hhi hc5 s5 k (by omega) hpc5 hcnt_5
    have hmem6 : s6.mem = s2.mem := hmem6'.trans hmem5
    have h16 : StepsTo oracle s s6 6 0 [] :=
      ((hs2.trans hs5).trans hst5).eq_of rfl (by decide) (by decide) (by simp)
    cases k with
    | zero =>
      have hpc6 : s6.pc = pcWord (base + 6) := by simpa only [ite_true] using hpc6_if
      refine ⟨s6, h16, hpc6, (hreg6 .x25).trans hx25_5, (hreg6 .x12).trans hx12_5,
        (hreg6 rCnt).trans hcnt_5,
        fun r htmp h12 h25 hrc => (hreg6 r).trans ((hreg5 r h12 h25 hrc).trans (hreg2 r htmp)),
        ?_, hout2.trans (MemEqOutside.of_mem_eq hmem6 dst (dst + 1))⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [Nat.add_zero, MachineState.getByte, MachineState.getMem, hmem6]
      exact hcopy2
    | succ m =>
      have hpc6 : s6.pc = pcWord base := by simpa only [Nat.succ_ne_zero, ite_false] using hpc6_if
      obtain ⟨sFin, hsFin, hpcFin, hx25Fin, hx12Fin, hcntFin, hregFin, hcopyFin, houtFin⟩ :=
        ih (by omega) (by omega) s6 (src + 1) (dst + 1) hpc6
          ((hreg6 .x25).trans hx25_5) ((hreg6 .x12).trans hx12_5) ((hreg6 rCnt).trans hcnt_5)
          (by omega) (by omega) (by omega)
      have hout_s6 : MemEqOutside s s6 dst (dst + 1) :=
        hout2.trans (MemEqOutside.of_mem_eq hmem6 dst (dst + 1))
      refine ⟨sFin, ?_, hpcFin, ?_, ?_, hcntFin, ?_, ?_, ?_⟩
      · exact (h16.trans hsFin).eq_of rfl (by omega) (by decide) (by simp)
      · rw [hx25Fin]; congr 1; omega
      · rw [hx12Fin]; congr 1; omega
      · intro r htmp h12 h25 hrc
        exact (hregFin r htmp h12 h25 hrc).trans ((hreg6 r).trans ((hreg5 r h12 h25 hrc).trans (hreg2 r htmp)))
      · intro j hj
        cases j with
        | zero =>
          rw [Nat.add_zero, Nat.add_zero, houtFin dst (by omega) (by omega)]
          simp only [MachineState.getByte, MachineState.getMem, hmem6]
          exact hcopy2
        | succ j' =>
          have h1 := hcopyFin j' (by omega)
          rw [show dst + (j' + 1) = dst + 1 + j' by omega,
            show src + (j' + 1) = src + 1 + j' by omega, h1]
          exact hout_s6 (src + 1 + j') (by omega) (by omega)
      · exact (hout_s6.mono (by omega) (by omega)).trans (houtFin.mono (by omega) (by omega))

/-- Call and return from `chk_read_n` (`pc[290..296]`), `6 * n + 1` steps (`n > 0`). -/
theorem step_chk_read_n (oracle : Oracle) (s : MachineState) (retIdx n src dst : Nat)
    (hn : 0 < n) (hn_lt : n < 2 ^ 64)
    (hpc : s.pc = pcWord 290) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 359)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src) (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hcnt : s.getReg .x10 = BitVec.ofNat 64 n)
    (hsrc_bd : src + n ≤ MEMORY_BYTES) (hdst_bd : dst + n ≤ MEMORY_BYTES)
    (hdisj : dst + n ≤ src ∨ src + n ≤ dst) :
    ∃ s', StepsTo oracle s s' (6 * n + 1) 0 [] ∧
      s'.pc = pcWord retIdx ∧
      s'.getReg .x25 = BitVec.ofNat 64 (src + n) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      (∀ j < n, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + n) := by
  obtain ⟨s1, hs1, hpc1, hx25_1, _, _, hreg1, hcopy1, hout1⟩ :=
    step_byte_copy_loop oracle 290 .x6 .x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl n hn hn_lt s src dst hpc hsrc hdst hcnt
      hsrc_bd hdst_bd hdisj
  have hst := step_ordinary oracle s1 296 (.JALR .x0 .x1 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.JALR .x0 .x1 0#12)
  have hmem2 : s2.mem = s1.mem := by simp [s2, execInstrBr, MachineState.setReg, mem_setPC]
  have hreg2 : ∀ r, s2.getReg r = s1.getReg r := fun r => by
    simp [s2, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
  refine ⟨s2, (hs1.trans hst).eq_of rfl (by omega) (by decide) (by simp), ?_,
    (hreg2 .x25).trans hx25_1,
    fun r h6 h10 h12 h25 => (hreg2 r).trans (hreg1 r h6 h12 h25 h10),
    fun j hj => by simp only [MachineState.getByte, MachineState.getMem, hmem2]; exact hcopy1 j hj,
    hout1.trans (MemEqOutside.of_mem_eq hmem2 dst (dst + n))⟩
  simp only [s2, execInstrBr, MachineState.setPC, hreg1 .x1 (by decide) (by decide) (by decide) (by decide), hret]
  exact jalr_pcWord retIdx (by omega)

/-- Helper: `ADDI .x10 .x0 n; JAL .x1` to `chk_read_n` (`pc[290]`), `6 * n + 3` steps. -/
theorem step_call_read_n (oracle : Oracle) (idx n : Nat) (s : MachineState) (src dst : Nat)
    (hn : 0 < n) (hn_lt : n < 2048) (hhi : idx + 2 ≤ 290)
    (haddi : checkInstr idx = .base (.ADDI .x10 .x0 (BitVec.ofNat 12 n)))
    (hjal : checkInstr (idx + 1) = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (290 - (idx + 1))))))
    (hpc : s.pc = pcWord idx)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_bd : src + n ≤ MEMORY_BYTES) (hdst_bd : dst + n ≤ MEMORY_BYTES)
    (hdisj : dst + n ≤ src ∨ src + n ≤ dst) :
    ∃ s', StepsTo oracle s s' (6 * n + 3) 0 [] ∧
      s'.pc = pcWord (idx + 2) ∧
      s'.getReg .x25 = BitVec.ofNat 64 (src + n) ∧
      (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      (∀ j < n, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + n) := by
  have hst0 := step_ordinary oracle s idx (.ADDI .x10 .x0 (BitVec.ofNat 12 n)) (by omega) hpc haddi (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x10 .x0 (BitVec.ofNat 12 n))
  have hpc1 : s1.pc = pcWord (idx + 1) := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx10_1 : s1.getReg .x10 = BitVec.ofNat 64 n := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_x0]
    rw [MachineState.getReg_setReg_eq (by decide), signExtend12_ofNat_lt2048 n hn_lt, BitVec.zero_add]
  have hreg1 : ∀ r, r ≠ .x10 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  let off := BitVec.ofNat 21 (4 * (290 - (idx + 1)))
  have hst1 := step_ordinary oracle s1 (idx + 1) (.JAL .x1 off) (by omega) hpc1 hjal (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.JAL .x1 off)
  have hpc2 : s2.pc = pcWord 290 := by
    simp only [s2, execInstrBr, MachineState.setPC, hpc1]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (290 - (idx + 1))) :=
      signExtend21_ofNat_lt _ (by omega)
    rw [hse21, pcWord, bv64_add]; congr 1; omega
  have hret2 : s2.getReg .x1 = pcWord (idx + 2) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, hpc1, pcWord_add_four]
    exact MachineState.getReg_setReg_eq (by decide)
  have hreg2 : ∀ r, r ≠ .x1 → s2.getReg r = s1.getReg r := fun r hr => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  obtain ⟨s3, hs3, hpc3, hx25_3, hreg3, hcopy3, hout3⟩ :=
    step_chk_read_n oracle s2 (idx + 2) n src dst hn (by omega) hpc2 hret2 (by omega)
      ((hreg2 .x25 (by decide)).trans ((hreg1 .x25 (by decide)).trans hsrc))
      ((hreg2 .x12 (by decide)).trans ((hreg1 .x12 (by decide)).trans hdst))
      ((hreg2 .x10 (by decide)).trans hx10_1) hsrc_bd hdst_bd hdisj
  refine ⟨s3, ?_, hpc3, hx25_3, ?_, ?_, ?_⟩
  · exact ((hst0.trans hst1).trans hs3).eq_of rfl (by omega) (by decide) (by simp)
  · intro r h1 h6 h10 h12 h25
    exact (hreg3 r h6 h10 h12 h25).trans ((hreg2 r h1).trans (hreg1 r h10))
  · intro j hj
    have hb := hcopy3 j hj
    simp only [MachineState.getByte, MachineState.getMem, hmem2] at hb ⊢
    exact hb
  · exact (MemEqOutside.of_mem_eq hmem2 dst (dst + n)).trans hout3

/-- Backward byte load + shift-OR refill (`pc[312..316]`, 5 steps) when `tailCntBits bitOff < tb < 8`. -/
private theorem step_var_load_backbyte (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (hplen : proofLen ≤ proofCap) (s : MachineState) (bitOff tb : Nat)
    (hlt : tailCntBits bitOff < tb) (htb : tb < 8) (htb_le : tailBytesBits (bitOff + tb) ≤ proofLen)
    (hpc : s.pc = pcWord 312)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits bitOff)))
    (hx3  : s.getReg .x3  = BitVec.ofNat 64 (tailBufBits s0 proofLen bitOff))
    (hx4  : s.getReg .x4  = BitVec.ofNat 64 (tailCntBits bitOff))
    (hhigh : HighMemPreserved s0 s) :
    ∃ s', StepsTo oracle s s' 5 0 [] ∧
      s'.pc = pcWord 317 ∧
      s'.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits (bitOff + tb))) ∧
      s'.getReg .x3  = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytesBits (bitOff + tb)) / 2 ^ bitOff) ∧
      s'.getReg .x4  = BitVec.ofNat 64 (tailCntBits (bitOff + tb) + tb) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x9 → r ≠ .x31 → s'.getReg r = s.getReg r) ∧
      s'.mem = s.mem := by
  have hplen_bd : proofLen ≤ 8556390424 := hplen
  obtain ⟨htb_s, htc_s⟩ := tailBytesBits_add_lt bitOff tb hlt htb
  have hst0 := step_ordinary oracle s 312 (.ADDI .x31 .x31 4095#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x31 .x31 4095#12)
  have hpc1 : s1.pc = pcWord 313 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits (bitOff + tb))) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx31,
      show 11341403200 + (proofLen - tailBytesBits bitOff) =
        (11341403200 + (proofLen - tailBytesBits (bitOff + tb))) + 1 by omega]
    exact bv64_add_neg1 _
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha1 : s1.getReg .x31 + signExtend12 0#12 =
      BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits bitOff)) := by
    rw [hx31_1, se12_0, BitVec.add_zero]; congr 1; omega
  have hv1 : memoryArgumentsValid s1 (.LBU .x9 .x31 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha1]
    exact accessValid_ofNat _ 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst1 := step_ordinary oracle s1 313 (.LBU .x9 .x31 0#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv1])
  let s2 := execInstrBr s1 (.LBU .x9 .x31 0#12)
  have hpc2 : s2.pc = pcWord 314 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = s.mem := by simp [s2, execInstrBr, mem_setPC, mem_setReg, hmem1]
  have hx31_2 : s2.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits (bitOff + tb))) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x31), hx31_1]
  let bk := (s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits bitOff)))).toNat
  have hbk_lt : bk < 256 := (s0.getByte _).isLt
  have hx9_2 : s2.getReg .x9 = BitVec.ofNat 64 bk := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, ha1]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb_eq : s1.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits bitOff))) =
        s0.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits bitOff))) := by
      have : s1.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits bitOff))) =
          s.getByte (BitVec.ofNat 64 (11341403200 + (proofLen - 1 - tailBytesBits bitOff))) := by
        simp [MachineState.getByte, MachineState.getMem, hmem1]
      rw [this]; exact hhigh _ (by omega) (by omega)
    rw [hb_eq]
    apply BitVec.eq_of_toNat_eq
    simp [bk, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hreg2 : ∀ r, r ≠ .x9 → r ≠ .x31 → s2.getReg r = s.getReg r := fun r h9 h31 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h31.symm]
  have hst2 := step_ordinary oracle s2 314 (.SLL .x9 .x9 .x4) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.SLL .x9 .x9 .x4)
  have hpc3 : s3.pc = pcWord 315 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hst3 := step_ordinary oracle s3 315 (.OR .x3 .x3 .x9) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.OR .x3 .x3 .x9)
  have hpc4 : s4.pc = pcWord 316 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hst4 := step_ordinary oracle s4 316 (.ADDI .x4 .x4 8#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.ADDI .x4 .x4 8#12)
  have hpc5 : s5.pc = pcWord 317 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simp [s5, s4, s3, execInstrBr, mem_setPC, mem_setReg, hmem2]
  have hx4_2 : s2.getReg .x4 = BitVec.ofNat 64 (tailCntBits bitOff) := (hreg2 .x4 (by decide) (by decide)).trans hx4
  have hx3_2 : s2.getReg .x3 = BitVec.ofNat 64 (tailBufBits s0 proofLen bitOff) := (hreg2 .x3 (by decide) (by decide)).trans hx3
  have hx9_3 : s3.getReg .x9 = BitVec.ofNat 64 (bk * 2 ^ tailCntBits bitOff) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx9_2, hx4_2,
      toNat_ofNat64 (tailCntBits bitOff) (by omega), Nat.mod_eq_of_lt (by omega : tailCntBits bitOff < 64),
      bv64_shl bk (tailCntBits bitOff) (by omega)]
  have hx3_3 : s3.getReg .x3 = BitVec.ofNat 64 (tailBufBits s0 proofLen bitOff) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x3), hx3_2]
  have hx3_5 : s5.getReg .x3 = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytesBits (bitOff + tb)) / 2 ^ bitOff) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x3), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hx3_3, hx9_3]
    have hpow7 : 2 ^ tailCntBits bitOff ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
    have h64 : 2 ^ 6 = 64 := by decide
    have htb_lt := tailBufBits_lt s0 proofLen bitOff
    have hsum_lt : tailBufBits s0 proofLen bitOff + bk * 2 ^ tailCntBits bitOff < 2 ^ 64 := by
      have : bk * 2 ^ tailCntBits bitOff ≤ 255 * 64 := Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [bv64_or_shift_eq_add _ bk (tailCntBits bitOff) htb_lt hsum_lt]
    exact congrArg (BitVec.ofNat 64) (tailStepBits_lt s0 proofLen bitOff tb hlt htb)
  have hx4_5 : s5.getReg .x4 = BitVec.ofNat 64 (tailCntBits (bitOff + tb) + tb) := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x4), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x4), hx4_2, se12_8, bv64_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx31_5 : s5.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits (bitOff + tb))) := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x31), hx31_2]
  have hreg5 : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x9 → r ≠ .x31 → s5.getReg r = s.getReg r :=
    fun r h3 h4 h9 h31 => by
      simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h4.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h3.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm]
      exact hreg2 r h9 h31
  exact ⟨s5, ((hst0.trans hst1).trans ((hst2.trans hst3).trans hst4)).eq_of rfl (by decide) (by decide) (by simp),
    hpc5, hx31_5, hx3_5, hx4_5, hreg5, hmem5⟩

/-- Variable-width tail pop + byte store + return (`pc[317..324]`, 8 steps) when `0 < tb < 8`. -/
private theorem step_var_pop_tail (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (s : MachineState) (retIdx pLo bitOff dst l : Nat)
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23) (htb_pos : levelTailBits l ≠ 0)
    (hpc : s.pc = pcWord 317) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 359)
    (hle_next : pLo + levelBodyBytes l + tailBytesBits (bitOff + levelTailBits l) ≤ proofLen)
    (hx7  : s.getReg .x7  = BitVec.ofNat 64 (levelTailBits l))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + (pLo + levelBodyBytes l)))
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits (bitOff + levelTailBits l))))
    (hx3  : s.getReg .x3  = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytesBits (bitOff + levelTailBits l)) / 2 ^ bitOff))
    (hx4  : s.getReg .x4  = BitVec.ofNat 64 (tailCntBits (bitOff + levelTailBits l) + levelTailBits l))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (dst + levelBodyBytes l))
    (hdst_hi : dst + 32 ≤ 4294971392)
    (hlo : ∀ j < levelBodyBytes l, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (11341403200 + pLo + j)))
    (hhi : ∀ j, levelBodyBytes l + 1 ≤ j → j < 32 → s.getByte (BitVec.ofNat 64 (dst + j)) = 0#8) :
    ∃ s', StepsTo oracle s s' 8 0 [] ∧
      s'.pc = pcWord retIdx ∧
      ProofCursor s0 proofLen (pLo + levelBodyBytes l) (bitOff + levelTailBits l) s' ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x9 → s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = proofDigestVar s0 proofLen (11341403200 + pLo) bitOff l ∧
      MemEqOutside s s' (dst + levelBodyBytes l) (dst + levelBodyBytes l + 1) := by
  let tb := levelTailBits l
  let m := levelBodyBytes l
  have htb_lt : tb < 8 := levelTailBits_lt_8 l
  have hm_bd := levelBodyBytes_bounds l hl1 hl2
  let curBits := backBytesNat s0 proofLen (tailBytesBits (bitOff + tb)) / 2 ^ bitOff
  have hcb_lt : curBits < 32768 := tailStepBits_lt32768 s0 proofLen bitOff tb htb_lt
  have hpow_le : 2 ^ tb ≤ 128 := by
    have h1 : 2 ^ tb ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  have hpow_pos : 0 < 2 ^ tb := Nat.pow_pos (by decide)
  -- pc[317..322]: 6 ALU instructions
  have hst0 := step_ordinary oracle s 317 (.ADDI .x9 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x9 .x0 1#12)
  have hpc1 : s1.pc = pcWord 318 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst1 := step_ordinary oracle s1 318 (.SLL .x9 .x9 .x7) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.SLL .x9 .x9 .x7)
  have hpc2 : s2.pc = pcWord 319 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hst2 := step_ordinary oracle s2 319 (.ADDI .x9 .x9 4095#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADDI .x9 .x9 4095#12)
  have hpc3 : s3.pc = pcWord 320 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hst3 := step_ordinary oracle s3 320 (.AND .x9 .x3 .x9) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.AND .x9 .x3 .x9)
  have hpc4 : s4.pc = pcWord 321 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hst4 := step_ordinary oracle s4 321 (.SRL .x3 .x3 .x7) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.SRL .x3 .x3 .x7)
  have hpc5 : s5.pc = pcWord 322 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hst5 := step_ordinary oracle s5 322 (.SUB .x4 .x4 .x7) (by decide) hpc5 rfl (by intro h; cases h) rfl
  let s6 := execInstrBr s5 (.SUB .x4 .x4 .x7)
  have hpc6 : s6.pc = pcWord 323 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
  have hmem6 : s6.mem = s.mem := by simp [s6, s5, s4, s3, s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg_s1 : ∀ r, r ≠ .x9 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hx9_1 : s1.getReg .x9 = BitVec.ofNat 64 1 := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_x0]
    rw [MachineState.getReg_setReg_eq (by decide), se12_1]; decide
  have hx9_2 : s2.getReg .x9 = BitVec.ofNat 64 (2 ^ tb) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx9_1, hreg_s1 .x7 (by decide), hx7,
      toNat_ofNat64 tb (by omega), Nat.mod_eq_of_lt (by omega : tb < 64), bv64_shl 1 tb (by decide), Nat.one_mul]
  have hx9_3 : s3.getReg .x9 = BitVec.ofNat 64 (2 ^ tb - 1) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx9_2,
      show 2 ^ tb = (2 ^ tb - 1) + 1 by omega]
    exact bv64_add_neg1 _
  have hreg_s3 : ∀ r, r ≠ .x9 → s3.getReg r = s.getReg r := fun r hr => by
    simp only [s3, s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ hr.symm, hreg_s1 r hr]
  have hx9_4 : s4.getReg .x9 = BitVec.ofNat 64 (curBits % 2 ^ tb) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hreg_s3 .x3 (by decide), hx3, hx9_3]
    exact bv64_and_pow_sub1 curBits tb (by omega) (by omega)
  have hreg_s4 : ∀ r, r ≠ .x9 → s4.getReg r = s.getReg r := fun r hr => by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, hreg_s3 r hr]
  have hx3_5 : s5.getReg .x3 = BitVec.ofNat 64 (tailBufBits s0 proofLen (bitOff + tb)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hreg_s4 .x3 (by decide), hx3,
      hreg_s4 .x7 (by decide), hx7, toNat_ofNat64 tb (by omega), Nat.mod_eq_of_lt (by omega : tb < 64),
      bv64_shr curBits tb (by omega)]
    exact congrArg (BitVec.ofNat 64) (tailStepBits_div s0 proofLen bitOff tb)
  have hx9_6 : s6.getReg .x9 = BitVec.ofNat 64 (curBits % 2 ^ tb) := by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x9), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x9), hx9_4]
  have hx3_6 : s6.getReg .x3 = BitVec.ofNat 64 (tailBufBits s0 proofLen (bitOff + tb)) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x3), hx3_5]
  have hx4_6 : s6.getReg .x4 = BitVec.ofNat 64 (tailCntBits (bitOff + tb)) := by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x4),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x7),
      hreg_s4 .x4 (by decide), hreg_s4 .x7 (by decide), hx4, hx7]
    have hlt8 := tailCntBits_lt8 (bitOff + tb)
    change BitVec.ofNat 64 (tailCntBits (bitOff + tb) + tb) - BitVec.ofNat 64 tb = _
    rw [bv64_sub _ tb (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hreg6 : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x9 → s6.getReg r = s.getReg r := fun r h3 h4 h9 => by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h4.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h3.symm, hreg_s4 r h9]
  -- pc[323]: SB x12, x9, 0
  have ha6 : s6.getReg .x12 + signExtend12 0#12 = BitVec.ofNat 64 (dst + m) := by
    rw [hreg6 .x12 (by decide) (by decide) (by decide), hx12, se12_0, BitVec.add_zero]
  have hv6 : memoryArgumentsValid s6 (.SB .x12 .x9 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha6]
    exact accessValid_ofNat (dst + m) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst6 := step_ordinary oracle s6 323 (.SB .x12 .x9 0#12) (by decide) hpc6 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv6])
  let s7 := execInstrBr s6 (.SB .x12 .x9 0#12)
  have hpc7 : s7.pc = pcWord 324 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
  have hreg7 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
    simp [s7, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
  -- pc[324]: JALR x0, x1, 0
  have hst7 := step_ordinary oracle s7 324 (.JALR .x0 .x1 0#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
  let s8 := execInstrBr s7 (.JALR .x0 .x1 0#12)
  have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, MachineState.setReg, mem_setPC]
  have hreg8 : ∀ r, s8.getReg r = s6.getReg r := fun r => by
    have : s8.getReg r = s7.getReg r := by simp [s8, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
    exact this.trans (hreg7 r)
  have hs8_byte : ∀ q : Word, s8.getByte q =
      (s.setByte (BitVec.ofNat 64 (dst + m)) (tailBitsAt s0 proofLen bitOff tb)).getByte q := by
    intro q
    have htr : (s6.getReg .x9).truncate 8 = tailBitsAt s0 proofLen bitOff tb := by
      rw [hx9_6, truncate8_ofNat64 (curBits % 2 ^ tb) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpow_pos) (by omega))]
      rfl
    simp only [MachineState.getByte, MachineState.getMem, hmem8]
    simp only [s7, execInstrBr, ha6, htr, MachineState.setByte, MachineState.getMem, MachineState.setMem,
      mem_setPC, hmem6]
  have hout_all : MemEqOutside s s8 (dst + m) (dst + m + 1) := by
    intro a ha hout
    rw [hs8_byte]
    exact MemEqOutside_setByte s (dst + m) _ (by omega) a ha hout
  have hdig : readBuffer s8 dst 32 = proofDigestVar s0 proofLen (11341403200 + pLo) bitOff l := by
    apply proofDigestVar_eq_readBuffer s8 s0 proofLen dst (11341403200 + pLo) bitOff l
    · intro j hj; exact (hout_all (dst + j) (by omega) (by omega)).trans (hlo j hj)
    · intro _; change s8.getByte (BitVec.ofNat 64 (dst + m)) = tailBitsAt s0 proofLen bitOff tb
      rw [hs8_byte, set_byte_read]; simp
    · intro j hj1 hj2
      have hj1' : m + 1 ≤ j := by
        change m + (if tb = 0 then 0 else 1) ≤ j at hj1
        have htb0' : tb ≠ 0 := htb_pos
        simpa only [htb0', ite_false] using hj1
      exact (hout_all (dst + j) (by omega) (by omega)).trans (hhi j hj1' hj2)
  refine ⟨s8, ?_, ?_, ?_, fun r h3 h4 h9 => (hreg8 r).trans (hreg6 r h3 h4 h9), hdig, hout_all⟩
  · have h := ((((hst0.trans hst1).trans hst2).trans (hst3.trans hst4)).trans hst5).trans (hst6.trans hst7)
    exact h.eq_of rfl (by decide) (by decide) (by simp)
  · simp only [s8, execInstrBr, MachineState.setPC, hreg7 .x1, hreg6 .x1 (by decide) (by decide) (by decide), hret]
    exact jalr_pcWord retIdx (by omega)
  · exact ⟨hle_next,
      (hreg8 .x25).trans ((hreg6 .x25 (by decide) (by decide) (by decide)).trans hx25),
      (hreg8 .x31).trans ((hreg6 .x31 (by decide) (by decide) (by decide)).trans hx31),
      (hreg8 .x3).trans hx3_6, (hreg8 .x4).trans hx4_6⟩

/-- Call and return from `readVarDigest` (`pc[297..324]`): reads `levelBodyBytes l` forward bytes
and `levelTailBits l` backward tail bits, writing `proofDigestVar` to `[dst, dst+32)` (≤ 205 steps). -/
theorem step_readVarDigest (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (hplen : proofLen ≤ proofCap)
    (s : MachineState) (retIdx pLo bitOff dst l : Nat)
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23)
    (hpc : s.pc = pcWord 297) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 359)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (levelMetaOC l))
    (hcur : ProofCursor s0 proofLen pLo bitOff s)
    (hhigh : HighMemPreserved s0 s)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hdst_al : dst % 8 = 0) (hdst_hi : dst + 32 ≤ 4294971392) :
    PhaseOutcome oracle s 205 0
      (proofLen < pLo + levelBodyBytes l + tailBytesBits (bitOff + levelTailBits l))
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = pcWord retIdx ∧
        ProofCursor s0 proofLen (pLo + levelBodyBytes l) (bitOff + levelTailBits l) s' ∧
        (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x7 → r ≠ .x9 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s'.getReg r = s.getReg r) ∧
        readBuffer s' dst 32 = proofDigestVar s0 proofLen (11341403200 + pLo) bitOff l ∧
        MemEqOutside s s' dst (dst + 32)) := by
  have hplen_bd : proofLen ≤ 8556390424 := hplen
  have hle_cur : pLo + tailBytesBits bitOff ≤ proofLen := hcur.le
  let m := levelBodyBytes l
  let tb := levelTailBits l
  have hm_bd := levelBodyBytes_bounds l hl1 hl2
  have htb_lt : tb < 8 := levelTailBits_lt_8 l
  -- pc[297]: ANDI x7, x6, 255
  have hst0 := step_ordinary oracle s 297 (.ANDI .x7 .x6 255#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ANDI .x7 .x6 255#12)
  have hpc1 : s1.pc = pcWord 298 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx7_1 : s1.getReg .x7 = BitVec.ofNat 64 m := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx6, se12_255]
    exact levelMetaOC_bodyBytes l hl1 (by omega)
  have hreg1 : ∀ r, r ≠ .x7 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  -- pc[298]: ADD x9, x25, x7
  have hst1 := step_ordinary oracle s1 298 (.ADD .x9 .x25 .x7) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADD .x9 .x25 .x7)
  have hpc2 : s2.pc = pcWord 299 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx9_2 : s2.getReg .x9 = BitVec.ofNat 64 (11341403200 + pLo + m) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hreg1 .x25 (by decide), hcur.x25, hx7_1, bv64_add]
  have hreg2 : ∀ r, r ≠ .x7 → r ≠ .x9 → s2.getReg r = s.getReg r := fun r h7 h9 => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h9.symm, hreg1 r h7]
  -- pc[299]: BLTU x31, x9, 8144 (-> 287)
  have hst2 := step_ordinary oracle s2 299 (.BLTU .x31 .x9 8144#13) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.BLTU .x31 .x9 8144#13)
  have hult1 : BitVec.ult (s2.getReg .x31) (s2.getReg .x9) = decide (proofLen < pLo + m + tailBytesBits bitOff) := by
    rw [hreg2 .x31 (by decide) (by decide), hcur.x31, hx9_2, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort1 : proofLen < pLo + m + tailBytesBits bitOff
  · have hpc3 : s3.pc = pcWord 287 := by
      simp only [s3, execInstrBr, hult1, hshort1, decide_true, ite_true, MachineState.setPC, hpc2]; decide
    have htb_mono := tailBytesBits_mono (show bitOff ≤ bitOff + levelTailBits l by omega)
    exact .rejected 6 0 [] (by change proofLen < pLo + m + tailBytesBits (bitOff + tb); dsimp only [m, tb]; omega)
      (by decide) (by decide)
      (by simpa using ((hst0.trans hst1).trans hst2).halt (halt_reject oracle s3 hpc3))
  · have hge_m : pLo + m + tailBytesBits bitOff ≤ proofLen := by omega
    have hpc3 : s3.pc = pcWord 300 := by
      simp only [s3, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by
      have : s3.mem = s2.mem := by
        simp only [s3, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      exact this.trans (by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg])
    have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x9 → s3.getReg r = s.getReg r := fun r h7 h9 => by
      have : s3.getReg r = s2.getReg r := by
        simp only [s3, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      exact this.trans (hreg2 r h7 h9)
    have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 m := by
      have : s3.getReg .x7 = s2.getReg .x7 := by
        simp only [s3, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      rw [this]; simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x7), hx7_1]
    -- pc[300]: SW x12, x0, 28
    have ha3 : s3.getReg .x12 + signExtend12 28#12 = BitVec.ofNat 64 (dst + 28) := by
      rw [hreg3 .x12 (by decide) (by decide), hdst, se12_28]; exact bv64_add dst 28
    have hv3 : memoryArgumentsValid s3 (.SW .x12 .x0 28#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha3]
      exact accessValid_ofNat (dst + 28) 4 (by unfold MEMORY_BYTES; omega) (by omega)
    have hst3 := step_ordinary oracle s3 300 (.SW .x12 .x0 28#12) (by decide) hpc3 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv3])
    let s4 := execInstrBr s3 (.SW .x12 .x0 28#12)
    have hpc4 : s4.pc = pcWord 301 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
    have hreg4 : ∀ r, s4.getReg r = s3.getReg r := fun r => by
      simp [s4, execInstrBr, MachineState.setWord32, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    have hs4_byte : ∀ q : Word, s4.getByte q = (s.setWord32 (BitVec.ofNat 64 (dst + 28)) 0#32).getByte q := by
      intro q
      simp only [s4, execInstrBr, ha3, getReg_x0,
        MachineState.getByte, MachineState.setWord32, MachineState.getMem, MachineState.setMem, mem_setPC, hmem3]
      rfl
    have hout_s4 : MemEqOutside s s4 (dst + 28) (dst + 32) := by
      intro a ha hout; rw [hs4_byte]; exact MemEqOutside_setWord32_zero_hi s dst hdst_al (by omega) a ha hout
    have hzero4 : ∀ j, 28 ≤ j → j < 32 → s4.getByte (BitVec.ofNat 64 (dst + j)) = 0#8 := fun j h1 h2 => by
      rw [hs4_byte]; exact setWord32_zero_hi_inside s dst j hdst_al h1 h2
    -- pc[301..306]: copy m forward bytes using rTmp = .x9, rCnt = .x7
    obtain ⟨s5, hs5, hpc5, hx25_5, hx12_5, _, hreg5, hcopy5, hout5⟩ :=
      step_byte_copy_loop oracle 301 .x9 .x7 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl m (by omega) (by omega) s4
        (11341403200 + pLo) dst hpc4
        ((hreg4 .x25).trans ((hreg3 .x25 (by decide) (by decide)).trans hcur.x25))
        ((hreg4 .x12).trans ((hreg3 .x12 (by decide) (by decide)).trans hdst))
        ((hreg4 .x7).trans hx7_3)
        (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
    have hout_s5 : MemEqOutside s s5 dst (dst + 32) :=
      (hout_s4.mono (by omega) (by omega)).trans (hout5.mono (by omega) (by omega))
    have hhigh5 : HighMemPreserved s0 s5 := hhigh.trans (hout_s5.mono (by omega) (by omega))
    have hlo5 : ∀ j < m, s5.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (11341403200 + pLo + j)) := by
      intro j hj
      rw [hcopy5 j hj]
      exact (hhigh.trans (hout_s4.mono (by omega) (by omega))) (11341403200 + pLo + j) (by omega) (by omega)
    have hhi5 : ∀ j, m ≤ j → j < 32 → s5.getByte (BitVec.ofNat 64 (dst + j)) = 0#8 := fun j h1 h2 =>
      (hout5 (dst + j) (by omega) (by omega)).trans (hzero4 j (by omega) h2)
    have hreg5_s : ∀ r, r ≠ .x7 → r ≠ .x9 → r ≠ .x12 → r ≠ .x25 → s5.getReg r = s.getReg r :=
      fun r h7 h9 h12 h25 => (hreg5 r h9 h12 h25 h7).trans ((hreg4 r).trans (hreg3 r h7 h9))
    -- pc[307]: SRLI x7, x6, 8; pc[308]: ANDI x7, x7, 255; pc[309]: BEQ x7, x0, 60 (-> 324)
    have hst5 := step_ordinary oracle s5 307 (.SRLI .x7 .x6 8#6) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.SRLI .x7 .x6 8#6)
    have hpc6 : s6.pc = pcWord 308 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
    have hst6 := step_ordinary oracle s6 308 (.ANDI .x7 .x7 255#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
    let s7 := execInstrBr s6 (.ANDI .x7 .x7 255#12)
    have hpc7 : s7.pc = pcWord 309 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
    have hx7_7 : s7.getReg .x7 = BitVec.ofNat 64 tb := by
      simp only [s7, s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide),
        hreg5_s .x6 (by decide) (by decide) (by decide) (by decide), hx6, se12_255,
        show (8#6 : BitVec 6).toNat = 8 by decide]
      exact levelMetaOC_tailBits l hl1 (by omega)
    have hreg7 : ∀ r, r ≠ .x7 → s7.getReg r = s5.getReg r := fun r hr => by
      simp only [s7, s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ hr.symm]
    have hmem7 : s7.mem = s5.mem := by simp [s7, s6, execInstrBr, mem_setPC, mem_setReg]
    have hst7 := step_ordinary oracle s7 309 (.BEQ .x7 .x0 60#13) (by decide) hpc7 rfl (by intro h; cases h) rfl
    let s8 := execInstrBr s7 (.BEQ .x7 .x0 60#13)
    have hbeq7 : (s7.getReg .x7 == s7.getReg .x0) = decide (tb = 0) := by
      rw [hx7_7, getReg_x0]; exact bv64_beq_eq tb 0 (by omega) (by decide)
    have hpre8 : StepsTo oracle s s8 (6 * m + 7) 0 [] := by
      have h := (((hst0.trans hst1).trans (hst2.trans hst3)).trans hs5).trans ((hst5.trans hst6).trans hst7)
      exact h.eq_of rfl (by omega) (by decide) (by simp)
    by_cases htb0 : tb = 0
    · -- No tail bits: jump to pc[324] JALR return!
      have hpc8 : s8.pc = pcWord 324 := by
        simp only [s8, execInstrBr, hbeq7, htb0, decide_true, ite_true, MachineState.setPC, hpc7]; decide
      have hmem8 : s8.mem = s5.mem := by
        simpa [s8, execInstrBr, hbeq7, htb0, MachineState.setPC] using hmem7
      have hreg8 : ∀ r, r ≠ .x7 → s8.getReg r = s5.getReg r := fun r hr => by
        simpa [s8, execInstrBr, hbeq7, htb0, MachineState.getReg_setPC] using hreg7 r hr
      have hst8 := step_ordinary oracle s8 324 (.JALR .x0 .x1 0#12) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let sFin := execInstrBr s8 (.JALR .x0 .x1 0#12)
      have hmemFin : sFin.mem = s5.mem := by
        simpa [sFin, execInstrBr, MachineState.setReg, mem_setPC] using hmem8
      have hregFin : ∀ r, r ≠ .x7 → sFin.getReg r = s5.getReg r := fun r hr => by
        have : sFin.getReg r = s8.getReg r := by simp [sFin, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
        exact this.trans (hreg8 r hr)
      have hdig : readBuffer sFin dst 32 = proofDigestVar s0 proofLen (11341403200 + pLo) bitOff l := by
        apply proofDigestVar_eq_readBuffer sFin s0 proofLen dst (11341403200 + pLo) bitOff l
        · intro j hj; simp only [MachineState.getByte, MachineState.getMem, hmemFin]; exact hlo5 j hj
        · intro hne; exact (hne htb0).elim
        · intro j hj1 hj2
          have hj1' : m ≤ j := by
            change m + (if tb = 0 then 0 else 1) ≤ j at hj1
            simpa only [htb0, ite_true, Nat.add_zero] using hj1
          simp only [MachineState.getByte, MachineState.getMem, hmemFin]; exact hhi5 j hj1' hj2
      refine .continued sFin (6 * m + 8) 0 [] (by omega) (by decide)
        ((hpre8.trans hst8).eq_of rfl (by omega) (by decide) (by simp))
        ⟨rfl, rfl, ?_, ?_, ?_, hdig, hout_s5.trans (MemEqOutside.of_mem_eq hmemFin dst (dst + 32))⟩
      · simp only [sFin, execInstrBr, MachineState.setPC, hreg8 .x1 (by decide),
          hreg5_s .x1 (by decide) (by decide) (by decide) (by decide), hret]
        exact jalr_pcWord retIdx (by omega)
      · change ProofCursor s0 proofLen (pLo + m) (bitOff + tb) sFin
        rw [htb0, Nat.add_zero]
        exact ⟨hge_m,
          by rw [hregFin .x25 (by decide), hx25_5, Nat.add_assoc],
          (hregFin .x31 (by decide)).trans ((hreg5_s .x31 (by decide) (by decide) (by decide) (by decide)).trans hcur.x31),
          (hregFin .x3 (by decide)).trans ((hreg5_s .x3 (by decide) (by decide) (by decide) (by decide)).trans hcur.x3),
          (hregFin .x4 (by decide)).trans ((hreg5_s .x4 (by decide) (by decide) (by decide) (by decide)).trans hcur.x4)⟩
      · intro r _ _ h7 h9 h12 h25 _
        exact (hregFin r h7).trans (hreg5_s r h7 h9 h12 h25)
    · -- tb > 0: pc[310] BGEU x4, x7, 28 (-> 317)
      have hpc8 : s8.pc = pcWord 310 := by
        simp only [s8, execInstrBr, hbeq7, htb0, decide_false, Bool.false_eq_true, ite_false,
          MachineState.setPC, hpc7, pcWord_add_four]
      have hmem8 : s8.mem = s5.mem := by
        simpa [s8, execInstrBr, hbeq7, htb0, MachineState.setPC] using hmem7
      have hreg8 : ∀ r, r ≠ .x7 → s8.getReg r = s5.getReg r := fun r hr => by
        simpa [s8, execInstrBr, hbeq7, htb0, MachineState.getReg_setPC] using hreg7 r hr
      have hx7_8 : s8.getReg .x7 = BitVec.ofNat 64 tb := by
        simpa [s8, execInstrBr, hbeq7, htb0, MachineState.getReg_setPC] using hx7_7
      have hst8 := step_ordinary oracle s8 310 (.BGEU .x4 .x7 28#13) (by decide) hpc8 rfl (by intro h; cases h) rfl
      let s9 := execInstrBr s8 (.BGEU .x4 .x7 28#13)
      have htc_lt8 := tailCntBits_lt8 bitOff
      have hult8 : BitVec.ult (s8.getReg .x4) (s8.getReg .x7) = decide (tailCntBits bitOff < tb) := by
        rw [hreg8 .x4 (by decide), hreg5_s .x4 (by decide) (by decide) (by decide) (by decide),
          hcur.x4, hx7_8, bv64_ult_eq _ _ (by omega) (by omega)]
      have hpre9 : StepsTo oracle s s9 (6 * m + 8) 0 [] :=
        (hpre8.trans hst8).eq_of rfl (by omega) (by decide) (by simp)
      by_cases hlt_tb : tailCntBits bitOff < tb
      · -- Need 1 backward byte: pc[311..316] -> pc[317..324]
        obtain ⟨htb_s, htc_s⟩ := tailBytesBits_add_lt bitOff tb hlt_tb htb_lt
        have hpc9 : s9.pc = pcWord 311 := by
          simp only [s9, execInstrBr, hult8, hlt_tb, decide_true, not_true_eq_false, ite_false,
            MachineState.setPC, hpc8, pcWord_add_four]
        have hmem9 : s9.mem = s5.mem := by
          simpa [s9, execInstrBr, hult8, hlt_tb, MachineState.setPC] using hmem8
        have hreg9 : ∀ r, r ≠ .x7 → s9.getReg r = s5.getReg r := fun r hr => by
          simpa [s9, execInstrBr, hult8, hlt_tb, MachineState.getReg_setPC] using hreg8 r hr
        have hx7_9 : s9.getReg .x7 = BitVec.ofNat 64 tb := by
          simpa [s9, execInstrBr, hult8, hlt_tb, MachineState.getReg_setPC] using hx7_8
        -- pc[311]: BGEU x25, x31, 8096 (-> 287)
        have hst9 := step_ordinary oracle s9 311 (.BGEU .x25 .x31 8096#13) (by decide) hpc9 rfl (by intro h; cases h) rfl
        let s10 := execInstrBr s9 (.BGEU .x25 .x31 8096#13)
        have hx25_9 : s9.getReg .x25 = BitVec.ofNat 64 (11341403200 + pLo + m) := by
          rw [hreg9 .x25 (by decide), hx25_5]
        have hx31_9 : s9.getReg .x31 = BitVec.ofNat 64 (11341403200 + (proofLen - tailBytesBits bitOff)) := by
          rw [hreg9 .x31 (by decide), hreg5_s .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31]
        have hult9 : BitVec.ult (s9.getReg .x25) (s9.getReg .x31) =
            decide (pLo + m + tailBytesBits (bitOff + tb) ≤ proofLen) := by
          rw [hx25_9, hx31_9, bv64_ult_eq _ _ (by omega) (by omega)]
          exact decide_eq_decide.mpr (by omega)
        by_cases hok : pLo + m + tailBytesBits (bitOff + tb) ≤ proofLen
        · have hpc10 : s10.pc = pcWord 312 := by
            simp only [s10, execInstrBr, hult9, hok, decide_true, not_true_eq_false, ite_false,
              MachineState.setPC, hpc9, pcWord_add_four]
          have hmem10 : s10.mem = s5.mem := by
            simpa [s10, execInstrBr, hult9, hok, MachineState.setPC] using hmem9
          have hreg10 : ∀ r, r ≠ .x7 → s10.getReg r = s5.getReg r := fun r hr => by
            simpa [s10, execInstrBr, hult9, hok, MachineState.getReg_setPC] using hreg9 r hr
          have hx7_10 : s10.getReg .x7 = BitVec.ofNat 64 tb := by
            simpa [s10, execInstrBr, hult9, hok, MachineState.getReg_setPC] using hx7_9
          obtain ⟨s15, hs15, hpc15, hx31_15, hx3_15, hx4_15, hreg15, hmem15_10⟩ :=
            step_var_load_backbyte oracle s0 proofLen hplen s10 bitOff tb hlt_tb htb_lt (by omega) hpc10
              ((hreg10 .x31 (by decide)).trans ((hreg5_s .x31 (by decide) (by decide) (by decide) (by decide)).trans hcur.x31))
              ((hreg10 .x3 (by decide)).trans ((hreg5_s .x3 (by decide) (by decide) (by decide) (by decide)).trans hcur.x3))
              ((hreg10 .x4 (by decide)).trans ((hreg5_s .x4 (by decide) (by decide) (by decide) (by decide)).trans hcur.x4))
              (hhigh5.trans (MemEqOutside.of_mem_eq hmem10 0 4294971392))
          have hmem15 : s15.mem = s5.mem := hmem15_10.trans hmem10
          obtain ⟨sFin, hsFin, hpcFin, hcurFin, hregFin, hdigFin, houtFin⟩ :=
            step_var_pop_tail oracle s0 proofLen s15 retIdx pLo bitOff dst l hl1 hl2 htb0 hpc15
              ((hreg15 .x1 (by decide) (by decide) (by decide) (by decide)).trans
                ((hreg10 .x1 (by decide)).trans ((hreg5_s .x1 (by decide) (by decide) (by decide) (by decide)).trans hret)))
              hret_lt hok
              ((hreg15 .x7 (by decide) (by decide) (by decide) (by decide)).trans hx7_10)
              (by rw [hreg15 .x25 (by decide) (by decide) (by decide) (by decide), hreg10 .x25 (by decide), hx25_5, Nat.add_assoc])
              hx31_15 hx3_15 hx4_15
              ((hreg15 .x12 (by decide) (by decide) (by decide) (by decide)).trans ((hreg10 .x12 (by decide)).trans hx12_5))
              hdst_hi
              (fun j hj => by simp only [MachineState.getByte, MachineState.getMem, hmem15]; exact hlo5 j hj)
              (fun j h1 h2 => by simp only [MachineState.getByte, MachineState.getMem, hmem15]; exact hhi5 j (by omega) h2)
          refine .continued sFin (6 * m + 22) 0 [] (by omega) (by decide)
            (((hpre9.trans hst9).trans (hs15.trans hsFin)).eq_of rfl (by omega) (by decide) (by simp))
            ⟨rfl, rfl, hpcFin, hcurFin, ?_, hdigFin, ?_⟩
          · intro r h3 h4 h7 h9 h12 h25 h31
            exact (hregFin r h3 h4 h9).trans ((hreg15 r h3 h4 h9 h31).trans ((hreg10 r h7).trans (hreg5_s r h7 h9 h12 h25)))
          · exact hout_s5.trans ((MemEqOutside.of_mem_eq hmem15 dst (dst + 32)).trans (houtFin.mono (by omega) (by omega)))
        · have hpc10 : s10.pc = pcWord 287 := by
            simp only [s10, execInstrBr, hult9, hok, decide_false, Bool.false_eq_true, not_false_eq_true, ite_true,
              MachineState.setPC, hpc9]; decide
          exact .rejected (6 * m + 12) 0 [] (by change proofLen < pLo + m + tailBytesBits (bitOff + tb); omega)
            (by omega) (by decide)
            (by simpa [Nat.add_assoc] using (hpre9.trans hst9).halt (halt_reject oracle s10 hpc10))
      · -- Already have ≥ tb bits: jump straight to pc[317]
        have hge_tb : tb ≤ tailCntBits bitOff := by omega
        obtain ⟨htb_s, htc_s⟩ := tailBytesBits_add_ge bitOff tb hge_tb
        have hpc9 : s9.pc = pcWord 317 := by
          simp only [s9, execInstrBr, hult8, hlt_tb, decide_false, Bool.false_eq_true, not_false_eq_true, ite_true,
            MachineState.setPC, hpc8]; decide
        have hmem9 : s9.mem = s5.mem := by
          simpa [s9, execInstrBr, hult8, hlt_tb, MachineState.setPC] using hmem8
        have hreg9 : ∀ r, r ≠ .x7 → s9.getReg r = s5.getReg r := fun r hr => by
          simpa [s9, execInstrBr, hult8, hlt_tb, MachineState.getReg_setPC] using hreg8 r hr
        have hx7_9 : s9.getReg .x7 = BitVec.ofNat 64 tb := by
          simpa [s9, execInstrBr, hult8, hlt_tb, MachineState.getReg_setPC] using hx7_8
        obtain ⟨sFin, hsFin, hpcFin, hcurFin, hregFin, hdigFin, houtFin⟩ :=
          step_var_pop_tail oracle s0 proofLen s9 retIdx pLo bitOff dst l hl1 hl2 htb0 hpc9
            ((hreg9 .x1 (by decide)).trans ((hreg5_s .x1 (by decide) (by decide) (by decide) (by decide)).trans hret))
            hret_lt (by rw [htb_s]; exact hge_m) hx7_9
            (by rw [hreg9 .x25 (by decide), hx25_5, Nat.add_assoc])
            (by rw [hreg9 .x31 (by decide), hreg5_s .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31, htb_s])
            (by rw [hreg9 .x3 (by decide), hreg5_s .x3 (by decide) (by decide) (by decide) (by decide), hcur.x3, htb_s]; rfl)
            (by rw [hreg9 .x4 (by decide), hreg5_s .x4 (by decide) (by decide) (by decide) (by decide), hcur.x4]; congr 1; dsimp only [tb] at htc_s hge_tb ⊢; omega)
            ((hreg9 .x12 (by decide)).trans hx12_5) hdst_hi
            (fun j hj => by simp only [MachineState.getByte, MachineState.getMem, hmem9]; exact hlo5 j hj)
            (fun j h1 h2 => by simp only [MachineState.getByte, MachineState.getMem, hmem9]; exact hhi5 j (by omega) h2)
        refine .continued sFin (6 * m + 16) 0 [] (by omega) (by decide)
          ((hpre9.trans hsFin).eq_of rfl (by omega) (by decide) (by simp))
          ⟨rfl, rfl, hpcFin, hcurFin, ?_, hdigFin, ?_⟩
        · intro r h3 h4 h7 h9 h12 h25 _
          exact (hregFin r h3 h4 h9).trans ((hreg9 r h7).trans (hreg5_s r h7 h9 h12 h25))
        · exact hout_s5.trans ((MemEqOutside.of_mem_eq hmem9 dst (dst + 32)).trans (houtFin.mono (by omega) (by omega)))

/-- Helper: `JAL .x1` to `readVarDigest` (`pc[297]`), ≤ 206 steps. -/
theorem step_call_readVarDigest (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (hplen : proofLen ≤ proofCap)
    (idx : Nat) (s : MachineState) (pLo bitOff dst l : Nat)
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23) (hhi : idx + 1 ≤ 297)
    (hjal : checkInstr idx = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (297 - idx)))))
    (hpc : s.pc = pcWord idx)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (levelMetaOC l))
    (hcur : ProofCursor s0 proofLen pLo bitOff s)
    (hhigh : HighMemPreserved s0 s)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hdst_al : dst % 8 = 0) (hdst_hi : dst + 32 ≤ 4294971392) :
    PhaseOutcome oracle s 206 0
      (proofLen < pLo + levelBodyBytes l + tailBytesBits (bitOff + levelTailBits l))
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = pcWord (idx + 1) ∧
        ProofCursor s0 proofLen (pLo + levelBodyBytes l) (bitOff + levelTailBits l) s' ∧
        (∀ r : Reg, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x7 → r ≠ .x9 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s'.getReg r = s.getReg r) ∧
        readBuffer s' dst 32 = proofDigestVar s0 proofLen (11341403200 + pLo) bitOff l ∧
        MemEqOutside s s' dst (dst + 32)) := by
  let off := BitVec.ofNat 21 (4 * (297 - idx))
  have hst0 := step_ordinary oracle s idx (.JAL .x1 off) (by omega) hpc hjal (by intro h; cases h) rfl
  let s1 := execInstrBr s (.JAL .x1 off)
  have hpc1 : s1.pc = pcWord 297 := by
    simp only [s1, execInstrBr, MachineState.setPC, hpc]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (297 - idx)) :=
      signExtend21_ofNat_lt _ (by omega)
    rw [hse21, pcWord, bv64_add]; congr 1; omega
  have hret1 : s1.getReg .x1 = pcWord (idx + 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, hpc, pcWord_add_four]
    exact MachineState.getReg_setReg_eq (by decide)
  have hreg1 : ∀ r, r ≠ .x1 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hcur1 : ProofCursor s0 proofLen pLo bitOff s1 :=
    hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl))
  have hsub := step_readVarDigest oracle s0 proofLen hplen s1 (idx + 1) pLo bitOff dst l hl1 hl2
    hpc1 hret1 (by omega) ((hreg1 .x6 (by decide)).trans hx6)
    hcur1 (hhigh.trans (MemEqOutside.of_mem_eq hmem1 0 4294971392))
    ((hreg1 .x12 (by decide)).trans hdst) hdst_al hdst_hi
  refine (hst0.prepend_pure hsub).weaken (by omega) (by omega) id ?_
  rintro s' q tr ⟨hq, htr, hpc', hcur', hreg', hdig', hout'⟩
  exact ⟨hq, htr, hpc', hcur',
    fun r h1 h3 h4 h7 h9 h12 h25 h31 => (hreg' r h3 h4 h7 h9 h12 h25 h31).trans (hreg1 r h1),
    hdig', (MemEqOutside.of_mem_eq hmem1 dst (dst + 32)).trans hout'⟩

/-! #### `hashLevelNode` (`pc[325..358]`): Domain-Separated Chain + Width Mask -/

/-- Mask epilogue (`pc[351..358]`, 8 steps): masks `[dst, dst+32)` to `maskLevel lvl` and returns to `x1`. -/
private theorem step_hashLevelNode_mask (oracle : Oracle) (s : MachineState)
    (retIdx dst lvl : Nat) (hl1 : 2 ≤ lvl) (hl2 : lvl ≤ 24)
    (hpc : s.pc = pcWord 351) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 359)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (levelMetaOC lvl))
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 dst)
    (hdst_al : dst % 8 = 0) (hdst_bd : dst + 32 ≤ MEMORY_BYTES) :
    ∃ s', StepsTo oracle s s' 8 0 [] ∧
      s'.pc = pcWord retIdx ∧
      (∀ r : Reg, r ≠ .x7 → r ≠ .x9 → s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = maskLevel lvl (readBuffer s dst 32) ∧
      MemEqOutside s s' dst (dst + 32) := by
  have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
  have hsh_lt : levelShift lvl < 64 := levelShift_lt64 lvl hl1 hl2
  have hw1 : 192 ≤ levelWidth lvl := levelWidth_ge_192 lvl
  have hw2 : levelWidth lvl ≤ 256 := levelWidth_le_256 lvl
  -- pc[351..354]: x7 = levelShift lvl, x9 = maskTopWord (levelWidth lvl)
  have hst0 := step_ordinary oracle s 351 (.SRLI .x7 .x6 24#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SRLI .x7 .x6 24#6)
  have hpc1 : s1.pc = pcWord 352 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst1 := step_ordinary oracle s1 352 (.ANDI .x7 .x7 255#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ANDI .x7 .x7 255#12)
  have hpc2 : s2.pc = pcWord 353 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hst2 := step_ordinary oracle s2 353 (.ADDI .x9 .x0 4095#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADDI .x9 .x0 4095#12)
  have hpc3 : s3.pc = pcWord 354 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hst3 := step_ordinary oracle s3 354 (.SRL .x9 .x9 .x7) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.SRL .x9 .x9 .x7)
  have hpc4 : s4.pc = pcWord 355 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simp [s4, s3, s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hx7_2 : s2.getReg .x7 = BitVec.ofNat 64 (levelShift lvl) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide),
      hx6, se12_255, show (24#6 : BitVec 6).toNat = 24 by decide]
    exact levelMetaOC_shift lvl hl1 hl2
  have hx9_3 : s3.getReg .x9 = BitVec.allOnes 64 := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, getReg_x0]
    rw [MachineState.getReg_setReg_eq (by decide), se12_4095_allOnes, BitVec.zero_add]
  have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (levelShift lvl) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x7), hx7_2]
  have hx9_4 : s4.getReg .x9 = maskTopWord (levelWidth lvl) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx9_3, hx7_3,
      toNat_ofNat64 (levelShift lvl) (by omega), Nat.mod_eq_of_lt hsh_lt]
    rfl
  have hreg4 : ∀ r, r ≠ .x7 → r ≠ .x9 → s4.getReg r = s.getReg r := fun r h7 h9 => by
    simp only [s4, s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
  -- pc[355..357]: LD x7, 24(x28); AND x7, x7, x9; SD x28, x7, 24
  have ha4 : s4.getReg .x28 + signExtend12 24#12 = BitVec.ofNat 64 (dst + 24) := by
    rw [hreg4 .x28 (by decide) (by decide), hx28, se12_24]; exact bv64_add dst 24
  have hv4 : memoryArgumentsValid s4 (.LD .x7 .x28 24#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha4]
    exact accessValid_ofNat (dst + 24) 8 (by omega) (by omega)
  have hst4 := step_ordinary oracle s4 355 (.LD .x7 .x28 24#12) (by decide) hpc4 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv4])
  let s5 := execInstrBr s4 (.LD .x7 .x28 24#12)
  have hpc5 : s5.pc = pcWord 356 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hx7_5 : s5.getReg .x7 = s.getMem (BitVec.ofNat 64 (dst + 24)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, ha4]
    rw [MachineState.getReg_setReg_eq (by decide)]
    simp only [MachineState.getMem, hmem4]
  have hst5 := step_ordinary oracle s5 356 (.AND .x7 .x7 .x9) (by decide) hpc5 rfl (by intro h; cases h) rfl
  let s6 := execInstrBr s5 (.AND .x7 .x7 .x9)
  have hpc6 : s6.pc = pcWord 357 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
  have hx7_6 : s6.getReg .x7 = s.getMem (BitVec.ofNat 64 (dst + 24)) &&& maskTopWord (levelWidth lvl) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx7_5]
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x9), hx9_4]
  have hreg6 : ∀ r, r ≠ .x7 → r ≠ .x9 → s6.getReg r = s.getReg r := fun r h7 h9 => by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg4 r h7 h9]
  have hmem6 : s6.mem = s.mem := by simpa [s6, s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
  have ha6 : s6.getReg .x28 + signExtend12 24#12 = BitVec.ofNat 64 (dst + 24) := by
    rw [hreg6 .x28 (by decide) (by decide), hx28, se12_24]; exact bv64_add dst 24
  have hv6 : memoryArgumentsValid s6 (.SD .x28 .x7 24#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha6]
    exact accessValid_ofNat (dst + 24) 8 (by omega) (by omega)
  have hst6 := step_ordinary oracle s6 357 (.SD .x28 .x7 24#12) (by decide) hpc6 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv6])
  let s7 := execInstrBr s6 (.SD .x28 .x7 24#12)
  have hpc7 : s7.pc = pcWord 358 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
  have hreg7 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
    simp [s7, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
  -- pc[358]: JALR x0, x1, 0
  have hst7 := step_ordinary oracle s7 358 (.JALR .x0 .x1 0#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
  let s8 := execInstrBr s7 (.JALR .x0 .x1 0#12)
  have hmem8 : s8.mem = s7.mem := by simp [s8, execInstrBr, MachineState.setReg, mem_setPC]
  have hreg8 : ∀ r, s8.getReg r = s6.getReg r := fun r => by
    have : s8.getReg r = s7.getReg r := by simp [s8, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
    exact this.trans (hreg7 r)
  have hs8_byte : ∀ q : Word, s8.getByte q =
      (s.setMem (BitVec.ofNat 64 (dst + 24))
        (s.getMem (BitVec.ofNat 64 (dst + 24)) &&& maskTopWord (levelWidth lvl))).getByte q := by
    intro q
    simp only [MachineState.getByte, MachineState.getMem, hmem8]
    simp only [s7, execInstrBr, ha6, hx7_6, MachineState.setMem, MachineState.getMem, mem_setPC, hmem6]
  refine ⟨s8, ((((hst0.trans hst1).trans (hst2.trans hst3)).trans (hst4.trans hst5)).trans (hst6.trans hst7)).eq_of rfl (by decide) (by decide) (by simp),
    ?_, fun r h7 h9 => (hreg8 r).trans (hreg6 r h7 h9), ?_, ?_⟩
  · simp only [s8, execInstrBr, MachineState.setPC, hreg7 .x1, hreg6 .x1 (by decide) (by decide), hret]
    exact jalr_pcWord retIdx (by omega)
  · have hr : readBuffer s8 dst 32 =
        readBuffer (s.setMem (BitVec.ofNat 64 (dst + 24))
          (s.getMem (BitVec.ofNat 64 (dst + 24)) &&& maskTopWord (levelWidth lvl))) dst 32 :=
      readBuffer_congr2 _ _ _ _ _ (fun _ _ => hs8_byte _)
    rw [hr, sd_and_maskWidth s dst (levelWidth lvl) hw1 hw2 hdst_al (by omega)]
    rfl
  · intro a ha hout
    rw [hs8_byte]
    exact setMem_getByte_ofNat s (dst + 24) a _ (by omega) (by omega) ha (by omega)

private theorem mem_execInstrBr_bne (s : MachineState) (r1 r2 : Reg) (imm : BitVec 13) :
    (execInstrBr s (.BNE r1 r2 imm)).mem = s.mem := by
  simp only [execInstrBr]; split <;> rfl

private theorem mem_execInstrBr_beq (s : MachineState) (r1 r2 : Reg) (imm : BitVec 13) :
    (execInstrBr s (.BEQ r1 r2 imm)).mem = s.mem := by
  simp only [execInstrBr]; split <;> rfl

private theorem getReg_execInstrBr_bne (s : MachineState) (r1 r2 : Reg) (imm : BitVec 13) (r : Reg) :
    (execInstrBr s (.BNE r1 r2 imm)).getReg r = s.getReg r := by
  simp only [execInstrBr]; split <;> simp only [MachineState.getReg_setPC]

private theorem getReg_execInstrBr_beq (s : MachineState) (r1 r2 : Reg) (imm : BitVec 13) (r : Reg) :
    (execInstrBr s (.BEQ r1 r2 imm)).getReg r = s.getReg r := by
  simp only [execInstrBr]; split <;> simp only [MachineState.getReg_setPC]

/-- Intermediate chain loop (`pc[344..347]`): executes stages `2 .. (c - 1)` in `4 * (c - 2)` steps
and `c - 2` oracle calls, transforming `[512..544)` from `d1` to `chainIter c96 lvl (c - 2) d1`. -/
private theorem step_hashLevelNode_chainLoop (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (lvl : Nat) (hl1 : 9 ≤ lvl) (hl2 : lvl ≤ 16)
    (d1 : Digest) (n : Nat) (hn : n ≤ levelChain lvl - 2)
    (s : MachineState)
    (hpc : s.pc = pcWord 344)
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = 512#64) (hx12 : s.getReg .x12 = 512#64)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 (256 * lvl + levelChain lvl))
    (hx7 : s.getReg .x7 = BitVec.ofNat 64 (256 * lvl + (levelChain lvl - n)))
    (hcur : readBuffer s 512 32 = chainIter (fun x => oracle.compression (x.cast h768.symm)) lvl (levelChain lvl - 2 - n) d1)
    (hzero : ChainScratchZero s)
    (hn_pos : 0 < n) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s' tr,
      StepsTo oracle s s' (4 * n) n tr ∧
      s'.pc = pcWord 348 ∧
      s'.getReg .x7 = BitVec.ofNat 64 (256 * lvl + levelChain lvl) ∧
      (∀ r : Reg, r ≠ .x7 → s'.getReg r = s.getReg r) ∧
      readBuffer s' 512 32 = chainIter c96 lvl (levelChain lvl - 2) d1 ∧
      ChainScratchZero s' ∧
      MemEqOutside s s' 512 608 ∧
      (∀ x ∈ chainIterInputs c96 lvl (levelChain lvl - 2) d1,
        x ∈ chainIterInputs c96 lvl (levelChain lvl - 2 - n) d1 ∨
        (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ tr) := by
  intro c96
  have hc_bd := levelChain_bounds lvl (by omega) (by omega)
  induction n generalizing s with
  | zero => omega
  | succ m ih =>
    let k := levelChain lvl - 2 - (m + 1)
    have hk_eq : levelChain lvl - (m + 1) = k + 2 := by omega
    have htag_lt : 256 * lvl + (k + 2) < 2 ^ 64 := by omega
    have hfin_lt : 256 * lvl + levelChain lvl < 2 ^ 64 := by omega
    -- pc[344]: SD x10, x7, 64 -> writes levelTag lvl (k + 2) to 576
    have ha0 : s.getReg .x10 + signExtend12 64#12 = BitVec.ofNat 64 576 := by
      rw [hx10, se12_64]; decide
    have hv0 : memoryArgumentsValid s (.SD .x10 .x7 64#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha0]
      exact accessValid_ofNat 576 8 (by unfold MEMORY_BYTES; decide) (by decide)
    have hst0 := step_ordinary oracle s 344 (.SD .x10 .x7 64#12) (by decide) hpc rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv0])
    let s1 := execInstrBr s (.SD .x10 .x7 64#12)
    have hpc1 : s1.pc = pcWord 345 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
    have hreg1 : ∀ r, s1.getReg r = s.getReg r := fun r => by
      simp [s1, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    have hs1_byte : ∀ q : Word, s1.getByte q = (s.setMem (BitVec.ofNat 64 576) (levelTag lvl (k + 2))).getByte q := by
      intro q
      simp only [s1, execInstrBr, ha0, hx7, hk_eq, levelTag,
        MachineState.getByte, MachineState.getMem, MachineState.setMem, mem_setPC]
    have hout1 : MemEqOutside s s1 576 584 := fun a ha hout => by
      rw [hs1_byte]; exact MemEqOutside_setMem s 576 _ (by decide) (by decide) a ha hout
    have hzero1 : ChainScratchZero s1 := hzero.of_outside hout1 (by omega) (by omega)
    have hinp : readBuffer s1 512 96 = chainStepInput (chainIter c96 lvl k d1) (levelTag lvl (k + 2)) := by
      have htag1 : readBuffer s1 (512 + 64) 8 = levelTag lvl (k + 2) := by
        rw [show 512 + 64 = 576 by omega, readBuffer_word s1 576 (by decide)]
        simp only [s1, execInstrBr, ha0, hx7, hk_eq, levelTag, MachineState.getMem_setPC,
          MachineState.getMem_setMem_eq]
      have hlo1 : readBuffer s1 512 32 = chainIter c96 lvl k d1 :=
        (hout1.readBuffer_eq (by decide) (by omega)).trans hcur
      have hmid1 : readBuffer s1 (512 + 32) 32 = 0 := hzero1.mid_zero
      have hhi1 : readBuffer s1 (512 + 72) 24 = 0 := hzero1.hi_zero
      rw [readBuffer_chainStep s1 512 (levelTag lvl (k + 2)) hmid1 htag1 hhi1, hlo1]
    -- pc[345]: ECALL (512 -> 512)
    have hec := step_ecall_compress h768 oracle s1 345 512 512 (by decide) hpc1 rfl
      ((hreg1 .x5).trans hx5) ((hreg1 .x11).trans hx11) ((hreg1 .x13).trans hx13)
      ((hreg1 .x10).trans hx10) ((hreg1 .x12).trans hx12)
      (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
    rw [hinp] at hec
    let inp := chainStepInput (chainIter c96 lvl k d1) (levelTag lvl (k + 2))
    let dNext := c96 inp
    let s2 := writeBits s1 (BitVec.ofNat 64 512) dNext
    have hpc2 : s2.pc = pcWord 346 := by simp only [s2, writeBits, MachineState.setPC, hpc1, pcWord_add_four]
    have hreg2 : ∀ r, s2.getReg r = s.getReg r := fun r => (writeBits_register s1 _ dNext r).trans (hreg1 r)
    have hout2 : MemEqOutside s s2 512 608 :=
      (hout1.mono (by omega) (by omega)).trans ((MemEqOutside_writeBits_digest s1 512 dNext (by decide)).mono (by omega) (by omega))
    have hzero2 : ChainScratchZero s2 :=
      hzero1.of_outside (MemEqOutside_writeBits_digest s1 512 dNext (by decide)) (by omega) (by omega)
    have hd2 : readBuffer s2 512 32 = chainIter c96 lvl (k + 1) d1 :=
      writeBits_readBuffer_digest s1 512 dNext
    -- pc[346]: ADDI x7, x7, 1
    have hst2 := step_ordinary oracle s2 346 (.ADDI .x7 .x7 1#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x7 .x7 1#12)
    have hpc3 : s3.pc = pcWord 347 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (256 * lvl + (levelChain lvl - m)) := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg2 .x7, hx7, se12_1]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 1 = _
      rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
    have hreg3 : ∀ r, r ≠ .x7 → s3.getReg r = s.getReg r := fun r hr => by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, hreg2 r]
    have hmem3 : s3.mem = s2.mem := by simp [s3, execInstrBr, mem_setPC, mem_setReg]
    -- pc[347]: BNE x7, x9, 8180 (-12 -> 344)
    have hst3 := step_ordinary oracle s3 347 (.BNE .x7 .x9 8180#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
    let s4 := execInstrBr s3 (.BNE .x7 .x9 8180#13)
    have hbne : (s3.getReg .x7 != s3.getReg .x9) = decide (m ≠ 0) := by
      rw [hx7_3, hreg3 .x9 (by decide), hx9, bv64_bne_eq _ _ (by omega) hfin_lt]
      exact decide_eq_decide.mpr (by omega)
    have hmem4 : s4.mem = s2.mem :=
      (mem_execInstrBr_bne s3 .x7 .x9 8180#13).trans hmem3
    have hreg4 : ∀ r, s4.getReg r = s3.getReg r := fun r =>
      getReg_execInstrBr_bne s3 .x7 .x9 8180#13 r
    have hstep4 : StepsTo oracle s s4 4 1 [(inp.cast h768.symm, dNext)] :=
      ((hst0.trans hec).trans (hst2.trans hst3)).eq_of rfl (by decide) (by decide) (by simp [inp, dNext, c96])
    cases m with
    | zero =>
      have hpc4 : s4.pc = pcWord 348 := by
        simp only [s4, execInstrBr, hbne, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ite_false, MachineState.setPC, hpc3, pcWord_add_four]
      have hk1 : k + 1 = levelChain lvl - 2 := by omega
      refine ⟨s4, [(inp.cast h768.symm, dNext)], hstep4, hpc4,
        (hreg4 .x7).trans hx7_3, fun r hr => (hreg4 r).trans (hreg3 r hr),
        by rw [(MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega), hd2, hk1],
        hzero2.of_mem_eq hmem4,
        hout2.trans (MemEqOutside.of_mem_eq hmem4 512 608), ?_⟩
      intro x hx
      rw [← hk1] at hx
      simp only [chainIterInputs, List.mem_append, List.mem_singleton] at hx
      rcases hx with hprev | rfl
      · exact Or.inl hprev
      · exact Or.inr (List.mem_singleton_self _)
    | succ m' =>
      have hpc4 : s4.pc = pcWord 344 := by
        simp only [s4, execInstrBr, hbne, ne_eq, Nat.succ_ne_zero, not_false_eq_true, decide_true,
          ite_true, MachineState.setPC, hpc3]; decide
      have hk1 : k + 1 = levelChain lvl - 2 - (m' + 1) := by omega
      obtain ⟨sFin, trRest, hrest, hpcFin, hx7Fin, hregFin, hdFin, hzeroFin, houtFin, htrRest⟩ :=
        ih (by omega) s4 hpc4
          ((hreg4 .x5).trans ((hreg3 .x5 (by decide)).trans hx5))
          ((hreg4 .x11).trans ((hreg3 .x11 (by decide)).trans hx11))
          ((hreg4 .x13).trans ((hreg3 .x13 (by decide)).trans hx13))
          ((hreg4 .x10).trans ((hreg3 .x10 (by decide)).trans hx10))
          ((hreg4 .x12).trans ((hreg3 .x12 (by decide)).trans hx12))
          ((hreg4 .x9).trans ((hreg3 .x9 (by decide)).trans hx9))
          ((hreg4 .x7).trans hx7_3)
          (by rw [(MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by decide) (by omega), hd2, hk1])
          (hzero2.of_mem_eq hmem4) (by omega)
      refine ⟨sFin, [(inp.cast h768.symm, dNext)] ++ trRest,
        (hstep4.trans hrest).eq_of rfl (by omega) (by omega) rfl,
        hpcFin, hx7Fin, fun r hr => (hregFin r hr).trans ((hreg4 r).trans (hreg3 r hr)),
        hdFin, hzeroFin,
        (hout2.trans (MemEqOutside.of_mem_eq hmem4 512 608)).trans houtFin, ?_⟩
      intro x hx
      rcases htrRest x hx with hprev | hmem
      · rw [← hk1] at hprev
        simp only [chainIterInputs, List.mem_append, List.mem_singleton] at hprev
        rcases hprev with hprev0 | rfl
        · exact Or.inl hprev0
        · exact Or.inr (List.mem_append_left _ (List.mem_singleton_self _))
      · exact Or.inr (List.mem_append_right _ hmem)

/-- Stage 1 + chain loop setup (`pc[332..343]`, 12 steps, 1 oracle call) when `9 ≤ lvl ≤ 16`. -/
private theorem step_hashLevelNode_stage1 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (s : MachineState) (src dst lvl : Nat)
    (hl1 : 9 ≤ lvl) (hl2 : lvl ≤ 16)
    (hpc : s.pc = pcWord 332)
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (levelMetaOC lvl))
    (hx7 : s.getReg .x7 = BitVec.ofNat 64 (levelChain lvl))
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hsrc_hi : src + 96 ≤ 4294971392)
    (hsrc_disj : src + 96 ≤ 512 ∨ 608 ≤ src)
    (hgap : readBuffer s (src + 64) 32 = 0)
    (hzero : ChainScratchZero s) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let x1 := binaryTaggedInput (readBuffer s src 32) (readBuffer s (src + 32) 32) (levelTag lvl 1)
    let d1 := c96 x1
    ∃ s16,
      StepsTo oracle s s16 12 1 [(x1.cast h768.symm, d1)] ∧
      s16.pc = (if levelChain lvl = 2 then pcWord 348 else pcWord 344) ∧
      s16.getReg .x28 = BitVec.ofNat 64 dst ∧
      s16.getReg .x10 = 512#64 ∧
      s16.getReg .x12 = 512#64 ∧
      s16.getReg .x9 = BitVec.ofNat 64 (256 * lvl + levelChain lvl) ∧
      s16.getReg .x7 = BitVec.ofNat 64 (256 * lvl + 2) ∧
      (∀ r : Reg, r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → s16.getReg r = s.getReg r) ∧
      readBuffer s16 512 32 = d1 ∧
      ChainScratchZero s16 ∧
      MemEqOutside s s16 512 544 := by
  intro c96 x1 d1
  have hc_bd := levelChain_bounds lvl (by omega) (by omega)
  have htag_eq : levelTagStart lvl = 256 * lvl + 1 := by interval_cases lvl <;> decide
  have hst332 := step_ordinary oracle s 332 (.ADDI .x28 .x12 0#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s (.ADDI .x28 .x12 0#12)
  have hpc5 : s5.pc = pcWord 333 := by simp only [s5, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst333 := step_ordinary oracle s5 333 (.SRLI .x9 .x6 32#6) (by decide) hpc5 rfl (by intro h; cases h) rfl
  let s6 := execInstrBr s5 (.SRLI .x9 .x6 32#6)
  have hpc6 : s6.pc = pcWord 334 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
  have hx28_6 : s6.getReg .x28 = BitVec.ofNat 64 dst := by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x28), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hx12, se12_0, BitVec.add_zero]
  have hx9_6 : s6.getReg .x9 = levelTag lvl 1 := by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x6),
      hx6, show (32#6 : BitVec 6).toNat = 32 by decide,
      levelMetaOC_tagStart lvl (by omega) (by omega), htag_eq]; rfl
  have hreg6 : ∀ r, r ≠ .x9 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h9 h28 => by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h28.symm]
  have hmem6 : s6.mem = s.mem := by simp [s6, s5, execInstrBr, mem_setPC, mem_setReg]
  have ha334 : s6.getReg .x10 + signExtend12 64#12 = BitVec.ofNat 64 (src + 64) := by
    rw [hreg6 .x10 (by decide) (by decide), hx10, se12_64]; exact bv64_add src 64
  have hv334 : memoryArgumentsValid s6 (.SD .x10 .x9 64#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha334]
    exact accessValid_ofNat (src + 64) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst334 := step_ordinary oracle s6 334 (.SD .x10 .x9 64#12) (by decide) hpc6 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv334])
  let s7 := execInstrBr s6 (.SD .x10 .x9 64#12)
  have hpc7 : s7.pc = pcWord 335 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
  have hreg7 : ∀ r, s7.getReg r = s6.getReg r := fun r => by
    simp [s7, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
  have hst335 := step_ordinary oracle s7 335 (.ADDI .x12 .x0 512#12) (by decide) hpc7 rfl (by intro h; cases h) rfl
  let s8 := execInstrBr s7 (.ADDI .x12 .x0 512#12)
  have hpc8 : s8.pc = pcWord 336 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
  have hx12_8 : s8.getReg .x12 = 512#64 := by
    simp only [s8, execInstrBr, MachineState.getReg_setPC, getReg_x0]
    rw [MachineState.getReg_setReg_eq (by decide), se12_512, BitVec.zero_add]
  have hreg8 : ∀ r, r ≠ .x12 → s8.getReg r = s6.getReg r := fun r hr => by
    simp only [s8, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, hreg7 r]
  have hs8_byte : ∀ q : Word, s8.getByte q = (s.setMem (BitVec.ofNat 64 (src + 64)) (levelTag lvl 1)).getByte q := by
    intro q
    simp only [s8, execInstrBr, MachineState.getByte, MachineState.getMem, mem_setPC, mem_setReg]
    simp only [s7, execInstrBr, ha334, hx9_6, MachineState.setMem, mem_setPC, hmem6]
  have hout8 : MemEqOutside s s8 (src + 64) (src + 72) := fun a ha hout => by
    rw [hs8_byte]; exact MemEqOutside_setMem s (src + 64) _ (by omega) (by omega) a ha hout
  have hgap_bytes : ∀ j < 32, s.getByte (BitVec.ofNat 64 (src + 64 + j)) = 0#8 := by
    intro j hj
    have hb := read_buffer_byte s (src + 64) 32 j hj
    rw [hgap] at hb; simpa using hb.symm
  have hinp1 : readBuffer s8 src 96 = x1 := by
    have hlo : readBuffer s8 src 32 = readBuffer s src 32 := hout8.readBuffer_eq (by omega) (by omega)
    have hmid : readBuffer s8 (src + 32) 32 = readBuffer s (src + 32) 32 := hout8.readBuffer_eq (by omega) (by omega)
    have htag : readBuffer s8 (src + 64) 8 = levelTag lvl 1 := by
      rw [readBuffer_word s8 (src + 64) (by omega)]
      simp only [s8, execInstrBr, MachineState.getMem_setPC, MachineState.getMem_setReg]
      simp only [s7, execInstrBr, ha334, hx9_6, MachineState.getMem_setPC, MachineState.getMem_setMem_eq]
    have hhi : readBuffer s8 (src + 72) 24 = 0 := by
      apply readBuffer_zero_of_bytes; intro j hj
      rw [hout8 (src + 72 + j) (by omega) (by omega), show src + 72 + j = src + 64 + (8 + j) by omega]
      exact hgap_bytes (8 + j) (by omega)
    rw [readBuffer_binaryTagged s8 src (levelTag lvl 1) htag hhi, hlo, hmid]
  have hec1 := step_ecall_compress h768 oracle s8 336 src 512 (by decide) hpc8 rfl
    ((hreg8 .x5 (by decide)).trans ((hreg6 .x5 (by decide) (by decide)).trans hx5))
    ((hreg8 .x11 (by decide)).trans ((hreg6 .x11 (by decide) (by decide)).trans hx11))
    ((hreg8 .x13 (by decide)).trans ((hreg6 .x13 (by decide) (by decide)).trans hx13))
    ((hreg8 .x10 (by decide)).trans ((hreg6 .x10 (by decide) (by decide)).trans hx10))
    hx12_8 hsrc_al (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; decide)
  rw [hinp1] at hec1
  let s9 := writeBits s8 (BitVec.ofNat 64 512) d1
  have hpc9 : s9.pc = pcWord 337 := by simp only [s9, writeBits, MachineState.setPC, hpc8, pcWord_add_four]
  have hreg9 : ∀ r, s9.getReg r = s8.getReg r := fun r => writeBits_register s8 _ d1 r
  have ha337 : s9.getReg .x10 + signExtend12 64#12 = BitVec.ofNat 64 (src + 64) := by
    rw [hreg9 .x10, hreg8 .x10 (by decide), hreg6 .x10 (by decide) (by decide), hx10, se12_64]
    exact bv64_add src 64
  have hv337 : memoryArgumentsValid s9 (.SD .x10 .x0 64#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha337]
    exact accessValid_ofNat (src + 64) 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst337 := step_ordinary oracle s9 337 (.SD .x10 .x0 64#12) (by decide) hpc9 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv337])
  -- Wrap s10 opaquely to prevent nested execInstrBr expansion in pc[338..343]
  have hstage1 : ∃ s10,
      StepsTo oracle s s10 6 1 [(x1.cast h768.symm, d1)] ∧
      s10.pc = pcWord 338 ∧
      s10.getReg .x28 = BitVec.ofNat 64 dst ∧
      s10.getReg .x9 = levelTag lvl 1 ∧
      s10.getReg .x12 = 512#64 ∧
      (∀ r : Reg, r ≠ .x9 → r ≠ .x12 → r ≠ .x28 → s10.getReg r = s.getReg r) ∧
      readBuffer s10 512 32 = d1 ∧
      ChainScratchZero s10 ∧
      MemEqOutside s s10 512 544 := by
    let s10 := execInstrBr s9 (.SD .x10 .x0 64#12)
    have hreg10 : ∀ r, s10.getReg r = s8.getReg r := fun r => by
      have : s10.getReg r = s9.getReg r := by simp [s10, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      exact this.trans (hreg9 r)
    have hout10 : MemEqOutside s s10 512 544 := by
      intro a ha hout
      have h10_byte : s10.getByte (BitVec.ofNat 64 a) =
          (s9.setMem (BitVec.ofNat 64 (src + 64)) 0#64).getByte (BitVec.ofNat 64 a) := by
        simp only [s10, execInstrBr, ha337, getReg_x0, MachineState.getByte, MachineState.getMem_setPC]
      rw [h10_byte]
      by_cases hin : src + 64 ≤ a ∧ a < src + 72
      · have hj : a - (src + 64) < 8 := by omega
        rw [show a = src + 64 + (a - (src + 64)) by omega,
          setMem_getByte_inside s9 (src + 64) (a - (src + 64)) 0#64 (by omega) hj,
          hgap_bytes (a - (src + 64)) (by omega)]
        simp [BitVec.extractLsb']
      · rw [setMem_getByte_ofNat s9 (src + 64) a 0#64 (by omega) (by omega) ha (by omega),
          MemEqOutside_writeBits_digest s8 512 d1 (by decide) a ha hout,
          hout8 a ha (by omega)]
    have hd10 : readBuffer s10 512 32 = d1 := by
      have h10_out : MemEqOutside s9 s10 (src + 64) (src + 72) := fun a ha hout => by
        simp only [s10, execInstrBr, ha337, getReg_x0, MachineState.getByte, MachineState.getMem_setPC]
        exact MemEqOutside_setMem s9 (src + 64) 0#64 (by omega) (by omega) a ha hout
      exact (h10_out.readBuffer_eq (by decide) (by omega)).trans (writeBits_readBuffer_digest s8 512 d1)
    exact ⟨s10, (((hst332.trans hst333).trans (hst334.trans hst335)).trans (hec1.trans hst337)).eq_of rfl (by decide) (by decide) (by simp [d1, c96]),
      by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four],
      (hreg10 .x28).trans ((hreg8 .x28 (by decide)).trans hx28_6),
      (hreg10 .x9).trans ((hreg8 .x9 (by decide)).trans hx9_6),
      (hreg10 .x12).trans hx12_8,
      fun r h9 h12 h28 => (hreg10 r).trans ((hreg8 r h12).trans (hreg6 r h9 h28)),
      hd10, hzero.of_outside hout10 (by omega) (by omega), hout10⟩
  obtain ⟨s10, hs10, hpc10, hx28_10, hx9_10, hx12_10, hreg10, hd10, hzero10, hout10⟩ := hstage1
  -- pc[338..343]: setup loop bounds
  have hst338 := step_ordinary oracle s10 338 (.ADD .x9 .x9 .x7) (by decide) hpc10 rfl (by intro h; cases h) rfl
  let s11 := execInstrBr s10 (.ADD .x9 .x9 .x7)
  have hpc11 : s11.pc = pcWord 339 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
  have hst339 := step_ordinary oracle s11 339 (.ADDI .x9 .x9 4095#12) (by decide) hpc11 rfl (by intro h; cases h) rfl
  let s12 := execInstrBr s11 (.ADDI .x9 .x9 4095#12)
  have hpc12 : s12.pc = pcWord 340 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
  have hst340 := step_ordinary oracle s12 340 (.SRLI .x7 .x6 32#6) (by decide) hpc12 rfl (by intro h; cases h) rfl
  let s13 := execInstrBr s12 (.SRLI .x7 .x6 32#6)
  have hpc13 : s13.pc = pcWord 341 := by simp only [s13, execInstrBr, MachineState.setPC, hpc12, pcWord_add_four]
  have hst341 := step_ordinary oracle s13 341 (.ADDI .x7 .x7 1#12) (by decide) hpc13 rfl (by intro h; cases h) rfl
  let s14 := execInstrBr s13 (.ADDI .x7 .x7 1#12)
  have hpc14 : s14.pc = pcWord 342 := by simp only [s14, execInstrBr, MachineState.setPC, hpc13, pcWord_add_four]
  have hst342 := step_ordinary oracle s14 342 (.ADDI .x10 .x0 512#12) (by decide) hpc14 rfl (by intro h; cases h) rfl
  let s15 := execInstrBr s14 (.ADDI .x10 .x0 512#12)
  have hpc15 : s15.pc = pcWord 343 := by simp only [s15, execInstrBr, MachineState.setPC, hpc14, pcWord_add_four]
  have hmem15 : s15.mem = s10.mem := by simp [s15, s14, s13, s12, s11, execInstrBr, mem_setPC, mem_setReg]
  have hx9_15 : s15.getReg .x9 = BitVec.ofNat 64 (256 * lvl + levelChain lvl) := by
    simp only [s15, s14, s13, s12, s11, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x9), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x9), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x9), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide),
      hx9_10, hreg10 .x7 (by decide) (by decide) (by decide), hx7]
    unfold levelTag; rw [bv64_add, show 256 * lvl + 1 + levelChain lvl = (256 * lvl + levelChain lvl) + 1 by omega]
    exact bv64_add_neg1 _
  have hx7_15 : s15.getReg .x7 = BitVec.ofNat 64 (256 * lvl + 2) := by
    simp only [s15, s14, s13, s12, s11, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x6), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x6),
      hreg10 .x6 (by decide) (by decide) (by decide), hx6,
      show (32#6 : BitVec 6).toNat = 32 by decide, levelMetaOC_tagStart lvl (by omega) (by omega), htag_eq, se12_1]
    change BitVec.ofNat 64 (256 * lvl + 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (256 * lvl + 2)
    rw [bv64_add]
  have hx10_15 : s15.getReg .x10 = 512#64 := by
    simp only [s15, execInstrBr, MachineState.getReg_setPC, getReg_x0]
    rw [MachineState.getReg_setReg_eq (by decide), se12_512, BitVec.zero_add]
  have hreg15 : ∀ r, r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s15.getReg r = s10.getReg r := fun r h7 h9 h10 => by
    simp only [s15, s14, s13, s12, s11, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h9.symm]
  have hst343 := step_ordinary oracle s15 343 (.BEQ .x7 .x9 20#13) (by decide) hpc15 rfl (by intro h; cases h) rfl
  let s16 := execInstrBr s15 (.BEQ .x7 .x9 20#13)
  have hbeq15 : (s15.getReg .x7 == s15.getReg .x9) = decide (levelChain lvl = 2) := by
    rw [hx7_15, hx9_15, bv64_beq_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have hmem16 : s16.mem = s10.mem :=
    (mem_execInstrBr_beq s15 .x7 .x9 20#13).trans hmem15
  have hreg16 : ∀ r, s16.getReg r = s15.getReg r := fun r =>
    getReg_execInstrBr_beq s15 .x7 .x9 20#13 r
  have hpc16 : s16.pc = if levelChain lvl = 2 then pcWord 348 else pcWord 344 := by
    by_cases hc2 : levelChain lvl = 2
    · rw [if_pos hc2]; simp only [s16, execInstrBr, hbeq15, hc2, decide_true, ite_true, MachineState.setPC, hpc15]; decide
    · rw [if_neg hc2]; simp only [s16, execInstrBr, hbeq15, hc2, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc15, pcWord_add_four]
  refine ⟨s16, (hs10.trans (((hst338.trans hst339).trans (hst340.trans hst341)).trans (hst342.trans hst343))).eq_of rfl (by decide) (by decide) (by simp),
    hpc16,
    (hreg16 .x28).trans ((hreg15 .x28 (by decide) (by decide) (by decide)).trans hx28_10),
    (hreg16 .x10).trans hx10_15,
    (hreg16 .x12).trans ((hreg15 .x12 (by decide) (by decide) (by decide)).trans hx12_10),
    (hreg16 .x9).trans hx9_15,
    (hreg16 .x7).trans hx7_15,
    fun r h7 h9 h10 h12 h28 => (hreg16 r).trans ((hreg15 r h7 h9 h10).trans (hreg10 r h9 h12 h28)),
    by rw [(MemEqOutside.of_mem_eq hmem16 0 0).readBuffer_eq (by decide) (by omega), hd10],
    hzero10.of_mem_eq hmem16,
    hout10.trans (MemEqOutside.of_mem_eq hmem16 512 544)⟩

/-- Call and return from `hashLevelNode` (`pc[325..358]`): computes `chainHash c96 lvl dL dR`
from `[src, src+64)` (with zero gap `[src+64, src+96)`) into `[dst, dst+32)`, using exact
`levelChain lvl` oracle calls and recording every input of `chainInputs c96 lvl dL dR` in the trace. -/
theorem step_hashLevelNode (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (s : MachineState) (retIdx src dst lvl : Nat)
    (hl1 : 2 ≤ lvl) (hl2 : lvl ≤ 24)
    (hpc : s.pc = pcWord 325) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 359)
    (hfix : CheckFixedRegs s)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (levelMetaOC lvl))
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_hi : src + 96 ≤ 4294971392) (hdst_hi : dst + 32 ≤ 4294971392)
    (hsrc_disj : src + 96 ≤ 512 ∨ 608 ≤ src)
    (hdst_disj : dst + 32 ≤ 512 ∨ 608 ≤ dst)
    (hgap : readBuffer s (src + 64) 32 = 0)
    (hzero : ChainScratchZero s) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let dL := readBuffer s src 32
    let dR := readBuffer s (src + 32) 32
    ∃ s' k tr,
      k ≤ 83 ∧
      StepsTo oracle s s' k (levelChain lvl) tr ∧
      s'.pc = pcWord retIdx ∧
      (∀ r : Reg, r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = chainHash c96 lvl dL dR ∧
      ChainScratchZero s' ∧
      (∀ a : Nat, a < 2 ^ 64 → (a < dst ∨ dst + 32 ≤ a) → (a < 512 ∨ 608 ≤ a) →
        s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
      (∀ x ∈ chainInputs c96 lvl dL dR, (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ tr) := by
  intro c96 dL dR
  have hc_bd := levelChain_bounds lvl hl1 hl2
  -- pc[325..328]: x7 = levelChain lvl, x9 = 1, BNE x7, x9, 16 (-> 332)
  have hst0 := step_ordinary oracle s 325 (.SRLI .x7 .x6 16#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SRLI .x7 .x6 16#6)
  have hpc1 : s1.pc = pcWord 326 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst1 := step_ordinary oracle s1 326 (.ANDI .x7 .x7 255#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ANDI .x7 .x7 255#12)
  have hpc2 : s2.pc = pcWord 327 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hst2 := step_ordinary oracle s2 327 (.ADDI .x9 .x0 1#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADDI .x9 .x0 1#12)
  have hpc3 : s3.pc = pcWord 328 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 (levelChain lvl) := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x7), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide),
      hx6, se12_255, show (16#6 : BitVec 6).toNat = 16 by decide]
    exact levelMetaOC_chain lvl hl1 hl2
  have hx9_3 : s3.getReg .x9 = BitVec.ofNat 64 1 := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, getReg_x0]
    rw [MachineState.getReg_setReg_eq (by decide), se12_1]; decide
  have hreg3 : ∀ r, r ≠ .x7 → r ≠ .x9 → s3.getReg r = s.getReg r := fun r h7 h9 => by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h9.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
  have hmem3 : s3.mem = s.mem := by simp [s3, s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hst3 := step_ordinary oracle s3 328 (.BNE .x7 .x9 16#13) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.BNE .x7 .x9 16#13)
  have hbne3 : (s3.getReg .x7 != s3.getReg .x9) = decide (levelChain lvl ≠ 1) := by
    rw [hx7_3, hx9_3]; exact bv64_bne_eq (levelChain lvl) 1 (by omega) (by decide)
  have hmem4 : s4.mem = s.mem :=
    (mem_execInstrBr_bne s3 .x7 .x9 16#13).trans hmem3
  have hreg4 : ∀ r, s4.getReg r = s3.getReg r := fun r =>
    getReg_execInstrBr_bne s3 .x7 .x9 16#13 r
  have hpre4 : StepsTo oracle s s4 4 0 [] :=
    (((hst0.trans hst1).trans hst2).trans hst3).eq_of rfl (by decide) (by decide) (by simp)
  by_cases hc1 : levelChain lvl = 1
  · -- Branch A (c = 1): pc[329..331] -> pc[351..358]
    have hpc4 : s4.pc = pcWord 329 := by
      simp only [s4, execInstrBr, hbne3, hc1, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc3, pcWord_add_four]
    have hec := step_ecall_compress h768 oracle s4 329 src dst (by decide) hpc4 rfl
      ((hreg4 .x5).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))
      ((hreg4 .x11).trans ((hreg3 .x11 (by decide) (by decide)).trans hfix.x11))
      ((hreg4 .x13).trans ((hreg3 .x13 (by decide) (by decide)).trans hfix.x13))
      ((hreg4 .x10).trans ((hreg3 .x10 (by decide) (by decide)).trans hx10))
      ((hreg4 .x12).trans ((hreg3 .x12 (by decide) (by decide)).trans hx12))
      hsrc_al hdst_al (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
    have hinp : readBuffer s4 src 96 = binaryInput dL dR := by
      rw [(MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega)]
      exact readBuffer_binary_of_zero_gap s src hgap
    rw [hinp] at hec
    let d0 := c96 (binaryInput dL dR)
    let s5 := writeBits s4 (BitVec.ofNat 64 dst) d0
    have hpc5 : s5.pc = pcWord 330 := by simp only [s5, writeBits, MachineState.setPC, hpc4, pcWord_add_four]
    have hst5 := step_ordinary oracle s5 330 (.ADDI .x28 .x12 0#12) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.ADDI .x28 .x12 0#12)
    have hpc6 : s6.pc = pcWord 331 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
    have hst6 := step_ordinary oracle s6 331 (.JAL .x0 80#21) (by decide) hpc6 rfl (by intro h; cases h) rfl
    let s7 := execInstrBr s6 (.JAL .x0 80#21)
    have hpc7 : s7.pc = pcWord 351 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6]; decide
    have hmem7 : s7.mem = s5.mem := by simp [s7, s6, execInstrBr, MachineState.setReg, mem_setPC]
    have hreg7 : ∀ r, r ≠ .x7 → r ≠ .x9 → r ≠ .x28 → s7.getReg r = s.getReg r := fun r h7 h9 h28 => by
      have h76 : s7.getReg r = s6.getReg r := by simp [s7, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
      rw [h76]; simp only [s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h28.symm, writeBits_register s4 _ d0 r, hreg4 r, hreg3 r h7 h9]
    have hx28_7 : s7.getReg .x28 = BitVec.ofNat 64 dst := by
      have h76 : s7.getReg .x28 = s6.getReg .x28 := by simp [s7, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
      rw [h76]; simp only [s6, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), writeBits_register s4 _ d0 .x12, hreg4 .x12,
        hreg3 .x12 (by decide) (by decide), hx12, se12_0, BitVec.add_zero]
    obtain ⟨sFin, hmask, hpcFin, hregFin, hdigFin, houtFin⟩ :=
      step_hashLevelNode_mask oracle s7 retIdx dst lvl hl1 hl2 hpc7
        ((hreg7 .x1 (by decide) (by decide) (by decide)).trans hret) hret_lt
        ((hreg7 .x6 (by decide) (by decide) (by decide)).trans hx6) hx28_7
        hdst_al (by unfold MEMORY_BYTES; omega)
    have hout_all : MemEqOutside s sFin dst (dst + 32) :=
      ((MemEqOutside.of_mem_eq hmem4 dst (dst + 32)).trans
        ((MemEqOutside_writeBits_digest s4 dst d0 (by omega)).trans
          (MemEqOutside.of_mem_eq hmem7 dst (dst + 32)))).trans houtFin
    refine ⟨sFin, 15, [((binaryInput dL dR).cast h768.symm, d0)], by decide,
      (((hpre4.trans hec).trans (hst5.trans hst6)).trans hmask).eq_of rfl (by decide) (by omega) (by simp [d0, c96]),
      hpcFin, fun r h7 h9 _ _ h28 => (hregFin r h7 h9).trans (hreg7 r h7 h9 h28), ?_,
      hzero.of_outside hout_all (by omega) (by omega),
      fun a ha hd _ => hout_all a ha hd, ?_⟩
    · rw [hdigFin, (MemEqOutside.of_mem_eq hmem7 0 0).readBuffer_eq (by omega) (by omega),
        writeBits_readBuffer_digest s4 dst d0, chainHash_unchained c96 lvl (by omega)]
    · intro x hx
      unfold chainInputs at hx
      rw [if_pos (by omega)] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact List.mem_singleton_self _
  · -- Branch B (2 ≤ levelChain lvl ≤ 16, so 9 ≤ lvl ≤ 16): pc[332..350] -> pc[351..358]
    obtain ⟨hc_ge2, _⟩ := levelTagStart_of_gt1 lvl hl1 hl2 hc1
    have hl9 : 9 ≤ lvl ∧ lvl ≤ 16 := by interval_cases lvl <;> first | exact (hc1 rfl).elim | omega
    have hpc4 : s4.pc = pcWord 332 := by
      simp only [s4, execInstrBr, hbne3, hc1, ne_eq, not_false_eq_true, decide_true,
        ite_true, MachineState.setPC, hpc3]; decide
    have hdL4 : readBuffer s4 src 32 = dL := (MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega)
    have hdR4 : readBuffer s4 (src + 32) 32 = dR := (MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega)
    obtain ⟨s16, hs16, hpc16, hx28_16, hx10_16, hx12_16, hx9_16, hx7_16, hreg16_4, hd16, hzero16, hout16_4⟩ :=
      step_hashLevelNode_stage1 h768 oracle s4 src dst lvl hl9.1 hl9.2 hpc4
        ((hreg4 .x5).trans ((hreg3 .x5 (by decide) (by decide)).trans hfix.x5))
        ((hreg4 .x11).trans ((hreg3 .x11 (by decide) (by decide)).trans hfix.x11))
        ((hreg4 .x13).trans ((hreg3 .x13 (by decide) (by decide)).trans hfix.x13))
        ((hreg4 .x6).trans ((hreg3 .x6 (by decide) (by decide)).trans hx6))
        ((hreg4 .x7).trans hx7_3)
        ((hreg4 .x10).trans ((hreg3 .x10 (by decide) (by decide)).trans hx10))
        ((hreg4 .x12).trans ((hreg3 .x12 (by decide) (by decide)).trans hx12))
        hsrc_al hsrc_hi hsrc_disj
        (by rw [(MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega)]; exact hgap)
        (hzero.of_mem_eq hmem4)
    rw [hdL4, hdR4] at hs16 hd16
    let x1 := binaryTaggedInput dL dR (levelTag lvl 1)
    let d1 := c96 x1
    have hreg16_s : ∀ r, r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → s16.getReg r = s.getReg r :=
      fun r h7 h9 h10 h12 h28 => (hreg16_4 r h7 h9 h10 h12 h28).trans ((hreg4 r).trans (hreg3 r h7 h9))
    have hout16 : MemEqOutside s s16 512 544 :=
      (MemEqOutside.of_mem_eq hmem4 512 544).trans hout16_4
    have hpre16 : StepsTo oracle s s16 16 1 [(x1.cast h768.symm, d1)] :=
      (hpre4.trans hs16).eq_of rfl (by decide) (by decide) (by simp [x1, d1, c96])
    -- Reach pc[348] with readBuffer 512 32 = chainIter c96 lvl (c - 2) d1 in 4 * (c - 2) steps and (c - 2) calls
    have hto348 : ∃ s17 trMid,
        StepsTo oracle s16 s17 (4 * (levelChain lvl - 2)) (levelChain lvl - 2) trMid ∧
        s17.pc = pcWord 348 ∧
        (∀ r : Reg, r ≠ .x7 → s17.getReg r = s16.getReg r) ∧
        readBuffer s17 512 32 = chainIter c96 lvl (levelChain lvl - 2) d1 ∧
        ChainScratchZero s17 ∧
        MemEqOutside s16 s17 512 608 ∧
        (∀ x ∈ chainIterInputs c96 lvl (levelChain lvl - 2) d1,
          (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ trMid) := by
      by_cases hc2 : levelChain lvl = 2
      · rw [if_pos hc2] at hpc16
        refine ⟨s16, [], (StepsTo.refl oracle s16).eq_of rfl (by omega) (by omega) rfl, hpc16,
          fun _ _ => rfl,
          by rw [hd16, show levelChain lvl - 2 = 0 by omega]; rfl,
          hzero16, MemEqOutside.refl s16 512 608,
          fun x hx => by rw [show levelChain lvl - 2 = 0 by omega] at hx; simp [chainIterInputs] at hx⟩
      · rw [if_neg hc2] at hpc16
        obtain ⟨s17, trMid, hloop, hpc17, _, hreg17, hd17, hzero17, hout17, htr17⟩ :=
          step_hashLevelNode_chainLoop h768 oracle lvl hl9.1 hl9.2 d1 (levelChain lvl - 2) (Nat.le_refl _) s16 hpc16
            ((hreg16_s .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5)
            ((hreg16_s .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11)
            ((hreg16_s .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13)
            hx10_16 hx12_16 hx9_16
            (by rw [hx7_16]; congr 1; omega)
            (by rw [hd16, show levelChain lvl - 2 - (levelChain lvl - 2) = 0 by omega]; rfl)
            hzero16 (by omega)
        refine ⟨s17, trMid, hloop, hpc17, hreg17, hd17, hzero17, hout17, ?_⟩
        intro x hx
        rcases htr17 x hx with h0 | hm
        · rw [show levelChain lvl - 2 - (levelChain lvl - 2) = 0 by omega] at h0; simp [chainIterInputs] at h0
        · exact hm
    obtain ⟨s17, trMid, hloop, hpc17, hreg17, hd17, hzero17, hout17, htr17⟩ := hto348
    -- pc[348..350]: SD x10, x9, 64; ADDI x12, x28, 0; ECALL (512 -> dst)
    have hx10_17 : s17.getReg .x10 = 512#64 := (hreg17 .x10 (by decide)).trans hx10_16
    have hx9_17 : s17.getReg .x9 = levelTag lvl (levelChain lvl) := (hreg17 .x9 (by decide)).trans hx9_16
    have hx28_17 : s17.getReg .x28 = BitVec.ofNat 64 dst := (hreg17 .x28 (by decide)).trans hx28_16
    have ha348 : s17.getReg .x10 + signExtend12 64#12 = BitVec.ofNat 64 576 := by
      rw [hx10_17, se12_64]; decide
    have hv348 : memoryArgumentsValid s17 (.SD .x10 .x9 64#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha348]
      exact accessValid_ofNat 576 8 (by unfold MEMORY_BYTES; decide) (by decide)
    have hst348 := step_ordinary oracle s17 348 (.SD .x10 .x9 64#12) (by decide) hpc17 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv348])
    let s18 := execInstrBr s17 (.SD .x10 .x9 64#12)
    have hpc18 : s18.pc = pcWord 349 := by simp only [s18, execInstrBr, MachineState.setPC, hpc17, pcWord_add_four]
    have hst349 := step_ordinary oracle s18 349 (.ADDI .x12 .x28 0#12) (by decide) hpc18 rfl (by intro h; cases h) rfl
    let s19 := execInstrBr s18 (.ADDI .x12 .x28 0#12)
    have hpc19 : s19.pc = pcWord 350 := by simp only [s19, execInstrBr, MachineState.setPC, hpc18, pcWord_add_four]
    have hreg18 : ∀ r, s18.getReg r = s17.getReg r := fun r => by
      simp [s18, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    have hx12_19 : s19.getReg .x12 = BitVec.ofNat 64 dst := by
      simp only [s19, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg18 .x28, hx28_17, se12_0, BitVec.add_zero]
    have hreg19 : ∀ r, r ≠ .x12 → s19.getReg r = s17.getReg r := fun r hr => by
      simp only [s19, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, hreg18 r]
    have hs19_byte : ∀ q : Word, s19.getByte q = (s17.setMem (BitVec.ofNat 64 576) (levelTag lvl (levelChain lvl))).getByte q := by
      intro q
      simp only [s19, execInstrBr, MachineState.getByte, MachineState.getMem, mem_setPC, mem_setReg]
      simp only [s18, execInstrBr, ha348, hx9_17, MachineState.setMem, mem_setPC]
    have hout19 : MemEqOutside s17 s19 576 584 := fun a ha hout => by
      rw [hs19_byte]; exact MemEqOutside_setMem s17 576 _ (by decide) (by decide) a ha hout
    have hzero19 : ChainScratchZero s19 := hzero17.of_outside hout19 (by omega) (by omega)
    have hinpFin : readBuffer s19 512 96 =
        chainStepInput (chainIter c96 lvl (levelChain lvl - 2) d1) (levelTag lvl (levelChain lvl)) := by
      have htag19 : readBuffer s19 (512 + 64) 8 = levelTag lvl (levelChain lvl) := by
        rw [show 512 + 64 = 576 by omega, readBuffer_word s19 576 (by decide)]
        simp only [s19, execInstrBr, MachineState.getMem_setPC, MachineState.getMem_setReg]
        simp only [s18, execInstrBr, ha348, hx9_17, MachineState.getMem_setPC, MachineState.getMem_setMem_eq]
      rw [readBuffer_chainStep s19 512 _ hzero19.mid_zero htag19 hzero19.hi_zero,
        (hout19.readBuffer_eq (by decide) (by omega)).trans hd17]
    have hecFin := step_ecall_compress h768 oracle s19 350 512 dst (by decide) hpc19 rfl
      ((hreg19 .x5 (by decide)).trans ((hreg17 .x5 (by decide)).trans ((hreg16_s .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x5)))
      ((hreg19 .x11 (by decide)).trans ((hreg17 .x11 (by decide)).trans ((hreg16_s .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x11)))
      ((hreg19 .x13 (by decide)).trans ((hreg17 .x13 (by decide)).trans ((hreg16_s .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x13)))
      ((hreg19 .x10 (by decide)).trans hx10_17) hx12_19
      (by decide) hdst_al (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; omega)
    rw [hinpFin] at hecFin
    let xFin := chainStepInput (chainIter c96 lvl (levelChain lvl - 2) d1) (levelTag lvl (levelChain lvl))
    let dFin := c96 xFin
    let s20 := writeBits s19 (BitVec.ofNat 64 dst) dFin
    have hpc20 : s20.pc = pcWord 351 := by simp only [s20, writeBits, MachineState.setPC, hpc19, pcWord_add_four]
    have hreg20_s : ∀ r, r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → s20.getReg r = s.getReg r :=
      fun r h7 h9 h10 h12 h28 =>
        (writeBits_register s19 _ dFin r).trans ((hreg19 r h12).trans ((hreg17 r h7).trans (hreg16_s r h7 h9 h10 h12 h28)))
    have hx28_20 : s20.getReg .x28 = BitVec.ofNat 64 dst :=
      (writeBits_register s19 _ dFin .x28).trans ((hreg19 .x28 (by decide)).trans hx28_17)
    obtain ⟨sFin, hmask, hpcFin, hregFin, hdigFin, houtMask⟩ :=
      step_hashLevelNode_mask oracle s20 retIdx dst lvl hl1 hl2 hpc20
        ((hreg20_s .x1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hret) hret_lt
        ((hreg20_s .x6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx6) hx28_20
        hdst_al (by unfold MEMORY_BYTES; omega)
    have hzero20 : ChainScratchZero s20 :=
      hzero19.of_outside (MemEqOutside_writeBits_digest s19 dst dFin (by omega)) (by omega) (by omega)
    have htr_tot := (((hpre16.trans hloop).trans ((hst348.trans hst349).trans hecFin)).trans hmask)
    refine ⟨sFin, 16 + 4 * (levelChain lvl - 2) + 3 + 8,
      [(x1.cast h768.symm, d1)] ++ trMid ++ [(xFin.cast h768.symm, dFin)],
      by omega, htr_tot.eq_of rfl (by omega) (by omega) (by simp [xFin, dFin, c96]),
      hpcFin, fun r h7 h9 h10 h12 h28 => (hregFin r h7 h9).trans (hreg20_s r h7 h9 h10 h12 h28),
      ?_, hzero20.of_outside houtMask (by omega) (by omega), ?_, ?_⟩
    · rw [hdigFin, writeBits_readBuffer_digest s19 dst dFin]
      unfold chainHash chainEval
      rw [if_neg (by omega), show levelChain lvl - 1 = (levelChain lvl - 2) + 1 by omega]
      simp only [chainIter, show levelChain lvl - 2 + 2 = levelChain lvl by omega]
      rfl
    · intro a ha hdst_out h512_out
      rw [houtMask a ha hdst_out, MemEqOutside_writeBits_digest s19 dst dFin (by omega) a ha hdst_out,
        hout19 a ha (by omega), hout17 a ha h512_out, hout16 a ha (by omega)]
    · intro x hx
      unfold chainInputs at hx
      rw [if_neg (by omega), show levelChain lvl - 1 = (levelChain lvl - 2) + 1 by omega] at hx
      simp only [chainIterInputs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        show levelChain lvl - 2 + 2 = levelChain lvl by omega] at hx
      rcases hx with rfl | hmid | rfl
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))
      · exact List.mem_append_left _ (List.mem_append_right _ (htr17 x hmid))
      · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Helper: `JAL .x1` to `hashLevelNode` (`pc[325]`), ≤ 84 steps, exact `levelChain lvl` oracle calls. -/
theorem step_call_hashLevelNode (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (idx : Nat) (s : MachineState) (src dst lvl : Nat)
    (hl1 : 2 ≤ lvl) (hl2 : lvl ≤ 24) (hhi : idx + 1 ≤ 325)
    (hjal : checkInstr idx = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (325 - idx)))))
    (hpc : s.pc = pcWord idx)
    (hfix : CheckFixedRegs s)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (levelMetaOC lvl))
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_hi : src + 96 ≤ 4294971392) (hdst_hi : dst + 32 ≤ 4294971392)
    (hsrc_disj : src + 96 ≤ 512 ∨ 608 ≤ src)
    (hdst_disj : dst + 32 ≤ 512 ∨ 608 ≤ dst)
    (hgap : readBuffer s (src + 64) 32 = 0)
    (hzero : ChainScratchZero s) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let dL := readBuffer s src 32
    let dR := readBuffer s (src + 32) 32
    ∃ s' k tr,
      k ≤ 84 ∧
      StepsTo oracle s s' k (levelChain lvl) tr ∧
      s'.pc = pcWord (idx + 1) ∧
      (∀ r : Reg, r ≠ .x1 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = chainHash c96 lvl dL dR ∧
      ChainScratchZero s' ∧
      (∀ a : Nat, a < 2 ^ 64 → (a < dst ∨ dst + 32 ≤ a) → (a < 512 ∨ 608 ≤ a) →
        s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
      (∀ x ∈ chainInputs c96 lvl dL dR, (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ tr) := by
  let off := BitVec.ofNat 21 (4 * (325 - idx))
  have hst0 := step_ordinary oracle s idx (.JAL .x1 off) (by omega) hpc hjal (by intro h; cases h) rfl
  let s1 := execInstrBr s (.JAL .x1 off)
  have hpc1 : s1.pc = pcWord 325 := by
    simp only [s1, execInstrBr, MachineState.setPC, hpc]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (325 - idx)) :=
      signExtend21_ofNat_lt _ (by omega)
    rw [hse21, pcWord, bv64_add]; congr 1; omega
  have hret1 : s1.getReg .x1 = pcWord (idx + 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, hpc, pcWord_add_four]
    exact MachineState.getReg_setReg_eq (by decide)
  have hreg1 : ∀ r, r ≠ .x1 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hfix1 : CheckFixedRegs s1 := hfix.of_agree (fun r hr => hreg1 r (isFixedReg_ne_of_false hr rfl))
  obtain ⟨s', k, tr, hk, hsub, hpc', hreg', hdig', hzero', hout', htr'⟩ :=
    step_hashLevelNode h768 oracle s1 (idx + 1) src dst lvl hl1 hl2 hpc1 hret1 (by omega) hfix1
      ((hreg1 .x6 (by decide)).trans hx6) ((hreg1 .x10 (by decide)).trans hx10)
      ((hreg1 .x12 (by decide)).trans hx12) hsrc_al hdst_al hsrc_hi hdst_hi hsrc_disj hdst_disj
      (by rw [(MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)]; exact hgap)
      (hzero.of_mem_eq hmem1)
  have hdL : readBuffer s1 src 32 = readBuffer s src 32 :=
    (MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)
  have hdR : readBuffer s1 (src + 32) 32 = readBuffer s (src + 32) 32 :=
    (MemEqOutside.of_mem_eq hmem1 0 0).readBuffer_eq (by omega) (by omega)
  rw [hdL, hdR] at hdig' htr'
  refine ⟨s', 1 + k, tr, by omega, (hst0.trans hsub).eq_of rfl rfl (by omega) (by simp),
    hpc', fun r h1 h7 h9 h10 h12 h28 => (hreg' r h7 h9 h10 h12 h28).trans (hreg1 r h1),
    hdig', hzero', fun a ha hd h512 => (hout' a ha hd h512).trans (by simp [MachineState.getByte, MachineState.getMem, hmem1]),
    htr'⟩

/-- Generic `m`-dword copy (`LD x6, (srcOff + 8j)(rSrc); SD x6, (dstOff + 8j)(rDst)`). -/
theorem step_copy_dwords (oracle : Oracle) (base m : Nat) (rSrc rDst : Reg)
    (srcOff dstOff : Nat) (s : MachineState) (srcBase dstBase : Nat)
    (hrSrc : rSrc ≠ .x6) (hrDst : rDst ≠ .x6)
    (hso : srcOff + 8 * m ≤ 256) (hdo : dstOff + 8 * m ≤ 256)
    (hhi : base + 2 * m ≤ 359)
    (hcode : ∀ j < m,
      checkInstr (base + 2 * j) = .base (.LD .x6 rSrc (BitVec.ofNat 12 (srcOff + 8 * j))) ∧
      checkInstr (base + 2 * j + 1) = .base (.SD rDst .x6 (BitVec.ofNat 12 (dstOff + 8 * j))))
    (hpc : s.pc = pcWord base)
    (hsrc : s.getReg rSrc = BitVec.ofNat 64 srcBase)
    (hdst : s.getReg rDst = BitVec.ofNat 64 dstBase)
    (hsrc_al : (srcBase + srcOff) % 8 = 0) (hdst_al : (dstBase + dstOff) % 8 = 0)
    (hsrc_bd : srcBase + srcOff + 8 * m ≤ MEMORY_BYTES)
    (hdst_bd : dstBase + dstOff + 8 * m ≤ MEMORY_BYTES)
    (hdisj : dstBase + dstOff + 8 * m ≤ srcBase + srcOff ∨
             srcBase + srcOff + 8 * m ≤ dstBase + dstOff) :
    ∃ s', StepsTo oracle s s' (2 * m) 0 [] ∧
      s'.pc = pcWord (base + 2 * m) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      (∀ j < 8 * m,
        s'.getByte (BitVec.ofNat 64 (dstBase + dstOff + j)) =
          s.getByte (BitVec.ofNat 64 (srcBase + srcOff + j))) ∧
      MemEqOutside s s' (dstBase + dstOff) (dstBase + dstOff + 8 * m) := by
  induction m with
  | zero =>
    exact ⟨s, StepsTo.refl oracle s, hpc, fun _ _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim,
      MemEqOutside.refl s _ _⟩
  | succ k ih =>
    obtain ⟨sk, hsteps, hpc_k, hregs_k, hcopy_k, hout_k⟩ :=
      ih (by omega) (by omega) (by omega) (fun j hj => hcode j (by omega))
        (by omega) (by omega) (by omega)
    have hse_s : signExtend12 (BitVec.ofNat 12 (srcOff + 8 * k)) = BitVec.ofNat 64 (srcOff + 8 * k) :=
      signExtend12_ofNat_lt256 ⟨srcOff + 8 * k, by omega⟩
    have hse_d : signExtend12 (BitVec.ofNat 12 (dstOff + 8 * k)) = BitVec.ofNat 64 (dstOff + 8 * k) :=
      signExtend12_ofNat_lt256 ⟨dstOff + 8 * k, by omega⟩
    have hsrc_k : sk.getReg rSrc = BitVec.ofNat 64 srcBase := (hregs_k rSrc hrSrc).trans hsrc
    have hdst_k : sk.getReg rDst = BitVec.ofNat 64 dstBase := (hregs_k rDst hrDst).trans hdst
    have ha_s : sk.getReg rSrc + signExtend12 (BitVec.ofNat 12 (srcOff + 8 * k)) =
        BitVec.ofNat 64 (srcBase + srcOff + 8 * k) := by
      rw [hsrc_k, hse_s, bv64_add]; congr 1; omega
    have hval1 : memoryArgumentsValid sk (.LD .x6 rSrc (BitVec.ofNat 12 (srcOff + 8 * k))) = true := by
      simp only [memoryArgumentsValid, memAccess, ha_s]
      exact accessValid_ofNat (srcBase + srcOff + 8 * k) 8 (by omega) (by omega)
    have hst1 : StepsTo oracle sk (execInstrBr sk (.LD .x6 rSrc (BitVec.ofNat 12 (srcOff + 8 * k)))) 1 0 [] :=
      step_ordinary oracle sk (base + 2 * k) _ (by omega) hpc_k (hcode k (by omega)).1 (by intro h; cases h)
        (by simp [ordinaryStep, hval1])
    let sk1 := execInstrBr sk (.LD .x6 rSrc (BitVec.ofNat 12 (srcOff + 8 * k)))
    have hpc1 : sk1.pc = pcWord (base + 2 * k + 1) := by
      simp only [sk1, execInstrBr, MachineState.setPC, hpc_k, pcWord_add_four]
    have hdst1 : sk1.getReg rDst = BitVec.ofNat 64 dstBase := by
      simp only [sk1, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hrDst.symm, hdst_k]
    have hx6_1 : sk1.getReg .x6 = sk.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) := by
      simp only [sk1, execInstrBr, MachineState.getReg_setPC, ha_s]
      rw [MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0)]
    have ha_d : sk1.getReg rDst + signExtend12 (BitVec.ofNat 12 (dstOff + 8 * k)) =
        BitVec.ofNat 64 (dstBase + dstOff + 8 * k) := by
      rw [hdst1, hse_d, bv64_add]; congr 1; omega
    have hval2 : memoryArgumentsValid sk1 (.SD rDst .x6 (BitVec.ofNat 12 (dstOff + 8 * k))) = true := by
      simp only [memoryArgumentsValid, memAccess, ha_d]
      exact accessValid_ofNat (dstBase + dstOff + 8 * k) 8 (by omega) (by omega)
    have hst2 : StepsTo oracle sk1 (execInstrBr sk1 (.SD rDst .x6 (BitVec.ofNat 12 (dstOff + 8 * k)))) 1 0 [] :=
      step_ordinary oracle sk1 (base + 2 * k + 1) _ (by omega) hpc1 (hcode k (by omega)).2 (by intro h; cases h)
        (by simp [ordinaryStep, hval2])
    let sk2 := execInstrBr sk1 (.SD rDst .x6 (BitVec.ofNat 12 (dstOff + 8 * k)))
    have hmem_sk1 : sk1.mem = sk.mem := by simp [sk1, execInstrBr, mem_setPC, mem_setReg]
    have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
    have hsrc_mem : sk.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) =
        s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) :=
      hout_k.getMem_eq (by omega) (by omega) (by omega)
    have hsk2_byte : ∀ q : Word, sk2.getByte q =
        (sk.setMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * k))
          (s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)))).getByte q := by
      intro q
      simp only [sk2, execInstrBr, ha_d, hx6_1, hsrc_mem]
      simp only [MachineState.getByte, MachineState.getMem, MachineState.setMem, mem_setPC, hmem_sk1]
    have hout_step : MemEqOutside sk sk2 (dstBase + dstOff + 8 * k) (dstBase + dstOff + 8 * k + 8) := by
      intro a ha hout
      rw [hsk2_byte]
      exact MemEqOutside_setMem sk (dstBase + dstOff + 8 * k) _ (by omega) (by omega) a ha hout
    refine ⟨sk2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [show 2 * (k + 1) = 2 * k + (1 + 1) by omega, Nat.add_zero, List.append_nil] using
        hsteps.trans (hst1.trans hst2)
    · simp only [sk2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
      congr 1
    · intro r hr
      have hr1 : sk2.getReg r = sk1.getReg r := by
        simp [sk2, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [hr1]
      simp only [sk1, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm]
      exact hregs_k r hr
    · intro j hj
      by_cases hlt : j < 8 * k
      · rw [hout_step (dstBase + dstOff + j) (by omega) (by omega)]
        exact hcopy_k j hlt
      · have hrem : j - 8 * k < 8 := by omega
        have heq_d : dstBase + dstOff + j = dstBase + dstOff + 8 * k + (j - 8 * k) := by omega
        have heq_s : srcBase + srcOff + j = srcBase + srcOff + 8 * k + (j - 8 * k) := by omega
        rw [heq_d, hsk2_byte, setMem_getByte_inside sk _ _ _ (by omega) hrem]
        rw [← readBuffer_word s (srcBase + srcOff + 8 * k) (by omega),
          read_buffer_byte s (srcBase + srcOff + 8 * k) 8 (j - 8 * k) hrem, ← heq_s]
    · exact (hout_k.mono (by omega) (by omega)).trans (hout_step.mono (by omega) (by omega))

/-- Generic 4-dword comparison (`LD x6, (8j)(rA); LD x7, (8j)(rB); BNE x6, x7, pc[287]`). -/
theorem step_compare4 (oracle : Oracle) (base : Nat) (rA rB : Reg)
    (s : MachineState) (addrA addrB : Nat)
    (hrA6 : rA ≠ .x6) (hrA7 : rA ≠ .x7) (hrB6 : rB ≠ .x6) (hrB7 : rB ≠ .x7)
    (hhi : base + 12 ≤ 287)
    (hcode : ∀ j < 4,
      checkInstr (base + 3 * j) = .base (.LD .x6 rA (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 3 * j + 1) = .base (.LD .x7 rB (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (287 - (base + 3 * j + 2))))))
    (hpc : s.pc = pcWord base)
    (hA : s.getReg rA = BitVec.ofNat 64 addrA)
    (hB : s.getReg rB = BitVec.ofNat 64 addrB)
    (hA_al : addrA % 8 = 0) (hB_al : addrB % 8 = 0)
    (hA_bd : addrA + 32 ≤ MEMORY_BYTES) (hB_bd : addrB + 32 ≤ MEMORY_BYTES) :
    PhaseOutcome oracle s 15 0 (readBuffer s addrA 32 ≠ readBuffer s addrB 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        readBuffer s addrA 32 = readBuffer s addrB 32 ∧
        s'.pc = pcWord (base + 12) ∧
        s'.mem = s.mem ∧
        ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → s'.getReg r = s.getReg r) := by
  have hiter : ∀ m ≤ 4,
      PhaseOutcome oracle s (3 * m + 3) 0
        (∃ j < m, s.getMem (BitVec.ofNat 64 (addrA + 8 * j)) ≠ s.getMem (BitVec.ofNat 64 (addrB + 8 * j)))
        (fun s' q tr =>
          q = 0 ∧ tr = [] ∧
          (∀ j < m, s.getMem (BitVec.ofNat 64 (addrA + 8 * j)) = s.getMem (BitVec.ofNat 64 (addrB + 8 * j))) ∧
          s'.pc = pcWord (base + 3 * m) ∧
          s'.mem = s.mem ∧
          ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → s'.getReg r = s.getReg r) := by
    intro m hm
    have hiter_exact : ∀ m ≤ 4,
        (∃ j < m, s.getMem (BitVec.ofNat 64 (addrA + 8 * j)) ≠ s.getMem (BitVec.ofNat 64 (addrB + 8 * j))) ∧
          (∃ steps, steps ≤ 3 * m + 3 ∧ HaltsWith oracle s steps 0 .failure []) ∨
        (∃ s', StepsTo oracle s s' (3 * m) 0 [] ∧
          (∀ j < m, s.getMem (BitVec.ofNat 64 (addrA + 8 * j)) = s.getMem (BitVec.ofNat 64 (addrB + 8 * j))) ∧
          s'.pc = pcWord (base + 3 * m) ∧
          s'.mem = s.mem ∧
          ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → s'.getReg r = s.getReg r) := by
      intro n hn
      induction n with
      | zero =>
        right
        exact ⟨s, StepsTo.refl oracle s, fun _ h => (Nat.not_lt_zero _ h).elim, hpc, rfl, fun _ _ _ => rfl⟩
      | succ k ih =>
        rcases ih (by omega) with ⟨⟨j, hj, hne⟩, ⟨steps, hst, hh⟩⟩ | ⟨sk, hsteps, hprev, hpc_k, hmem_k, hreg_k⟩
        · exact Or.inl ⟨⟨j, by omega, hne⟩, ⟨steps, by omega, hh⟩⟩
        · have hse : signExtend12 (BitVec.ofNat 12 (8 * k)) = BitVec.ofNat 64 (8 * k) :=
            signExtend12_ofNat_lt256 ⟨8 * k, by omega⟩
          have hAk : sk.getReg rA = BitVec.ofNat 64 addrA := (hreg_k rA hrA6 hrA7).trans hA
          have hBk : sk.getReg rB = BitVec.ofNat 64 addrB := (hreg_k rB hrB6 hrB7).trans hB
          have haA : sk.getReg rA + signExtend12 (BitVec.ofNat 12 (8 * k)) = BitVec.ofNat 64 (addrA + 8 * k) := by
            rw [hAk, hse, bv64_add]
          have hval1 : memoryArgumentsValid sk (.LD .x6 rA (BitVec.ofNat 12 (8 * k))) = true := by
            simp only [memoryArgumentsValid, memAccess, haA]
            exact accessValid_ofNat (addrA + 8 * k) 8 (by omega) (by omega)
          have hst1 := step_ordinary oracle sk (base + 3 * k) _ (by omega) hpc_k (hcode k (by omega)).1
            (by intro h; cases h) (by simp [ordinaryStep, hval1])
          let sk1 := execInstrBr sk (.LD .x6 rA (BitVec.ofNat 12 (8 * k)))
          have hpc1 : sk1.pc = pcWord (base + 3 * k + 1) := by
            simp only [sk1, execInstrBr, MachineState.setPC, hpc_k, pcWord_add_four]
          have hB1 : sk1.getReg rB = BitVec.ofNat 64 addrB := by
            simp only [sk1, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ hrB6.symm, hBk]
          have haB : sk1.getReg rB + signExtend12 (BitVec.ofNat 12 (8 * k)) = BitVec.ofNat 64 (addrB + 8 * k) := by
            rw [hB1, hse, bv64_add]
          have hval2 : memoryArgumentsValid sk1 (.LD .x7 rB (BitVec.ofNat 12 (8 * k))) = true := by
            simp only [memoryArgumentsValid, memAccess, haB]
            exact accessValid_ofNat (addrB + 8 * k) 8 (by omega) (by omega)
          have hst2 := step_ordinary oracle sk1 (base + 3 * k + 1) _ (by omega) hpc1 (hcode k (by omega)).2.1
            (by intro h; cases h) (by simp [ordinaryStep, hval2])
          let sk2 := execInstrBr sk1 (.LD .x7 rB (BitVec.ofNat 12 (8 * k)))
          have hpc2 : sk2.pc = pcWord (base + 3 * k + 2) := by
            simp only [sk2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
          have hmem2 : sk2.mem = s.mem := by
            simpa [sk2, sk1, execInstrBr, mem_setPC, mem_setReg] using hmem_k
          have hx6 : sk2.getReg .x6 = s.getMem (BitVec.ofNat 64 (addrA + 8 * k)) := by
            simp only [sk2, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6)]
            simp only [sk1, execInstrBr, MachineState.getReg_setPC, haA]
            rw [MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0)]
            simp only [MachineState.getMem, hmem_k]
          have hx7 : sk2.getReg .x7 = s.getMem (BitVec.ofNat 64 (addrB + 8 * k)) := by
            simp only [sk2, execInstrBr, MachineState.getReg_setPC, haB]
            rw [MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0)]
            simp only [sk1, execInstrBr, MachineState.getMem, mem_setPC, mem_setReg, hmem_k]
          let off := BitVec.ofNat 13 (4 * (287 - (base + 3 * k + 2)))
          have hst3 := step_ordinary oracle sk2 (base + 3 * k + 2) (.BNE .x6 .x7 off) (by omega) hpc2
            (hcode k (by omega)).2.2 (by intro h; cases h) rfl
          have h123 : StepsTo oracle sk (execInstrBr sk2 (.BNE .x6 .x7 off)) 3 0 [] := by
            simpa using (hst1.trans hst2).trans hst3
          by_cases heq : s.getMem (BitVec.ofNat 64 (addrA + 8 * k)) = s.getMem (BitVec.ofNat 64 (addrB + 8 * k))
          · right
            have hpc3 : (execInstrBr sk2 (.BNE .x6 .x7 off)).pc = pcWord (base + 3 * (k + 1)) := by
              simp only [execInstrBr, hx6, hx7, heq, bne_self_eq_false, Bool.false_eq_true, ite_false,
                MachineState.setPC, hpc2, pcWord_add_four]
              congr 1
            refine ⟨_, by simpa [show 3 * (k + 1) = 3 * k + 3 by omega] using hsteps.trans h123, ?_, hpc3, ?_, ?_⟩
            · intro j hj
              by_cases hjk : j < k
              · exact hprev j hjk
              · have : j = k := by omega
                subst this; exact heq
            · simpa only [execInstrBr, hx6, hx7, heq, bne_self_eq_false, Bool.false_eq_true, ite_false,
                MachineState.setPC] using hmem2
            · intro r hr6 hr7
              simp only [execInstrBr, hx6, hx7, heq, bne_self_eq_false, Bool.false_eq_true, ite_false,
                MachineState.getReg_setPC]
              simp only [sk2, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ hr7.symm]
              simp only [sk1, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ hr6.symm]
              exact hreg_k r hr6 hr7
          · left
            have hne_b : (sk2.getReg .x6 != sk2.getReg .x7) = true := by
              rw [hx6, hx7, bne_iff_ne]; exact heq
            have hpc3 : (execInstrBr sk2 (.BNE .x6 .x7 off)).pc = pcWord 287 := by
              simp only [execInstrBr, hne_b, ite_true, MachineState.setPC, hpc2]
              have hse13 : signExtend13 off = BitVec.ofNat 64 (4 * (287 - (base + 3 * k + 2))) :=
                signExtend13_ofNat_lt4096 _ (by omega)
              rw [hse13, pcWord, bv64_add]; congr 1; omega
            refine ⟨⟨k, by omega, heq⟩, ⟨3 * k + 3 + 3, by omega, ?_⟩⟩
            simpa using (hsteps.trans h123).halt (halt_reject oracle _ hpc3)
    rcases hiter_exact m hm with ⟨hne, ⟨steps, hst, hh⟩⟩ | ⟨s', hsteps, hwords, hpc', hmem', hreg'⟩
    · exact .rejected steps 0 [] hne hst (by omega) hh
    · exact .continued s' (3 * m) 0 [] (by omega) (by omega) hsteps ⟨rfl, rfl, hwords, hpc', hmem', hreg'⟩
  refine (hiter 4 (by omega)).weaken (by omega) (by omega) ?_ ?_
  · rintro ⟨j, hj, hne⟩ heq
    exact hne ((read_digest_eq_iff s s addrA addrB hA_al hB_al).mp heq j hj)
  · rintro s' q tr ⟨hq, htr, hwords, hpc', hmem', hreg'⟩
    exact ⟨hq, htr, (read_digest_eq_iff s s addrA addrB hA_al hB_al).mpr hwords, hpc', hmem', hreg'⟩

/-- Zero 4 consecutive dwords at `S[off..off+32)` via `SD x21, x0, (off + 8*k)` (4 steps). -/
theorem step_zero_4dwords (oracle : Oracle) (base off : Nat) (s : MachineState)
    (hhi : base + 4 ≤ 359) (hoff : off + 32 ≤ 256) (hal : off % 8 = 0)
    (hcode : ∀ k < 4, checkInstr (base + k) = .base (.SD .x21 .x0 (BitVec.ofNat 12 (off + 8 * k))))
    (hpc : s.pc = pcWord base) (hx21 : s.getReg .x21 = 256#64) :
    ∃ s', StepsTo oracle s s' 4 0 [] ∧
      s'.pc = pcWord (base + 4) ∧
      (∀ r : Reg, s'.getReg r = s.getReg r) ∧
      readBuffer s' (256 + off) 32 = 0 ∧
      MemEqOutside s s' (256 + off) (256 + off + 32) := by
  have hloop : ∀ m ≤ 4,
      ∃ s', StepsTo oracle s s' m 0 [] ∧
        s'.pc = pcWord (base + m) ∧
        (∀ r : Reg, s'.getReg r = s.getReg r) ∧
        (∀ j < 8 * m, s'.getByte (BitVec.ofNat 64 (256 + off + j)) = 0) ∧
        MemEqOutside s s' (256 + off) (256 + off + 8 * m) := by
    intro m hm
    induction m with
    | zero =>
      exact ⟨s, StepsTo.refl oracle s, hpc, fun _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim,
        MemEqOutside.refl s (256 + off) (256 + off)⟩
    | succ k ih =>
      obtain ⟨sk, hsteps, hpc_k, hreg_k, hzero_k, hout_k⟩ := ih (by omega)
      have hse : signExtend12 (BitVec.ofNat 12 (off + 8 * k)) = BitVec.ofNat 64 (off + 8 * k) :=
        signExtend12_ofNat_lt256 ⟨off + 8 * k, by omega⟩
      have ha : sk.getReg .x21 + signExtend12 (BitVec.ofNat 12 (off + 8 * k)) =
          BitVec.ofNat 64 (256 + off + 8 * k) := by
        rw [hreg_k .x21, hx21, hse, bv64_add]; congr 1; omega
      have hval : memoryArgumentsValid sk (.SD .x21 .x0 (BitVec.ofNat 12 (off + 8 * k))) = true := by
        simp only [memoryArgumentsValid, memAccess, ha]
        exact accessValid_ofNat (256 + off + 8 * k) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst := step_ordinary oracle sk (base + k) _ (by omega) hpc_k (hcode k (by omega))
        (by intro h; cases h) (by simp [ordinaryStep, hval])
      let sk1 := execInstrBr sk (.SD .x21 .x0 (BitVec.ofNat 12 (off + 8 * k)))
      have hbyte : ∀ q : Word, sk1.getByte q = (sk.setMem (BitVec.ofNat 64 (256 + off + 8 * k)) 0#64).getByte q := by
        intro q; simp [sk1, execInstrBr, ha, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
      have hout1 : MemEqOutside sk sk1 (256 + off + 8 * k) (256 + off + 8 * k + 8) := by
        intro a ha2 hout
        rw [hbyte]
        exact MemEqOutside_setMem sk (256 + off + 8 * k) 0#64 (by omega) (by omega) a ha2 hout
      refine ⟨sk1, by simpa using hsteps.trans hst, ?_, ?_, ?_, ?_⟩
      · simp only [sk1, execInstrBr, MachineState.setPC, hpc_k, pcWord_add_four]; congr 1
      · intro r
        have : sk1.getReg r = sk.getReg r := by
          simp [sk1, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        exact this.trans (hreg_k r)
      · intro j hj
        by_cases hlt : j < 8 * k
        · rw [hout1 (256 + off + j) (by omega) (by omega)]; exact hzero_k j hlt
        · have hrem : j - 8 * k < 8 := by omega
          have heq : 256 + off + j = 256 + off + 8 * k + (j - 8 * k) := by omega
          rw [heq, hbyte, setMem_getByte_inside sk _ _ 0#64 (by omega) hrem]
          simp [BitVec.extractLsb']
      · exact (hout_k.mono (by omega) (by omega)).trans (hout1.mono (by omega) (by omega))
  obtain ⟨s', hsteps, hpc', hreg', hzero', hout'⟩ := hloop 4 (by omega)
  exact ⟨s', hsteps, hpc', hreg', readBuffer_zero_of_bytes s' (256 + off) 32 hzero', hout'⟩

/-- Zero `S[64..96)` (`pc[113..116]`, 4 steps). -/
theorem step_zero_gap (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = pcWord 113) (hx21 : s.getReg .x21 = 256#64) :
    ∃ s', StepsTo oracle s s' 4 0 [] ∧
      s'.pc = pcWord 117 ∧
      (∀ r : Reg, s'.getReg r = s.getReg r) ∧
      readBuffer s' 320 32 = 0 ∧
      MemEqOutside s s' 320 352 :=
  step_zero_4dwords oracle 113 64 s (by decide) (by decide) (by decide)
    (fun k hk => by interval_cases k <;> rfl) hpc hx21

/-- Zero `S[32..64)` (`pc[164..167]`, 4 steps, odd-node chain hash). -/
theorem step_zero_right (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = pcWord 164) (hx21 : s.getReg .x21 = 256#64) :
    ∃ s', StepsTo oracle s s' 4 0 [] ∧
      s'.pc = pcWord 168 ∧
      (∀ r : Reg, s'.getReg r = s.getReg r) ∧
      readBuffer s' 288 32 = 0 ∧
      MemEqOutside s s' 288 320 :=
  step_zero_4dwords oracle 164 32 s (by decide) (by decide) (by decide)
    (fun k hk => by interval_cases k <;> rfl) hpc hx21

/-! ### 4. Straight-Line Pure-Instruction Block Stepper -/

/-- Execute a straight-line list of pure (non-memory, non-branch) instructions. -/
def runInstrs (s : MachineState) (l : List Instr) : MachineState :=
  l.foldl execInstrBr s

theorem step_pure_list (oracle : Oracle) (base : Nat) (l : List Instr) (s : MachineState)
    (hhi : base + l.length ≤ 359)
    (hcode : ∀ i (hi : i < l.length), checkInstr (base + i) = .base (l[i]'hi))
    (hpure : ∀ i (hi : i < l.length),
      Instruction.base (l[i]'hi) ≠ .base .ECALL ∧
      ∀ st, ordinaryStep st (.base (l[i]'hi)) = some (execInstrBr st (l[i]'hi)) ∧
            (execInstrBr st (l[i]'hi)).pc = st.pc + (4 : Word) ∧
            (execInstrBr st (l[i]'hi)).mem = st.mem)
    (hpc : s.pc = pcWord base) :
    StepsTo oracle s (runInstrs s l) l.length 0 [] ∧
    (runInstrs s l).pc = pcWord (base + l.length) ∧
    (runInstrs s l).mem = s.mem := by
  induction l generalizing base s with
  | nil =>
    exact ⟨StepsTo.refl oracle s, by simpa [runInstrs] using hpc, rfl⟩
  | cons hd tl ih =>
    have h0 := hcode 0 (by simp)
    have hp0 := hpure 0 (by simp)
    simp only [List.getElem_cons_zero] at h0 hp0
    have hst0 := step_ordinary oracle s base hd (by simp at hhi; omega) hpc (by simpa using h0)
      hp0.1 (hp0.2 s).1
    have hpc1 : (execInstrBr s hd).pc = pcWord (base + 1) := by
      rw [(hp0.2 s).2.1, hpc, pcWord_add_four]
    have hmem1 : (execInstrBr s hd).mem = s.mem := (hp0.2 s).2.2
    obtain ⟨hst_tl, hpc_tl, hmem_tl⟩ :=
      ih (base + 1) (execInstrBr s hd) (by simp at hhi; omega)
        (fun i hi => by
          have := hcode (i + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
        (fun i hi => hpure (i + 1) (by simp; omega)) hpc1
    refine ⟨?_, ?_, hmem_tl.trans hmem1⟩
    · simpa [runInstrs, List.foldl_cons, Nat.add_comm 1 tl.length] using hst0.trans hst_tl
    · simpa [runInstrs, List.foldl_cons, Nat.add_assoc, Nat.add_comm 1 tl.length] using hpc_tl

end CommitGolfCandidate
