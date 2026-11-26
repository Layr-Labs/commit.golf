import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! Deterministic symbolic execution infrastructure for the submitted `check` image (`checkInstr`,
words `0..419`):
- Equivalence between coin-free `execute` and the pure deterministic evaluator `detExec` under
  `Oracle.run`, `Oracle.eval`, and `fixedOracleRun (traceCompressionReplies _)`.
- Compositional step/halt/phase combinators with byte-level memory frames.
- Reusable instruction-block lemmas (`step_ordinary`, `step_ecall_compress`, halt/copy/compare/
  zero-gap/helper-call blocks) and `CheckFixedRegs`. -/
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
theorem se12_30 : signExtend12 30#12 = 30#64 := by decide
theorem se12_30_ofNat : signExtend12 30#12 = BitVec.ofNat 64 30 := signExtend12_ofNat_lt2048 30 (by decide)
theorem se12_32 : signExtend12 32#12 = 32#64 := by decide
theorem se12_48 : signExtend12 48#12 = 48#64 := by decide
theorem se12_56 : signExtend12 56#12 = 56#64 := by decide
theorem se12_64 : signExtend12 64#12 = 64#64 := by decide
theorem se12_256 : signExtend12 256#12 = BitVec.ofNat 64 256 := signExtend12_ofNat_lt2048 256 (by decide)
theorem se12_480 : signExtend12 480#12 = BitVec.ofNat 64 480 := signExtend12_ofNat_lt2048 480 (by decide)
theorem se12_736 : signExtend12 736#12 = BitVec.ofNat 64 736 := signExtend12_ofNat_lt2048 736 (by decide)
theorem se12_768 : signExtend12 768#12 = BitVec.ofNat 64 768 := signExtend12_ofNat_lt2048 768 (by decide)
theorem se12_792 : signExtend12 792#12 = BitVec.ofNat 64 792 := signExtend12_ofNat_lt2048 792 (by decide)
theorem se12_4095 : signExtend12 4095#12 = (-1#64 : Word) := by decide

theorem bv64_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bv64_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  rw [se12_4095, ← bv64_add n 1]
  change BitVec.ofNat 64 n + 1#64 + (-1#64 : Word) = BitVec.ofNat 64 n
  rw [BitVec.add_assoc, show (1#64 : Word) + (-1#64 : Word) = 0#64 by decide, BitVec.add_zero]

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

theorem truncate16_zeroExtend64 (h : BitVec 16) :
    (h.zeroExtend 64).truncate 16 = h := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hlt : h.toNat < 2 ^ 16 := h.isLt
  rw [Nat.mod_eq_of_lt (by omega : h.toNat < 2 ^ 64), Nat.mod_eq_of_lt hlt]

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

/-! #### Byte-Level Memory Frame Helpers -/

/-- `s2` agrees with `s1` on every byte address outside `[lo, hi)`. -/
def MemEqOutside (s1 s2 : MachineState) (lo hi : Nat) : Prop :=
  ∀ a : Nat, a < 2 ^ 64 → (a < lo ∨ hi ≤ a) →
    s2.getByte (BitVec.ofNat 64 a) = s1.getByte (BitVec.ofNat 64 a)

/-- All read-only input buffers and embedded data (`addr ≥ 4294971392`) are preserved. -/
abbrev HighMemPreserved (s0 s : MachineState) : Prop :=
  MemEqOutside s0 s 0 4294971392

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

theorem MemEqOutside_setMem (s : MachineState) (addr : Nat) (val : Word)
    (halign : addr % 8 = 0) (hbound : addr + 8 ≤ 2 ^ 64) :
    MemEqOutside s (s.setMem (BitVec.ofNat 64 addr) val) addr (addr + 8) :=
  fun a ha hout => setMem_getByte_ofNat s addr a val halign hbound ha hout

theorem MemEqOutside_setHalfword (s : MachineState) (addr : Nat) (h : BitVec 16)
    (halign : addr % 2 = 0) (hbound : addr + 2 ≤ 2 ^ 64) :
    MemEqOutside s (s.setHalfword (BitVec.ofNat 64 addr) h) addr (addr + 2) := by
  intro a ha hout
  have ha2 : (BitVec.ofNat 64 addr).toNat % 2 = 0 := by
    rw [toNat_ofNat64 addr (by omega)]; exact halign
  rw [setHalfword_getByte s _ _ h ha2]
  have hne0 : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 addr := by
    rw [ne_eq, bv64_eq_iff a addr ha (by omega)]; omega
  have hne1 : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 addr + 1#64 := by
    change BitVec.ofNat 64 a ≠ BitVec.ofNat 64 addr + BitVec.ofNat 64 1
    rw [bv64_add, ne_eq, bv64_eq_iff a (addr + 1) ha (by omega)]; omega
  rw [if_neg hne0, if_neg hne1]

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

/-- 30-byte little-endian digest from memory, zero-extended in the top 16 bits. -/
def proofDigest30 (s : MachineState) (addr : Nat) : Digest :=
  (0#16) ++ readBuffer s addr 30

theorem proofDigest30_eq_readBuffer_of_zero_top (s s0 : MachineState) (dst src : Nat)
    (htop : s.getByte (BitVec.ofNat 64 (dst + 30)) = 0 ∧ s.getByte (BitVec.ofNat 64 (dst + 31)) = 0)
    (hlo : ∀ j < 30, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (src + j))) :
    readBuffer s dst 32 = proofDigest30 s0 src := by
  have hd : readBuffer s dst 32 = mask240 (proofDigest30 s0 src) := by
    apply readBuffer_30_mask240 s dst htop (proofDigest30 s0 src)
    intro j hj
    rw [hlo j hj]
    unfold proofDigest30
    rw [show ((0#16 : BitVec 16) ++ readBuffer s0 src 30).extractLsb' (8 * j) 8 =
        (readBuffer s0 src 30).extractLsb' (8 * j) 8 by
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
        BitVec.getLsbD_append, show 8 * j + b < 240 by omega, decide_true, ite_true]]
    exact (read_buffer_byte s0 src 30 j hj).symm
  have hmask : mask240 (proofDigest30 s0 src) = proofDigest30 s0 src := by
    unfold mask240 low240 proofDigest30
    rw [BitVec.extractLsb'_append_eq_right]
  exact hd.trans hmask

theorem proofDigest30_of_bytes_eq (s0 : MachineState) (src : Nat) (d : Digest)
    (hlo : ∀ j < 30, s0.getByte (BitVec.ofNat 64 (src + j)) = d.extractLsb' (8 * j) 8) :
    proofDigest30 s0 src = mask240 d := by
  unfold proofDigest30 mask240 low240
  exact congrArg ((0#16 : BitVec 16) ++ ·) (by
    have hr := read_serialized_slice s0 d src 0 30 (by simpa only [Nat.zero_add] using hlo)
    simpa using hr)

theorem sh_zero_readBuffer30 (s s0 : MachineState) (dst src : Nat)
    (halign : dst % 8 = 0) (hbound : dst + 32 ≤ 2 ^ 64)
    (hlo : ∀ j < 30, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (src + j))) :
    readBuffer (s.setHalfword (BitVec.ofNat 64 (dst + 30)) 0#16) dst 32 = proofDigest30 s0 src := by
  have ha30 : (BitVec.ofNat 64 (dst + 30)).toNat % 2 = 0 := by
    rw [toNat_ofNat64 (dst + 30) (by omega)]; omega
  apply proofDigest30_eq_readBuffer_of_zero_top _ s0 dst src
  · constructor
    · rw [setHalfword_getByte s _ _ 0#16 ha30, if_pos rfl]; decide
    · rw [setHalfword_getByte s _ _ 0#16 ha30]
      have hne : BitVec.ofNat 64 (dst + 31) ≠ BitVec.ofNat 64 (dst + 30) := by
        rw [ne_eq, bv64_eq_iff _ _ (by omega) (by omega)]; omega
      have heq : BitVec.ofNat 64 (dst + 31) = BitVec.ofNat 64 (dst + 30) + 1#64 := by
        change _ = BitVec.ofNat 64 (dst + 30) + BitVec.ofNat 64 1
        rw [bv64_add]
      rw [if_neg hne, if_pos heq]; decide
  · intro j hj
    rw [setHalfword_getByte s _ _ 0#16 ha30]
    have hne0 : BitVec.ofNat 64 (dst + j) ≠ BitVec.ofNat 64 (dst + 30) := by
      rw [ne_eq, bv64_eq_iff _ _ (by omega) (by omega)]; omega
    have hne1 : BitVec.ofNat 64 (dst + j) ≠ BitVec.ofNat 64 (dst + 30) + 1#64 := by
      change BitVec.ofNat 64 (dst + j) ≠ BitVec.ofNat 64 (dst + 30) + BitVec.ofNat 64 1
      rw [bv64_add, ne_eq, bv64_eq_iff _ _ (by omega) (by omega)]; omega
    rw [if_neg hne0, if_neg hne1]
    exact hlo j hj

/-! ### 3. Single-Instruction and Reusable Block Execution Lemmas -/

theorem step_ordinary (oracle : Oracle) (s : MachineState) (idx : Nat) (instr : Instr)
    (hhi : idx < 420) (hpc : s.pc = pcWord idx)
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
    (hhi : idx < 420) (hpc : s.pc = pcWord idx)
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

theorem halt_accept (oracle : Oracle) (s : MachineState) (hpc : s.pc = pcWord 333) :
    HaltsWith oracle s 3 0 .success [] := by
  refine ⟨by decide, fun extra => ?_⟩
  have s1 : StepsTo oracle s (execInstrBr s (.ADDI .x5 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle s 333 (.ADDI .x5 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let st1 := execInstrBr s (.ADDI .x5 .x0 1#12)
  have hpc1 : st1.pc = pcWord 334 := by
    simp only [st1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have s2 : StepsTo oracle st1 (execInstrBr st1 (.ADDI .x10 .x0 0#12)) 1 0 [] :=
    step_ordinary oracle st1 334 (.ADDI .x10 .x0 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let st2 := execInstrBr st1 (.ADDI .x10 .x0 0#12)
  have hpc2 : st2.pc = pcWord 335 := by
    simp only [st2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have s12 : StepsTo oracle s st2 2 0 [] := by simpa using s1.trans s2
  have h2 := s12 (extra + 1)
  rw [show 3 + extra = 2 + (extra + 1) by omega]
  have hfetch3 : fetch (submission.image .check) st2 = some (.base .ECALL) := by
    rw [check_fetch st2 335 (by decide) hpc2]; rfl
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

theorem halt_reject (oracle : Oracle) (s : MachineState) (hpc : s.pc = pcWord 336) :
    HaltsWith oracle s 3 0 .failure [] := by
  refine ⟨by decide, fun extra => ?_⟩
  have s1 : StepsTo oracle s (execInstrBr s (.ADDI .x5 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle s 336 (.ADDI .x5 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let st1 := execInstrBr s (.ADDI .x5 .x0 1#12)
  have hpc1 : st1.pc = pcWord 337 := by
    simp only [st1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have s2 : StepsTo oracle st1 (execInstrBr st1 (.ADDI .x10 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle st1 337 (.ADDI .x10 .x0 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let st2 := execInstrBr st1 (.ADDI .x10 .x0 1#12)
  have hpc2 : st2.pc = pcWord 338 := by
    simp only [st2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have s12 : StepsTo oracle s st2 2 0 [] := by simpa using s1.trans s2
  have h2 := s12 (extra + 1)
  rw [show 3 + extra = 2 + (extra + 1) by omega]
  have hfetch3 : fetch (submission.image .check) st2 = some (.base .ECALL) := by
    rw [check_fetch st2 338 (by decide) hpc2]; rfl
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

/-! #### Reusable Block Steppers -/

/-- Generic `m`-halfword copy (`LHU x6, (2j)(x25); SH x6, (2j)(x12)`). -/
theorem step_copy_halfwords (oracle : Oracle) (base m : Nat) (s : MachineState) (src dst : Nat)
    (hm : 2 * m < 256) (hhi : base + 2 * m ≤ 420)
    (hcode : ∀ j < m,
      checkInstr (base + 2 * j) = .base (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * j))) ∧
      checkInstr (base + 2 * j + 1) = .base (.SH .x12 .x6 (BitVec.ofNat 12 (2 * j))))
    (hpc : s.pc = pcWord base)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 2 = 0) (hdst_al : dst % 2 = 0)
    (hsrc_bd : src + 2 * m ≤ MEMORY_BYTES) (hdst_bd : dst + 2 * m ≤ MEMORY_BYTES)
    (hdisj : dst + 2 * m ≤ src ∨ src + 2 * m ≤ dst) :
    ∃ s', StepsTo oracle s s' (2 * m) 0 [] ∧
      s'.pc = pcWord (base + 2 * m) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      (∀ j < 2 * m, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + 2 * m) := by
  induction m with
  | zero =>
    exact ⟨s, StepsTo.refl oracle s, hpc, fun _ _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim,
      MemEqOutside.refl s dst dst⟩
  | succ k ih =>
    obtain ⟨sk, hsteps, hpc_k, hregs_k, hcopy_k, hout_k⟩ :=
      ih (by omega) (by omega) (fun j hj => hcode j (by omega)) (by omega) (by omega) (by omega)
    have h2k_lt : 2 * k < 256 := by omega
    have hse : signExtend12 (BitVec.ofNat 12 (2 * k)) = BitVec.ofNat 64 (2 * k) :=
      signExtend12_ofNat_lt256 ⟨2 * k, h2k_lt⟩
    have hsrc_k : sk.getReg .x25 = BitVec.ofNat 64 src := (hregs_k .x25 (by decide)).trans hsrc
    have hdst_k : sk.getReg .x12 = BitVec.ofNat 64 dst := (hregs_k .x12 (by decide)).trans hdst
    have haddr_src : sk.getReg .x25 + signExtend12 (BitVec.ofNat 12 (2 * k)) = BitVec.ofNat 64 (src + 2 * k) := by
      rw [hsrc_k, hse, bv64_add]
    have haddr_dst : sk.getReg .x12 + signExtend12 (BitVec.ofNat 12 (2 * k)) = BitVec.ofNat 64 (dst + 2 * k) := by
      rw [hdst_k, hse, bv64_add]
    have hval1 : memoryArgumentsValid sk (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * k))) = true := by
      simp only [memoryArgumentsValid, memAccess, haddr_src]
      exact accessValid_ofNat (src + 2 * k) 2 (by omega) (by omega)
    have hst1 : StepsTo oracle sk (execInstrBr sk (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * k)))) 1 0 [] :=
      step_ordinary oracle sk (base + 2 * k) _ (by omega) hpc_k (hcode k (by omega)).1 (by intro h; cases h)
        (by simp [ordinaryStep, hval1])
    let sk1 := execInstrBr sk (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * k)))
    have hpc1 : sk1.pc = pcWord (base + 2 * k + 1) := by
      simp only [sk1, execInstrBr, MachineState.setPC, hpc_k, pcWord_add_four]
    have hdst1 : sk1.getReg .x12 = BitVec.ofNat 64 dst := by
      simp only [sk1, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12), hdst_k]
    have hx6_1 : sk1.getReg .x6 = (sk.getHalfword (BitVec.ofNat 64 (src + 2 * k))).zeroExtend 64 := by
      simp only [sk1, execInstrBr, MachineState.getReg_setPC, haddr_src]
      rw [MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0)]
    have haddr_dst1 : sk1.getReg .x12 + signExtend12 (BitVec.ofNat 12 (2 * k)) = BitVec.ofNat 64 (dst + 2 * k) := by
      rw [hdst1, hse, bv64_add]
    have hval2 : memoryArgumentsValid sk1 (.SH .x12 .x6 (BitVec.ofNat 12 (2 * k))) = true := by
      simp only [memoryArgumentsValid, memAccess, haddr_dst1]
      exact accessValid_ofNat (dst + 2 * k) 2 (by omega) (by omega)
    have hst2 : StepsTo oracle sk1 (execInstrBr sk1 (.SH .x12 .x6 (BitVec.ofNat 12 (2 * k)))) 1 0 [] :=
      step_ordinary oracle sk1 (base + 2 * k + 1) _ (by omega) hpc1 (hcode k (by omega)).2 (by intro h; cases h)
        (by simp [ordinaryStep, hval2])
    let sk2 := execInstrBr sk1 (.SH .x12 .x6 (BitVec.ofNat 12 (2 * k)))
    have hmem_sk1 : sk1.mem = sk.mem := by simp [sk1, execInstrBr, mem_setPC, mem_setReg]
    have hsk2_byte : ∀ q : Word, sk2.getByte q =
        (sk.setHalfword (BitVec.ofNat 64 (dst + 2 * k))
          (sk.getHalfword (BitVec.ofNat 64 (src + 2 * k)))).getByte q := by
      intro q
      simp only [sk2, execInstrBr, haddr_dst1, hx6_1, truncate16_zeroExtend64,
        MachineState.getByte, MachineState.setHalfword,
        MachineState.getMem, MachineState.setMem, mem_setPC, hmem_sk1]
    have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
    have hout_step : MemEqOutside sk sk2 (dst + 2 * k) (dst + 2 * k + 2) := by
      intro a ha hout
      rw [hsk2_byte]
      exact MemEqOutside_setHalfword sk (dst + 2 * k) _ (by omega) (by omega) a ha hout
    refine ⟨sk2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [show 2 * (k + 1) = 2 * k + (1 + 1) by omega, Nat.add_zero, List.append_nil] using
        hsteps.trans (hst1.trans hst2)
    · simp only [sk2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
      congr 1 <;> omega
    · intro r hr
      have hr1 : sk2.getReg r = sk1.getReg r := by
        simp [sk2, execInstrBr, MachineState.setHalfword, MachineState.setMem, MachineState.setPC,
          MachineState.getReg]
      rw [hr1]
      simp only [sk1, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm]
      exact hregs_k r hr
    · intro j hj
      by_cases hlt : j < 2 * k
      · rw [hout_step (dst + j) (by omega) (by omega)]
        exact hcopy_k j hlt
      · rw [hsk2_byte]
        have hs_al : (BitVec.ofNat 64 (src + 2 * k)).toNat % 2 = 0 := by
          rw [toNat_ofNat64 (src + 2 * k) (by omega)]; omega
        have hd_al : (BitVec.ofNat 64 (dst + 2 * k)).toNat % 2 = 0 := by
          rw [toNat_ofNat64 (dst + 2 * k) (by omega)]; omega
        rw [copyHalfword_getByte sk _ _ _ hs_al hd_al]
        have hcases : j = 2 * k ∨ j = 2 * k + 1 := by omega
        rcases hcases with rfl | rfl
        · rw [if_pos rfl]
          exact hout_k (src + 2 * k) (by omega) (by omega)
        · have hne0 : BitVec.ofNat 64 (dst + (2 * k + 1)) ≠ BitVec.ofNat 64 (dst + 2 * k) := by
            rw [ne_eq, bv64_eq_iff _ _ (by omega) (by omega)]; omega
          have heq1 : BitVec.ofNat 64 (dst + (2 * k + 1)) = BitVec.ofNat 64 (dst + 2 * k) + 1#64 := by
            change _ = BitVec.ofNat 64 (dst + 2 * k) + BitVec.ofNat 64 1
            rw [bv64_add] <;> congr 1 <;> omega
          have hsrc1 : BitVec.ofNat 64 (src + 2 * k) + 1#64 = BitVec.ofNat 64 (src + (2 * k + 1)) := by
            change BitVec.ofNat 64 (src + 2 * k) + BitVec.ofNat 64 1 = _
            rw [bv64_add] <;> congr 1 <;> omega
          rw [if_neg hne0, if_pos heq1, hsrc1]
          exact hout_k (src + (2 * k + 1)) (by omega) (by omega)
    · exact (hout_k.mono (by omega) (by omega)).trans (hout_step.mono (by omega) (by omega))

/-- Call and return from `chk_read16` (`pc[339..355]`), 17 steps. -/
theorem step_chk_read16 (oracle : Oracle) (s : MachineState) (retIdx src dst : Nat)
    (hpc : s.pc = pcWord 339) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 420)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src) (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 2 = 0) (hdst_al : dst % 2 = 0)
    (hsrc_bd : src + 16 ≤ MEMORY_BYTES) (hdst_bd : dst + 16 ≤ MEMORY_BYTES)
    (hdisj : dst + 16 ≤ src ∨ src + 16 ≤ dst) :
    ∃ s', StepsTo oracle s s' 17 0 [] ∧
      s'.pc = pcWord retIdx ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      (∀ j < 16, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + 16) := by
  have hcode : ∀ j < 8,
      checkInstr (339 + 2 * j) = .base (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * j))) ∧
      checkInstr (339 + 2 * j + 1) = .base (.SH .x12 .x6 (BitVec.ofNat 12 (2 * j))) := by
    intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
  obtain ⟨s1, hs1, hpc1, hreg1, hcopy1, hout1⟩ :=
    step_copy_halfwords oracle 339 8 s src dst (by decide) (by decide) hcode hpc hsrc hdst
      hsrc_al hdst_al hsrc_bd hdst_bd hdisj
  have hret1 : s1.getReg .x1 = pcWord retIdx := (hreg1 .x1 (by decide)).trans hret
  have hjalr : StepsTo oracle s1 (execInstrBr s1 (.JALR .x0 .x1 0#12)) 1 0 [] :=
    step_ordinary oracle s1 355 (.JALR .x0 .x1 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  refine ⟨execInstrBr s1 (.JALR .x0 .x1 0#12), by simpa using hs1.trans hjalr, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.setPC, hret1]
    exact jalr_pcWord retIdx (by omega)
  · intro r hr
    simpa only [execInstrBr, MachineState.getReg_setPC, MachineState.setReg] using hreg1 r hr
  · intro j hj
    simpa only [execInstrBr, MachineState.getByte, MachineState.getMem_setPC, MachineState.setReg] using hcopy1 j hj
  · exact hout1.trans (MemEqOutside.of_mem_eq rfl dst (dst + 16))

/-- Call and return from `chk_read30` (`pc[356..386]`), 31 steps. -/
theorem step_chk_read30 (oracle : Oracle) (s : MachineState) (retIdx src dst : Nat)
    (hpc : s.pc = pcWord 356) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 420)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src) (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 2 = 0) (hdst_al : dst % 2 = 0)
    (hsrc_bd : src + 30 ≤ MEMORY_BYTES) (hdst_bd : dst + 30 ≤ MEMORY_BYTES)
    (hdisj : dst + 30 ≤ src ∨ src + 30 ≤ dst) :
    ∃ s', StepsTo oracle s s' 31 0 [] ∧
      s'.pc = pcWord retIdx ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      (∀ j < 30, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + 30) := by
  have hcode : ∀ j < 15,
      checkInstr (356 + 2 * j) = .base (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * j))) ∧
      checkInstr (356 + 2 * j + 1) = .base (.SH .x12 .x6 (BitVec.ofNat 12 (2 * j))) := by
    intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
  obtain ⟨s1, hs1, hpc1, hreg1, hcopy1, hout1⟩ :=
    step_copy_halfwords oracle 356 15 s src dst (by decide) (by decide) hcode hpc hsrc hdst
      hsrc_al hdst_al hsrc_bd hdst_bd hdisj
  have hret1 : s1.getReg .x1 = pcWord retIdx := (hreg1 .x1 (by decide)).trans hret
  have hjalr : StepsTo oracle s1 (execInstrBr s1 (.JALR .x0 .x1 0#12)) 1 0 [] :=
    step_ordinary oracle s1 386 (.JALR .x0 .x1 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  refine ⟨execInstrBr s1 (.JALR .x0 .x1 0#12), by simpa using hs1.trans hjalr, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.setPC, hret1]
    exact jalr_pcWord retIdx (by omega)
  · intro r hr
    simpa only [execInstrBr, MachineState.getReg_setPC, MachineState.setReg] using hreg1 r hr
  · intro j hj
    simpa only [execInstrBr, MachineState.getByte, MachineState.getMem_setPC, MachineState.setReg] using hcopy1 j hj
  · exact hout1.trans (MemEqOutside.of_mem_eq rfl dst (dst + 30))

/-- Call and return from `chk_read32` (`pc[387..419]`), 33 steps. -/
theorem step_chk_read32 (oracle : Oracle) (s : MachineState) (retIdx src dst : Nat)
    (hpc : s.pc = pcWord 387) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 420)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src) (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 2 = 0) (hdst_al : dst % 2 = 0)
    (hsrc_bd : src + 32 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES)
    (hdisj : dst + 32 ≤ src ∨ src + 32 ≤ dst) :
    ∃ s', StepsTo oracle s s' 33 0 [] ∧
      s'.pc = pcWord retIdx ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      (∀ j < 32, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + 32) := by
  have hcode : ∀ j < 16,
      checkInstr (387 + 2 * j) = .base (.LHU .x6 .x25 (BitVec.ofNat 12 (2 * j))) ∧
      checkInstr (387 + 2 * j + 1) = .base (.SH .x12 .x6 (BitVec.ofNat 12 (2 * j))) := by
    intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
  obtain ⟨s1, hs1, hpc1, hreg1, hcopy1, hout1⟩ :=
    step_copy_halfwords oracle 387 16 s src dst (by decide) (by decide) hcode hpc hsrc hdst
      hsrc_al hdst_al hsrc_bd hdst_bd hdisj
  have hret1 : s1.getReg .x1 = pcWord retIdx := (hreg1 .x1 (by decide)).trans hret
  have hjalr : StepsTo oracle s1 (execInstrBr s1 (.JALR .x0 .x1 0#12)) 1 0 [] :=
    step_ordinary oracle s1 419 (.JALR .x0 .x1 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  refine ⟨execInstrBr s1 (.JALR .x0 .x1 0#12), by simpa using hs1.trans hjalr, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.setPC, hret1]
    exact jalr_pcWord retIdx (by omega)
  · intro r hr
    simpa only [execInstrBr, MachineState.getReg_setPC, MachineState.setReg] using hreg1 r hr
  · intro j hj
    simpa only [execInstrBr, MachineState.getByte, MachineState.getMem_setPC, MachineState.setReg] using hcopy1 j hj
  · exact hout1.trans (MemEqOutside.of_mem_eq rfl dst (dst + 32))

/-- Generic `m`-dword copy (`LD x6, (srcOff + 8j)(rSrc); SD x6, (dstOff + 8j)(rDst)`). -/
theorem step_copy_dwords (oracle : Oracle) (base m : Nat) (rSrc rDst : Reg)
    (srcOff dstOff : Nat) (s : MachineState) (srcBase dstBase : Nat)
    (hrSrc : rSrc ≠ .x6) (hrDst : rDst ≠ .x6)
    (hso : srcOff + 8 * m ≤ 256) (hdo : dstOff + 8 * m ≤ 256)
    (hhi : base + 2 * m ≤ 420)
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
      rw [hsrc_k, hse_s, bv64_add] <;> (congr 1 <;> omega)
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
      rw [hdst1, hse_d, bv64_add] <;> (congr 1 <;> omega)
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
      congr 1 <;> omega
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

/-- Generic 4-dword comparison (`LD x6, (8j)(rA); LD x7, (8j)(rB); BNE x6, x7, pc[336]`). -/
theorem step_compare4 (oracle : Oracle) (base : Nat) (rA rB : Reg)
    (s : MachineState) (addrA addrB : Nat)
    (hrA6 : rA ≠ .x6) (hrA7 : rA ≠ .x7) (hrB6 : rB ≠ .x6) (hrB7 : rB ≠ .x7)
    (hhi : base + 12 ≤ 336)
    (hcode : ∀ j < 4,
      checkInstr (base + 3 * j) = .base (.LD .x6 rA (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 3 * j + 1) = .base (.LD .x7 rB (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (336 - (base + 3 * j + 2))))))
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
          let off := BitVec.ofNat 13 (4 * (336 - (base + 3 * k + 2)))
          have hst3 := step_ordinary oracle sk2 (base + 3 * k + 2) (.BNE .x6 .x7 off) (by omega) hpc2
            (hcode k (by omega)).2.2 (by intro h; cases h) rfl
          have h123 : StepsTo oracle sk (execInstrBr sk2 (.BNE .x6 .x7 off)) 3 0 [] := by
            simpa using (hst1.trans hst2).trans hst3
          by_cases heq : s.getMem (BitVec.ofNat 64 (addrA + 8 * k)) = s.getMem (BitVec.ofNat 64 (addrB + 8 * k))
          · right
            have hpc3 : (execInstrBr sk2 (.BNE .x6 .x7 off)).pc = pcWord (base + 3 * (k + 1)) := by
              simp only [execInstrBr, hx6, hx7, heq, bne_self_eq_false, Bool.false_eq_true, ite_false,
                MachineState.setPC, hpc2, pcWord_add_four]
              congr 1 <;> omega
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
            have hpc3 : (execInstrBr sk2 (.BNE .x6 .x7 off)).pc = pcWord 336 := by
              simp only [execInstrBr, hne_b, ite_true, MachineState.setPC, hpc2]
              have hse13 : signExtend13 off = BitVec.ofNat 64 (4 * (336 - (base + 3 * k + 2))) :=
                signExtend13_ofNat_lt4096 _ (by omega)
              rw [hse13, pcWord, bv64_add] <;> (congr 1 <;> omega)
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

/-- Zero `S[64..96)` (`pc[156..159]`, 4 steps). -/
theorem step_zero_gap (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = pcWord 156) (hx21 : s.getReg .x21 = 256#64) :
    ∃ s', StepsTo oracle s s' 4 0 [] ∧
      s'.pc = pcWord 160 ∧
      (∀ r : Reg, s'.getReg r = s.getReg r) ∧
      readBuffer s' 320 32 = 0 ∧
      MemEqOutside s s' 320 352 := by
  have hloop : ∀ m ≤ 4,
      ∃ s', StepsTo oracle s s' m 0 [] ∧
        s'.pc = pcWord (156 + m) ∧
        (∀ r : Reg, s'.getReg r = s.getReg r) ∧
        (∀ j < 8 * m, s'.getByte (BitVec.ofNat 64 (320 + j)) = 0) ∧
        MemEqOutside s s' 320 (320 + 8 * m) := by
    intro m hm
    induction m with
    | zero =>
      exact ⟨s, StepsTo.refl oracle s, hpc, fun _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim,
        MemEqOutside.refl s 320 320⟩
    | succ k ih =>
      obtain ⟨sk, hsteps, hpc_k, hreg_k, hzero_k, hout_k⟩ := ih (by omega)
      have hcode : checkInstr (156 + k) = .base (.SD .x21 .x0 (BitVec.ofNat 12 (64 + 8 * k))) := by
        have hk : k < 4 := by omega
        interval_cases k <;> rfl
      have hse : signExtend12 (BitVec.ofNat 12 (64 + 8 * k)) = BitVec.ofNat 64 (64 + 8 * k) :=
        signExtend12_ofNat_lt256 ⟨64 + 8 * k, by omega⟩
      have ha : sk.getReg .x21 + signExtend12 (BitVec.ofNat 12 (64 + 8 * k)) = BitVec.ofNat 64 (320 + 8 * k) := by
        rw [hreg_k .x21, hx21, hse]; change BitVec.ofNat 64 256 + _ = _; rw [bv64_add] <;> (congr 1 <;> omega)
      have hval : memoryArgumentsValid sk (.SD .x21 .x0 (BitVec.ofNat 12 (64 + 8 * k))) = true := by
        simp only [memoryArgumentsValid, memAccess, ha]
        exact accessValid_ofNat (320 + 8 * k) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst := step_ordinary oracle sk (156 + k) _ (by omega) hpc_k hcode (by intro h; cases h)
        (by simp [ordinaryStep, hval])
      let sk1 := execInstrBr sk (.SD .x21 .x0 (BitVec.ofNat 12 (64 + 8 * k)))
      have hbyte : ∀ q : Word, sk1.getByte q = (sk.setMem (BitVec.ofNat 64 (320 + 8 * k)) 0#64).getByte q := by
        intro q; simp [sk1, execInstrBr, ha, MachineState.getByte, MachineState.getMem_setPC, getReg_x0]
      have hout1 : MemEqOutside sk sk1 (320 + 8 * k) (320 + 8 * k + 8) := by
        intro a ha2 hout
        rw [hbyte]
        exact MemEqOutside_setMem sk (320 + 8 * k) 0#64 (by omega) (by omega) a ha2 hout
      refine ⟨sk1, by simpa using hsteps.trans hst, ?_, ?_, ?_, ?_⟩
      · simp only [sk1, execInstrBr, MachineState.setPC, hpc_k, pcWord_add_four]
        congr 1 <;> omega
      · intro r
        have : sk1.getReg r = sk.getReg r := by
          simp [sk1, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
        exact this.trans (hreg_k r)
      · intro j hj
        by_cases hlt : j < 8 * k
        · rw [hout1 (320 + j) (by omega) (by omega)]; exact hzero_k j hlt
        · have hrem : j - 8 * k < 8 := by omega
          have heq : 320 + j = 320 + 8 * k + (j - 8 * k) := by omega
          rw [heq, hbyte, setMem_getByte_inside sk _ _ 0#64 (by omega) hrem]
          simp [BitVec.extractLsb']
      · exact (hout_k.mono (by omega) (by omega)).trans (hout1.mono (by omega) (by omega))
  obtain ⟨s', hsteps, hpc', hreg', hzero', hout'⟩ := hloop 4 (by omega)
  exact ⟨s', hsteps, hpc', hreg', readBuffer_zero_of_bytes s' 320 32 hzero', hout'⟩

/-! ### 4. Checker Phase Invariants and Symbolic Execution -/

/-- Execute a straight-line list of pure (non-memory, non-branch) instructions. -/
def runInstrs (s : MachineState) (l : List Instr) : MachineState :=
  l.foldl execInstrBr s

theorem step_pure_list (oracle : Oracle) (base : Nat) (l : List Instr) (s : MachineState)
    (hhi : base + l.length ≤ 420)
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

/-- Helper: `JAL .x1` to `chk_read32` (`pc[387]`) followed by `ADDI .x25 .x25 32#12` (35 steps). -/
theorem step_call_read32 (oracle : Oracle) (idx : Nat) (s : MachineState) (src dst : Nat)
    (hhi : idx + 2 ≤ 387)
    (hjal : checkInstr idx = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (387 - idx)))))
    (hadv : checkInstr (idx + 1) = .base (.ADDI .x25 .x25 32#12))
    (hpc : s.pc = pcWord idx)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 2 = 0) (hdst_al : dst % 2 = 0)
    (hsrc_bd : src + 32 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES)
    (hdisj : dst + 32 ≤ src ∨ src + 32 ≤ dst) :
    ∃ s', StepsTo oracle s s' 35 0 [] ∧
      s'.pc = pcWord (idx + 2) ∧
      s'.getReg .x25 = BitVec.ofNat 64 (src + 32) ∧
      (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      (∀ j < 32, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + 32) := by
  let off := BitVec.ofNat 21 (4 * (387 - idx))
  have hst1 := step_ordinary oracle s idx (.JAL .x1 off) (by omega) hpc hjal (by intro h; cases h) rfl
  let s1 := execInstrBr s (.JAL .x1 off)
  have hpc1 : s1.pc = pcWord 387 := by
    simp only [s1, execInstrBr, MachineState.setPC, hpc]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (387 - idx)) :=
      signExtend21_ofNat_lt _ (by omega)
    rw [hse21, pcWord, bv64_add] <;> (congr 1 <;> omega)
  have hret1 : s1.getReg .x1 = pcWord (idx + 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, hpc, pcWord_add_four]
    exact MachineState.getReg_setReg_eq (by decide)
  have hsrc1 : s1.getReg .x25 = BitVec.ofNat 64 src := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x25), hsrc]
  have hdst1 : s1.getReg .x12 = BitVec.ofNat 64 dst := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x12), hdst]
  obtain ⟨s2, hs2, hpc2, hreg2, hcopy2, hout2⟩ :=
    step_chk_read32 oracle s1 (idx + 1) src dst hpc1 hret1 (by omega) hsrc1 hdst1
      hsrc_al hdst_al hsrc_bd hdst_bd hdisj
  have hst3 := step_ordinary oracle s2 (idx + 1) (.ADDI .x25 .x25 32#12) (by omega) hpc2 hadv (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADDI .x25 .x25 32#12)
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hmem3 : s3.mem = s2.mem := by simp [s3, execInstrBr, mem_setPC, mem_setReg]
  refine ⟨s3, by simpa using (hst1.trans hs2).trans hst3, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  · simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0), hreg2 .x25 (by decide), hsrc1,
      se12_32]
    change BitVec.ofNat 64 src + BitVec.ofNat 64 32 = _; exact bv64_add src 32
  · intro r hr1 hr6 hr25
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr25.symm, hreg2 r hr6]
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr1.symm
  · intro j hj
    have hb := hcopy2 j hj
    simp only [MachineState.getByte, MachineState.getMem, hmem3, hmem1] at hb ⊢
    exact hb
  · exact (MemEqOutside.of_mem_eq hmem1 dst (dst + 32)).trans
      (hout2.trans (MemEqOutside.of_mem_eq hmem3 dst (dst + 32)))

/-- Helper: `JAL .x1` to `chk_read30` (`pc[356]`), 32 steps. -/
theorem step_call_read30 (oracle : Oracle) (idx : Nat) (s : MachineState) (src dst : Nat)
    (hhi : idx + 1 ≤ 356)
    (hjal : checkInstr idx = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (356 - idx)))))
    (hpc : s.pc = pcWord idx)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 2 = 0) (hdst_al : dst % 2 = 0)
    (hsrc_bd : src + 30 ≤ MEMORY_BYTES) (hdst_bd : dst + 30 ≤ MEMORY_BYTES)
    (hdisj : dst + 30 ≤ src ∨ src + 30 ≤ dst) :
    ∃ s', StepsTo oracle s s' 32 0 [] ∧
      s'.pc = pcWord (idx + 1) ∧
      (∀ r : Reg, r ≠ .x1 → r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      (∀ j < 30, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + 30) := by
  let off := BitVec.ofNat 21 (4 * (356 - idx))
  have hst1 := step_ordinary oracle s idx (.JAL .x1 off) (by omega) hpc hjal (by intro h; cases h) rfl
  let s1 := execInstrBr s (.JAL .x1 off)
  have hpc1 : s1.pc = pcWord 356 := by
    simp only [s1, execInstrBr, MachineState.setPC, hpc]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (356 - idx)) :=
      signExtend21_ofNat_lt _ (by omega)
    rw [hse21, pcWord, bv64_add] <;> (congr 1 <;> omega)
  have hret1 : s1.getReg .x1 = pcWord (idx + 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, hpc, pcWord_add_four]
    exact MachineState.getReg_setReg_eq (by decide)
  have hsrc1 : s1.getReg .x25 = BitVec.ofNat 64 src := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x25), hsrc]
  have hdst1 : s1.getReg .x12 = BitVec.ofNat 64 dst := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x12), hdst]
  obtain ⟨s2, hs2, hpc2, hreg2, hcopy2, hout2⟩ :=
    step_chk_read30 oracle s1 (idx + 1) src dst hpc1 hret1 (by omega) hsrc1 hdst1
      hsrc_al hdst_al hsrc_bd hdst_bd hdisj
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  refine ⟨s2, by simpa using hst1.trans hs2, hpc2, ?_, ?_, ?_⟩
  · intro r hr1 hr6
    rw [hreg2 r hr6]
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr1.symm
  · intro j hj
    have hb := hcopy2 j hj
    simp only [MachineState.getByte, MachineState.getMem, hmem1] at hb ⊢
    exact hb
  · exact (MemEqOutside.of_mem_eq hmem1 dst (dst + 30)).trans hout2

/-! #### Invariant Registers and Prologue (`pc[0..16]`) -/

/-- Registers kept constant throughout the per-position loop, cap walk, and epilogue. -/
structure CheckFixedRegs (s : MachineState) (proofLen : Nat) : Prop where
  x2  : s.getReg .x2  = BitVec.ofNat 64 68719475936
  x5  : s.getReg .x5  = 0#64
  x11 : s.getReg .x11 = 96#64
  x13 : s.getReg .x13 = 0#64
  x18 : s.getReg .x18 = 4096#64
  x19 : s.getReg .x19 = 8192#64
  x21 : s.getReg .x21 = 256#64
  x26 : s.getReg .x26 = BitVec.ofNat 64 4294971392
  x31 : s.getReg .x31 = BitVec.ofNat 64 (10066334784 + proofLen)

def isFixedReg (r : Reg) : Bool :=
  r == .x2 || r == .x5 || r == .x11 || r == .x13 ||
  r == .x18 || r == .x19 || r == .x21 || r == .x26 || r == .x31

theorem CheckFixedRegs.of_agree {s1 s2 : MachineState} {proofLen : Nat}
    (h : CheckFixedRegs s1 proofLen)
    (heq : ∀ r : Reg, isFixedReg r = true → s2.getReg r = s1.getReg r) :
    CheckFixedRegs s2 proofLen :=
  ⟨(heq .x2 rfl).trans h.x2, (heq .x5 rfl).trans h.x5,
   (heq .x11 rfl).trans h.x11, (heq .x13 rfl).trans h.x13,
   (heq .x18 rfl).trans h.x18, (heq .x19 rfl).trans h.x19,
   (heq .x21 rfl).trans h.x21, (heq .x26 rfl).trans h.x26,
   (heq .x31 rfl).trans h.x31⟩

theorem isFixedReg_ne_of_false {r r' : Reg} (h : isFixedReg r = true) (hf : isFixedReg r' = false) :
    r ≠ r' := by
  intro heq; subst heq; rw [h] at hf; cases hf

end CommitGolfCandidate
