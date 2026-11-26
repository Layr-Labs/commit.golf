import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! Deterministic symbolic execution infrastructure for the submitted `check` image (`checkInstr`,
words `0..264`):
- Equivalence between coin-free `execute` and the pure deterministic evaluator `detExec` under
  `Oracle.run`, `Oracle.eval`, and `fixedOracleRun (traceCompressionReplies _)`.
- Compositional step/halt/phase combinators with byte-level memory frames.
- Reusable instruction-block lemmas (`step_ordinary`, `step_ecall_compress`, `step_bne_reg`,
  halt/copy/compare/zero-gap/helper-call blocks) and `CheckFixedRegs`. -/
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
theorem se12_6 : signExtend12 6#12 = 6#64 := by decide
theorem se12_8 : signExtend12 8#12 = 8#64 := by decide
theorem se12_16 : signExtend12 16#12 = 16#64 := by decide
theorem se12_24 : signExtend12 24#12 = 24#64 := by decide
theorem se12_29 : signExtend12 29#12 = 29#64 := by decide
theorem se12_29_ofNat : signExtend12 29#12 = BitVec.ofNat 64 29 := signExtend12_ofNat_lt2048 29 (by decide)
theorem se12_30 : signExtend12 30#12 = 30#64 := by decide
theorem se12_30_ofNat : signExtend12 30#12 = BitVec.ofNat 64 30 := signExtend12_ofNat_lt2048 30 (by decide)
theorem se12_32 : signExtend12 32#12 = 32#64 := by decide
theorem se12_48 : signExtend12 48#12 = 48#64 := by decide
theorem se12_56 : signExtend12 56#12 = 56#64 := by decide
theorem se12_62 : signExtend12 62#12 = 62#64 := by decide
theorem se12_63 : signExtend12 63#12 = 63#64 := by decide
theorem se12_64 : signExtend12 64#12 = 64#64 := by decide
theorem se12_96 : signExtend12 96#12 = 96#64 := by decide
theorem se12_120 : signExtend12 120#12 = 120#64 := by decide
theorem se12_160 : signExtend12 160#12 = 160#64 := by decide
theorem se12_168 : signExtend12 168#12 = 168#64 := by decide
theorem se12_256 : signExtend12 256#12 = BitVec.ofNat 64 256 := signExtend12_ofNat_lt2048 256 (by decide)
theorem se12_512 : signExtend12 512#12 = BitVec.ofNat 64 512 := signExtend12_ofNat_lt2048 512 (by decide)
theorem se12_736 : signExtend12 736#12 = BitVec.ofNat 64 736 := signExtend12_ofNat_lt2048 736 (by decide)
theorem se12_768 : signExtend12 768#12 = BitVec.ofNat 64 768 := signExtend12_ofNat_lt2048 768 (by decide)
theorem se12_792 : signExtend12 792#12 = BitVec.ofNat 64 792 := signExtend12_ofNat_lt2048 792 (by decide)
theorem se12_4090 : signExtend12 4090#12 = (-6#64 : Word) := by decide
theorem se12_4095 : signExtend12 4095#12 = (-1#64 : Word) := by decide
theorem chk_se12_7 : signExtend12 7#12 = 7#64 := by decide
theorem chk_se12_15 : signExtend12 15#12 = 15#64 := by decide
theorem chk_se12_2036 : signExtend12 2036#12 = 2036#64 := by decide
theorem chk_bv64_and_7 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& 7#64 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat64 a ha, toNat_ofNat64 (a % 8) (by omega),
    show (7#64 : Word).toNat = 7 by decide]
  change a &&& (2 ^ 3 - 1) = a % 2 ^ 3
  exact Nat.and_two_pow_sub_one_eq_mod a 3

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

theorem bv64_add_neg6 (n : Nat) :
    BitVec.ofNat 64 (n + 6) + signExtend12 (4090#12) = BitVec.ofNat 64 n := by
  rw [se12_4090, ← bv64_add n 6]
  change BitVec.ofNat 64 n + 6#64 + (-6#64 : Word) = BitVec.ofNat 64 n
  rw [BitVec.add_assoc, show (6#64 : Word) + (-6#64 : Word) = 0#64 by decide, BitVec.add_zero]

private theorem chk_bv64_and_63 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& 63#64 = BitVec.ofNat 64 (a % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat64 a ha, toNat_ofNat64 (a % 64) (by omega),
    show (63#64 : Word).toNat = 63 by decide]
  change a &&& (2 ^ 6 - 1) = a % 2 ^ 6
  exact Nat.and_two_pow_sub_one_eq_mod a 6

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

/-! #### Backward 6-Bit Tail Stream and Two-End Proof Cursor -/

/-- Exact number of backward tail bytes read after consuming `t` 6-bit tails. -/
def tailBytes (t : Nat) : Nat := (6 * t + 7) / 8

/-- Exact number of pending tail bits remaining in `x4` (`cCnt ∈ [0..7]`) after `t` tails. -/
def tailCnt (t : Nat) : Nat := 8 * tailBytes t - 6 * t

/-- Little-endian integer value of the first `k` backward bytes read from the end of `proof`. -/
def backBytesNat (s0 : MachineState) (proofLen k : Nat) : Nat :=
  ∑ j ∈ Finset.range k,
    (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - j)))).toNat * 2 ^ (8 * j)

/-- Exact pending bit-buffer value in `x3` (`cBuf < 2 ^ tailCnt t`) after `t` tails. -/
def tailBuf (s0 : MachineState) (proofLen t : Nat) : Nat :=
  backBytesNat s0 proofLen (tailBytes t) / 2 ^ (6 * t)

/-- Exact `t`-th 6-bit tail popped from the backward tail stream. -/
def tailAt (s0 : MachineState) (proofLen t : Nat) : BitVec 6 :=
  BitVec.ofNat 6 (backBytesNat s0 proofLen (tailBytes (t + 1)) / 2 ^ (6 * t))

/-- 238-bit digest assembled from 29 forward proof bytes at `fwdAddr` and the `t`-th 6-bit tail. -/
def proofDigest238 (s0 : MachineState) (proofLen fwdAddr t : Nat) : Digest :=
  ((0#18) ++ tailAt s0 proofLen t) ++ readBuffer s0 fwdAddr 29

theorem tailBytes_zero : tailBytes 0 = 0 := rfl
theorem tailCnt_zero : tailCnt 0 = 0 := rfl

theorem tailCnt_lt8 (t : Nat) : tailCnt t < 8 := by
  unfold tailCnt tailBytes; omega

theorem tailBytes_le_bits (t : Nat) : 6 * t ≤ 8 * tailBytes t := by
  unfold tailBytes; omega

theorem tailBytes_mono {a b : Nat} (h : a ≤ b) : tailBytes a ≤ tailBytes b := by
  unfold tailBytes; omega

theorem tailBytes_succ_ge6 (t : Nat) (h : 6 ≤ tailCnt t) :
    tailBytes (t + 1) = tailBytes t ∧ tailCnt (t + 1) = tailCnt t - 6 := by
  unfold tailCnt tailBytes at *; omega

theorem tailBytes_succ_lt6 (t : Nat) (h : tailCnt t < 6) :
    tailBytes (t + 1) = tailBytes t + 1 ∧ tailCnt (t + 1) = tailCnt t + 8 - 6 := by
  unfold tailCnt tailBytes at *; omega

theorem backBytesNat_zero (s0 : MachineState) (proofLen : Nat) :
    backBytesNat s0 proofLen 0 = 0 := by
  simp [backBytesNat]

theorem backBytesNat_succ (s0 : MachineState) (proofLen k : Nat) :
    backBytesNat s0 proofLen (k + 1) =
      backBytesNat s0 proofLen k +
        (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - k)))).toNat * 2 ^ (8 * k) :=
  Finset.sum_range_succ _ k

theorem backBytesNat_lt (s0 : MachineState) (proofLen k : Nat) :
    backBytesNat s0 proofLen k < 2 ^ (8 * k) := by
  induction k with
  | zero => simp [backBytesNat]
  | succ k ih =>
    rw [backBytesNat_succ, Nat.mul_succ, Nat.pow_add]
    have hb : (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - k)))).toNat ≤ 255 := by
      have := (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - k)))).isLt; omega
    have hm := Nat.mul_le_mul_right (2 ^ (8 * k)) hb
    have h256 : 2 ^ 8 = 256 := by decide
    rw [h256]
    omega

theorem tailBuf_zero (s0 : MachineState) (proofLen : Nat) :
    tailBuf s0 proofLen 0 = 0 := by
  simp [tailBuf, tailBytes_zero, backBytesNat_zero]

theorem tailBuf_lt (s0 : MachineState) (proofLen t : Nat) :
    tailBuf s0 proofLen t < 2 ^ tailCnt t := by
  unfold tailBuf
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]
  have hle := tailBytes_le_bits t
  have hpow : 2 ^ tailCnt t * 2 ^ (6 * t) = 2 ^ (8 * tailBytes t) := by
    rw [← Nat.pow_add]; congr 1; unfold tailCnt; omega
  rw [hpow]
  exact backBytesNat_lt s0 proofLen (tailBytes t)

theorem tailBuf_lt256 (s0 : MachineState) (proofLen t : Nat) :
    tailBuf s0 proofLen t < 256 := by
  have h1 := tailBuf_lt s0 proofLen t
  have h2 := tailCnt_lt8 t
  have h3 : 2 ^ tailCnt t ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 2 ^ 7 = 128 := by decide
  omega

theorem tailStep_lt6 (s0 : MachineState) (proofLen t : Nat) (h : tailCnt t < 6) :
    tailBuf s0 proofLen t +
      (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes t)))).toNat *
        2 ^ tailCnt t =
      backBytesNat s0 proofLen (tailBytes (t + 1)) / 2 ^ (6 * t) := by
  have hs := (tailBytes_succ_lt6 t h).1
  rw [hs, backBytesNat_succ]
  have hle := tailBytes_le_bits t
  have hpow : 2 ^ (8 * tailBytes t) = 2 ^ tailCnt t * 2 ^ (6 * t) := by
    rw [← Nat.pow_add]; congr 1; unfold tailCnt; omega
  rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
  rfl

theorem tailStep_div64 (s0 : MachineState) (proofLen t : Nat) :
    (backBytesNat s0 proofLen (tailBytes (t + 1)) / 2 ^ (6 * t)) / 64 =
      tailBuf s0 proofLen (t + 1) := by
  unfold tailBuf
  rw [Nat.div_div_eq_div_mul]
  congr 1
  rw [show 6 * (t + 1) = 6 * t + 6 by omega, Nat.pow_add]

theorem tailStep_lt16384 (s0 : MachineState) (proofLen t : Nat) :
    backBytesNat s0 proofLen (tailBytes (t + 1)) / 2 ^ (6 * t) < 16384 := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]
  have h1 := backBytesNat_lt s0 proofLen (tailBytes (t + 1))
  have hbits : 8 * tailBytes (t + 1) ≤ 6 * t + 14 := by unfold tailBytes; omega
  have h2 : 2 ^ (8 * tailBytes (t + 1)) ≤ 2 ^ (6 * t + 14) := Nat.pow_le_pow_right (by decide) hbits
  have h3 : 2 ^ (6 * t + 14) = 16384 * 2 ^ (6 * t) := by
    rw [Nat.add_comm, Nat.pow_add]
  omega

theorem byte_ofNat_tail6 (v : BitVec 6) : BitVec.ofNat 8 v.toNat = (0#2) ++ v := by
  apply BitVec.eq_of_toNat_eq
  have hv : v.toNat < 64 := v.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v.toNat < 256), BitVec.toNat_append]
  simp

theorem proofDigest238_byte_lt29 (s0 : MachineState) (proofLen fwdAddr t j : Nat) (hj : j < 29) :
    (proofDigest238 s0 proofLen fwdAddr t).extractLsb' (8 * j) 8 =
      s0.getByte (BitVec.ofNat 64 (fwdAddr + j)) := by
  rw [← read_buffer_byte s0 fwdAddr 29 j hj]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold proofDigest238
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    BitVec.getLsbD_append, show 8 * j + b < 8 * 29 by omega, ite_true]

theorem proofDigest238_byte_29 (s0 : MachineState) (proofLen fwdAddr t : Nat) :
    (proofDigest238 s0 proofLen fwdAddr t).extractLsb' (8 * 29) 8 =
      (0#2) ++ tailAt s0 proofLen t := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold proofDigest238
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, BitVec.getLsbD_append]
  have hge : ¬ (8 * 29 + b < 8 * 29) := by omega
  simp only [hge, Bool.false_eq_true, ite_false, show 8 * 29 + b - 8 * 29 = b by omega]
  by_cases h6 : b < 6
  · simp [h6]
  · simp [h6]

theorem proofDigest238_byte_ge30 (s0 : MachineState) (proofLen fwdAddr t j : Nat) (hj : 30 ≤ j) :
    (proofDigest238 s0 proofLen fwdAddr t).extractLsb' (8 * j) 8 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold proofDigest238
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, BitVec.getLsbD_append]
  have hge1 : ¬ (8 * j + b < 8 * 29) := by omega
  have hge2 : ¬ (8 * j + b - 8 * 29 < 6) := by omega
  simp [hge1, hge2]

theorem proofDigest238_eq_readBuffer (s s0 : MachineState) (proofLen dst src t : Nat)
    (hlo : ∀ j < 29, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (src + j)))
    (h29 : s.getByte (BitVec.ofNat 64 (dst + 29)) = (0#2) ++ tailAt s0 proofLen t)
    (h30 : s.getByte (BitVec.ofNat 64 (dst + 30)) = 0#8)
    (h31 : s.getByte (BitVec.ofNat 64 (dst + 31)) = 0#8) :
    readBuffer s dst 32 = proofDigest238 s0 proofLen src t := by
  have hr := read_serialized_slice s (proofDigest238 s0 proofLen src t) dst 0 32 (by
    intro j hj
    simp only [Nat.zero_add]
    by_cases hlt : j < 29
    · rw [hlo j hlt, proofDigest238_byte_lt29 s0 proofLen src t j hlt]
    · by_cases h29' : j = 29
      · subst h29'; rw [h29, proofDigest238_byte_29 s0 proofLen src t]
      · by_cases h30' : j = 30
        · subst h30'; rw [h30, proofDigest238_byte_ge30 s0 proofLen src t 30 (by omega)]
        · have h31' : j = 31 := by omega
          subst h31'; rw [h31, proofDigest238_byte_ge30 s0 proofLen src t 31 (by omega)])
  simpa using hr

theorem proofDigest238_of_bytes_eq (s0 : MachineState) (proofLen src t : Nat) (d : Digest)
    (hlo : ∀ j < 29, s0.getByte (BitVec.ofNat 64 (src + j)) = d.extractLsb' (8 * j) 8)
    (htail : tailAt s0 proofLen t = tail6 d) :
    proofDigest238 s0 proofLen src t = mask238 d := by
  apply mask238_eq_of_bytes
  · intro j hj
    rw [proofDigest238_byte_lt29 s0 proofLen src t j hj, hlo j hj]
  · rw [proofDigest238_byte_29 s0 proofLen src t, htail]
  · exact proofDigest238_byte_ge30 s0 proofLen src t 30 (by omega)
  · exact proofDigest238_byte_ge30 s0 proofLen src t 31 (by omega)

/-- Registers kept constant throughout the per-position loop, cap walk, and epilogue. -/
structure CheckFixedRegs (s : MachineState) : Prop where
  x2  : s.getReg .x2  = BitVec.ofNat 64 68719475936
  x5  : s.getReg .x5  = 0#64
  x9  : s.getReg .x9  = mask238Word
  x11 : s.getReg .x11 = 96#64
  x13 : s.getReg .x13 = 0#64
  x18 : s.getReg .x18 = 4096#64
  x19 : s.getReg .x19 = 8192#64
  x21 : s.getReg .x21 = 256#64
  x26 : s.getReg .x26 = BitVec.ofNat 64 4294971392

def isFixedReg (r : Reg) : Bool :=
  r == .x2 || r == .x5 || r == .x9 || r == .x11 || r == .x13 ||
  r == .x18 || r == .x19 || r == .x21 || r == .x26

theorem CheckFixedRegs.of_agree {s1 s2 : MachineState}
    (h : CheckFixedRegs s1)
    (heq : ∀ r : Reg, isFixedReg r = true → s2.getReg r = s1.getReg r) :
    CheckFixedRegs s2 :=
  ⟨(heq .x2 rfl).trans h.x2, (heq .x5 rfl).trans h.x5,
   (heq .x9 rfl).trans h.x9, (heq .x11 rfl).trans h.x11,
   (heq .x13 rfl).trans h.x13, (heq .x18 rfl).trans h.x18,
   (heq .x19 rfl).trans h.x19, (heq .x21 rfl).trans h.x21,
   (heq .x26 rfl).trans h.x26⟩

theorem isFixedReg_ne_of_false {r r' : Reg} (h : isFixedReg r = true) (hf : isFixedReg r' = false) :
    r ≠ r' := by
  intro heq; subst heq; rw [h] at hf; cases hf

/-- Two-end proof cursor invariant for forward byte offset `pLo` and consumed 6-bit tail count `tCnt`. -/
structure ProofCursor (s0 : MachineState) (proofLen pLo tCnt : Nat) (s : MachineState) : Prop where
  le  : pLo + tailBytes tCnt ≤ proofLen
  x25 : s.getReg .x25 = BitVec.ofNat 64 (10603204576 + pLo)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes tCnt))
  x3  : s.getReg .x3  = BitVec.ofNat 64 (tailBuf s0 proofLen tCnt)
  x4  : s.getReg .x4  = BitVec.ofNat 64 (tailCnt tCnt)

def isCursorReg (r : Reg) : Bool :=
  r == .x25 || r == .x31 || r == .x3 || r == .x4

theorem ProofCursor.of_agree {s0 s1 s2 : MachineState} {proofLen pLo tCnt : Nat}
    (h : ProofCursor s0 proofLen pLo tCnt s1)
    (heq : ∀ r : Reg, isCursorReg r = true → s2.getReg r = s1.getReg r) :
    ProofCursor s0 proofLen pLo tCnt s2 :=
  ⟨h.le, (heq .x25 rfl).trans h.x25, (heq .x31 rfl).trans h.x31,
   (heq .x3 rfl).trans h.x3, (heq .x4 rfl).trans h.x4⟩

theorem isCursorReg_ne_of_false {r r' : Reg} (h : isCursorReg r = true) (hf : isCursorReg r' = false) :
    r ≠ r' := by
  intro heq; subst heq; rw [h] at hf; cases hf

/-! ### 3. Single-Instruction and Reusable Block Execution Lemmas -/

theorem step_ordinary (oracle : Oracle) (s : MachineState) (idx : Nat) (instr : Instr)
    (hhi : idx < 295) (hpc : s.pc = pcWord idx)
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

/-- Standalone 1-step `BNE r1, r2, imm` helper isolating negative branch immediates from inductions. -/
theorem step_bne_reg (oracle : Oracle) (idx target : Nat) (r1 r2 : Reg) (imm : BitVec 13)
    (hhi : idx < 295) (hc : checkInstr idx = .base (.BNE r1 r2 imm))
    (htgt : pcWord idx + signExtend13 imm = pcWord target)
    (s : MachineState) (v1 v2 : Nat) (hv1 : v1 < 2 ^ 64) (hv2 : v2 < 2 ^ 64)
    (hpc : s.pc = pcWord idx)
    (hr1 : s.getReg r1 = BitVec.ofNat 64 v1)
    (hr2 : s.getReg r2 = BitVec.ofNat 64 v2) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if v1 = v2 then pcWord (idx + 1) else pcWord target) ∧
      (∀ r, s'.getReg r = s.getReg r) ∧
      s'.mem = s.mem := by
  have hst := step_ordinary oracle s idx (.BNE r1 r2 imm) hhi hpc hc
    (by intro h; cases h) (ordinaryStep_BNE_base s r1 r2 imm)
  refine ⟨execInstrBr s (.BNE r1 r2 imm), hst, ?_,
    execInstrBr_BNE_getReg_base s r1 r2 imm,
    execInstrBr_BNE_mem_base s r1 r2 imm⟩
  by_cases heq : v1 = v2
  · rw [if_pos heq]
    have hne_f : (s.getReg r1 != s.getReg r2) = false := by
      rw [hr1, hr2, heq, bne_self_eq_false]
    rw [execInstrBr_BNE_pc_false_base s r1 r2 imm hne_f, hpc, pcWord_add_four]
  · rw [if_neg heq]
    have hne_t : (s.getReg r1 != s.getReg r2) = true := by
      rw [hr1, hr2]
      exact (bv64_bne_eq v1 v2 hv1 hv2).trans (decide_eq_true heq)
    rw [execInstrBr_BNE_pc_true_base s r1 r2 imm hne_t, hpc, htgt]

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
    (hhi : idx < 295) (hpc : s.pc = pcWord idx)
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

theorem halt_accept (oracle : Oracle) (s : MachineState) (hpc : s.pc = pcWord 258) :
    HaltsWith oracle s 3 0 .success [] := by
  refine ⟨by decide, fun extra => ?_⟩
  have s1 : StepsTo oracle s (execInstrBr s (.ADDI .x5 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle s 258 (.ADDI .x5 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let st1 := execInstrBr s (.ADDI .x5 .x0 1#12)
  have hpc1 : st1.pc = pcWord 259 := by
    simp only [st1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have s2 : StepsTo oracle st1 (execInstrBr st1 (.ADDI .x10 .x0 0#12)) 1 0 [] :=
    step_ordinary oracle st1 259 (.ADDI .x10 .x0 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let st2 := execInstrBr st1 (.ADDI .x10 .x0 0#12)
  have hpc2 : st2.pc = pcWord 260 := by
    simp only [st2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have s12 : StepsTo oracle s st2 2 0 [] := by simpa using s1.trans s2
  have h2 := s12 (extra + 1)
  rw [show 3 + extra = 2 + (extra + 1) by omega]
  have hfetch3 : fetch (submission.image .check) st2 = some (.base .ECALL) := by
    rw [check_fetch st2 260 (by decide) hpc2]; rfl
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

theorem halt_reject (oracle : Oracle) (s : MachineState) (hpc : s.pc = pcWord 261) :
    HaltsWith oracle s 3 0 .failure [] := by
  refine ⟨by decide, fun extra => ?_⟩
  have s1 : StepsTo oracle s (execInstrBr s (.ADDI .x5 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle s 261 (.ADDI .x5 .x0 1#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let st1 := execInstrBr s (.ADDI .x5 .x0 1#12)
  have hpc1 : st1.pc = pcWord 262 := by
    simp only [st1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have s2 : StepsTo oracle st1 (execInstrBr st1 (.ADDI .x10 .x0 1#12)) 1 0 [] :=
    step_ordinary oracle st1 262 (.ADDI .x10 .x0 1#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let st2 := execInstrBr st1 (.ADDI .x10 .x0 1#12)
  have hpc2 : st2.pc = pcWord 263 := by
    simp only [st2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have s12 : StepsTo oracle s st2 2 0 [] := by simpa using s1.trans s2
  have h2 := s12 (extra + 1)
  rw [show 3 + extra = 2 + (extra + 1) by omega]
  have hfetch3 : fetch (submission.image .check) st2 = some (.base .ECALL) := by
    rw [check_fetch st2 263 (by decide) hpc2]; rfl
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

/-- First 2 instructions of byte-copy loop (`LBU x6, 0(x25); SB x12, x6, 0`). -/
private theorem step_byte_copy_mem (oracle : Oracle) (base : Nat)
    (hhi : base + 2 ≤ 295)
    (hc0 : checkInstr base = .base (.LBU .x6 .x25 0#12))
    (hc1 : checkInstr (base + 1) = .base (.SB .x12 .x6 0#12))
    (s : MachineState) (src dst : Nat)
    (hpc : s.pc = pcWord base)
    (hsrc : s.getReg .x25 = BitVec.ofNat 64 src)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_bd : src + 1 ≤ MEMORY_BYTES) (hdst_bd : dst + 1 ≤ MEMORY_BYTES) :
    ∃ s', StepsTo oracle s s' 2 0 [] ∧
      s'.pc = pcWord (base + 2) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      s'.getByte (BitVec.ofNat 64 dst) = s.getByte (BitVec.ofNat 64 src) ∧
      MemEqOutside s s' dst (dst + 1) := by
  have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
  have ha0 : s.getReg .x25 + signExtend12 0#12 = BitVec.ofNat 64 src := by
    rw [hsrc, se12_0, BitVec.add_zero]
  have hv0 : memoryArgumentsValid s (.LBU .x6 .x25 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha0]
    exact accessValid_ofNat src 1 (by omega) (by omega)
  have hst0 := step_ordinary oracle s base (.LBU .x6 .x25 0#12) (by omega) hpc hc0 (by intro h; cases h)
    (by simp [ordinaryStep, hv0])
  let s1 := execInstrBr s (.LBU .x6 .x25 0#12)
  have hpc1 : s1.pc = pcWord (base + 1) := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = (s.getByte (BitVec.ofNat 64 src)).zeroExtend 64 := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha0]
    exact MachineState.getReg_setReg_eq (by decide)
  have hreg1 : ∀ r, r ≠ .x6 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha1 : s1.getReg .x12 + signExtend12 0#12 = BitVec.ofNat 64 dst := by
    rw [hreg1 .x12 (by decide), hdst, se12_0, BitVec.add_zero]
  have hv1 : memoryArgumentsValid s1 (.SB .x12 .x6 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha1]
    exact accessValid_ofNat dst 1 (by omega) (by omega)
  have hst1 := step_ordinary oracle s1 (base + 1) (.SB .x12 .x6 0#12) (by omega) hpc1 hc1 (by intro h; cases h)
    (by simp [ordinaryStep, hv1])
  let s2 := execInstrBr s1 (.SB .x12 .x6 0#12)
  have hpc2 : s2.pc = pcWord (base + 2) := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r hr => by
    have : s2.getReg r = s1.getReg r := by
      simp [s2, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    exact this.trans (hreg1 r hr)
  have hs2_byte : ∀ q : Word, s2.getByte q =
      (s.setByte (BitVec.ofNat 64 dst) (s.getByte (BitVec.ofNat 64 src))).getByte q := by
    intro q
    simp only [s2, execInstrBr, ha1, hx6_1, truncate8_zeroExtend64,
      MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, mem_setPC, hmem1]
  refine ⟨s2, (hst0.trans hst1).eq_of rfl (by decide) (by decide) (by simp), hpc2, hreg2, ?_, ?_⟩
  · rw [hs2_byte, set_byte_read]; simp
  · intro a ha hout
    rw [hs2_byte]
    exact MemEqOutside_setByte s dst _ (by omega) a ha hout

/-- Next 3 instructions of byte-copy loop (`ADDI x25, 1; ADDI x12, 1; ADDI rCnt, -1`). -/
private theorem step_byte_copy_inc (oracle : Oracle) (base : Nat) (rCnt : Reg)
    (hr0 : rCnt ≠ .x0) (hr12 : rCnt ≠ .x12) (hr25 : rCnt ≠ .x25)
    (hhi : base + 5 ≤ 295)
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

/-- Generic `n`-byte copy loop (`LBU x6, 0(x25); SB x12, x6, 0; ADDI x25, x25, 1;
ADDI x12, x12, 1; ADDI rCnt, rCnt, -1; BNE rCnt, x0, -20`). -/
theorem step_byte_copy_loop (oracle : Oracle) (base : Nat) (rCnt : Reg)
    (hr0 : rCnt ≠ .x0) (hr6 : rCnt ≠ .x6) (hr12 : rCnt ≠ .x12) (hr25 : rCnt ≠ .x25)
    (hhi : base + 6 ≤ 295)
    (hc0 : checkInstr base = .base (.LBU .x6 .x25 0#12))
    (hc1 : checkInstr (base + 1) = .base (.SB .x12 .x6 0#12))
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
      (∀ r : Reg, r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → r ≠ rCnt → s'.getReg r = s.getReg r) ∧
      (∀ j < n, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      MemEqOutside s s' dst (dst + n) := by
  have hmb : MEMORY_BYTES = 2 ^ 36 := rfl
  induction n generalizing s src dst with
  | zero => omega
  | succ k ih =>
    obtain ⟨s2, hs2, hpc2, hreg2, hcopy2, hout2⟩ :=
      step_byte_copy_mem oracle base (by omega) hc0 hc1 s src dst hpc hsrc hdst (by omega) (by omega)
    obtain ⟨s5, hs5, hpc5, hx25_5, hx12_5, hcnt_5, hreg5, hmem5⟩ :=
      step_byte_copy_inc oracle base rCnt hr0 hr12 hr25 (by omega) hc2 hc3 hc4 s2 src dst k hpc2
        ((hreg2 .x25 (by decide)).trans hsrc) ((hreg2 .x12 (by decide)).trans hdst)
        ((hreg2 rCnt hr6).trans hcnt)
    obtain ⟨s6, hst5, hpc6_if, hreg6, hmem6'⟩ :=
      step_bne_reg oracle (base + 5) base rCnt .x0 8172#13 (by omega) hc5 (pcWord_sub_20 base)
        s5 k 0 (by omega) (by omega) hpc5 hcnt_5 (getReg_x0 s5)
    have hmem6 : s6.mem = s2.mem := hmem6'.trans hmem5
    have h16 : StepsTo oracle s s6 6 0 [] :=
      ((hs2.trans hs5).trans hst5).eq_of rfl (by decide) (by decide) (by simp)
    cases k with
    | zero =>
      have hpc6 : s6.pc = pcWord (base + 6) := by simpa only [ite_true] using hpc6_if
      refine ⟨s6, h16, hpc6, (hreg6 .x25).trans hx25_5, (hreg6 .x12).trans hx12_5,
        (hreg6 rCnt).trans hcnt_5,
        fun r h6 h12 h25 hrc => (hreg6 r).trans ((hreg5 r h12 h25 hrc).trans (hreg2 r h6)),
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
      · intro r h6 h12 h25 hrc
        exact (hregFin r h6 h12 h25 hrc).trans ((hreg6 r).trans ((hreg5 r h12 h25 hrc).trans (hreg2 r h6)))
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

/-- Call and return from `readN` (`pc[264..270]`), `6 * n + 1` steps (`n > 0`). -/
theorem step_chk_read_n (oracle : Oracle) (s : MachineState) (retIdx n src dst : Nat)
    (hn : 0 < n) (hn_lt : n < 2 ^ 64)
    (hpc : s.pc = pcWord 264) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 295)
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
    step_byte_copy_loop oracle 264 .x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl n hn hn_lt s src dst hpc hsrc hdst hcnt hsrc_bd hdst_bd hdisj
  have hst := step_ordinary oracle s1 270 (.JALR .x0 .x1 0#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.JALR .x0 .x1 0#12)
  have hmem2 : s2.mem = s1.mem := by simp [s2, execInstrBr, MachineState.setReg, mem_setPC]
  have hreg2 : ∀ r, s2.getReg r = s1.getReg r := fun r => by
    simp [s2, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
  refine ⟨s2, (hs1.trans hst).eq_of rfl (by omega) (by decide) (by simp), ?_, (hreg2 .x25).trans hx25_1,
    fun r h6 h10 h12 h25 => (hreg2 r).trans (hreg1 r h6 h12 h25 h10),
    fun j hj => by simpa only [MachineState.getByte, MachineState.getMem, hmem2] using hcopy1 j hj,
    hout1.trans (MemEqOutside.of_mem_eq hmem2 dst (dst + n))⟩
  simp only [s2, execInstrBr, MachineState.setPC, hreg1 .x1 (by decide) (by decide) (by decide) (by decide), hret]
  exact jalr_pcWord retIdx (by omega)

/-- Helper: `ADDI .x10 .x0 n; JAL .x1 readN` (`6 * n + 3` steps). -/
theorem step_call_read_n (oracle : Oracle) (idx n : Nat) (s : MachineState) (src dst : Nat)
    (hn : 0 < n) (hn_lt : n < 2048) (hhi : idx + 2 ≤ 264)
    (haddi : checkInstr idx = .base (.ADDI .x10 .x0 (BitVec.ofNat 12 n)))
    (hjal : checkInstr (idx + 1) = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (264 - (idx + 1))))))
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
  let off := BitVec.ofNat 21 (4 * (264 - (idx + 1)))
  have hst1 := step_ordinary oracle s1 (idx + 1) (.JAL .x1 off) (by omega) hpc1 hjal (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.JAL .x1 off)
  have hpc2 : s2.pc = pcWord 264 := by
    simp only [s2, execInstrBr, MachineState.setPC, hpc1]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (264 - (idx + 1))) :=
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

/-- Tail epilogue ALU part (`pc[288..290]`): pop 6 bits from `x3`, decrement `x4` by 6 (3 steps). -/
private theorem step_chk_have6_alu (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (s : MachineState) (tCnt : Nat)
    (hpc : s.pc = pcWord 288)
    (hx3  : s.getReg .x3  = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)))
    (hx4  : s.getReg .x4  = BitVec.ofNat 64 (tailCnt (tCnt + 1) + 6)) :
    ∃ s', StepsTo oracle s s' 3 0 [] ∧
      s'.pc = pcWord 291 ∧
      s'.getReg .x6 = BitVec.ofNat 64 ((backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)) % 64) ∧
      s'.getReg .x3 = BitVec.ofNat 64 (tailBuf s0 proofLen (tCnt + 1)) ∧
      s'.getReg .x4 = BitVec.ofNat 64 (tailCnt (tCnt + 1)) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      s'.mem = s.mem := by
  let curBits := backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)
  have hcb_lt : curBits < 16384 := tailStep_lt16384 s0 proofLen tCnt
  have hst0 := step_ordinary oracle s 288 (.ANDI .x6 .x3 63#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ANDI .x6 .x3 63#12)
  have hpc1 : s1.pc = pcWord 289 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst1 := step_ordinary oracle s1 289 (.SRLI .x3 .x3 6#6) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.SRLI .x3 .x3 6#6)
  have hpc2 : s2.pc = pcWord 290 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hst2 := step_ordinary oracle s2 290 (.ADDI .x4 .x4 4090#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADDI .x4 .x4 4090#12)
  have hpc3 : s3.pc = pcWord 291 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem3 : s3.mem = s.mem := by simp [s3, s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (curBits % 64) := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x6), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x6), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hx3, se12_63]
    exact chk_bv64_and_63 curBits (by omega)
  have hx3_3 : s3.getReg .x3 = BitVec.ofNat 64 (tailBuf s0 proofLen (tCnt + 1)) := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x3), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x3), hx3,
      show (6#6 : BitVec 6).toNat = 6 by decide, bv64_shr curBits 6 (by omega)]
    exact congrArg (BitVec.ofNat 64) (tailStep_div64 s0 proofLen tCnt)
  have hx4_3 : s3.getReg .x4 = BitVec.ofNat 64 (tailCnt (tCnt + 1)) := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x4), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x4), hx4]
    exact bv64_add_neg6 (tailCnt (tCnt + 1))
  have hreg3 : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → s3.getReg r = s.getReg r := fun r h3 h4 h6 => by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h4.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h3.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  exact ⟨s3, ((hst0.trans hst1).trans hst2).eq_of rfl (by decide) (by decide) (by simp),
    hpc3, hx6_3, hx3_3, hx4_3, hreg3, hmem3⟩

/-- Single byte-store helper at `pc[idx]` (`SB .x12 rVal off#12`). -/
private theorem step_sb_x12 (oracle : Oracle) (idx : Nat) (rVal : Reg) (off : Nat)
    (hhi : idx < 295) (hoff : off < 2048)
    (hc : checkInstr idx = .base (.SB .x12 rVal (BitVec.ofNat 12 off)))
    (s : MachineState) (baseAddr : Nat)
    (hpc : s.pc = pcWord idx)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 baseAddr)
    (hbd : baseAddr + off + 1 ≤ MEMORY_BYTES) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = pcWord (idx + 1) ∧
      (∀ r : Reg, s'.getReg r = s.getReg r) ∧
      s'.getByte (BitVec.ofNat 64 (baseAddr + off)) = (s.getReg rVal).truncate 8 ∧
      MemEqOutside s s' (baseAddr + off) (baseAddr + off + 1) := by
  have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
  have ha : s.getReg .x12 + signExtend12 (BitVec.ofNat 12 off) = BitVec.ofNat 64 (baseAddr + off) := by
    rw [hx12, signExtend12_ofNat_lt2048 off hoff, bv64_add]
  have hv : memoryArgumentsValid s (.SB .x12 rVal (BitVec.ofNat 12 off)) = true := by
    simp only [memoryArgumentsValid, memAccess, ha]
    exact accessValid_ofNat (baseAddr + off) 1 (by omega) (by omega)
  have hst := step_ordinary oracle s idx (.SB .x12 rVal (BitVec.ofNat 12 off)) hhi hpc hc (by intro h; cases h)
    (by simp [ordinaryStep, hv])
  let s1 := execInstrBr s (.SB .x12 rVal (BitVec.ofNat 12 off))
  refine ⟨s1, hst, by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four],
    fun r => by simp [s1, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg],
    ?_, ?_⟩
  · simp only [s1, execInstrBr, ha, MachineState.getByte, MachineState.getMem_setPC]
    change (s.setByte (BitVec.ofNat 64 (baseAddr + off)) ((s.getReg rVal).truncate 8)).getByte
      (BitVec.ofNat 64 (baseAddr + off)) = _
    rw [set_byte_read]; simp
  · intro a ha' hout
    simp only [s1, execInstrBr, ha, MachineState.getByte, MachineState.getMem_setPC]
    exact MemEqOutside_setByte s (baseAddr + off) _ (by omega) a ha' hout

/-- Tail epilogue `r29_pop` (`pc[288..294]`): pop 6 bits from `x3`, decrement `x4` by 6,
write byte 29 and zero bytes 30..31, return to `x1` (7 steps). -/
private theorem step_chk_have6 (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (s : MachineState) (retIdx pLo tCnt dst : Nat)
    (hpc : s.pc = pcWord 288) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 295)
    (hle_next : pLo + 29 + tailBytes (tCnt + 1) ≤ proofLen)
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10603204576 + (pLo + 29)))
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes (tCnt + 1))))
    (hx3  : s.getReg .x3  = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)))
    (hx4  : s.getReg .x4  = BitVec.ofNat 64 (tailCnt (tCnt + 1) + 6))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (dst + 29))
    (hdst_hi : dst + 32 ≤ 4294971392)
    (hlo : ∀ j < 29, s.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (10603204576 + pLo + j))) :
    ∃ s', StepsTo oracle s s' 7 0 [] ∧
      s'.pc = pcWord retIdx ∧
      ProofCursor s0 proofLen (pLo + 29) (tCnt + 1) s' ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = proofDigest238 s0 proofLen (10603204576 + pLo) tCnt ∧
      MemEqOutside s s' (dst + 29) (dst + 32) := by
  let curBits := backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)
  obtain ⟨s3, hs3, hpc3, hx6_3, hx3_3, hx4_3, hreg3, hmem3⟩ :=
    step_chk_have6_alu oracle s0 proofLen s tCnt hpc hx3 hx4
  have hx12_3 : s3.getReg .x12 = BitVec.ofNat 64 (dst + 29) :=
    (hreg3 .x12 (by decide) (by decide) (by decide)).trans hx12
  obtain ⟨s4, hs4, hpc4, hreg4, hb29_4, hout34⟩ :=
    step_sb_x12 oracle 291 .x6 0 (by decide) (by decide) rfl s3 (dst + 29) hpc3 hx12_3 (by unfold MEMORY_BYTES; omega)
  obtain ⟨s5, hs5, hpc5, hreg5, hb30_5, hout45⟩ :=
    step_sb_x12 oracle 292 .x0 1 (by decide) (by decide) rfl s4 (dst + 29) hpc4 ((hreg4 .x12).trans hx12_3) (by unfold MEMORY_BYTES; omega)
  obtain ⟨s6, hs6, hpc6, hreg6, hb31_6, hout56⟩ :=
    step_sb_x12 oracle 293 .x0 2 (by decide) (by decide) rfl s5 (dst + 29) hpc5 ((hreg5 .x12).trans ((hreg4 .x12).trans hx12_3)) (by unfold MEMORY_BYTES; omega)
  have hst6 := step_ordinary oracle s6 294 (.JALR .x0 .x1 0#12) (by decide) hpc6 rfl (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.JALR .x0 .x1 0#12)
  have hmem7 : s7.mem = s6.mem := by simp [s7, execInstrBr, MachineState.setReg, mem_setPC]
  have hreg6_3 : ∀ r, s6.getReg r = s3.getReg r := fun r => (hreg6 r).trans ((hreg5 r).trans (hreg4 r))
  have hreg7 : ∀ r, s7.getReg r = s3.getReg r := fun r => by
    have : s7.getReg r = s6.getReg r := by simp [s7, execInstrBr, MachineState.setReg, MachineState.getReg_setPC]
    exact this.trans (hreg6_3 r)
  have hout_all : MemEqOutside s s7 (dst + 29) (dst + 32) :=
    (MemEqOutside.of_mem_eq hmem3 (dst + 29) (dst + 32)).trans
      ((hout34.mono (by omega) (by omega)).trans
        ((hout45.mono (by omega) (by omega)).trans
          ((hout56.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem7 (dst + 29) (dst + 32)))))
  have hb29 : s7.getByte (BitVec.ofNat 64 (dst + 29)) = (0#2) ++ tailAt s0 proofLen tCnt := by
    rw [show s7.getByte (BitVec.ofNat 64 (dst + 29)) = s6.getByte (BitVec.ofNat 64 (dst + 29)) by
          simp [MachineState.getByte, MachineState.getMem, hmem7],
      hout56 (dst + 29) (by omega) (by omega), hout45 (dst + 29) (by omega) (by omega),
      show dst + 29 = dst + 29 + 0 by omega, hb29_4, hx6_3, truncate8_ofNat64 (curBits % 64) (by omega)]
    have hta : (tailAt s0 proofLen tCnt).toNat = curBits % 64 := by
      simp [tailAt, curBits, BitVec.toNat_ofNat]
    rw [← hta, byte_ofNat_tail6]
  have hb30 : s7.getByte (BitVec.ofNat 64 (dst + 30)) = 0#8 := by
    rw [show s7.getByte (BitVec.ofNat 64 (dst + 30)) = s6.getByte (BitVec.ofNat 64 (dst + 30)) by
          simp [MachineState.getByte, MachineState.getMem, hmem7],
      hout56 (dst + 30) (by omega) (by omega), show dst + 30 = dst + 29 + 1 by omega, hb30_5, getReg_x0]
    decide
  have hb31 : s7.getByte (BitVec.ofNat 64 (dst + 31)) = 0#8 := by
    rw [show s7.getByte (BitVec.ofNat 64 (dst + 31)) = s6.getByte (BitVec.ofNat 64 (dst + 31)) by
          simp [MachineState.getByte, MachineState.getMem, hmem7],
      show dst + 31 = dst + 29 + 2 by omega, hb31_6, getReg_x0]
    decide
  refine ⟨s7, ?_, ?_, ?_, fun r h3 h4 h6 => (hreg7 r).trans (hreg3 r h3 h4 h6), ?_, hout_all⟩
  · have h := ((hs3.trans hs4).trans (hs5.trans hs6)).trans hst6
    exact h.eq_of rfl (by decide) (by decide) (by simp)
  · simp only [s7, execInstrBr, MachineState.setPC, hreg6_3, hreg3 .x1 (by decide) (by decide) (by decide), hret]
    exact jalr_pcWord retIdx (by omega)
  · exact ⟨hle_next,
      (hreg7 .x25).trans ((hreg3 .x25 (by decide) (by decide) (by decide)).trans hx25),
      (hreg7 .x31).trans ((hreg3 .x31 (by decide) (by decide) (by decide)).trans hx31),
      (hreg7 .x3).trans hx3_3, (hreg7 .x4).trans hx4_3⟩
  · exact proofDigest238_eq_readBuffer s7 s0 proofLen dst (10603204576 + pLo) tCnt
      (fun j hj => (hout_all (dst + j) (by omega) (by omega)).trans (hlo j hj)) hb29 hb30 hb31

/-- Backward byte load + shift-OR refill (`pc[283..287]`, 5 steps) when `tailCnt tCnt < 6`. -/
private theorem step_chk_load_backbyte (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (hplen : proofLen ≤ proofCap) (s : MachineState) (tCnt : Nat)
    (hlt6 : tailCnt tCnt < 6) (htb_lt : tailBytes (tCnt + 1) ≤ proofLen)
    (hpc : s.pc = pcWord 283)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes tCnt)))
    (hx3  : s.getReg .x3  = BitVec.ofNat 64 (tailBuf s0 proofLen tCnt))
    (hx4  : s.getReg .x4  = BitVec.ofNat 64 (tailCnt tCnt))
    (hhigh : HighMemPreserved s0 s) :
    ∃ s', StepsTo oracle s s' 5 0 [] ∧
      s'.pc = pcWord 288 ∧
      s'.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes (tCnt + 1))) ∧
      s'.getReg .x3  = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)) ∧
      s'.getReg .x4  = BitVec.ofNat 64 (tailCnt (tCnt + 1) + 6) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x31 → s'.getReg r = s.getReg r) ∧
      s'.mem = s.mem := by
  have hplen_bd : proofLen ≤ 8239714016 := hplen
  obtain ⟨htb_s, htc_s⟩ := tailBytes_succ_lt6 tCnt hlt6
  -- Part A: pc[283..284]: ADDI x31, x31, -1; LBU x6, 0(x31)
  have hst0 := step_ordinary oracle s 283 (.ADDI .x31 .x31 4095#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x31 .x31 4095#12)
  have hpc1 : s1.pc = pcWord 284 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx31_1 : s1.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes (tCnt + 1))) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx31,
      show 10603204576 + (proofLen - tailBytes tCnt) =
        (10603204576 + (proofLen - tailBytes (tCnt + 1))) + 1 by omega]
    exact bv64_add_neg1 _
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have ha1 : s1.getReg .x31 + signExtend12 0#12 =
      BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt)) := by
    rw [hx31_1, se12_0, BitVec.add_zero]; congr 1; omega
  have hv1 : memoryArgumentsValid s1 (.LBU .x6 .x31 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha1]
    exact accessValid_ofNat _ 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst1 := step_ordinary oracle s1 284 (.LBU .x6 .x31 0#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv1])
  have h2 : ∃ s2, StepsTo oracle s s2 2 0 [] ∧
      s2.pc = pcWord 285 ∧
      s2.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes (tCnt + 1))) ∧
      s2.getReg .x6 = BitVec.ofNat 64 (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt)))).toNat ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x31 → s2.getReg r = s.getReg r) ∧
      s2.mem = s.mem := by
    let s2 := execInstrBr s1 (.LBU .x6 .x31 0#12)
    refine ⟨s2, (hst0.trans hst1).eq_of rfl (by decide) (by decide) (by simp),
      by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four], ?_, ?_, ?_,
      by simp [s2, execInstrBr, mem_setPC, mem_setReg, hmem1]⟩
    · simp only [s2, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hx31_1]
    · simp only [s2, execInstrBr, MachineState.getReg_setPC, ha1]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hb_eq : s1.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt))) =
          s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt))) := by
        have : s1.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt))) =
            s.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt))) := by
          simp [MachineState.getByte, MachineState.getMem, hmem1]
        rw [this]
        exact hhigh _ (by omega) (by omega)
      rw [hb_eq]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.zeroExtend, BitVec.toNat_setWidth]
    · intro r h6 h31
      simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h31.symm]
  -- Part B: pc[285..287]: SLL x6, x6, x4; OR x3, x3, x6; ADDI x4, x4, 8
  obtain ⟨s2, hs2, hpc2, hx31_2, hx6_2, hreg2, hmem2⟩ := h2
  let bk := (s0.getByte (BitVec.ofNat 64 (10603204576 + (proofLen - 1 - tailBytes tCnt)))).toNat
  have hbk_lt : bk < 256 := (s0.getByte _).isLt
  have hst2 := step_ordinary oracle s2 285 (.SLL .x6 .x6 .x4) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.SLL .x6 .x6 .x4)
  have hpc3 : s3.pc = pcWord 286 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hst3 := step_ordinary oracle s3 286 (.OR .x3 .x3 .x6) (by decide) hpc3 rfl (by intro h; cases h) rfl
  let s4 := execInstrBr s3 (.OR .x3 .x3 .x6)
  have hpc4 : s4.pc = pcWord 287 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hst4 := step_ordinary oracle s4 287 (.ADDI .x4 .x4 8#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.ADDI .x4 .x4 8#12)
  have hpc5 : s5.pc = pcWord 288 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simp [s5, s4, s3, execInstrBr, mem_setPC, mem_setReg, hmem2]
  have hx4_2 : s2.getReg .x4 = BitVec.ofNat 64 (tailCnt tCnt) := (hreg2 .x4 (by decide) (by decide)).trans hx4
  have hx3_2 : s2.getReg .x3 = BitVec.ofNat 64 (tailBuf s0 proofLen tCnt) := (hreg2 .x3 (by decide) (by decide)).trans hx3
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (bk * 2 ^ tailCnt tCnt) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx6_2, hx4_2,
      toNat_ofNat64 (tailCnt tCnt) (by omega), Nat.mod_eq_of_lt (by omega : tailCnt tCnt < 64),
      bv64_shl bk (tailCnt tCnt) (by omega)]
  have hx3_3 : s3.getReg .x3 = BitVec.ofNat 64 (tailBuf s0 proofLen tCnt) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x3), hx3_2]
  have hx3_5 : s5.getReg .x3 = BitVec.ofNat 64 (backBytesNat s0 proofLen (tailBytes (tCnt + 1)) / 2 ^ (6 * tCnt)) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x3), MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide), hx3_3, hx6_3]
    have hpow6 : 2 ^ tailCnt tCnt ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    have h32 : 2 ^ 5 = 32 := by decide
    have htb_lt := tailBuf_lt s0 proofLen tCnt
    have hsum_lt : tailBuf s0 proofLen tCnt + bk * 2 ^ tailCnt tCnt < 2 ^ 64 := by
      have : bk * 2 ^ tailCnt tCnt ≤ 285 * 32 := Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [bv64_or_shift_eq_add _ bk (tailCnt tCnt) htb_lt hsum_lt]
    exact congrArg (BitVec.ofNat 64) (tailStep_lt6 s0 proofLen tCnt hlt6)
  have hx4_5 : s5.getReg .x4 = BitVec.ofNat 64 (tailCnt (tCnt + 1) + 6) := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x4), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x4), hx4_2, se12_8, bv64_add]
    have htc := (tailBytes_succ_lt6 tCnt hlt6).2
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx31_5 : s5.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes (tCnt + 1))) := by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x4 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x3 ≠ .x31), MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hx31_2]
  have hreg5 : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x31 → s5.getReg r = s.getReg r :=
    fun r h3 h4 h6 h31 => by
      simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h4.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h3.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
      exact hreg2 r h6 h31
  exact ⟨s5, (hs2.trans ((hst2.trans hst3).trans hst4)).eq_of rfl (by decide) (by decide) (by simp),
    hpc5, hx31_5, hx3_5, hx4_5, hreg5, hmem5⟩

private theorem pc_272_reject : pcWord 272 + signExtend13 8148#13 = pcWord 261 := by decide
private theorem pc_281_have6 : pcWord 281 + signExtend13 28#13 = pcWord 288 := by decide
private theorem pc_282_reject : pcWord 282 + signExtend13 8108#13 = pcWord 261 := by decide

/-- Call and return from `read29_t6` (`pc[271..294]`): reads 29 forward bytes + 1 6-bit tail,
writing the full 32-byte `proofDigest238` to `[dst, dst + 32)` (≤ 192 steps). -/
theorem step_chk_read29_tail (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (hplen : proofLen ≤ proofCap)
    (s : MachineState) (retIdx pLo tCnt dst : Nat)
    (hpc : s.pc = pcWord 271) (hret : s.getReg .x1 = pcWord retIdx) (hret_lt : retIdx < 295)
    (hcur : ProofCursor s0 proofLen pLo tCnt s)
    (hhigh : HighMemPreserved s0 s)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hdst_hi : dst + 32 ≤ 4294971392) :
    PhaseOutcome oracle s 192 0 (proofLen < pLo + 29 + tailBytes (tCnt + 1))
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = pcWord retIdx ∧
        ProofCursor s0 proofLen (pLo + 29) (tCnt + 1) s' ∧
        (∀ r : Reg, r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s'.getReg r = s.getReg r) ∧
        readBuffer s' dst 32 = proofDigest238 s0 proofLen (10603204576 + pLo) tCnt ∧
        MemEqOutside s s' dst (dst + 32)) := by
  have hplen_bd : proofLen ≤ 8239714016 := hplen
  have hle_cur : pLo + tailBytes tCnt ≤ proofLen := hcur.le
  -- pc[271]: ADDI x6, x25, 29; pc[272]: BLTU x31, x6, pc[261]
  have hst0 := step_ordinary oracle s 271 (.ADDI .x6 .x25 29#12) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.ADDI .x6 .x25 29#12)
  have hpc1 : s1.pc = pcWord 272 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = BitVec.ofNat 64 (10603204576 + pLo + 29) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hcur.x25, se12_29_ofNat, bv64_add]
  have hreg1 : ∀ r, r ≠ .x6 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hst1 := step_ordinary oracle s1 272 (.BLTU .x31 .x6 8148#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.BLTU .x31 .x6 8148#13)
  have hult1 : BitVec.ult (s1.getReg .x31) (s1.getReg .x6) = decide (proofLen < pLo + 29 + tailBytes tCnt) := by
    rw [hreg1 .x31 (by decide), hcur.x31, hx6_1, bv64_ult_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hshort1 : proofLen < pLo + 29 + tailBytes tCnt
  · have hpc2 : s2.pc = pcWord 261 := by
      simp only [s2, execInstrBr, hult1, hshort1, decide_true, ite_true, MachineState.setPC, hpc1]
      exact pc_272_reject
    have htb_mono := tailBytes_mono (show tCnt ≤ tCnt + 1 by omega)
    exact .rejected 5 0 [] (by omega) (by decide) (by decide)
      (by simpa using (hst0.trans hst1).halt (halt_reject oracle s2 hpc2))
  · have hge29 : pLo + 29 + tailBytes tCnt ≤ proofLen := by omega
    have hpc2 : s2.pc = pcWord 273 := by
      simp only [s2, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false,
        MachineState.setPC, hpc1, pcWord_add_four]
    have hmem2 : s2.mem = s.mem := by
      have : s2.mem = s1.mem := by
        simp only [s2, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false, mem_setPC]
      exact this.trans (by simp [s1, execInstrBr, mem_setPC, mem_setReg])
    have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r hr => by
      have : s2.getReg r = s1.getReg r := by
        simp only [s2, execInstrBr, hult1, hshort1, decide_false, Bool.false_eq_true, ite_false,
          MachineState.getReg_setPC]
      exact this.trans (hreg1 r hr)
    -- pc[273]: ADDI x7, x0, 29
    have hst2 := step_ordinary oracle s2 273 (.ADDI .x7 .x0 29#12) (by decide) hpc2 rfl (by intro h; cases h) rfl
    let s3 := execInstrBr s2 (.ADDI .x7 .x0 29#12)
    have hpc3 : s3.pc = pcWord 274 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hx7_3 : s3.getReg .x7 = BitVec.ofNat 64 29 := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC, getReg_x0]
      rw [MachineState.getReg_setReg_eq (by decide), se12_29_ofNat, BitVec.zero_add]
    have hreg3 : ∀ r, r ≠ .x6 → r ≠ .x7 → s3.getReg r = s.getReg r := fun r h6 h7 => by
      simp only [s3, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm, hreg2 r h6]
    -- pc[274..279]: copy 29 forward bytes
    obtain ⟨s4, hs4, hpc4, hx25_4, hx12_4, _, hreg4, hcopy4, hout4⟩ :=
      step_byte_copy_loop oracle 274 .x7 (by decide) (by decide) (by decide) (by decide) (by decide)
        rfl rfl rfl rfl rfl rfl 29 (by omega) (by omega) s3 (10603204576 + pLo) dst hpc3
        ((hreg3 .x25 (by decide) (by decide)).trans hcur.x25)
        ((hreg3 .x12 (by decide) (by decide)).trans hdst) hx7_3
        (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
    have hout_s4 : MemEqOutside s s4 dst (dst + 29) :=
      (MemEqOutside.of_mem_eq hmem3 dst (dst + 29)).trans hout4
    have hhigh4 : HighMemPreserved s0 s4 := hhigh.trans (hout_s4.mono (by omega) (by omega))
    have hlo4 : ∀ j < 29, s4.getByte (BitVec.ofNat 64 (dst + j)) = s0.getByte (BitVec.ofNat 64 (10603204576 + pLo + j)) := by
      intro j hj
      rw [hcopy4 j hj]
      have h30 : HighMemPreserved s0 s3 := hhigh.trans (MemEqOutside.of_mem_eq hmem3 0 4294971392)
      exact h30 (10603204576 + pLo + j) (by omega) (by omega)
    have hreg4_s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → s4.getReg r = s.getReg r :=
      fun r h6 h7 h12 h25 => (hreg4 r h6 h12 h25 h7).trans (hreg3 r h6 h7)
    -- pc[280]: ADDI x7, x0, 6; pc[281]: BGEU x4, x7, pc[288]
    have hst4 := step_ordinary oracle s4 280 (.ADDI .x7 .x0 6#12) (by decide) hpc4 rfl (by intro h; cases h) rfl
    let s5 := execInstrBr s4 (.ADDI .x7 .x0 6#12)
    have hpc5 : s5.pc = pcWord 281 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
    have hx7_5 : s5.getReg .x7 = BitVec.ofNat 64 6 := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_x0]
      rw [MachineState.getReg_setReg_eq (by decide), se12_6]; decide
    have hreg5 : ∀ r, r ≠ .x7 → s5.getReg r = s4.getReg r := fun r hr => by
      simp only [s5, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
    have hmem5 : s5.mem = s4.mem := by simp [s5, execInstrBr, mem_setPC, mem_setReg]
    have hst5 := step_ordinary oracle s5 281 (.BGEU .x4 .x7 28#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
    let s6 := execInstrBr s5 (.BGEU .x4 .x7 28#13)
    have htc_lt8 := tailCnt_lt8 tCnt
    have hult5 : BitVec.ult (s5.getReg .x4) (s5.getReg .x7) = decide (tailCnt tCnt < 6) := by
      rw [hreg5 .x4 (by decide), hreg4_s .x4 (by decide) (by decide) (by decide) (by decide),
        hcur.x4, hx7_5, bv64_ult_eq _ _ (by omega) (by omega)]
    have hpre5 : StepsTo oracle s s6 179 0 [] := by
      have h := (((hst0.trans hst1).trans hst2).trans hs4).trans (hst4.trans hst5)
      exact h.eq_of rfl (by decide) (by decide) (by simp)
    by_cases hlt6 : tailCnt tCnt < 6
    · -- Need to load 1 backward byte: pc[282..287]
      obtain ⟨htb_s, htc_s⟩ := tailBytes_succ_lt6 tCnt hlt6
      have hpc6 : s6.pc = pcWord 282 := by
        simp only [s6, execInstrBr, hult5, hlt6, decide_true, not_true_eq_false, ite_false,
          MachineState.setPC, hpc5, pcWord_add_four]
      have hmem6 : s6.mem = s4.mem := by
        simpa [s6, execInstrBr, hult5, hlt6, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x7 → s6.getReg r = s4.getReg r := fun r hr => by
        simpa [s6, execInstrBr, hult5, hlt6, MachineState.getReg_setPC] using hreg5 r hr
      -- pc[282]: BGEU x25, x31, pc[261]
      have hst6 := step_ordinary oracle s6 282 (.BGEU .x25 .x31 8108#13) (by decide) hpc6 rfl (by intro h; cases h) rfl
      let s7 := execInstrBr s6 (.BGEU .x25 .x31 8108#13)
      have hx25_6 : s6.getReg .x25 = BitVec.ofNat 64 (10603204576 + pLo + 29) := by
        rw [hreg6 .x25 (by decide), hx25_4]
      have hx31_6 : s6.getReg .x31 = BitVec.ofNat 64 (10603204576 + (proofLen - tailBytes tCnt)) := by
        rw [hreg6 .x31 (by decide), hreg4_s .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31]
      have hult6 : BitVec.ult (s6.getReg .x25) (s6.getReg .x31) = decide (pLo + 29 + tailBytes (tCnt + 1) ≤ proofLen) := by
        rw [hx25_6, hx31_6, bv64_ult_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      by_cases hok : pLo + 29 + tailBytes (tCnt + 1) ≤ proofLen
      · have hpc7 : s7.pc = pcWord 283 := by
          simp only [s7, execInstrBr, hult6, hok, decide_true, not_true_eq_false, ite_false,
            MachineState.setPC, hpc6, pcWord_add_four]
        have hmem7 : s7.mem = s4.mem := by
          simpa [s7, execInstrBr, hult6, hok, MachineState.setPC] using hmem6
        have hreg7 : ∀ r, r ≠ .x7 → s7.getReg r = s4.getReg r := fun r hr => by
          simpa [s7, execInstrBr, hult6, hok, MachineState.getReg_setPC] using hreg6 r hr
        obtain ⟨s12, hs12, hpc12, hx31_12, hx3_12, hx4_12, hreg12, hmem12_7⟩ :=
          step_chk_load_backbyte oracle s0 proofLen hplen s7 tCnt hlt6 (by omega) hpc7
            ((hreg7 .x31 (by decide)).trans ((hreg4_s .x31 (by decide) (by decide) (by decide) (by decide)).trans hcur.x31))
            ((hreg7 .x3 (by decide)).trans ((hreg4_s .x3 (by decide) (by decide) (by decide) (by decide)).trans hcur.x3))
            ((hreg7 .x4 (by decide)).trans ((hreg4_s .x4 (by decide) (by decide) (by decide) (by decide)).trans hcur.x4))
            (hhigh4.trans (MemEqOutside.of_mem_eq hmem7 0 4294971392))
        have hmem12 : s12.mem = s4.mem := hmem12_7.trans hmem7
        obtain ⟨sFin, hsFin, hpcFin, hcurFin, hregFin, hdigFin, houtFin⟩ :=
          step_chk_have6 oracle s0 proofLen s12 retIdx pLo tCnt dst hpc12
            ((hreg12 .x1 (by decide) (by decide) (by decide) (by decide)).trans
              ((hreg7 .x1 (by decide)).trans ((hreg4_s .x1 (by decide) (by decide) (by decide) (by decide)).trans hret)))
            hret_lt hok
            (by rw [hreg12 .x25 (by decide) (by decide) (by decide) (by decide), hreg7 .x25 (by decide), hx25_4, Nat.add_assoc])
            hx31_12 hx3_12 hx4_12
            ((hreg12 .x12 (by decide) (by decide) (by decide) (by decide)).trans ((hreg7 .x12 (by decide)).trans hx12_4))
            hdst_hi (fun j hj => by
              have : s12.getByte (BitVec.ofNat 64 (dst + j)) = s4.getByte (BitVec.ofNat 64 (dst + j)) := by
                simp [MachineState.getByte, MachineState.getMem, hmem12]
              exact this.trans (hlo4 j hj))
        refine .continued sFin 192 0 [] (by decide) (by decide)
          (((hpre5.trans hst6).trans (hs12.trans hsFin)).eq_of rfl (by decide) (by decide) (by simp))
          ⟨rfl, rfl, hpcFin, hcurFin, ?_, hdigFin, ?_⟩
        · intro r h3 h4 h6 h7 h12 h25 h31
          exact (hregFin r h3 h4 h6).trans ((hreg12 r h3 h4 h6 h31).trans ((hreg7 r h7).trans (hreg4_s r h6 h7 h12 h25)))
        · exact (hout_s4.mono (by omega) (by omega)).trans
            ((MemEqOutside.of_mem_eq hmem12 dst (dst + 32)).trans (houtFin.mono (by omega) (by omega)))
      · -- Rejected at pc[282]: proofLen < pLo + 29 + tailBytes (tCnt + 1)
        have hpc7 : s7.pc = pcWord 261 := by
          simp only [s7, execInstrBr, hult6, hok, decide_false, Bool.false_eq_true, not_false_eq_true, ite_true,
            MachineState.setPC, hpc6]
          exact pc_282_reject
        exact .rejected 183 0 [] (by omega) (by decide) (by decide)
          (by simpa using (hpre5.trans hst6).halt (halt_reject oracle s7 hpc7))
    · -- Already have ≥ 6 bits: jump straight to pc[288]
      have hge6 : 6 ≤ tailCnt tCnt := by omega
      obtain ⟨htb_s, htc_s⟩ := tailBytes_succ_ge6 tCnt hge6
      have hpc6 : s6.pc = pcWord 288 := by
        simp only [s6, execInstrBr, hult5, hlt6, decide_false, Bool.false_eq_true, not_false_eq_true, ite_true,
          MachineState.setPC, hpc5]
        exact pc_281_have6
      have hmem6 : s6.mem = s4.mem := by
        simpa [s6, execInstrBr, hult5, hlt6, MachineState.setPC] using hmem5
      have hreg6 : ∀ r, r ≠ .x7 → s6.getReg r = s4.getReg r := fun r hr => by
        simpa [s6, execInstrBr, hult5, hlt6, MachineState.getReg_setPC] using hreg5 r hr
      obtain ⟨sFin, hsFin, hpcFin, hcurFin, hregFin, hdigFin, houtFin⟩ :=
        step_chk_have6 oracle s0 proofLen s6 retIdx pLo tCnt dst hpc6
          ((hreg6 .x1 (by decide)).trans ((hreg4_s .x1 (by decide) (by decide) (by decide) (by decide)).trans hret))
          hret_lt (by rw [htb_s]; exact hge29)
          (by rw [hreg6 .x25 (by decide), hx25_4, Nat.add_assoc])
          (by rw [hreg6 .x31 (by decide), hreg4_s .x31 (by decide) (by decide) (by decide) (by decide), hcur.x31, htb_s])
          (by rw [hreg6 .x3 (by decide), hreg4_s .x3 (by decide) (by decide) (by decide) (by decide), hcur.x3, htb_s]; rfl)
          (by rw [hreg6 .x4 (by decide), hreg4_s .x4 (by decide) (by decide) (by decide) (by decide), hcur.x4]; congr 1; omega)
          ((hreg6 .x12 (by decide)).trans hx12_4) hdst_hi
          (fun j hj => by
            have : s6.getByte (BitVec.ofNat 64 (dst + j)) = s4.getByte (BitVec.ofNat 64 (dst + j)) := by
              simp [MachineState.getByte, MachineState.getMem, hmem6]
            exact this.trans (hlo4 j hj))
      refine .continued sFin 186 0 [] (by decide) (by decide)
        ((hpre5.trans hsFin).eq_of rfl (by decide) (by decide) (by simp))
        ⟨rfl, rfl, hpcFin, hcurFin, ?_, hdigFin, ?_⟩
      · intro r h3 h4 h6 h7 h12 h25 _
        exact (hregFin r h3 h4 h6).trans ((hreg6 r h7).trans (hreg4_s r h6 h7 h12 h25))
      · exact (hout_s4.mono (by omega) (by omega)).trans
          ((MemEqOutside.of_mem_eq hmem6 dst (dst + 32)).trans (houtFin.mono (by omega) (by omega)))

/-- Helper: `JAL .x1` to `read29_t6` (`pc[271]`), ≤ 193 steps. -/
theorem step_call_read29_tail (oracle : Oracle) (s0 : MachineState) (proofLen : Nat)
    (hplen : proofLen ≤ proofCap)
    (idx : Nat) (s : MachineState) (pLo tCnt dst : Nat)
    (hhi : idx + 1 ≤ 271)
    (hjal : checkInstr idx = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (271 - idx)))))
    (hpc : s.pc = pcWord idx)
    (hcur : ProofCursor s0 proofLen pLo tCnt s)
    (hhigh : HighMemPreserved s0 s)
    (hdst : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hdst_hi : dst + 32 ≤ 4294971392) :
    PhaseOutcome oracle s 193 0 (proofLen < pLo + 29 + tailBytes (tCnt + 1))
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = pcWord (idx + 1) ∧
        ProofCursor s0 proofLen (pLo + 29) (tCnt + 1) s' ∧
        (∀ r : Reg, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
          s'.getReg r = s.getReg r) ∧
        readBuffer s' dst 32 = proofDigest238 s0 proofLen (10603204576 + pLo) tCnt ∧
        MemEqOutside s s' dst (dst + 32)) := by
  let off := BitVec.ofNat 21 (4 * (271 - idx))
  have hst0 := step_ordinary oracle s idx (.JAL .x1 off) (by omega) hpc hjal (by intro h; cases h) rfl
  let s1 := execInstrBr s (.JAL .x1 off)
  have hpc1 : s1.pc = pcWord 271 := by
    simp only [s1, execInstrBr, MachineState.setPC, hpc]
    have hse21 : signExtend21 off = BitVec.ofNat 64 (4 * (271 - idx)) :=
      signExtend21_ofNat_lt _ (by omega)
    rw [hse21, pcWord, bv64_add]; congr 1; omega
  have hret1 : s1.getReg .x1 = pcWord (idx + 1) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, hpc, pcWord_add_four]
    exact MachineState.getReg_setReg_eq (by decide)
  have hreg1 : ∀ r, r ≠ .x1 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  have hcur1 : ProofCursor s0 proofLen pLo tCnt s1 :=
    hcur.of_agree (fun r hr => hreg1 r (isCursorReg_ne_of_false hr rfl))
  have hsub := step_chk_read29_tail oracle s0 proofLen hplen s1 (idx + 1) pLo tCnt dst hpc1 hret1 (by omega)
    hcur1 (hhigh.trans (MemEqOutside.of_mem_eq hmem1 0 4294971392))
    ((hreg1 .x12 (by decide)).trans hdst) hdst_hi
  refine (hst0.prepend_pure hsub).weaken (by omega) (by omega) id ?_
  rintro s' q tr ⟨hq, htr, hpc', hcur', hreg', hdig', hout'⟩
  exact ⟨hq, htr, hpc', hcur',
    fun r h1 h3 h4 h6 h7 h12 h25 h31 => (hreg' r h3 h4 h6 h7 h12 h25 h31).trans (hreg1 r h1),
    hdig', (MemEqOutside.of_mem_eq hmem1 dst (dst + 32)).trans hout'⟩

/-- Generic 3-instruction 268-bit masking (`LD x6, 24(rDst); AND x6, x6, x9; SD rDst, x6, 24`). -/
theorem step_mask238 (oracle : Oracle) (base : Nat) (rDst : Reg) (s : MachineState) (addr : Nat)
    (hrDst : rDst ≠ .x6) (hhi : base + 3 ≤ 295)
    (hc0 : checkInstr base = .base (.LD .x6 rDst 24#12))
    (hc1 : checkInstr (base + 1) = .base (.AND .x6 .x6 .x9))
    (hc2 : checkInstr (base + 2) = .base (.SD rDst .x6 24#12))
    (hpc : s.pc = pcWord base)
    (hdst : s.getReg rDst = BitVec.ofNat 64 addr)
    (hx9 : s.getReg .x9 = mask238Word)
    (hal : addr % 8 = 0) (hbd : addr + 32 ≤ MEMORY_BYTES) :
    ∃ s', StepsTo oracle s s' 3 0 [] ∧
      s'.pc = pcWord (base + 3) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      readBuffer s' addr 32 = mask238 (readBuffer s addr 32) ∧
      MemEqOutside s s' addr (addr + 32) := by
  have hmem_lt : MEMORY_BYTES ≤ 2 ^ 64 := by unfold MEMORY_BYTES; omega
  have ha0 : s.getReg rDst + signExtend12 24#12 = BitVec.ofNat 64 (addr + 24) := by
    rw [hdst, se12_24]; exact bv64_add addr 24
  have hv0 : memoryArgumentsValid s (.LD .x6 rDst 24#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha0]
    exact accessValid_ofNat (addr + 24) 8 (by omega) (by omega)
  have hst0 := step_ordinary oracle s base (.LD .x6 rDst 24#12) (by omega) hpc hc0 (by intro h; cases h)
    (by simp [ordinaryStep, hv0])
  let s1 := execInstrBr s (.LD .x6 rDst 24#12)
  have hpc1 : s1.pc = pcWord (base + 1) := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hx6_1 : s1.getReg .x6 = s.getMem (BitVec.ofNat 64 (addr + 24)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha0]
    exact MachineState.getReg_setReg_eq (by decide)
  have hreg1 : ∀ r, r ≠ .x6 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ hr.symm
  have hst1 := step_ordinary oracle s1 (base + 1) (.AND .x6 .x6 .x9) (by omega) hpc1 hc1 (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.AND .x6 .x6 .x9)
  have hpc2 : s2.pc = pcWord (base + 2) := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = s.getMem (BitVec.ofNat 64 (addr + 24)) &&& mask238Word := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx6_1, hreg1 .x9 (by decide), hx9]
  have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r hr => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ hr.symm, hreg1 r hr]
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have ha2 : s2.getReg rDst + signExtend12 24#12 = BitVec.ofNat 64 (addr + 24) := by
    rw [hreg2 rDst hrDst, hdst, se12_24]; exact bv64_add addr 24
  have hv2 : memoryArgumentsValid s2 (.SD rDst .x6 24#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha2]
    exact accessValid_ofNat (addr + 24) 8 (by omega) (by omega)
  have hst2 := step_ordinary oracle s2 (base + 2) (.SD rDst .x6 24#12) (by omega) hpc2 hc2 (by intro h; cases h)
    (by simp [ordinaryStep, hv2])
  let s3 := execInstrBr s2 (.SD rDst .x6 24#12)
  have hpc3 : s3.pc = pcWord (base + 3) := by
    simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hs3_byte : ∀ q : Word, s3.getByte q =
      (s.setMem (BitVec.ofNat 64 (addr + 24))
        (s.getMem (BitVec.ofNat 64 (addr + 24)) &&& mask238Word)).getByte q := by
    intro q
    simp only [s3, execInstrBr, ha2, hx6_2, MachineState.getByte, MachineState.getMem,
      MachineState.setMem, mem_setPC, hmem2]
  refine ⟨s3, ((hst0.trans hst1).trans hst2).eq_of rfl (by decide) (by decide) (by simp), hpc3, ?_, ?_, ?_⟩
  · intro r hr
    have : s3.getReg r = s2.getReg r := by
      simp [s3, execInstrBr, MachineState.setMem, MachineState.setPC, MachineState.getReg]
    exact this.trans (hreg2 r hr)
  · have hr : readBuffer s3 addr 32 =
        readBuffer (s.setMem (BitVec.ofNat 64 (addr + 24))
          (s.getMem (BitVec.ofNat 64 (addr + 24)) &&& mask238Word)) addr 32 :=
      readBuffer_congr2 _ _ _ _ _ (fun j _ => hs3_byte _)
    rw [hr, sd_and_mask238 s addr hal (by omega)]
  · intro a ha hout
    rw [hs3_byte]
    exact setMem_getByte_ofNat s (addr + 24) a _ (by omega) (by omega) ha (by omega)

/-- Generic `m`-dword copy (`LD x6, (srcOff + 8j)(rSrc); SD x6, (dstOff + 8j)(rDst)`). -/
theorem step_copy_dwords (oracle : Oracle) (base m : Nat) (rSrc rDst : Reg)
    (srcOff dstOff : Nat) (s : MachineState) (srcBase dstBase : Nat)
    (hrSrc : rSrc ≠ .x6) (hrDst : rDst ≠ .x6)
    (hso : srcOff + 8 * m ≤ 256) (hdo : dstOff + 8 * m ≤ 256)
    (hhi : base + 2 * m ≤ 295)
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

/-- Generic 4-dword comparison (`LD x6, (8j)(rA); LD x7, (8j)(rB); BNE x6, x7, pc[261]`). -/
theorem step_compare4 (oracle : Oracle) (base : Nat) (rA rB : Reg)
    (s : MachineState) (addrA addrB : Nat)
    (hrA6 : rA ≠ .x6) (hrA7 : rA ≠ .x7) (hrB6 : rB ≠ .x6) (hrB7 : rB ≠ .x7)
    (hhi : base + 12 ≤ 261)
    (hcode : ∀ j < 4,
      checkInstr (base + 3 * j) = .base (.LD .x6 rA (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 3 * j + 1) = .base (.LD .x7 rB (BitVec.ofNat 12 (8 * j))) ∧
      checkInstr (base + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (261 - (base + 3 * j + 2))))))
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
          let off := BitVec.ofNat 13 (4 * (261 - (base + 3 * k + 2)))
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
            have hpc3 : (execInstrBr sk2 (.BNE .x6 .x7 off)).pc = pcWord 261 := by
              simp only [execInstrBr, hne_b, ite_true, MachineState.setPC, hpc2]
              have hse13 : signExtend13 off = BitVec.ofNat 64 (4 * (261 - (base + 3 * k + 2))) :=
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

/-- Zero `S[64..96)` (`pc[132..135]`, 4 steps). -/
theorem step_zero_gap (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = pcWord 132) (hx21 : s.getReg .x21 = 256#64) :
    ∃ s', StepsTo oracle s s' 4 0 [] ∧
      s'.pc = pcWord 136 ∧
      (∀ r : Reg, s'.getReg r = s.getReg r) ∧
      readBuffer s' 320 32 = 0 ∧
      MemEqOutside s s' 320 352 := by
  have hloop : ∀ m ≤ 4,
      ∃ s', StepsTo oracle s s' m 0 [] ∧
        s'.pc = pcWord (132 + m) ∧
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
      have hcode : checkInstr (132 + k) = .base (.SD .x21 .x0 (BitVec.ofNat 12 (64 + 8 * k))) := by
        have hk : k < 4 := by omega
        interval_cases k <;> rfl
      have hse : signExtend12 (BitVec.ofNat 12 (64 + 8 * k)) = BitVec.ofNat 64 (64 + 8 * k) :=
        signExtend12_ofNat_lt256 ⟨64 + 8 * k, by omega⟩
      have ha : sk.getReg .x21 + signExtend12 (BitVec.ofNat 12 (64 + 8 * k)) = BitVec.ofNat 64 (320 + 8 * k) := by
        rw [hreg_k .x21, hx21, hse, bv64_add]; congr 1; omega
      have hval : memoryArgumentsValid sk (.SD .x21 .x0 (BitVec.ofNat 12 (64 + 8 * k))) = true := by
        simp only [memoryArgumentsValid, memAccess, ha]
        exact accessValid_ofNat (320 + 8 * k) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst := step_ordinary oracle sk (132 + k) _ (by omega) hpc_k hcode (by intro h; cases h)
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
        congr 1
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

/-! ### 4. Straight-Line Pure Instruction List Runner -/

/-- Execute a straight-line list of pure (non-memory, non-branch) instructions. -/
def runInstrs (s : MachineState) (l : List Instr) : MachineState :=
  l.foldl execInstrBr s

theorem step_pure_list (oracle : Oracle) (base : Nat) (l : List Instr) (s : MachineState)
    (hhi : base + l.length ≤ 295)
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
