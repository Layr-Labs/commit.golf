import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonBinding

/-! Deterministic symbolic execution infrastructure for the 269-word pure 3-ary `check` image:
- Pure deterministic evaluator `detExec` matching `execute ... false` under `Oracle.run`,
  `Oracle.eval`, and `fixedOracleRun (traceCompressionReplies _)`.
- Compositional `StepsTo`, `HaltsWith`, and `PhaseOutcome` combinators with byte-level frames.
- Reusable single-instruction steppers, compression ECALL stepper, halt blocks, aligned
  24/32/64-byte copy blocks, 32-byte compare-or-reject block, and `CheckFixedRegs`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Pure Deterministic Evaluator and Bridges -/

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

def checkEval (oracle : Oracle) {α : Type} (computation : OracleComp World α) : α × Nat :=
  oracle.eval (simulateQ checkHandler computation)

theorem checkEval_pure (oracle : Oracle) {α : Type} (v : α) :
    checkEval oracle (pure v) = (v, 0) := by
  simp [checkEval, Oracle.eval]; rfl

theorem checkEval_bind (oracle : Oracle) {α β : Type} (c : OracleComp World α)
    (k : α → OracleComp World β) :
    checkEval oracle (c >>= k) =
      let (v, n1) := checkEval oracle c
      let (r, n2) := checkEval oracle (k v)
      (r, n1 + n2) := by
  simp only [checkEval, Oracle.eval, simulateQ_bind, WriterT.run_bind]; rfl

theorem checkEval_public_bind (oracle : Oracle) {α : Type} (q : PublicSpec.Domain)
    (k : PublicSpec.Range q → OracleComp World α) :
    checkEval oracle ((World.query (.inr q) : OracleComp World _) >>= k) =
      let (r, n) := checkEval oracle (k (oracle.answer (m := Id) q))
      (r, 1 + n) := by
  rw [checkEval_bind]
  have hq : checkEval oracle (World.query (.inr q) : OracleComp World _) =
      (oracle.answer (m := Id) q, 1) := by
    simp [checkEval, Oracle.eval, checkHandler, QueryImpl.withAddCost, QueryImpl.withCost]; rfl
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
  simp only [Submission.scheme, Oracle.eval, simulateQ_map, WriterT.run_map]; rfl

private theorem traceReplies_bind_pure {α β : Type} (c : OracleComp World α) (f : α → β) :
    traceCompressionReplies (c >>= fun x => pure (f x)) =
      (fun p => (f p.1, p.2)) <$> traceCompressionReplies c := by
  induction c using OracleComp.inductionOn with
  | pure v => simp only [pure_bind, map_pure]; rfl
  | query_bind q next ih =>
    rw [bind_assoc]
    rcases q with coins | (input | permQuery)
    · change ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
        traceCompressionReplies (next answer >>= fun x => pure (f x))) =
        (fun p => (f p.1, p.2)) <$>
          ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer))
      rw [map_bind]; apply bind_congr; intro answer; exact ih answer
    · change ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
        traceCompressionReplies (next answer >>= fun x => pure (f x)) >>= fun p =>
          pure (p.1, (input, answer) :: p.2)) =
        (fun p => (f p.1, p.2)) <$>
          ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer) >>= fun p =>
              pure (p.1, (input, answer) :: p.2))
      rw [map_bind]; apply bind_congr; intro answer
      rw [ih answer, bind_map_left, map_bind]
      apply bind_congr; rintro ⟨v, t⟩; simp
    · change ((liftM (World.query (.inr (.inr permQuery))) : OracleComp World _) >>= fun answer =>
        traceCompressionReplies (next answer >>= fun x => pure (f x))) =
        (fun p => (f p.1, p.2)) <$>
          ((liftM (World.query (.inr (.inr permQuery))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer))
      rw [map_bind]; apply bind_congr; intro answer; exact ih answer

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
              rw [ih, map_pure, pure_bind, fixed_oracle_run_pure]; rfl
            | inr pq =>
              change fixedOracleRun oracle
                ((liftM (World.query (.inr (.inr pq))) : OracleComp World _) >>= fun answer =>
                  traceCompressionReplies
                    ((execute image steps (writeOracleAnswer state (state.getReg .x12) (.inr pq) answer) false) >>=
                      fun result => pure (result.charge PERMUTATION_CYCLES 1))) = _
              rw [fixed_oracle_run_public, traceReplies_bind_pure, fixed_oracle_run_map, ih, map_pure]; rfl
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

/-! ### 2. `StepsTo`, `HaltsWith`, `PhaseOutcome`, and `InTrace` -/

def StepsTo (oracle : Oracle) (s1 s2 : MachineState) (steps calls : Nat)
    (tr : CompressionReplies) : Prop :=
  ∀ extra,
    let r1 := detExec oracle (submission.image .check) (steps + extra) s1
    let r2 := detExec oracle (submission.image .check) extra s2
    r1.1.exit = r2.1.exit ∧
    r1.1.state = r2.1.state ∧
    r1.1.oracleCalls = calls + r2.1.oracleCalls ∧
    r1.2 = tr ++ r2.2

def HaltsWith (oracle : Oracle) (s : MachineState) (steps calls : Nat)
    (exit : Exit) (tr : CompressionReplies) : Prop :=
  exit ≠ .unfinished ∧
  ∀ extra,
    let r := detExec oracle (submission.image .check) (steps + extra) s
    r.1.exit = exit ∧ r.1.oracleCalls = calls ∧ r.2 = tr

inductive PhaseOutcome (oracle : Oracle) (s : MachineState) (maxSteps maxCalls : Nat)
    (CanReject : Prop) (P : MachineState → Nat → CompressionReplies → Prop) : Prop where
  | rejected (k q : Nat) (tr : CompressionReplies) :
      CanReject → k ≤ maxSteps → q ≤ maxCalls → HaltsWith oracle s k q .failure tr →
      PhaseOutcome oracle s maxSteps maxCalls CanReject P
  | continued (s' : MachineState) (k q : Nat) (tr : CompressionReplies) :
      k ≤ maxSteps → q ≤ maxCalls → StepsTo oracle s s' k q tr → P s' q tr →
      PhaseOutcome oracle s maxSteps maxCalls CanReject P

def InTrace (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (tr : CompressionReplies) (x : BitVec 768) : Prop :=
  (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ tr

theorem InTrace.append_left {h768 oracle t1 t2 x}
    (h : InTrace h768 oracle t1 x) : InTrace h768 oracle (t1 ++ t2) x :=
  List.mem_append_left t2 h

theorem InTrace.append_right {h768 oracle t1 t2 x}
    (h : InTrace h768 oracle t2 x) : InTrace h768 oracle (t1 ++ t2) x :=
  List.mem_append_right t1 h

theorem StepsTo.refl (oracle : Oracle) (s : MachineState) : StepsTo oracle s s 0 0 [] := by
  intro extra; simp

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

theorem StepsTo.halt {oracle : Oracle} {s1 s2 : MachineState}
    {k1 k2 q1 q2 : Nat} {ex : Exit} {t1 t2 : CompressionReplies}
    (h1 : StepsTo oracle s1 s2 k1 q1 t1) (h2 : HaltsWith oracle s2 k2 q2 ex t2) :
    HaltsWith oracle s1 (k1 + k2) (q1 + q2) ex (t1 ++ t2) := by
  refine ⟨h2.1, fun extra => ?_⟩
  have a := h1 (k2 + extra)
  have b := h2.2 extra
  rw [show k1 + k2 + extra = k1 + (k2 + extra) by omega]
  exact ⟨a.1.trans b.1, by rw [a.2.2.1, b.2.1], by rw [a.2.2.2, b.2.2]⟩

theorem HaltsWith.eval_of_le {oracle : Oracle} {s : MachineState}
    {k N q : Nat} {ex : Exit} {tr : CompressionReplies}
    (h : HaltsWith oracle s k q ex tr) (hle : k ≤ N) :
    let r := detExec oracle (submission.image .check) N s
    r.1.exit = ex ∧ r.1.oracleCalls = q ∧ r.2 = tr := by
  have a := h.2 (N - k)
  simpa only [show k + (N - k) = N by omega] using a

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

/-! ### 3. BitVec, PC, Register, and Byte-Frame Helpers -/

def kPcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

theorem k_getReg_x0 (s : MachineState) : s.getReg .x0 = 0#64 := rfl
theorem k_setReg_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl
theorem k_getReg_setPC (s : MachineState) (v : Word) (r : Reg) : (s.setPC v).getReg r = s.getReg r := rfl
theorem k_getReg_setMem (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
  cases r <;> rfl
theorem k_getReg_setByte (s : MachineState) (a : Word) (b : Byte) (r : Reg) : (s.setByte a b).getReg r = s.getReg r := by
  cases r <;> rfl
theorem k_getByte_setReg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setReg]
theorem k_getByte_setPC (s : MachineState) (v a : Word) : (s.setPC v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setPC]
theorem k_mem_setPC (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl
theorem k_mem_setReg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem k_card_le (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions
  rw [Fintype.card_fin] at h
  exact h

theorem kPcAt_add4 (idx : Nat) : kPcAt idx + 4 = kPcAt (idx + 1) := by
  unfold kPcAt
  change BitVec.ofNat 64 (0x1000 + 4 * idx) + BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_add]; congr 1

theorem k_toNat_ofNat (a : Nat) (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem k_bv_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem k_bv_sub (a b : Nat) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 b) h.symm
  simpa only [BitVec.add_sub_cancel] using hc

theorem k_bv_shl (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod (a % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod]

theorem k_bv_and1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& signExtend12 (1#12) = BitVec.ofNat 64 (a % 2) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Nat) < 2 ^ 64 := by omega
  have hm : a % 2 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hm]
  change a &&& (2 ^ 1 - 1) = a % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod a 1

theorem k_bv_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  have hse : signExtend12 (4095#12) = (-1#64 : Word) := by decide
  rw [hse, ← k_bv_add n 1]
  change BitVec.ofNat 64 n + 1#64 + (-1#64 : Word) = BitVec.ofNat 64 n
  rw [BitVec.add_assoc, show (1#64 : Word) + (-1#64 : Word) = 0#64 by decide, BitVec.add_zero]

theorem k_bv_eq_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h; have hn := congrArg BitVec.toNat h
    rwa [k_toNat_ofNat a ha, k_toNat_ofNat b hb] at hn
  · intro h; rw [h]

theorem k_bv_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h => hne ((k_bv_eq_iff a b ha hb).mp h)

theorem k_se12_lt2048 (n : Nat) (hn : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  unfold signExtend12
  apply BitVec.eq_of_toNat_eq
  have h12 : n % 2 ^ 12 = n := Nat.mod_eq_of_lt (by omega)
  have h64 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmsb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, h12]; exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, if_neg (by rw [hmsb]; decide), Nat.add_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, h12, h64, k_toNat_ofNat n (by omega)]

theorem k_rangeValid (addr n : Nat) (hn : addr + n ≤ 68719476736) :
    rangeValid (BitVec.ofNat 64 addr) n = true := by
  unfold rangeValid MEMORY_BYTES
  rw [k_toNat_ofNat addr (by omega)]
  exact decide_eq_true (by omega)

theorem k_accessValid (addr w : Nat) (hn : addr + w ≤ 68719476736) (ha : addr % w = 0) :
    accessValid (BitVec.ofNat 64 addr) w = true := by
  unfold accessValid
  rw [k_rangeValid addr w hn, Bool.true_and, k_toNat_ofNat addr (by omega)]
  exact decide_eq_true ha

theorem k_bool_byte_zext (b : Bool) :
    (if b then (1#8 : Byte) else 0#8).zeroExtend 64 = if b then 1#64 else 0#64 := by
  cases b <;> decide

theorem k_bool_word_or (a b : Bool) :
    (if a then (1#64 : Word) else 0#64) ||| (if b then 1#64 else 0#64) =
      if (a || b) then 1#64 else 0#64 := by
  cases a <;> cases b <;> decide

theorem k_getMem_extractByte (s : MachineState) (addr j : Nat)
    (halign : addr % 8 = 0) (hj : j < 8) :
    (s.getMem (BitVec.ofNat 64 addr)).extractLsb' (8 * j) 8 =
      s.getByte (BitVec.ofNat 64 (addr + j)) := by
  have hal := alignToDword_ofNat_eq addr j hj halign
  have hbo : byteOffset (BitVec.ofNat 64 (addr + j)) = j := by
    unfold byteOffset
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((addr + j) % 2 ^ 64) &&& (2 ^ 3 - 1) = j
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
  simp only [MachineState.getByte, hal, hbo]
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mul_comm 8 j]

theorem k_readBuffer_congr2 (s1 s2 : MachineState) (a1 a2 n : Nat)
    (h : ∀ j < n, s1.getByte (BitVec.ofNat 64 (a1 + j)) = s2.getByte (BitVec.ofNat 64 (a2 + j))) :
    readBuffer s1 a1 n = readBuffer s2 a2 n := by
  unfold readBuffer; congr 1
  apply Finset.sum_congr rfl; intro j hj; rw [h j (Finset.mem_range.mp hj)]

def MemEqOutside (s1 s2 : MachineState) (lo hi : Nat) : Prop :=
  ∀ a : Nat, a < 2 ^ 64 → (a < lo ∨ hi ≤ a) →
    s2.getByte (BitVec.ofNat 64 a) = s1.getByte (BitVec.ofNat 64 a)

abbrev HighMemPreserved (s0 s : MachineState) : Prop :=
  MemEqOutside s0 s 0 4294971392

theorem MemEqOutside.refl (s : MachineState) (lo hi : Nat) : MemEqOutside s s lo hi :=
  fun _ _ _ => rfl

theorem MemEqOutside.of_mem_eq {s1 s2 : MachineState} (h : s2.mem = s1.mem) (lo hi : Nat) :
    MemEqOutside s1 s2 lo hi := by
  intro a _ _; simp only [MachineState.getByte, MachineState.getMem, h]

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
  apply k_readBuffer_congr2; intro j hj; exact h (addr + j) (by omega) (by omega)

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
  rw [set_byte_read, if_neg (k_bv_ne ha hbound (by omega))]

theorem MemEqOutside_writeBits_digest (s : MachineState) (addr : Nat) (d : Digest)
    (hbound : addr + 32 ≤ 2 ^ 64) :
    MemEqOutside s (writeBits s (BitVec.ofNat 64 addr) d) addr (addr + 32) := by
  intro a ha hout
  apply write_bits_byte_outside s (BitVec.ofNat 64 addr) (BitVec.ofNat 64 a) d
  intro i hi heq
  rw [k_bv_add, k_bv_eq_iff a (addr + i) ha (by omega)] at heq
  omega

/-! ### 4. Single-Instruction Step Lemmas (`idx < 269`) and Compression ECALL -/

theorem k_step_ordinary (oracle : Oracle) (s : MachineState) (idx : Nat) (inst : Instr)
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base inst)
    (hne : inst ≠ .ECALL) (s' : MachineState)
    (hstep : ordinaryStep s (.base inst) = some s') :
    StepsTo oracle s s' 1 0 [] := by
  intro extra
  have hf : fetch (submission.image .check) s = some (.base inst) := by
    rw [check_fetch s idx hhi hpc, hi]
  rw [Nat.add_comm 1 extra, detExec_succ_other oracle _ extra s (.base inst) (by intro h; cases h; exact hne rfl) hf, hstep]
  simp [Execution.charge]

theorem k_step_ADDI {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.ADDI rd rs1 imm)) :
    StepsTo oracle s ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_ADD {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.ADD rd rs1 rs2)) :
    StepsTo oracle s ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_SUB {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.SUB rd rs1 rs2)) :
    StepsTo oracle s ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_SLLI {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.SLLI rd rs1 shamt)) :
    StepsTo oracle s ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_ANDI {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.ANDI rd rs1 imm)) :
    StepsTo oracle s ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_OR {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.OR rd rs1 rs2)) :
    StepsTo oracle s ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_DIVU {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.DIVU rd rs1 rs2)) :
    StepsTo oracle s ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
  rw [hpc, kPcAt_add4]

theorem k_step_LD {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.LD rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    StepsTo oracle s ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
          then some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (s.pc + 4))
          else none) = _
  simp only [hvalid, ite_true, hpc, kPcAt_add4]

theorem k_step_SD {oracle : Oracle} {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.SD rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    StepsTo oracle s ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
          then some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4))
          else none) = _
  simp only [hvalid, ite_true, hpc, kPcAt_add4]

theorem k_step_LBU {oracle : Oracle} {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.LBU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    StepsTo oracle s ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
          then some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
          else none) = _
  simp only [hvalid, ite_true, hpc, kPcAt_add4]

theorem k_step_SB {oracle : Oracle} {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.SB rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    StepsTo oracle s ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
          then some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4))
          else none) = _
  simp only [hvalid, ite_true, hpc, kPcAt_add4]

theorem k_step_BEQ_taken {oracle : Oracle} {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.BEQ rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) (htgt : kPcAt idx + signExtend13 off = kPcAt tgt) :
    StepsTo oracle s (s.setPC (kPcAt tgt)) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  have hcond : (s.getReg rs1 == s.getReg rs2) = true := by rw [heq]; simp
  change some (if (s.getReg rs1 == s.getReg rs2) = true
               then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
  simp only [hcond, ite_true, hpc, htgt]

theorem k_step_BEQ_not_taken {oracle : Oracle} {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.BEQ rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    StepsTo oracle s (s.setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  have hcond : (s.getReg rs1 == s.getReg rs2) = false := by simp [hne]
  change some (if (s.getReg rs1 == s.getReg rs2) = true
               then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
  simp only [hcond, Bool.false_eq_true, ite_false, hpc, kPcAt_add4]

theorem k_step_BNE_taken {oracle : Oracle} {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.BNE rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) (htgt : kPcAt idx + signExtend13 off = kPcAt tgt) :
    StepsTo oracle s (s.setPC (kPcAt tgt)) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  have hcond : (s.getReg rs1 != s.getReg rs2) = true := by simp [hne]
  change some (if (s.getReg rs1 != s.getReg rs2) = true
               then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
  simp only [hcond, ite_true, hpc, htgt]

theorem k_step_BNE_not_taken {oracle : Oracle} {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.BNE rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) :
    StepsTo oracle s (s.setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  have hcond : (s.getReg rs1 != s.getReg rs2) = false := by rw [heq]; simp
  change some (if (s.getReg rs1 != s.getReg rs2) = true
               then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
  simp only [hcond, Bool.false_eq_true, ite_false, hpc, kPcAt_add4]

theorem k_step_BLTU_taken {oracle : Oracle} {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.BLTU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat)
    (htgt : kPcAt idx + signExtend13 off = kPcAt tgt) :
    StepsTo oracle s (s.setPC (kPcAt tgt)) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
  change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
               then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
  simp only [hcond, ite_true, hpc, htgt]

theorem k_step_BLTU_not_taken {oracle : Oracle} {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.BLTU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat) :
    StepsTo oracle s (s.setPC (kPcAt (idx + 1))) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = false := by
    simp only [BitVec.ult, decide_eq_false_iff_not]; omega
  change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
               then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
  simp only [hcond, Bool.false_eq_true, ite_false, hpc, kPcAt_add4]

theorem k_step_JAL_x0 {oracle : Oracle} {s : MachineState} {idx tgt : Nat} {off : BitVec 21}
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base (.JAL .x0 off))
    (htgt : kPcAt idx + signExtend21 off = kPcAt tgt) :
    StepsTo oracle s (s.setPC (kPcAt tgt)) 1 0 [] := by
  refine k_step_ordinary oracle s idx _ hhi hpc hi (by intro h; cases h) _ ?_
  change some ((s.setReg .x0 (s.pc + 4)).setPC (s.pc + signExtend21 off)) = _
  rw [k_setReg_x0, hpc, htgt]

private theorem k_readBuffer_toNat_congr (s : MachineState) (base : Nat) {n m : Nat} (h : n = m) :
    (readBuffer s base n).toNat = (readBuffer s base m).toNat := by
  subst h; rfl

private theorem k_ofNat_toNat_cast {n m : Nat} (h : n = m) (v : BitVec n) :
    BitVec.ofNat m v.toNat = v.cast h := by
  subst h; simp

/-- Single compression `ECALL` step recording `(x, c96 x)` and writing `c96 x` to `dst`. -/
theorem k_step_ecall_compress (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (s : MachineState) (idx src dst : Nat)
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base .ECALL)
    (hx5 : s.getReg .x5 = 0#64) (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx11 : s.getReg .x11 = BitVec.ofNat 64 96) (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hx13 : s.getReg .x13 = 0#64)
    (hsAl : src % 8 = 0) (hsBd : src + 96 ≤ 68719476736)
    (hdAl : dst % 8 = 0) (hdBd : dst + 32 ≤ 68719476736) :
    let x96 : BitVec 768 := readBuffer s src 96
    let ans : Digest := oracle.compression (x96.cast h768.symm)
    let s' := writeBits s (BitVec.ofNat 64 dst) ans
    StepsTo oracle s s' 1 1 [(x96.cast h768.symm, ans)] ∧
    s'.pc = kPcAt (idx + 1) ∧
    (∀ r, s'.getReg r = s.getReg r) ∧
    readBuffer s' dst 32 = ans ∧
    MemEqOutside s s' dst (dst + 32) := by
  intro x96 ans s'
  have hin : oracleInput s = some (.inl (x96.cast h768.symm)) := by
    unfold oracleInput
    dsimp only
    have hk0 : (s.getReg .x13).toNat = 0 := by rw [hx13]; rfl
    have h11 : (s.getReg .x11).toNat = 96 := by rw [hx11]; rfl
    have h10 : (s.getReg .x10).toNat = src := by rw [hx10, k_toNat_ofNat src (by omega)]
    have h12 : (s.getReg .x12).toNat = dst := by rw [hx12, k_toNat_ofNat dst (by omega)]
    have hib : (COMPRESSION_INPUT_LENGTH + 7) / 8 = 96 := by rw [h768]
    have hib_full :
        (((if (s.getReg .x13).toNat = 0 then COMPRESSION_INPUT_LENGTH else PERMUTATION_WIDTH) + 7) / 8) = 96 := by
      rw [hk0]; simp only [ite_true]; exact hib
    have hob : (COMPRESSION_OUTPUT_LENGTH + 7) / 8 = 32 := rfl
    have hrv1 : rangeValid (s.getReg .x10) 96 = true := by rw [hx10]; exact k_rangeValid src 96 hsBd
    have hrv2 : rangeValid (s.getReg .x12) 32 = true := by rw [hx12]; exact k_rangeValid dst 32 hdBd
    simp only [hk0, ite_true, h10]
    rw [k_readBuffer_toNat_congr s src hib_full]
    simp only [hib, hob, h11, h12, hsAl, hdAl, hrv1, hrv2, Nat.zero_le, and_self, ite_true]
    exact congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => (some (Sum.inl x) : Option PublicSpec.Domain))
      (k_ofNat_toNat_cast h768.symm x96)
  have hf : fetch (submission.image .check) s = some (.base .ECALL) := by
    rw [check_fetch s idx hhi hpc, hi]
  refine ⟨?_, ?_, fun r => writeBits_register s _ ans r,
    writeBits_readBuffer_digest s dst ans,
    MemEqOutside_writeBits_digest s dst ans (by omega)⟩
  · intro extra
    have hx5_0 : s.getReg .x5 = 0 := hx5
    have hdet := detExec_succ_ecall oracle (submission.image .check) extra s hf
    rw [show 1 + extra = extra + 1 by omega, hdet]
    simp only [hx5_0, ite_true, hin, hx12, Execution.charge, List.cons_append, List.nil_append, s', ans]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [s', writeBits, MachineState.setPC, hpc, kPcAt_add4]

theorem k_step_halt_ecall (oracle : Oracle) (s : MachineState) (idx : Nat)
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base .ECALL)
    (hx5 : s.getReg .x5 = 1#64) :
    HaltsWith oracle s 1 0 (if s.getReg .x10 = 0#64 then .success else .failure) [] := by
  have hf : fetch (submission.image .check) s = some (.base .ECALL) := by
    rw [check_fetch s idx hhi hpc, hi]
  refine ⟨by split <;> decide, fun extra => ?_⟩
  have hx5_ne0 : ¬ (s.getReg .x5 = 0) := by rw [hx5]; decide
  have hx5_1 : s.getReg .x5 = 1 := hx5
  have hdet := detExec_succ_ecall oracle (submission.image .check) extra s hf
  rw [show 1 + extra = extra + 1 by omega, hdet]
  simp only [hx5_ne0, ite_false, hx5_1, ite_true]
  exact ⟨rfl, rfl, rfl⟩

theorem k_step_halt_reject (oracle : Oracle) (s : MachineState) (hpc : s.pc = kPcAt 266) :
    HaltsWith oracle s 3 0 .failure [] := by
  have h0 := k_step_ADDI (oracle := oracle) (s := s) (idx := 266) (by decide) hpc rfl
  let s1 := (s.setReg .x5 (s.getReg .x0 + signExtend12 1#12)).setPC (kPcAt 267)
  have h1 := k_step_ADDI (oracle := oracle) (s := s1) (idx := 267) (by decide) rfl rfl
  let s2 := (s1.setReg .x10 (s1.getReg .x0 + signExtend12 1#12)).setPC (kPcAt 268)
  have hx5 : s2.getReg .x5 = 1#64 := by
    simp only [s2, s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx10 : s2.getReg .x10 = 1#64 := by
    simp only [s2, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hh := k_step_halt_ecall oracle s2 268 (by decide) rfl rfl hx5
  have hne : ¬ (s2.getReg .x10 = 0#64) := by rw [hx10]; decide
  simp only [hne, ite_false] at hh
  simpa using (h0.trans h1).halt hh

theorem k_step_halt_accept (oracle : Oracle) (s : MachineState) (hpc : s.pc = kPcAt 263) :
    HaltsWith oracle s 3 0 .success [] := by
  have h0 := k_step_ADDI (oracle := oracle) (s := s) (idx := 263) (by decide) hpc rfl
  let s1 := (s.setReg .x5 (s.getReg .x0 + signExtend12 1#12)).setPC (kPcAt 264)
  have h1 := k_step_ADDI (oracle := oracle) (s := s1) (idx := 264) (by decide) rfl rfl
  let s2 := (s1.setReg .x10 (s1.getReg .x0 + signExtend12 0#12)).setPC (kPcAt 265)
  have hx5 : s2.getReg .x5 = 1#64 := by
    simp only [s2, s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx10 : s2.getReg .x10 = 0#64 := by
    simp only [s2, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hh := k_step_halt_ecall oracle s2 265 (by decide) rfl rfl hx5
  rw [if_pos hx10] at hh
  simpa using (h0.trans h1).halt hh

theorem k_step_halt_empty_accept (oracle : Oracle) (s : MachineState) (hpc : s.pc = kPcAt 2) :
    HaltsWith oracle s 3 0 .success [] := by
  have h0 := k_step_ADDI (oracle := oracle) (s := s) (idx := 2) (by decide) hpc rfl
  let s1 := (s.setReg .x5 (s.getReg .x0 + signExtend12 1#12)).setPC (kPcAt 3)
  have h1 := k_step_ADDI (oracle := oracle) (s := s1) (idx := 3) (by decide) rfl rfl
  let s2 := (s1.setReg .x10 (s1.getReg .x0 + signExtend12 0#12)).setPC (kPcAt 4)
  have hx5 : s2.getReg .x5 = 1#64 := by
    simp only [s2, s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx10 : s2.getReg .x10 = 0#64 := by
    simp only [s2, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hh := k_step_halt_ecall oracle s2 4 (by decide) rfl rfl hx5
  rw [if_pos hx10] at hh
  simpa using (h0.trans h1).halt hh

/-! ### 5. `CheckFixedRegs` and Reusable Aligned Copy / Compare Blocks -/

structure CheckFixedRegs (input : CheckInput) (s : MachineState) : Prop where
  x5  : s.getReg .x5  = 0#64
  x8  : s.getReg .x8  = BitVec.ofNat 64 4294971392
  x11 : s.getReg .x11 = BitVec.ofNat 64 96
  x13 : s.getReg .x13 = 0#64
  x18 : s.getReg .x18 = BitVec.ofNat 64 (6643781664 + 8 * input.positions.card)
  x21 : s.getReg .x21 = BitVec.ofNat 64 (11072966688 + input.proof.length)
  x22 : s.getReg .x22 = BitVec.ofNat 64 LENGTH
  x23 : s.getReg .x23 = BitVec.ofNat 64 CAP_LEAF_LO
  x24 : s.getReg .x24 = BitVec.ofNat 64 4096
  x25 : s.getReg .x25 = BitVec.ofNat 64 8192
  x26 : s.getReg .x26 = BitVec.ofNat 64 256
  x27 : s.getReg .x27 = BitVec.ofNat 64 3

def isCheckFixedReg : Reg → Bool
  | .x5 | .x8 | .x11 | .x13 | .x18 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 => true
  | _ => false

theorem isCheckFixedReg_ne {r r' : Reg} (h : isCheckFixedReg r = true) (h' : isCheckFixedReg r' = false) :
    r ≠ r' := by
  intro heq; subst heq; rw [h] at h'; cases h'

theorem CheckFixedRegs.of_agree {input : CheckInput} {s1 s2 : MachineState}
    (hf : CheckFixedRegs input s1) (h : ∀ r, isCheckFixedReg r = true → s2.getReg r = s1.getReg r) :
    CheckFixedRegs input s2 where
  x5  := (h .x5  rfl).trans hf.x5
  x8  := (h .x8  rfl).trans hf.x8
  x11 := (h .x11 rfl).trans hf.x11
  x13 := (h .x13 rfl).trans hf.x13
  x18 := (h .x18 rfl).trans hf.x18
  x21 := (h .x21 rfl).trans hf.x21
  x22 := (h .x22 rfl).trans hf.x22
  x23 := (h .x23 rfl).trans hf.x23
  x24 := (h .x24 rfl).trans hf.x24
  x25 := (h .x25 rfl).trans hf.x25
  x26 := (h .x26 rfl).trans hf.x26
  x27 := (h .x27 rfl).trans hf.x27

/-- Copy one 8-byte aligned doubleword (`LD tmp srcReg srcOff; SD dstReg tmp dstOff`). -/
theorem k_copy_dword (oracle : Oracle) {s : MachineState} {idx : Nat} {tmp srcReg dstReg : Reg}
    {srcOff dstOff src dst : Nat}
    (hhi : idx + 1 < 269) (hpc : s.pc = kPcAt idx)
    (hso : srcOff < 2048) (hdo : dstOff < 2048)
    (hi0 : checkInstr idx = .base (.LD tmp srcReg (BitVec.ofNat 12 srcOff)))
    (hi1 : checkInstr (idx + 1) = .base (.SD dstReg tmp (BitVec.ofNat 12 dstOff)))
    (htmp0 : tmp ≠ .x0) (htmpDst : tmp ≠ dstReg)
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 src)
    (hdst : s.getReg dstReg = BitVec.ofNat 64 dst)
    (hsAl : (src + srcOff) % 8 = 0) (hsBd : src + srcOff + 8 ≤ 68719476736)
    (hdAl : (dst + dstOff) % 8 = 0) (hdBd : dst + dstOff + 8 ≤ 68719476736) :
    ∃ s' : MachineState,
      StepsTo oracle s s' 2 0 [] ∧
      s'.pc = kPcAt (idx + 2) ∧
      (∀ r, r ≠ tmp → s'.getReg r = s.getReg r) ∧
      (∀ j < 8, s'.getByte (BitVec.ofNat 64 (dst + dstOff + j)) =
        s.getByte (BitVec.ofNat 64 (src + srcOff + j))) ∧
      MemEqOutside s s' (dst + dstOff) (dst + dstOff + 8) := by
  have ha0 : s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff) =
      BitVec.ofNat 64 (src + srcOff) := by
    rw [hsrc, k_se12_lt2048 srcOff hso, k_bv_add]
  have hst0 := k_step_LD (oracle := oracle) (by omega) hpc hi0
    (by rw [ha0]; exact k_accessValid _ 8 hsBd hsAl)
  let s1 := (s.setReg tmp (s.getMem (s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff)))).setPC (kPcAt (idx + 1))
  have ha1 : s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 dstOff) =
      BitVec.ofNat 64 (dst + dstOff) := by
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ htmpDst,
      hdst, k_se12_lt2048 dstOff hdo, k_bv_add]
  have hst1 := k_step_SD (oracle := oracle) (s := s1) (by omega) rfl hi1
    (by rw [ha1]; exact k_accessValid _ 8 hdBd hdAl)
  let s2 := (s1.setMem (s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 dstOff)) (s1.getReg tmp)).setPC (kPcAt (idx + 2))
  refine ⟨s2, by simpa using hst0.trans hst1, rfl, ?_, ?_, ?_⟩
  · intro r hr
    simp only [s2, s1, MachineState.getReg_setPC, k_getReg_setMem]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)
  · intro j hj
    have hv : s1.getReg tmp = s.getMem (BitVec.ofNat 64 (src + srcOff)) := by
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq htmp0, ha0]
    simp only [s2, k_getByte_setPC, ha1, hv]
    rw [setMem_getByte_inside s1 (dst + dstOff) j _ hdAl hj]
    exact k_getMem_extractByte s (src + srcOff) j hsAl hj
  · intro a ha hout
    simp only [s2, k_getByte_setPC, ha1]
    rw [setMem_getByte_ofNat s1 (dst + dstOff) a _ hdAl (by omega) ha hout]
    simp only [s1, k_getByte_setPC, k_getByte_setReg]

/-- Copy 24 bytes (3 aligned dwords, `6` steps). -/
theorem k_copy_24 (oracle : Oracle) {s : MachineState} {idx : Nat} {tmp srcReg dstReg : Reg}
    {srcOff dstOff src dst : Nat}
    (hhi : idx + 5 < 269) (hpc : s.pc = kPcAt idx)
    (hso : srcOff + 16 < 2048) (hdo : dstOff + 16 < 2048)
    (hi0 : checkInstr idx = .base (.LD tmp srcReg (BitVec.ofNat 12 srcOff)))
    (hi1 : checkInstr (idx + 1) = .base (.SD dstReg tmp (BitVec.ofNat 12 dstOff)))
    (hi2 : checkInstr (idx + 2) = .base (.LD tmp srcReg (BitVec.ofNat 12 (srcOff + 8))))
    (hi3 : checkInstr (idx + 3) = .base (.SD dstReg tmp (BitVec.ofNat 12 (dstOff + 8))))
    (hi4 : checkInstr (idx + 4) = .base (.LD tmp srcReg (BitVec.ofNat 12 (srcOff + 16))))
    (hi5 : checkInstr (idx + 5) = .base (.SD dstReg tmp (BitVec.ofNat 12 (dstOff + 16))))
    (htmp0 : tmp ≠ .x0) (htmpSrc : tmp ≠ srcReg) (htmpDst : tmp ≠ dstReg)
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 src)
    (hdst : s.getReg dstReg = BitVec.ofNat 64 dst)
    (hsAl : (src + srcOff) % 8 = 0) (hsBd : src + srcOff + 24 ≤ 68719476736)
    (hdAl : (dst + dstOff) % 8 = 0) (hdBd : dst + dstOff + 24 ≤ 68719476736)
    (hdisj : src + srcOff + 24 ≤ dst + dstOff ∨ dst + dstOff + 24 ≤ src + srcOff) :
    ∃ s' : MachineState,
      StepsTo oracle s s' 6 0 [] ∧
      s'.pc = kPcAt (idx + 6) ∧
      (∀ r, r ≠ tmp → s'.getReg r = s.getReg r) ∧
      readBuffer s' (dst + dstOff) 24 = readBuffer s (src + srcOff) 24 ∧
      MemEqOutside s s' (dst + dstOff) (dst + dstOff + 24) := by
  obtain ⟨s1, hr1, hp1, hreg1, hin1, hout1⟩ := k_copy_dword oracle (by omega) hpc (by omega) (by omega)
    hi0 hi1 htmp0 htmpDst hsrc hdst hsAl (by omega) hdAl (by omega)
  obtain ⟨s2, hr2, hp2, hreg2, hin2, hout2⟩ := k_copy_dword oracle (s := s1) (by omega) hp1 (by omega) (by omega)
    hi2 hi3 htmp0 htmpDst ((hreg1 srcReg htmpSrc.symm).trans hsrc) ((hreg1 dstReg htmpDst.symm).trans hdst)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s3, hr3, hp3, hreg3, hin3, hout3⟩ := k_copy_dword oracle (s := s2) (by omega) hp2 (by omega) (by omega)
    hi4 hi5 htmp0 htmpDst
    ((hreg2 srcReg htmpSrc.symm).trans ((hreg1 srcReg htmpSrc.symm).trans hsrc))
    ((hreg2 dstReg htmpDst.symm).trans ((hreg1 dstReg htmpDst.symm).trans hdst))
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨s3, by simpa using (hr1.trans hr2).trans hr3, hp3,
    fun r hr => (hreg3 r hr).trans ((hreg2 r hr).trans (hreg1 r hr)), ?_,
    (hout1.mono (by omega) (by omega)).trans ((hout2.mono (by omega) (by omega)).trans (hout3.mono (by omega) (by omega)))⟩
  apply k_readBuffer_congr2; intro j hj
  by_cases h8 : j < 8
  · exact (hout3 _ (by omega) (by omega)).trans ((hout2 _ (by omega) (by omega)).trans (hin1 j h8))
  · by_cases h16 : j < 16
    · have h2 := hin2 (j - 8) (by omega)
      have eq1 : dst + (dstOff + 8) + (j - 8) = dst + dstOff + j := by omega
      have eq2 : src + (srcOff + 8) + (j - 8) = src + srcOff + j := by omega
      rw [eq1, eq2] at h2
      exact (hout3 _ (by omega) (by omega)).trans (h2.trans (hout1 _ (by omega) (by omega)))
    · have h3 := hin3 (j - 16) (by omega)
      have eq1 : dst + (dstOff + 16) + (j - 16) = dst + dstOff + j := by omega
      have eq2 : src + (srcOff + 16) + (j - 16) = src + srcOff + j := by omega
      rw [eq1, eq2] at h3
      exact h3.trans ((hout2 _ (by omega) (by omega)).trans (hout1 _ (by omega) (by omega)))

/-- Copy 32 bytes (4 aligned dwords, `8` steps). -/
theorem k_copy_32 (oracle : Oracle) {s : MachineState} {idx : Nat} {tmp srcReg dstReg : Reg}
    {srcOff dstOff src dst : Nat}
    (hhi : idx + 7 < 269) (hpc : s.pc = kPcAt idx)
    (hso : srcOff + 24 < 2048) (hdo : dstOff + 24 < 2048)
    (hi0 : checkInstr idx = .base (.LD tmp srcReg (BitVec.ofNat 12 srcOff)))
    (hi1 : checkInstr (idx + 1) = .base (.SD dstReg tmp (BitVec.ofNat 12 dstOff)))
    (hi2 : checkInstr (idx + 2) = .base (.LD tmp srcReg (BitVec.ofNat 12 (srcOff + 8))))
    (hi3 : checkInstr (idx + 3) = .base (.SD dstReg tmp (BitVec.ofNat 12 (dstOff + 8))))
    (hi4 : checkInstr (idx + 4) = .base (.LD tmp srcReg (BitVec.ofNat 12 (srcOff + 16))))
    (hi5 : checkInstr (idx + 5) = .base (.SD dstReg tmp (BitVec.ofNat 12 (dstOff + 16))))
    (hi6 : checkInstr (idx + 6) = .base (.LD tmp srcReg (BitVec.ofNat 12 (srcOff + 24))))
    (hi7 : checkInstr (idx + 7) = .base (.SD dstReg tmp (BitVec.ofNat 12 (dstOff + 24))))
    (htmp0 : tmp ≠ .x0) (htmpSrc : tmp ≠ srcReg) (htmpDst : tmp ≠ dstReg)
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 src)
    (hdst : s.getReg dstReg = BitVec.ofNat 64 dst)
    (hsAl : (src + srcOff) % 8 = 0) (hsBd : src + srcOff + 32 ≤ 68719476736)
    (hdAl : (dst + dstOff) % 8 = 0) (hdBd : dst + dstOff + 32 ≤ 68719476736)
    (hdisj : src + srcOff + 32 ≤ dst + dstOff ∨ dst + dstOff + 32 ≤ src + srcOff) :
    ∃ s' : MachineState,
      StepsTo oracle s s' 8 0 [] ∧
      s'.pc = kPcAt (idx + 8) ∧
      (∀ r, r ≠ tmp → s'.getReg r = s.getReg r) ∧
      readBuffer s' (dst + dstOff) 32 = readBuffer s (src + srcOff) 32 ∧
      MemEqOutside s s' (dst + dstOff) (dst + dstOff + 32) := by
  obtain ⟨s1, hr1, hp1, hreg1, hin1, hout1⟩ := k_copy_dword oracle (by omega) hpc (by omega) (by omega)
    hi0 hi1 htmp0 htmpDst hsrc hdst hsAl (by omega) hdAl (by omega)
  obtain ⟨s2, hr2, hp2, hreg2, hin2, hout2⟩ := k_copy_dword oracle (s := s1) (by omega) hp1 (by omega) (by omega)
    hi2 hi3 htmp0 htmpDst ((hreg1 srcReg htmpSrc.symm).trans hsrc) ((hreg1 dstReg htmpDst.symm).trans hdst)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s3, hr3, hp3, hreg3, hin3, hout3⟩ := k_copy_dword oracle (s := s2) (by omega) hp2 (by omega) (by omega)
    hi4 hi5 htmp0 htmpDst
    ((hreg2 srcReg htmpSrc.symm).trans ((hreg1 srcReg htmpSrc.symm).trans hsrc))
    ((hreg2 dstReg htmpDst.symm).trans ((hreg1 dstReg htmpDst.symm).trans hdst))
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s4, hr4, hp4, hreg4, hin4, hout4⟩ := k_copy_dword oracle (s := s3) (by omega) hp3 (by omega) (by omega)
    hi6 hi7 htmp0 htmpDst
    ((hreg3 srcReg htmpSrc.symm).trans ((hreg2 srcReg htmpSrc.symm).trans ((hreg1 srcReg htmpSrc.symm).trans hsrc)))
    ((hreg3 dstReg htmpDst.symm).trans ((hreg2 dstReg htmpDst.symm).trans ((hreg1 dstReg htmpDst.symm).trans hdst)))
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨s4, by simpa using (hr1.trans hr2).trans (hr3.trans hr4), hp4,
    fun r hr => (hreg4 r hr).trans ((hreg3 r hr).trans ((hreg2 r hr).trans (hreg1 r hr))), ?_,
    (hout1.mono (by omega) (by omega)).trans ((hout2.mono (by omega) (by omega)).trans
      ((hout3.mono (by omega) (by omega)).trans (hout4.mono (by omega) (by omega))))⟩
  apply k_readBuffer_congr2; intro j hj
  by_cases h8 : j < 8
  · exact (hout4 _ (by omega) (by omega)).trans ((hout3 _ (by omega) (by omega)).trans
      ((hout2 _ (by omega) (by omega)).trans (hin1 j h8)))
  · by_cases h16 : j < 16
    · have h2 := hin2 (j - 8) (by omega)
      have eq1 : dst + (dstOff + 8) + (j - 8) = dst + dstOff + j := by omega
      have eq2 : src + (srcOff + 8) + (j - 8) = src + srcOff + j := by omega
      rw [eq1, eq2] at h2
      exact (hout4 _ (by omega) (by omega)).trans ((hout3 _ (by omega) (by omega)).trans
        (h2.trans (hout1 _ (by omega) (by omega))))
    · by_cases h24 : j < 24
      · have h3 := hin3 (j - 16) (by omega)
        have eq1 : dst + (dstOff + 16) + (j - 16) = dst + dstOff + j := by omega
        have eq2 : src + (srcOff + 16) + (j - 16) = src + srcOff + j := by omega
        rw [eq1, eq2] at h3
        exact (hout4 _ (by omega) (by omega)).trans
          (h3.trans ((hout2 _ (by omega) (by omega)).trans (hout1 _ (by omega) (by omega))))
      · have h4 := hin4 (j - 24) (by omega)
        have eq1 : dst + (dstOff + 24) + (j - 24) = dst + dstOff + j := by omega
        have eq2 : src + (srcOff + 24) + (j - 24) = src + srcOff + j := by omega
        rw [eq1, eq2] at h4
        exact h4.trans ((hout3 _ (by omega) (by omega)).trans
          ((hout2 _ (by omega) (by omega)).trans (hout1 _ (by omega) (by omega))))

/-- Compare one 8-byte aligned dword (`LD x29 aReg aOff; LD x30 bReg bOff; BNE x29 x30 -> 266`). -/
private theorem k_cmp_dword (oracle : Oracle) {s : MachineState} {idx : Nat} {aReg bReg : Reg}
    {aOff bOff a b : Nat} {bImm : BitVec 13}
    (hhi : idx + 2 < 269) (hpc : s.pc = kPcAt idx)
    (hao : aOff < 2048) (hbo : bOff < 2048)
    (hi0 : checkInstr idx = .base (.LD .x29 aReg (BitVec.ofNat 12 aOff)))
    (hi1 : checkInstr (idx + 1) = .base (.LD .x30 bReg (BitVec.ofNat 12 bOff)))
    (hi2 : checkInstr (idx + 2) = .base (.BNE .x29 .x30 bImm))
    (htgt : kPcAt (idx + 2) + signExtend13 bImm = kPcAt 266)
    (hbReg29 : bReg ≠ .x29)
    (ha : s.getReg aReg = BitVec.ofNat 64 a)
    (hb : s.getReg bReg = BitVec.ofNat 64 b)
    (haAl : (a + aOff) % 8 = 0) (haBd : a + aOff + 8 ≤ 68719476736)
    (hbAl : (b + bOff) % 8 = 0) (hbBd : b + bOff + 8 ≤ 68719476736) :
    (s.getMem (BitVec.ofNat 64 (a + aOff)) ≠ s.getMem (BitVec.ofNat 64 (b + bOff)) ∧
      HaltsWith oracle s 6 0 .failure []) ∨
    (∃ s', StepsTo oracle s s' 3 0 [] ∧
      s'.pc = kPcAt (idx + 3) ∧
      s.getMem (BitVec.ofNat 64 (a + aOff)) = s.getMem (BitVec.ofNat 64 (b + bOff)) ∧
      s'.mem = s.mem ∧
      ∀ r, r ≠ .x29 → r ≠ .x30 → s'.getReg r = s.getReg r) := by
  have ha0 : s.getReg aReg + signExtend12 (BitVec.ofNat 12 aOff) = BitVec.ofNat 64 (a + aOff) := by
    rw [ha, k_se12_lt2048 aOff hao, k_bv_add]
  have hst0 := k_step_LD (oracle := oracle) (by omega) hpc hi0
    (by rw [ha0]; exact k_accessValid _ 8 haBd haAl)
  let s1 := (s.setReg .x29 (s.getMem (s.getReg aReg + signExtend12 (BitVec.ofNat 12 aOff)))).setPC (kPcAt (idx + 1))
  have hb1 : s1.getReg bReg + signExtend12 (BitVec.ofNat 12 bOff) = BitVec.ofNat 64 (b + bOff) := by
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hbReg29.symm,
      hb, k_se12_lt2048 bOff hbo, k_bv_add]
  have hst1 := k_step_LD (oracle := oracle) (s := s1) (by omega) rfl hi1
    (by rw [hb1]; exact k_accessValid _ 8 hbBd hbAl)
  let s2 := (s1.setReg .x30 (s1.getMem (s1.getReg bReg + signExtend12 (BitVec.ofNat 12 bOff)))).setPC (kPcAt (idx + 2))
  have hx29 : s2.getReg .x29 = s.getMem (BitVec.ofNat 64 (a + aOff)) := by
    simp only [s2, s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x29),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha0]
  have hx30 : s2.getReg .x30 = s.getMem (BitVec.ofNat 64 (b + bOff)) := by
    simp only [s2, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hb1]
    simp only [s1, MachineState.getMem, k_mem_setPC, k_mem_setReg]
  have hmem2 : s2.mem = s.mem := by simp only [s2, s1, k_mem_setPC, k_mem_setReg]
  have hreg2 : ∀ r, r ≠ .x29 → r ≠ .x30 → s2.getReg r = s.getReg r := fun r h29 h30 => by
    simp only [s2, s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h30),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h29)]
  by_cases heq : s.getMem (BitVec.ofNat 64 (a + aOff)) = s.getMem (BitVec.ofNat 64 (b + bOff))
  · have hst2 := k_step_BNE_not_taken (oracle := oracle) (s := s2) (by omega) rfl hi2 (by rw [hx29, hx30, heq])
    exact .inr ⟨s2.setPC (kPcAt (idx + 3)), by simpa using (hst0.trans hst1).trans hst2,
      rfl, heq, hmem2, fun r h29 h30 => (k_getReg_setPC s2 _ r).trans (hreg2 r h29 h30)⟩
  · have hst2 := k_step_BNE_taken (oracle := oracle) (s := s2) (by omega) rfl hi2 (by rw [hx29, hx30]; exact heq) htgt
    have hh := k_step_halt_reject oracle (s2.setPC (kPcAt 266)) rfl
    exact .inl ⟨heq, by simpa using ((hst0.trans hst1).trans hst2).halt hh⟩

/-- Compare two 32-byte aligned digests (`12` steps, rejecting at `pc[266]` on any dword mismatch). -/
theorem k_cmp32_or_reject (oracle : Oracle) {s : MachineState} {idx : Nat} {aReg bReg : Reg}
    {aOff bOff a b : Nat} {i0 i1 i2 i3 : BitVec 13}
    (hhi : idx + 11 < 269) (hpc : s.pc = kPcAt idx)
    (hao : aOff + 24 < 2048) (hbo : bOff + 24 < 2048)
    (h0 : checkInstr idx = .base (.LD .x29 aReg (BitVec.ofNat 12 aOff)))
    (h1 : checkInstr (idx + 1) = .base (.LD .x30 bReg (BitVec.ofNat 12 bOff)))
    (h2 : checkInstr (idx + 2) = .base (.BNE .x29 .x30 i0))
    (h3 : checkInstr (idx + 3) = .base (.LD .x29 aReg (BitVec.ofNat 12 (aOff + 8))))
    (h4 : checkInstr (idx + 4) = .base (.LD .x30 bReg (BitVec.ofNat 12 (bOff + 8))))
    (h5 : checkInstr (idx + 5) = .base (.BNE .x29 .x30 i1))
    (h6 : checkInstr (idx + 6) = .base (.LD .x29 aReg (BitVec.ofNat 12 (aOff + 16))))
    (h7 : checkInstr (idx + 7) = .base (.LD .x30 bReg (BitVec.ofNat 12 (bOff + 16))))
    (h8 : checkInstr (idx + 8) = .base (.BNE .x29 .x30 i2))
    (h9 : checkInstr (idx + 9) = .base (.LD .x29 aReg (BitVec.ofNat 12 (aOff + 24))))
    (h10 : checkInstr (idx + 10) = .base (.LD .x30 bReg (BitVec.ofNat 12 (bOff + 24))))
    (h11 : checkInstr (idx + 11) = .base (.BNE .x29 .x30 i3))
    (ht0 : kPcAt (idx + 2) + signExtend13 i0 = kPcAt 266)
    (ht1 : kPcAt (idx + 5) + signExtend13 i1 = kPcAt 266)
    (ht2 : kPcAt (idx + 8) + signExtend13 i2 = kPcAt 266)
    (ht3 : kPcAt (idx + 11) + signExtend13 i3 = kPcAt 266)
    (ha29 : aReg ≠ .x29) (ha30 : aReg ≠ .x30) (hb29 : bReg ≠ .x29) (hb30 : bReg ≠ .x30)
    (ha : s.getReg aReg = BitVec.ofNat 64 a)
    (hb : s.getReg bReg = BitVec.ofNat 64 b)
    (haAl : (a + aOff) % 8 = 0) (haBd : a + aOff + 32 ≤ 68719476736)
    (hbAl : (b + bOff) % 8 = 0) (hbBd : b + bOff + 32 ≤ 68719476736) :
    PhaseOutcome oracle s 15 0
      (readBuffer s (a + aOff) 32 ≠ readBuffer s (b + bOff) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = kPcAt (idx + 12) ∧
        readBuffer s (a + aOff) 32 = readBuffer s (b + bOff) 32 ∧
        s'.mem = s.mem ∧
        ∀ r, r ≠ .x29 → r ≠ .x30 → s'.getReg r = s.getReg r) := by
  have hneq_of_word : ∀ w < 4,
      s.getMem (BitVec.ofNat 64 (a + aOff + 8 * w)) ≠ s.getMem (BitVec.ofNat 64 (b + bOff + 8 * w)) →
      readBuffer s (a + aOff) 32 ≠ readBuffer s (b + bOff) 32 := fun w hw hne heq =>
    hne ((read_digest_eq_iff s s (a + aOff) (b + bOff) haAl hbAl).mp heq w hw)
  have hc0 := k_cmp_dword oracle (s := s) (by omega) hpc (by omega) (by omega)
    h0 h1 h2 ht0 hb29 ha hb haAl (by omega) hbAl (by omega)
  rcases hc0 with ⟨hne0, hh0⟩ | ⟨s1, hst0, hpc1, hw0, hmem1, hreg1⟩
  · exact .rejected 6 0 [] (hneq_of_word 0 (by decide) (by simpa using hne0)) (by omega) (by omega) hh0
  · have hget1 : ∀ addr, s1.getMem addr = s.getMem addr := fun addr => congrFun hmem1 addr
    have hc1 := k_cmp_dword oracle (s := s1) (by omega) hpc1 (by omega) (by omega)
      h3 h4 h5 ht1 hb29 ((hreg1 aReg ha29 ha30).trans ha) ((hreg1 bReg hb29 hb30).trans hb)
      (by omega) (by omega) (by omega) (by omega)
    rcases hc1 with ⟨hne1, hh1⟩ | ⟨s2, hst1, hpc2, hw1, hmem2, hreg2⟩
    · rw [hget1, hget1] at hne1
      exact .rejected 9 0 [] (hneq_of_word 1 (by decide) (by simpa [Nat.add_assoc] using hne1))
        (by omega) (by omega) (by simpa using hst0.halt hh1)
    · rw [hget1, hget1] at hw1
      have hget2 : ∀ addr, s2.getMem addr = s.getMem addr := fun addr => (congrFun hmem2 addr).trans (hget1 addr)
      have hc2 := k_cmp_dword oracle (s := s2) (by omega) hpc2 (by omega) (by omega)
        h6 h7 h8 ht2 hb29
        ((hreg2 aReg ha29 ha30).trans ((hreg1 aReg ha29 ha30).trans ha))
        ((hreg2 bReg hb29 hb30).trans ((hreg1 bReg hb29 hb30).trans hb))
        (by omega) (by omega) (by omega) (by omega)
      rcases hc2 with ⟨hne2, hh2⟩ | ⟨s3, hst2, hpc3, hw2, hmem3, hreg3⟩
      · rw [hget2, hget2] at hne2
        exact .rejected 12 0 [] (hneq_of_word 2 (by decide) (by simpa [Nat.add_assoc] using hne2))
          (by omega) (by omega) (by simpa using (hst0.trans hst1).halt hh2)
      · rw [hget2, hget2] at hw2
        have hget3 : ∀ addr, s3.getMem addr = s.getMem addr := fun addr => (congrFun hmem3 addr).trans (hget2 addr)
        have hc3 := k_cmp_dword oracle (s := s3) (by omega) hpc3 (by omega) (by omega)
          h9 h10 h11 ht3 hb29
          ((hreg3 aReg ha29 ha30).trans ((hreg2 aReg ha29 ha30).trans ((hreg1 aReg ha29 ha30).trans ha)))
          ((hreg3 bReg hb29 hb30).trans ((hreg2 bReg hb29 hb30).trans ((hreg1 bReg hb29 hb30).trans hb)))
          (by omega) (by omega) (by omega) (by omega)
        rcases hc3 with ⟨hne3, hh3⟩ | ⟨s4, hst3, hpc4, hw3, hmem4, hreg4⟩
        · rw [hget3, hget3] at hne3
          exact .rejected 15 0 [] (hneq_of_word 3 (by decide) (by simpa [Nat.add_assoc] using hne3))
            (by omega) (by omega) (by simpa using ((hst0.trans hst1).trans hst2).halt hh3)
        · rw [hget3, hget3] at hw3
          have hdig : readBuffer s (a + aOff) 32 = readBuffer s (b + bOff) 32 := by
            rw [read_digest_eq_iff s s (a + aOff) (b + bOff) haAl hbAl]
            intro w hw
            interval_cases w
            · simpa using hw0
            · simpa [Nat.add_assoc] using hw1
            · simpa [Nat.add_assoc] using hw2
            · simpa [Nat.add_assoc] using hw3
          exact .continued s4 12 0 [] (by omega) (by omega)
            (by simpa using ((hst0.trans hst1).trans hst2).trans hst3)
            ⟨rfl, rfl, hpc4, hdig,
              hmem4.trans (hmem3.trans (hmem2.trans hmem1)),
              fun r h29 h30 => (hreg4 r h29 h30).trans ((hreg3 r h29 h30).trans
                ((hreg2 r h29 h30).trans (hreg1 r h29 h30)))⟩

end CommitGolfCandidate
