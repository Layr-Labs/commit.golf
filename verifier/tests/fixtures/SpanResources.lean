import CommitGolfDepth.Span
import CommitGolf.Artifact
import CommitGolfDepth.Span.Proofs

/-! Resource-only proof client for delivered fork-mode images.

The program obtains its descriptors from its actual embedded data, through the normal
input-loading ABI. Both children execute MUL and SD instructions in the submitted image.
Embedded-data loading is unscored, as in the existing machine; the two setup instructions
and the FORK model's descriptor-read/context price are charged. No descriptor SD stores
are claimed to have executed.
No host-prepared MachineState, deterministic oracle observer, legacy certificate bridge,
or unrelated abstract scheme is used. This fixture proves resource behavior only; it
does not claim a cryptographically secure commitment scheme and cannot earn a score.
-/

namespace CommitGolf.Challenge
open OracleComp CommitGolfDepth.Span CommitGolfDepth.Span.SpanMachine

def fixtureCode : ArtifactEncoding.Packed 11 :=
  ArtifactEncoding.Packed.chunk 11
    245638509776927665064853415416344771737905652714888664781944627436367520193646501731756621802046739

def fixtureData : ArtifactEncoding.Packed 128 :=
  ArtifactEncoding.Packed.chunk 128
    257750135266274651647078463399442192694638283945435393309853092047654011823368286589386937055023437731559518789518793109199478258158647322714660486054162387323700241355099584822829628788246010336501444027448403896881299295519155707800957725301975027736

def fixtureCore : CommitGolf.Submission where
  sizes := ⟨16, 64⟩
  layout := ⟨4096, 4294971392, 4294971424, 4294971440, 4429189168, 8724156464⟩
  image
    | .commit => ⟨ArtifactEncoding.decode 32 fixtureCode, ArtifactEncoding.decode 8 fixtureData⟩
    | .opening => ⟨ArtifactEncoding.decode 32 fixtureCode, ArtifactEncoding.decode 8 fixtureData⟩
    | .check => ⟨ArtifactEncoding.decode 32 fixtureCode, ArtifactEncoding.decode 8 fixtureData⟩
  steps
    | .commit => 16
    | .opening => 16
    | .check => 16

def submission : CommitGolfDepth.Span.Submission where
  core := fixtureCore
  modes
    | .commit => .forkJoin
    | .opening => .forkJoin
    | .check => .forkJoin

theorem submission_matches_artifact : submission = Artifact.depthSubmission := by rfl

theorem admission : submission.core.Admission := by
  intro program
  cases program <;> decide +kernel

def observe (r : Result) : Riscv.Exit × Nat × Nat × Nat × Nat × BitVec 64 × BitVec 64 :=
  (r.exit, r.work, r.span, r.oracleCalls, r.trace.instructions, r.state.mem 512, r.state.mem 520)

/-- Syntactic inspection rejects every oracle/coin query constructor. It does not supply
answers to queries, so a successful inspection establishes a query-free computation. -/
def inspectPure : OracleComp World Result →
    Option (Riscv.Exit × Nat × Nat × Nat × Nat × BitVec 64 × BitVec 64)
  | .pure result => some (observe result)
  | .queryBind _ _ => none

theorem pure_of_inspection (computation : OracleComp World Result)
    (expected : Riscv.Exit × Nat × Nat × Nat × Nat × BitVec 64 × BitVec 64)
    (h : inspectPure computation = some expected) :
    ∃ result, computation = pure result ∧ observe result = expected := by
  cases computation with
  | pure result => exact ⟨result, rfl, Option.some.inj h⟩
  | queryBind query next => cases h

def checked : Option (Riscv.Exit × Nat × Nat × Nat × Nat × BitVec 64 × BitVec 64) → Bool
  | some (.success, work, span, queries, instructions, left, right) =>
    decide (work = 103) && decide (span = 95) && decide (queries = 0) &&
      decide (instructions = 16) && decide (left.toNat = 49) && decide (right.toNat = 81)
  | _ => false

theorem checked_sound (result : Result) (h : checked (some (observe result)) = true) :
    observe result = (.success, 103, 95, 0, 16, 49, 81) := by
  cases exit : result.exit with
  | failure => simp [checked, observe, exit] at h
  | unfinished => simp [checked, observe, exit] at h
  | success =>
    simp only [checked, observe, exit, Bool.and_eq_true, and_assoc] at h
    obtain ⟨hw, hs, hq, hi, hl, hr⟩ := h
    have work : result.work = 103 := of_decide_eq_true hw
    have span : result.span = 95 := of_decide_eq_true hs
    have queries : result.oracleCalls = 0 := of_decide_eq_true hq
    have instructions : result.trace.instructions = 16 := of_decide_eq_true hi
    have left : result.state.mem 512 = 49 := BitVec.eq_of_toNat_eq (of_decide_eq_true hl)
    have right : result.state.mem 520 = 81 := BitVec.eq_of_toNat_eq (of_decide_eq_true hr)
    exact Prod.ext exit (Prod.ext work (Prod.ext span (Prod.ext queries
      (Prod.ext instructions (Prod.ext left right)))))

theorem pure_of_checked (computation : OracleComp World Result)
    (h : checked (inspectPure computation) = true) :
    ∃ result, computation = pure result ∧
      observe result = (.success, 103, 95, 0, 16, 49, 81) := by
  cases computation with
  | pure result => exact ⟨result, rfl, checked_sound result h⟩
  | queryBind query next => cases h

theorem zero_inspection :
    checked (inspectPure (submission.run .commit (fun _ => 0))) = true := by
  decide +kernel

/-- Actual raw execution on the fixed ABI input is pure. This equality retains the full
oracle/coin computation, rather than checking one deterministic observer of that code. -/
theorem run_pure :
    ∃ result, submission.run .commit (fun _ => 0) = pure result ∧
      observe result = (.success, 103, 95, 0, 16, 49, 81) := by
  exact pure_of_checked _ zero_inspection

/-- The fixed-oracle theorem is deliberately separate from a production certificate.
Neither security, proof-size, opening behavior nor checker behavior is claimed. -/
theorem resources (oracle : Oracle) :
    Pr{let result ← oracle.run (submission.run .commit (fun _ => 0))}[
      result.1.exit = .success ∧ result.1.work ≤ 103 ∧ result.1.span ≤ 95 ∧
      result.1.oracleCalls = 0 ∧ result.2 = 0 ∧
      result.1.trace.instructions = 16 ∧ result.1.span < result.1.work ∧
      result.1.state.mem 512 = 49 ∧ result.1.state.mem 520 = 81] = 1 := by
  obtain ⟨result, executed, observation⟩ := run_pure
  rw [executed]
  simp only [observe, Prod.mk.injEq] at observation
  have ran : oracle.run (pure result) = pure (result, 0) := by rfl
  rw [ran]
  simp only [prEvent_pure]
  simp_all

theorem resource_fixture (oracle : Oracle) :
    Pr{let result ← oracle.run (submission.run .commit (fun _ => 0))}[
      result.1.exit = .success ∧ result.1.work ≤ 103 ∧ result.1.span ≤ 95 ∧
      result.1.oracleCalls = 0 ∧ result.2 = 0 ∧
      result.1.trace.instructions = 16 ∧ result.1.span < result.1.work ∧
      result.1.state.mem 512 = 49 ∧ result.1.state.mem 520 = 81] = 1 :=
  resources oracle

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Symbolic solver-side rules, checked against core-only trusted statements. -/
theorem symbolic_step : ∀ (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (reserved : left.fuel + right.fuel ≤ fuel),
    Subtype.val <$> runBody children true image p coins (fuel + 1) state = (do
      let l ← children (childPolicy p left.region right.region) left.fuel (childState state left)
      let r ← children (childPolicy p right.region left.region) right.fuel (childState state right)
      let c ← if childrenExit l.val.exit r.val.exit = .success then
          runBody children true image p coins (fuel - left.fuel - right.fuel)
            ((protectWrites p state
              (merge state l.val.state r.val.state left.region right.region)).setPC (state.pc + 4))
        else pure (boundedStop (fuel - left.fuel - right.fuel)
          (childrenExit l.val.exit r.val.exit) state)
      return {c.val with trace := .fork FORK_CYCLES JOIN_CYCLES l.val.trace r.val.trace c.val.trace}) := @CommitGolfDepth.Span.Proofs.runBody_fork_val

theorem symbolic_bounds : ∀ (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (reserved : left.fuel + right.fuel ≤ fuel)
    (lw ls lq rw rs rq cw cs cq : Nat)
    (hl : ∀ l ∈ support (children (childPolicy p left.region right.region) left.fuel
      (childState state left)), (l.val.work ≤ lw ∧ l.val.span ≤ ls ∧ l.val.oracleCalls ≤ lq))
    (hr : ∀ r ∈ support (children (childPolicy p right.region left.region) right.fuel
      (childState state right)), (r.val.work ≤ rw ∧ r.val.span ≤ rs ∧ r.val.oracleCalls ≤ rq))
    (hc : ∀ l ∈ support (children (childPolicy p left.region right.region) left.fuel
      (childState state left)), ∀ r ∈ support (children (childPolicy p right.region left.region)
      right.fuel (childState state right)), ∀ c ∈ support
      (if childrenExit l.val.exit r.val.exit = .success then
        runBody children true image p coins (fuel - left.fuel - right.fuel)
          ((protectWrites p state (merge state l.val.state r.val.state left.region right.region)).setPC
            (state.pc + 4))
      else pure (boundedStop (fuel - left.fuel - right.fuel)
        (childrenExit l.val.exit r.val.exit) state)), (c.val.work ≤ cw ∧ c.val.span ≤ cs ∧ c.val.oracleCalls ≤ cq))
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children true image p coins (fuel + 1) state)),
    (out.val.work ≤ FORK_CYCLES + lw + rw + JOIN_CYCLES + cw ∧
      out.val.span ≤ FORK_CYCLES + max ls rs + JOIN_CYCLES + cs ∧
      out.val.oracleCalls ≤ lq + rq + cq) := @CommitGolfDepth.Span.Proofs.runBody_fork_bounds

/-- Ordinary instruction equations and bounds, stated with core machine definitions. -/
theorem ordinary_step : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL),
    runBody children canFork image p coins (fuel + 1) state =
      (if ordinaryAllowed p state instruction then
        match Riscv.ordinaryStep state instruction with
        | none => pure (boundedExit fuel .failure state)
        | some next => do
          let result ← runBody children canFork image p coins fuel (protectWrites p state next)
          return boundedCharge result (Riscv.instructionCycles instruction) 0
      else pure (boundedExit fuel .failure state)) := @CommitGolfDepth.Span.Proofs.runBody_ordinary_cases

theorem ordinary_bounds : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state next : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) (allowed : ordinaryAllowed p state instruction = true)
    (stepped : Riscv.ordinaryStep state instruction = some next)
    (work span queries : Nat)
    (h : ∀ result ∈ support (runBody children canFork image p coins fuel
      (protectWrites p state next)), (result.val.work ≤ work ∧ result.val.span ≤ span ∧ result.val.oracleCalls ≤ queries))
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)),
    (out.val.work ≤ Riscv.instructionCycles instruction + work ∧
      out.val.span ≤ Riscv.instructionCycles instruction + span ∧ out.val.oracleCalls ≤ queries) := @CommitGolfDepth.Span.Proofs.runBody_ordinary_bounds

/-- Syscall rules and bounds, specified solely with live interpreter definitions. -/
theorem oracle_step : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0),
    runBody children canFork image p coins (fuel + 1) state =
      (if oracleAllowed p state then
        match Riscv.oracleInput state with
        | none => pure (boundedExit fuel .failure state)
        | some query => do
          let answer ← World.query (.inr query)
          let result ← runBody children canFork image p coins fuel
            (protectWrites p state (Riscv.writeOracleAnswer state (state.getReg .x12) query answer))
          return boundedCharge result (Riscv.oracleCycles query) 1
      else pure (boundedExit fuel .failure state)) := @CommitGolfDepth.Span.Proofs.runBody_oracle_cases

theorem oracle_bounds : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState) (query : PublicSpec.Domain)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0)
    (allowed : oracleAllowed p state = true) (input : Riscv.oracleInput state = some query)
    (work span queries : Nat)
    (h : ∀ answer : PublicSpec.Range query, ∀ result ∈ support
      (runBody children canFork image p coins fuel
        (protectWrites p state (Riscv.writeOracleAnswer state (state.getReg .x12) query answer))),
        (result.val.work ≤ work ∧ result.val.span ≤ span ∧ result.val.oracleCalls ≤ queries))
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)),
    (out.val.work ≤ Riscv.oracleCycles query + work ∧ out.val.span ≤ Riscv.oracleCycles query + span ∧
      out.val.oracleCalls ≤ 1 + queries) := @CommitGolfDepth.Span.Proofs.runBody_oracle_bounds

theorem halt_step : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 1),
    runBody children canFork image p coins (fuel + 1) state =
      pure (boundedExit fuel (if state.getReg .x10 = 0 then .success else .failure) state) := @CommitGolfDepth.Span.Proofs.runBody_halt

theorem halt_bounds : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 1)
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)),
    (out.val.work ≤ 1 ∧ out.val.span ≤ 1 ∧ out.val.oracleCalls ≤ 0) := @CommitGolfDepth.Span.Proofs.runBody_halt_bounds

theorem random_step : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2),
    runBody children canFork image p coins (fuel + 1) state =
      (if coins && randomAllowed p state then do
        let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
          ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
        let result ← runBody children canFork image p coins fuel
          (protectWrites p state (Riscv.writeBits state (state.getReg .x10) answer))
        return boundedCharge result (1 + ((state.getReg .x11).toNat + 7) / 8) 0
      else pure (boundedExit fuel .failure state)) := @CommitGolfDepth.Span.Proofs.runBody_random_cases

theorem random_bounds : ∀ (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2)
    (allowed : (coins && randomAllowed p state) = true) (work span queries : Nat)
    (h : ∀ answer : BitVec (8 * (state.getReg .x11).toNat), ∀ result ∈ support
      (runBody children canFork image p coins fuel
        (protectWrites p state (Riscv.writeBits state (state.getReg .x10) answer))),
        (result.val.work ≤ work ∧ result.val.span ≤ span ∧ result.val.oracleCalls ≤ queries))
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)),
    (out.val.work ≤ 1 + ((state.getReg .x11).toNat + 7) / 8 + work ∧
      out.val.span ≤ 1 + ((state.getReg .x11).toNat + 7) / 8 + span ∧ out.val.oracleCalls ≤ queries) := @CommitGolfDepth.Span.Proofs.runBody_random_bounds

end CommitGolf.Challenge
