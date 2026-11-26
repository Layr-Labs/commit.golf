import CommitGolfDepth.Span
import CommitGolf.Artifact

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

end CommitGolf.Challenge
