import CommitGolfCandidate.S3TreeExec

/-! Exact execution and resources of the actual commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000

attribute [local irreducible] execute s3CommitBody

/-- Exact execution from the real ABI: 12 setup instructions, the random syscall (the 32-byte
seed), 11 readiness instructions, then the nonce generator, the leaf phase, the parent sweep and
the root copy. Additional instruction fuel does not change the successful result. -/
theorem commit_execute (message : Message) (fuel : Nat) :
    execute (submission.image .commit) (216166231 + fuel)
      (submission.initialState .commit message) true = s3CommitExecution message := by
  let initial := submission.initialState .commit message
  let setup := commitSetupState initial
  have regs := commit_setup_registers initial
  have setupPC : setup.pc = 4236 := commit_setup_pc initial rfl
  have valid : randomArgumentsValid setup = true := by
    unfold randomArgumentsValid
    rw [regs.2.2.2.1, regs.2.2.2.2.1]
    have heap : initial.getReg .x12 = (4294971424 : Word) := rfl
    rw [heap]
    have sum : (4294971424 : Word) + 1073741824 = 5368713248#64 := rfl
    rw [sum]
    rfl
  rw [show 216166231 + fuel = 12 + (1 + (11 + (9 + 193 * 23832 + 14 + 759 * 2 ^ 18 +
      (7 + 3 * 4194303 + 16384 + 1 + (11 + fuel))))) by omega,
    commit_setup _ rfl, commit_random setup setupPC regs.1 valid]
  simp only [s3CommitExecution, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have pc : (writeBits setup (setup.getReg .x10) answer).pc = 4240 := by
    simp only [writeBits, MachineState.setPC]
    rw [setupPC]
    rfl
  have ready : ((commitReadyState (writeBits setup (setup.getReg .x10) answer)).setReg .x1 4316).setPC
      1011404 = s3CommitReady message answer := rfl
  rw [commit_ready_linked _ pc, ready, s3_body_execute message answer fuel]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun finished => ?_
  have bytes : (setup.getReg .x11).toNat = 32 := by rw [regs.2.2.2.2.1]; rfl
  simp only [Execution.charge, bytes]
  rfl

private theorem run_commit (candidate : Submission) (message : Message) :
    candidate.run .commit message = execute (candidate.image .commit) (candidate.steps .commit)
      (candidate.initialState .commit message) true := rfl

/-- The submitted commitment's full instruction allowance reaches the exact
successful execution above; no truncation is used to obtain the cost bound. -/
theorem commit_execution (message : Message) :
    submission.run .commit message = s3CommitExecution message := by
  rw [run_commit]
  have allowance : submission.steps .commit = 216166231 + 8373769385 := by decide
  rw [allowance, commit_execute]

/-- Exact machine resources for every commitment, before interpreting oracle calls.
These counts include the private-randomness syscall's work. -/
theorem commit_input_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 520444244 ∧ result.oracleCalls = 43468287 := by
  rw [commit_execution] at reachable
  simp only [s3CommitExecution, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, finished, _, rfl⟩ := reachable
  exact ⟨rfl, rfl, rfl⟩

end CommitGolfCandidate
