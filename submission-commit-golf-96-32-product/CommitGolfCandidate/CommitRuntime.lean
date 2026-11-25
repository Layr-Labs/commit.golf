import CommitGolfCandidate.CommitInput

/-! Exact execution and resources of the actual commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] execute commitBody

/-- Compose scratch setup with tree construction. -/
private theorem ready_body (state : MachineState) (pc : state.pc = 4212)
    (leaves : CommitLeavesInvariant (commitReadyState state) (2 ^ 19))
    (heapPointer : (commitReadyState state).getReg .x9 = BitVec.ofNat 64 4294971424)
    (output : ∀ word : Fin 4, accessValid ((commitReadyState state).getReg .x26 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true) (fuel : Nat) :
    execute (submission.image .commit) (10 + (393216022 + fuel)) state true =
      (do let finished ← commitBody (commitReadyState state) (2 ^ 24)
          return ⟨.success, finished, 980418585, 5 * 2 ^ 24 - 1⟩) := by
  rw [commit_ready state pc,
    commit_body (commitReadyState state) 4294971424 leaves heapPointer (by decide) (by decide) output]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation => commitBody (commitReadyState state) (2 ^ 24) >>= continuation)
  funext finished
  simp only [Execution.charge]
  congr 1

/-- After the random syscall, scratch initialization and complete tree construction
succeed for every possible salt buffer. -/
theorem commit_after_random (message : Message) {bits : Nat} (answer : BitVec bits) (fuel : Nat) :
    let setup := commitSetupState (submission.initialState .commit message)
    execute (submission.image .commit) (10 + (393216022 + fuel))
      (writeBits setup (setup.getReg .x10) answer) true =
        (do let finished ← commitBody (commitReadyState (writeBits
              (commitSetupState (submission.initialState .commit message))
              ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer)) (2 ^ 24)
            return ⟨.success, finished, 980418585, 5 * 2 ^ 24 - 1⟩) := by
  dsimp only
  have pc : (writeBits (commitSetupState (submission.initialState .commit message))
      ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer).pc = 4212 := by
    simp only [writeBits, MachineState.setPC]
    rw [commit_setup_pc _ rfl]; rfl
  exact ready_body _ pc (commit_input_leaves message answer)
    (commit_input_registers message answer).2.1 (commit_input_root message answer) fuel

/-- Exact distribution of the actual commitment machine, including private salts. -/
def commitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← commitBody (commitInputReady message answer) (2 ^ 24)
  return ⟨.success, finished, 1047527478, 5 * 2 ^ 24 - 1⟩

set_option maxRecDepth 4096 in
/-- Exact execution from the real ABI, including salt generation and all setup.
Additional instruction fuel does not change the successful result. -/
theorem commit_execute (message : Message) (fuel : Nat) :
    execute (submission.image .commit) (393216061 + fuel)
      (submission.initialState .commit message) true = commitExecution message := by
  let initial := submission.initialState .commit message
  let setup := commitSetupState initial
  have regs := commit_setup_registers initial
  have setupPC : setup.pc = 4208 := commit_setup_pc initial rfl
  have valid : randomArgumentsValid setup = true := by
    unfold randomArgumentsValid
    rw [regs.2.2.2.1, regs.2.2.2.2.1]
    have heap : initial.getReg .x12 = (4294971424 : Word) := rfl
    rw [heap]
    have sum : (4294971424 : Word) + 1610612736 = 5905584160#64 := rfl
    rw [sum]
    rfl
  have hsteps : 393216061 + fuel = 28 + (1 + (10 + (393216022 + fuel))) := by
    have hc : 393216061 = 28 + (1 + (10 + 393216022)) := rfl
    rw [hc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
  rw [hsteps,
    commit_setup _ rfl, commit_random setup setupPC regs.1 valid]
  simp only [commitExecution, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  rw [commit_after_random message answer fuel]
  simp only [bind_assoc, pure_bind, commitInputReady]
  apply congrArg (fun continuation => commitBody (commitReadyState
    (writeBits setup (setup.getReg .x10) answer)) (2 ^ 24) >>= continuation)
  funext finished
  have bytes : (setup.getReg .x11).toNat = 536870912 := by rw [regs.2.2.2.2.1]; rfl
  simp only [Execution.charge, bytes]
  rfl

private theorem run_commit (candidate : Submission) (message : Message) :
    candidate.run .commit message = execute (candidate.image .commit) (candidate.steps .commit)
      (candidate.initialState .commit message) true := rfl

/-- The submitted commitment's full instruction allowance reaches the exact
successful execution above; no truncation is used to obtain the cost bound. -/
theorem commit_execution (message : Message) : submission.run .commit message = commitExecution message := by
  rw [run_commit]
  have allowance : submission.steps .commit = 393216061 + 8196719555 := by decide
  rw [allowance, commit_execute]

/-- Exact machine resources for every commitment, before interpreting oracle calls.
These counts include the private-randomness syscall's work. -/
theorem commit_input_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 1047527478 ∧ result.oracleCalls = 83886079 := by
  rw [commit_execution] at reachable
  simp only [commitExecution, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, finished, _, rfl⟩ := reachable
  exact ⟨rfl, rfl, rfl⟩

end CommitGolfCandidate
