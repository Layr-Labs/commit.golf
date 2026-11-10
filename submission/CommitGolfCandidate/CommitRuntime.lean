import CommitGolfCandidate.CommitInput

/-! Exact execution and resources of the actual commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] execute commitBody

/-- Compose scratch setup with tree construction while the loop length is symbolic. -/
private theorem ready_body (state : MachineState) (count : Nat)
    (pc : state.pc = 4240) (positive : 2 ≤ count) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant (commitReadyState state) count)
    (total : (commitReadyState state).getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers ((commitReadyState state).getReg .x9) (count - 1))
    (root : ∀ word : Fin 4, accessValid ((commitReadyState state).getReg .x9 +
      BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (output : ∀ word : Fin 4, accessValid ((commitReadyState state).getReg .x26 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true) (fuel : Nat) :
    execute (submission.image .commit) (10 + (102 * count + 9 + fuel)) state true =
      (do let finished ← commitBody (commitReadyState state) count
          return ⟨.success, finished, 165 * count + 12, 9 * count - 1⟩) := by
  rw [commit_ready state pc,
    commit_body (commitReadyState state) count positive bounded leaves total parents root output]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation => commitBody (commitReadyState state) count >>= continuation)
  funext finished
  simp only [Execution.charge]
  congr 1
  congr 1 <;> omega

/-- After the random syscall, scratch initialization and complete tree construction
succeed for every possible salt buffer. -/
theorem commit_after_random (message : Message) {bits : Nat} (answer : BitVec bits) (fuel : Nat) :
    let setup := commitSetupState (submission.initialState .commit message)
    execute (submission.image .commit) (10 + (102 * 2 ^ 24 + 9 + fuel))
      (writeBits setup (setup.getReg .x10) answer) true =
        (do let finished ← commitBody (commitReadyState (writeBits
              (commitSetupState (submission.initialState .commit message))
              ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer)) (2 ^ 24)
            return ⟨.success, finished, 165 * 2 ^ 24 + 12, 9 * 2 ^ 24 - 1⟩) := by
  dsimp only
  have pc : (writeBits (commitSetupState (submission.initialState .commit message))
      ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer).pc = 4240 := by
    simp only [writeBits, MachineState.setPC]
    rw [commit_setup_pc _ rfl]; rfl
  have root := commit_input_root message answer
  exact ready_body _ (2 ^ 24) pc (by decide) (by decide)
    (commit_input_leaves message answer) (commit_input_registers message answer).2.2.2.1
    (commit_input_parents message answer) root.1 root.2 fuel

/-- Exact distribution of the actual commitment machine, including private salts. -/
def commitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← commitBody (commitInputReady message answer) (2 ^ 24)
  return ⟨.success, finished, 169 * 2 ^ 24 + 28, 9 * 2 ^ 24 - 1⟩

set_option maxRecDepth 4096 in
/-- Exact execution from the real ABI, including salt generation and all setup.
Additional instruction fuel does not change the successful result. -/
theorem commit_execute (message : Message) (fuel : Nat) :
    execute (submission.image .commit) (102 * 2 ^ 24 + 35 + fuel)
      (submission.initialState .commit message) true = commitExecution message := by
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
  rw [show 102 * 2 ^ 24 + 35 + fuel = 15 + (1 + (10 + (102 * 2 ^ 24 + 9 + fuel))) by omega,
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
  have allowance : submission.steps .commit = 102 * 2 ^ 24 + 35 + 6878659549 := by decide
  rw [allowance, commit_execute]

/-- Exact machine resources for every commitment, before interpreting oracle calls.
These counts include the private-randomness syscall's work. -/
theorem commit_input_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 2835349532 ∧ result.oracleCalls = 150994943 := by
  rw [commit_execution] at reachable
  simp only [commitExecution, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, finished, _, rfl⟩ := reachable
  exact ⟨rfl, rfl, rfl⟩

end CommitGolfCandidate
