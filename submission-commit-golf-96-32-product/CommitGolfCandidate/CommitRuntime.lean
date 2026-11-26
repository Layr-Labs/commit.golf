import CommitGolfCandidate.CommitInput

/-! Exact execution and resources of the actual commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] execute commitBody

/-- Compose post-random register setup with complete tree construction. -/
private theorem ready_body (state : MachineState) (pc : state.pc = 4216)
    (leaves : CommitLeavesInvariant (commitReadyState state) (2 ^ 19))
    (heapPointer : (commitReadyState state).getReg .x9 = BitVec.ofNat 64 4294971424)
    (leafHeapStart : (commitReadyState state).getReg .x23 = BitVec.ofNat 64 (4294971424 + 48 * 2 ^ 24))
    (output : ∀ word : Fin 4, accessValid ((commitReadyState state).getReg .x26 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true) (fuel : Nat) :
    execute (submission.image .commit) (4 + (338690065 + fuel)) state true =
      (do let finished ← commitBody (commitReadyState state) (2 ^ 24)
          return ⟨.success, finished, 925892622, 5 * 2 ^ 24 - 1⟩) := by
  rw [commit_ready state pc,
    commit_body (commitReadyState state) 4294971424 leaves heapPointer leafHeapStart
      (by decide) (by decide) output]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation => commitBody (commitReadyState state) (2 ^ 24) >>= continuation)
  funext finished
  simp only [Execution.charge]
  rfl

/-- After the random syscall, setup and complete tree construction succeed for every salt reply. -/
theorem commit_after_random (message : Message) {bits : Nat} (answer : BitVec bits) (fuel : Nat) :
    let setup := commitSetupState (submission.initialState .commit message)
    execute (submission.image .commit) (4 + (338690065 + fuel))
      (writeBits setup (setup.getReg .x10) answer) true =
        (do let finished ← commitBody (commitReadyState (writeBits
              (commitSetupState (submission.initialState .commit message))
              ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer)) (2 ^ 24)
            return ⟨.success, finished, 925892622, 5 * 2 ^ 24 - 1⟩) := by
  dsimp only
  have pc : (writeBits (commitSetupState (submission.initialState .commit message))
      ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer).pc = 4216 := by
    rw [writeBits_pc, commit_setup_pc _ rfl]; rfl
  have leafHeap : (commitInputReady message answer).getReg .x23 =
      BitVec.ofNat 64 (4294971424 + 48 * 2 ^ 24) := by
    rw [(commit_input_registers message answer).2.2.2.1]; rfl
  exact ready_body _ pc (commit_input_leaves message answer)
    (commit_input_registers message answer).2.1 leafHeap (commit_input_root message answer) fuel

/-- Exact distribution of the actual commitment machine, including private 128-bit salts. -/
def commitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← commitBody (commitInputReady message answer) (2 ^ 24)
  return ⟨.success, finished, 959447084, 5 * 2 ^ 24 - 1⟩

set_option maxRecDepth 4096 in
/-- Exact execution from the real ABI, including salt generation and all setup. -/
theorem commit_execute (message : Message) (fuel : Nat) :
    execute (submission.image .commit) (338690099 + fuel)
      (submission.initialState .commit message) true = commitExecution message := by
  let initial := submission.initialState .commit message
  let setup := commitSetupState initial
  have regs := commit_setup_registers initial
  have setupPC : setup.pc = 4212 := commit_setup_pc initial rfl
  have valid : randomArgumentsValid setup = true := by
    unfold randomArgumentsValid
    rw [regs.2.2.2.1, regs.2.2.2.2.1]
    have heap : initial.getReg .x12 = (4294971424 : Word) := rfl
    rw [heap]
    have sum : (4294971424 : Word) + 1610612736 = 5905584160#64 := rfl
    rw [sum]
    rfl
  rw [show 338690099 + fuel = 29 + (1 + (4 + (338690065 + fuel))) by omega,
    commit_setup _ rfl, commit_random setup setupPC regs.1 valid]
  simp only [commitExecution, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  rw [commit_after_random message answer fuel]
  simp only [bind_assoc, pure_bind, commitInputReady]
  apply congrArg (fun continuation => commitBody (commitReadyState
    (writeBits setup (setup.getReg .x10) answer)) (2 ^ 24) >>= continuation)
  funext finished
  have bytes : (setup.getReg .x11).toNat = 268435456 := by rw [regs.2.2.2.2.1]; rfl
  simp only [Execution.charge, bytes]
  rfl

private theorem run_commit (candidate : Submission) (message : Message) :
    candidate.run .commit message = execute (candidate.image .commit) (candidate.steps .commit)
      (candidate.initialState .commit message) true := rfl

/-- The submitted commitment's full instruction allowance reaches the exact
successful execution above. -/
theorem commit_execution (message : Message) : submission.run .commit message = commitExecution message := by
  rw [run_commit]
  have allowance : submission.steps .commit = 338690099 + 8251245517 := by decide
  rw [allowance, commit_execute]

/-- Exact machine resources for every commitment, before interpreting oracle calls. -/
theorem commit_input_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 959447084 ∧ result.oracleCalls = 83886079 := by
  rw [commit_execution] at reachable
  simp only [commitExecution, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, finished, _, rfl⟩ := reachable
  exact ⟨rfl, rfl, rfl⟩

end CommitGolfCandidate
