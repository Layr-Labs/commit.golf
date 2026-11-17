import CommitGolfCandidate.CommitInput
import CommitGolfCandidate.UnrolledTree

/-! Exact execution and resources of the actual commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096

attribute [local irreducible] execute commitBody

/-- Compose moving-chain setup with tree construction while the loop length is symbolic. -/
private theorem ready_body (state : MachineState) (count groups leafGroups : Nat)
    (pc : state.pc = 4240) (evenCount : count = 83886 * groups + 16)
    (leafCount : count = 64 * (leafGroups + 1)) (positive : 0<groups) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant (commitReadyState state) count)
    (heapWindow : ((commitReadyState state).getReg .x23).toNat+32*count=
      ((commitReadyState state).getReg .x22).toNat)
    (total : (commitReadyState state).getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers ((commitReadyState state).getReg .x9) (count - 1))
    (root : ∀ word : Fin 4, accessValid ((commitReadyState state).getReg .x9 +
      BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (output : ∀ word : Fin 4, accessValid ((commitReadyState state).getReg .x26 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true) (fuel : Nat) :
    execute (submission.image .commit)
        (11 + (1989 * (leafGroups + 1) + 251660 * groups + 66 + fuel)) state true =
      (do let finished ← commitBody (commitReadyState state) count
          return ⟨.success, cursorBaseFrame finished (state.getReg .x8),
            5573 * (leafGroups + 1) + 838862 * groups + 182, 9 * count - 1⟩) := by
  have initialFrame := cursor_initial_frame (commitReadyState state) (state.getReg .x8)
    (commit_ready_register state .x8 (by decide) (by decide) (by decide))
    (commit_ready_counters state).1 (commit_ready_input state)
    (commit_ready_counters state).2
  have scheduleCount : count=group341Schedule.parents groups+1 := by
    rw [group341_schedule_parents]
    omega
  have bodyRun := unrolled_schedule_linked_body group341Schedule group341_schedule_valid
    group341_schedule_entry contiguous_image_salt contiguous_image_prefix contiguous_image_tail
    group341_image_fetched
    (commitReadyState state) count groups leafGroups (state.getReg .x8) scheduleCount leafCount
    bounded positive leaves
    heapWindow total parents root output fuel
  simp only [group341_schedule_instructions,group341_schedule_cycles,Nat.add_assoc,
    show (49:Nat)+17=66 by decide,show (154:Nat)+17=171 by decide] at bodyRun
  rw [initialFrame] at bodyRun
  rw [commit_ready_linked state pc]
  simp only [Nat.add_assoc]
  rw [bodyRun]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation => commitBody (commitReadyState state) count >>= continuation)
  funext finished
  simp only [Execution.charge]
  congr 1
  congr 1 <;> omega

/-- After the random syscall, moving-chain initialization and complete tree construction
succeed for every possible salt buffer. -/
theorem commit_after_random (message : Message) {bits : Nat} (answer : BitVec bits) (fuel : Nat) :
    let setup := commitSetupState (submission.initialState .commit message)
    execute (submission.image .commit) (11 + (1989 * (262143 + 1) + 251660 * 200 + 66 + fuel))
      (writeBits setup (setup.getReg .x10) answer) true =
        (do let finished ← commitBody (commitReadyState (writeBits
              (commitSetupState (submission.initialState .commit message))
              ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer)) (2 ^ 24)
            return ⟨.success, cursorBaseFrame finished 4096, 5573 * (262143 + 1) + 838862 * 200 + 182, 9 * 2 ^ 24 - 1⟩) := by
  dsimp only
  have pc : (writeBits (commitSetupState (submission.initialState .commit message))
      ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer).pc = 4240 := by
    simp only [writeBits, MachineState.setPC]
    rw [commit_setup_pc _ rfl]; rfl
  have root := commit_input_root message answer
  have source : (writeBits (commitSetupState (submission.initialState .commit message))
      ((commitSetupState (submission.initialState .commit message)).getReg .x10) answer).getReg .x8 =
      (4096 : Word) := by
    rw [writeBits_register, (commit_setup_registers _).2.1]
    rfl
  simpa only [source] using ready_body _ (2 ^ 24) 200 262143 pc (by decide) (by decide)
    (by decide) (by decide)
    (commit_input_leaves message answer) (commit_input_heap_window message answer)
    (commit_input_registers message answer).2.2.2.1
    (commit_input_parents message answer) root.1 root.2 fuel

/-- Exact distribution of the actual commitment machine, including private salts. -/
def commitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← commitBody (commitInputReady message answer) (2 ^ 24)
  return ⟨.success, cursorBaseFrame finished 4096,
    5573 * (262143 + 1) + 3 * 2 ^ 24 + 838862 * 200 + 195, 9 * 2 ^ 24 - 1⟩

set_option maxRecDepth 4096 in
/-- Exact execution from the real ABI, including salt generation and all setup.
Additional instruction fuel does not change the successful result. -/
theorem commit_execute (message : Message) (fuel : Nat) :
    execute (submission.image .commit) (1989 * (262143 + 1) + 251660 * 200 + 90 + fuel)
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
  rw [show 1989 * (262143 + 1) + 251660 * 200 + 90 + fuel =
      12 + (1 + (11 + (1989 * (262143 + 1) + 251660 * 200 + 66 + fuel))) by omega,
    commit_setup _ rfl, commit_random setup setupPC regs.1 valid]
  simp only [commitExecution, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  rw [commit_after_random message answer fuel]
  simp only [bind_assoc, pure_bind, commitInputReady]
  apply congrArg (fun continuation => commitBody (commitReadyState
    (writeBits setup (setup.getReg .x10) answer)) (2 ^ 24) >>= continuation)
  funext finished
  have bytes : (setup.getReg .x11).toNat = 402653184 := by rw [regs.2.2.2.2.1]; rfl
  simp only [Execution.charge, bytes]
  rfl

private theorem run_commit (candidate : Submission) (message : Message) :
    candidate.run .commit message = execute (candidate.image .commit) (candidate.steps .commit)
      (candidate.initialState .commit message) true := rfl

/-- The submitted commitment's full instruction allowance reaches the exact
successful execution above; no truncation is used to obtain the cost bound. -/
theorem commit_execution (message : Message) : submission.run .commit message = commitExecution message := by
  rw [run_commit]
  have allowance : submission.steps .commit =
      1989 * (262143 + 1) + 251660 * 200 + 90 + 8018199110 := by decide
  rw [allowance, commit_execute]

/-- Exact machine resources for every commitment, before interpreting oracle calls.
These counts include the private-randomness syscall's work. -/
theorem commit_input_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 1679032755 ∧ result.oracleCalls = 150994943 := by
  rw [commit_execution] at reachable
  simp only [commitExecution, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, finished, _, rfl⟩ := reachable
  exact ⟨rfl, rfl, rfl⟩

end CommitGolfCandidate
