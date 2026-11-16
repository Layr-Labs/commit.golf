import CommitGolfCandidate.CommitOutput
import CommitGolfCandidate.CountingCoins

/-! Transfer commitment contents from fixed-oracle evaluation to the actual
probabilistic runner, retaining its independently counted public queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem deterministic_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β)
    (first : oracle.run computation = pure (checkEvaluation oracle computation))
    (second : ∀ value, oracle.run (continuation value) = pure (checkEvaluation oracle (continuation value))) :
    oracle.run (computation >>= continuation) = pure (checkEvaluation oracle (computation >>= continuation)) := by
  rw [oracle_run_bind, first, check_evaluation_bind]
  simp only [pure_bind, second]

private theorem deterministic_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (checkEvaluation oracle (pure value)) := by
  rw [oracle_run_pure, check_evaluation_pure]

/-- The leaf hash uses only public queries once its salt is supplied. -/
theorem commit_leaf_loop_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (commitLeafLoop state count) = pure (checkEvaluation oracle (commitLeafLoop state count)) := by
  induction count generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [commitLeafLoop, oracle_run_public_bind, check_evaluation_public_bind, ih]
    simp only [pure_bind]

/-- Salt copying, leaf hashing, and heap storage add no private randomness. -/
theorem commit_position_deterministic (oracle : Oracle) (state : MachineState) :
    oracle.run (commitPositionRun state) = pure (checkEvaluation oracle (commitPositionRun state)) := by
  unfold commitPositionRun
  exact deterministic_bind oracle _ _ (commit_leaf_loop_deterministic oracle _ 8)
    (fun leaf => deterministic_pure oracle _)

/-- After salt sampling, the full leaf loop is deterministic for a fixed oracle. -/
theorem commit_leaves_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (commitLeaves state count) = pure (checkEvaluation oracle (commitLeaves state count)) := by
  induction count generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [commitLeaves]
    exact deterministic_bind oracle _ _ (commit_position_deterministic oracle state) ih

/-- Parent construction is deterministic for the same fixed oracle. -/
theorem commit_parents_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (commitParents state count) = pure (checkEvaluation oracle (commitParents state count)) := by
  induction count generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [commitParents, oracle_run_public_bind, check_evaluation_public_bind, ih]
    simp only [pure_bind]

/-- The entire commitment body makes no additional coin requests. -/
theorem commit_body_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (commitBody state count) = pure (checkEvaluation oracle (commitBody state count)) := by
  unfold commitBody
  apply deterministic_bind oracle _ _ (commit_leaves_deterministic oracle state count)
  intro leaves
  exact deterministic_bind oracle _ _ (commit_parents_deterministic oracle _ _)
    (fun parents => deterministic_pure oracle _)

attribute [local irreducible] commitBody commitInputReady checkEvaluation

/-- The exact salt sampler requested by the commitment image's RANDOM syscall. -/
def commitSaltCoins (message : Message) :
    ProbComp (BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat)) :=
  $ᵗ BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat)

private def packCommitResult (body : MachineState × Nat) : Execution × Nat :=
  (⟨.success, body.1, 236*LENGTH+36, 9*LENGTH-1⟩, body.2)

private theorem pack_commit_state (body : MachineState × Nat) :
    (packCommitResult body).1.state = body.1 := rfl

/-- The deterministic result after one salt reply, including both counters. -/
def commitFinalResult (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) : Execution × Nat :=
  packCommitResult (checkEvaluation oracle (commitBody (commitInputReady message answer) LENGTH))

/-- The actual commitment distribution samples its salt vector once, then runs the
proved deterministic body. The query counter is the runner's counter throughout. -/
theorem commit_run_distribution (oracle : Oracle) (message : Message) :
    oracle.run (submission.run .commit message) =
      (commitSaltCoins message >>= fun answer => pure (commitFinalResult oracle message answer)) := by
  rw [commit_execution]
  unfold commitExecution commitSaltCoins commitFinalResult packCommitResult
  rw [oracle_run_coins_bind]
  simp only [oracle_run_bind, commit_body_deterministic, pure_bind, oracle_run_pure, Nat.add_zero]
  rfl

private theorem commit_final_state (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) :
    (commitFinalResult oracle message answer).1.state =
      (checkEvaluation oracle (commitBody (commitInputReady message answer) LENGTH)).1 :=
  pack_commit_state _

private theorem commit_body_matches_sized (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 256*LENGTH) :
    CommittedState oracle message
      (checkEvaluation oracle (commitBody (commitInputReady message answer) LENGTH)).1 := by
  subst bits
  exact commit_body_matches oracle message answer

private theorem commit_final_matches (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 256*LENGTH) :
    CommittedState oracle message (commitFinalResult oracle message answer).1.state := by
  rw [commit_final_state]
  exact commit_body_matches_sized oracle message answer width

private theorem salt_width (setup : MachineState) (bytes : setup.getReg .x11 = 536870912) :
    8*(setup.getReg .x11).toNat = 256*LENGTH := by
  rw [bytes]
  rfl

private theorem setup_salt_width (state : MachineState) :
    8*((commitSetupState state).getReg .x11).toNat = 256*LENGTH :=
  salt_width _ (commit_setup_registers state).2.2.2.2.1

private theorem sampled_witness {α β : Type} (coins : ProbComp α) (output : α → β)
    (result : β) (reachable : result ∈ support (coins >>= fun answer => pure (output answer))) :
    ∃ answer, result = output answer := by
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, equal⟩ := reachable
  exact ⟨answer, equal⟩

attribute [local irreducible] commitSetupState Submission.initialState submission
  CommittedState commitSaltCoins commitFinalResult

/-- Every returned result originates from an actual salt reply and deterministic body. -/
theorem commit_run_origin (oracle : Oracle) (message : Message) (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (submission.run .commit message))) :
    ∃ answer : BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat),
      result = commitFinalResult oracle message answer := by
  have sampled := (congrArg (fun computation : ProbComp (Execution × Nat) =>
    result ∈ support computation) (commit_run_distribution oracle message)).mp reachable
  exact sampled_witness (commitSaltCoins message) (commitFinalResult oracle message) result sampled

/-- Every possible actual commitment output has the required root/heap contents. -/
theorem commit_run_matches (oracle : Oracle) (message : Message) (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (submission.run .commit message))) :
    CommittedState oracle message result.1.state := by
  obtain ⟨answer, same⟩ := commit_run_origin oracle message result reachable
  rw [same]
  exact commit_final_matches oracle message answer
    (setup_salt_width (submission.initialState .commit message))

/-- The RANDOM syscall requests one 256-bit salt for each vector position. -/
theorem commit_salt_width (message : Message) :
    8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat =
      256*LENGTH := setup_salt_width _

/-- Explicit salt contents of the actual final state, for every possible random
reply. Keeping the reply width as a parameter avoids unfolding the large sampler. -/
theorem commit_final_salt (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) (width : bits = 256*LENGTH) (index : Index) :
    readBuffer (commitFinalResult oracle message answer).1.state
      (5368713248+32*index.val) 32 = answer.extractLsb' (256*index.val) 256 := by
  rw [commit_final_state]
  subst bits
  exact commit_body_salt oracle message answer index

/-- Functional correctness together with the identity of the retained salts.
These are deterministic facts about the machine, separate from the hiding bound. -/
theorem commit_final_contents (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) (width : bits = 256*LENGTH) :
    CommittedState oracle message (commitFinalResult oracle message answer).1.state ∧
    ∀ index : Index, readBuffer (commitFinalResult oracle message answer).1.state
      (5368713248+32*index.val) 32 = answer.extractLsb' (256*index.val) 256 :=
  ⟨commit_final_matches oracle message answer width, commit_final_salt oracle message answer width⟩

end CommitGolfCandidate
