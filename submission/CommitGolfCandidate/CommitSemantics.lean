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

/-- One stage-3 leaf makes two public permutation queries and uses no coins. -/
theorem s3_leaf_deterministic (oracle : Oracle) (u : Nat) (state : MachineState) :
    oracle.run (s3Leaf u state) = pure (checkEvaluation oracle (s3Leaf u state)) := by
  unfold s3Leaf
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only [oracle_run_pure, check_evaluation_pure, pure_bind]

theorem s3_group_leaves_deterministic (oracle : Oracle) (state : MachineState) (u count : Nat) :
    oracle.run (s3GroupLeaves state u count) =
      pure (checkEvaluation oracle (s3GroupLeaves state u count)) := by
  induction count generalizing state u with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [s3GroupLeaves]
    exact deterministic_bind oracle _ _ (s3_leaf_deterministic oracle u state) fun next => ih next (u + 1)

theorem s3_group_deterministic (oracle : Oracle) (state : MachineState) :
    oracle.run (s3Group state) = pure (checkEvaluation oracle (s3Group state)) := by
  unfold s3Group
  exact deterministic_bind oracle _ _ (s3_group_leaves_deterministic oracle state 0 64)
    fun leaves => deterministic_pure oracle _

theorem s3_groups_deterministic (oracle : Oracle) (state : MachineState) (groups : Nat) :
    oracle.run (s3Groups state groups) = pure (checkEvaluation oracle (s3Groups state groups)) := by
  induction groups generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ groups ih =>
    rw [s3Groups]
    exact deterministic_bind oracle _ _ (s3_group_deterministic oracle state) ih

/-- After nonce sampling, the full leaf phase is deterministic for a fixed oracle. -/
theorem s3_leaves_deterministic (oracle : Oracle) (state : MachineState) (groups : Nat) :
    oracle.run (s3Leaves state groups) = pure (checkEvaluation oracle (s3Leaves state groups)) := by
  unfold s3Leaves
  exact deterministic_bind oracle _ _ (s3_groups_deterministic oracle _ groups)
    fun hashed => deterministic_pure oracle _

/-- Parent construction is deterministic for the same fixed oracle. -/
theorem commit_parents_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (commitParents state count) = pure (checkEvaluation oracle (commitParents state count)) := by
  induction count generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [commitParents, oracle_run_public_bind, check_evaluation_public_bind, ih]
    simp only [pure_bind]

/-- The entire commitment body makes no additional coin requests. -/
theorem commit_body_deterministic (oracle : Oracle) (state : MachineState) (groups : Nat) :
    oracle.run (s3CommitBody state groups) =
      pure (checkEvaluation oracle (s3CommitBody state groups)) := by
  unfold s3CommitBody
  apply deterministic_bind oracle _ _ (s3_leaves_deterministic oracle state groups)
  intro leaves
  exact deterministic_bind oracle _ _ (commit_parents_deterministic oracle _ _)
    (fun parents => deterministic_pure oracle _)

attribute [local irreducible] s3CommitBody s3CommitReady checkEvaluation

/-- The exact nonce sampler requested by the commitment image's RANDOM syscall. -/
def commitSaltCoins (message : Message) :
    ProbComp (BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat)) :=
  $ᵗ BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat)

private def packCommitResult (body : MachineState × Nat) : Execution × Nat :=
  (⟨.success, body.1, 655098341, 3*LENGTH-1⟩, body.2)

private theorem pack_commit_state (body : MachineState × Nat) :
    (packCommitResult body).1.state = body.1 := rfl

/-- The deterministic result after one nonce reply, including both counters. -/
def commitFinalResult (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) : Execution × Nat :=
  packCommitResult (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2 ^ 18)))

/-- The actual commitment distribution samples its nonce vector once, then runs the
proved deterministic body. The query counter is the runner's counter throughout. -/
theorem commit_run_distribution (oracle : Oracle) (message : Message) :
    oracle.run (submission.run .commit message) =
      (commitSaltCoins message >>= fun answer => pure (commitFinalResult oracle message answer)) := by
  rw [commit_execution]
  unfold s3CommitExecution commitSaltCoins commitFinalResult packCommitResult
  rw [oracle_run_coins_bind]
  simp only [oracle_run_bind, commit_body_deterministic, pure_bind, oracle_run_pure, Nat.add_zero]
  rfl

private theorem commit_final_state (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) :
    (commitFinalResult oracle message answer).1.state =
      (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2 ^ 18))).1 :=
  pack_commit_state _

private theorem commit_body_matches_sized (oracle : Oracle)
    (message : Message) {bits : Nat} (answer : BitVec bits) (width : bits = 192*LENGTH) :
    CommittedState oracle message
      (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2 ^ 18))).1 := by
  subst bits
  exact commit_body_matches oracle message answer

private theorem commit_final_matches (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 192*LENGTH) :
    CommittedState oracle message (commitFinalResult oracle message answer).1.state := by
  rw [commit_final_state]
  exact commit_body_matches_sized oracle message answer width

private theorem salt_width (setup : MachineState) (bytes : setup.getReg .x11 = 402653184) :
    8*(setup.getReg .x11).toNat = 192*LENGTH := by
  rw [bytes]
  rfl

private theorem setup_salt_width (state : MachineState) :
    8*((commitSetupState state).getReg .x11).toNat = 192*LENGTH :=
  salt_width _ (commit_setup_registers state).2.2.2.2.1

private theorem sampled_witness {α β : Type} (coins : ProbComp α) (output : α → β)
    (result : β) (reachable : result ∈ support (coins >>= fun answer => pure (output answer))) :
    ∃ answer, result = output answer := by
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, equal⟩ := reachable
  exact ⟨answer, equal⟩

attribute [local irreducible] commitSetupState Submission.initialState submission
  CommittedState commitSaltCoins commitFinalResult

/-- Every returned result originates from an actual nonce reply and deterministic body. -/
theorem commit_run_origin (oracle : Oracle) (message : Message) (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (submission.run .commit message))) :
    ∃ answer : BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat),
      result = commitFinalResult oracle message answer := by
  have sampled := (congrArg (fun computation : ProbComp (Execution × Nat) =>
    result ∈ support computation) (commit_run_distribution oracle message)).mp reachable
  exact sampled_witness (commitSaltCoins message) (commitFinalResult oracle message) result sampled

/-- Every possible actual commitment output has the required root/heap contents. -/
theorem commit_run_matches (oracle : Oracle) (message : Message)
    (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (submission.run .commit message))) :
    CommittedState oracle message result.1.state := by
  obtain ⟨answer, same⟩ := commit_run_origin oracle message result reachable
  rw [same]
  exact commit_final_matches oracle message answer
    (setup_salt_width (submission.initialState .commit message))

/-- The RANDOM syscall requests one 192-bit nonce for each vector position. -/
theorem commit_salt_width (message : Message) :
    8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat =
      192*LENGTH := setup_salt_width _

/-- Explicit nonce contents of the actual final state, for every possible random reply. -/
theorem commit_final_salt (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 192*LENGTH) (index : Index) :
    readNonce (commitFinalResult oracle message answer).1.state
      (5368713248+24*index.val) = expandNonce192 (answer.extractLsb' (192*index.val) 192) := by
  rw [commit_final_state]
  subst bits
  exact commit_body_salt oracle message answer index

/-- Functional correctness together with the identity of the retained nonces. -/
theorem commit_final_contents (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 192*LENGTH) :
    CommittedState oracle message (commitFinalResult oracle message answer).1.state ∧
    ∀ index : Index, readNonce (commitFinalResult oracle message answer).1.state
      (5368713248+24*index.val) = expandNonce192 (answer.extractLsb' (192*index.val) 192) :=
  ⟨commit_final_matches oracle message answer width,
    commit_final_salt oracle message answer width⟩

end CommitGolfCandidate
