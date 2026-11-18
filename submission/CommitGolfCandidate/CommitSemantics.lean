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

/-- One leaf makes two public permutation queries and uses no coins. -/
theorem s3_leaf_deterministic (oracle : Oracle) (l : Nat) (state : MachineState) :
    oracle.run (s3Leaf l state) = pure (checkEvaluation oracle (s3Leaf l state)) := by
  unfold s3Leaf
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only [oracle_run_pure, check_evaluation_pure, pure_bind]

theorem s3_group_leaves_deterministic (oracle : Oracle) (state : MachineState) (l count : Nat) :
    oracle.run (s3GroupLeaves state l count) =
      pure (checkEvaluation oracle (s3GroupLeaves state l count)) := by
  induction count generalizing state l with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [s3GroupLeaves]
    exact deterministic_bind oracle _ _ (s3_leaf_deterministic oracle l state) fun next => ih next (l + 1)

/-- One group call makes one public permutation query and uses no coins. -/
theorem s6_group_call_deterministic (oracle : Oracle) (c : Nat) (state : MachineState) :
    oracle.run (s6GroupCall c state) = pure (checkEvaluation oracle (s6GroupCall c state)) := by
  unfold s6GroupCall
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only [oracle_run_pure, check_evaluation_pure, pure_bind]

theorem s6_group_calls_deterministic (oracle : Oracle) (state : MachineState) (c count : Nat) :
    oracle.run (s6GroupCalls state c count) =
      pure (checkEvaluation oracle (s6GroupCalls state c count)) := by
  induction count generalizing state c with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [s6GroupCalls]
    exact deterministic_bind oracle _ _ (s6_group_call_deterministic oracle c state)
      fun next => ih next (c + 1)

theorem s3_group_deterministic (oracle : Oracle) (state : MachineState) :
    oracle.run (s3Group state) = pure (checkEvaluation oracle (s3Group state)) := by
  unfold s3Group
  exact deterministic_bind oracle _ _ (s3_group_leaves_deterministic oracle _ 0 64)
    fun leaves => deterministic_bind oracle _ _ (s6_group_calls_deterministic oracle leaves 0 16)
      fun grouped => deterministic_pure oracle _

theorem s3_groups_deterministic (oracle : Oracle) (state : MachineState) (groups : Nat) :
    oracle.run (s3Groups state groups) = pure (checkEvaluation oracle (s3Groups state groups)) := by
  induction groups generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ groups ih =>
    rw [s3Groups]
    exact deterministic_bind oracle _ _ (s3_group_deterministic oracle state) ih

/-- One generator call makes one public permutation query and uses no coins. -/
theorem s4_gen_call_deterministic (oracle : Oracle) (state : MachineState) :
    oracle.run (s4GenCall state) = pure (checkEvaluation oracle (s4GenCall state)) := by
  unfold s4GenCall
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only [oracle_run_pure, check_evaluation_pure, pure_bind]

theorem s4_gen_calls_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (s4GenCalls state count) = pure (checkEvaluation oracle (s4GenCalls state count)) := by
  induction count generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ count ih =>
    rw [s4GenCalls]
    exact deterministic_bind oracle _ _ (s4_gen_call_deterministic oracle state) ih

theorem s4_gen_passes_deterministic (oracle : Oracle) (state : MachineState) (passes : Nat) :
    oracle.run (s4GenPasses state passes) =
      pure (checkEvaluation oracle (s4GenPasses state passes)) := by
  induction passes generalizing state with
  | zero => exact deterministic_pure oracle state
  | succ passes ih =>
    rw [s4GenPasses]
    refine deterministic_bind oracle _ _ ?_ ih
    unfold s4GenPass
    exact deterministic_bind oracle _ _ (s4_gen_calls_deterministic oracle state 64)
      fun called => deterministic_pure oracle _

/-- The nonce generator is deterministic for a fixed oracle. -/
theorem s4_generator_deterministic (oracle : Oracle) (state : MachineState) (passes : Nat) :
    oracle.run (s4Generator state passes) =
      pure (checkEvaluation oracle (s4Generator state passes)) :=
  s4_gen_passes_deterministic oracle _ passes

/-- After the seed reply, the generator and the full leaf phase are deterministic for a fixed
oracle. -/
theorem s3_leaves_deterministic (oracle : Oracle) (state : MachineState) (groups : Nat) :
    oracle.run (s3Leaves state groups) = pure (checkEvaluation oracle (s3Leaves state groups)) := by
  unfold s3Leaves
  exact deterministic_bind oracle _ _ (s4_generator_deterministic oracle state 23832)
    fun filled => s3_groups_deterministic oracle _ groups

/-- The entire commitment body makes no additional coin requests. -/
theorem commit_body_deterministic (oracle : Oracle) (state : MachineState) (groups : Nat) :
    oracle.run (s3CommitBody state groups) =
      pure (checkEvaluation oracle (s3CommitBody state groups)) := by
  unfold s3CommitBody
  apply deterministic_bind oracle _ _ (s3_leaves_deterministic oracle state groups)
  intro leaves
  exact deterministic_bind oracle _ _ (s6_parents_deterministic oracle _)
    (fun parents => deterministic_pure oracle _)

attribute [local irreducible] s3CommitBody s3CommitReady checkEvaluation

/-- The exact seed sampler requested by the commitment image's RANDOM syscall (32 bytes). -/
def commitSaltCoins (message : Message) :
    ProbComp (BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat)) :=
  $ᵗ BitVec (8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat)

private def packCommitResult (body : MachineState × Nat) : Execution × Nat :=
  (⟨.success, body.1, 524638547, 43468287⟩, body.2)

private theorem pack_commit_state (body : MachineState × Nat) :
    (packCommitResult body).1.state = body.1 := rfl

/-- The deterministic result after one seed reply, including both counters. -/
def commitFinalResult (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) : Execution × Nat :=
  packCommitResult (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2 ^ 18)))

/-- The actual commitment distribution samples its seed once, then runs the proved
deterministic body (generator included). The query counter is the runner's counter throughout. -/
theorem commit_run_distribution (oracle : Oracle) (message : Message) :
    oracle.run (submission.run .commit message) =
      (commitSaltCoins message >>= fun answer => pure (commitFinalResult oracle message answer)) := by
  rw [commit_execution]
  unfold s3CommitExecution commitSaltCoins commitFinalResult packCommitResult
  rw [oracle_run_coins_bind]
  simp only [oracle_run_bind, commit_body_deterministic, pure_bind, oracle_run_pure, Nat.add_zero]

private theorem commit_final_state (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) :
    (commitFinalResult oracle message answer).1.state =
      (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2 ^ 18))).1 :=
  pack_commit_state _

private theorem commit_body_matches_sized (oracle : Oracle)
    (message : Message) {bits : Nat} (answer : BitVec bits) (width : bits = 256) :
    CommittedState oracle message
      (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2 ^ 18))).1 := by
  subst bits
  exact commit_body_matches oracle message answer

private theorem commit_final_matches (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 256) :
    CommittedState oracle message (commitFinalResult oracle message answer).1.state := by
  rw [commit_final_state]
  exact commit_body_matches_sized oracle message answer width

private theorem salt_width (setup : MachineState) (bytes : setup.getReg .x11 = 32) :
    8*(setup.getReg .x11).toNat = 256 := by
  rw [bytes]
  rfl

private theorem setup_salt_width (state : MachineState) :
    8*((commitSetupState state).getReg .x11).toNat = 256 :=
  salt_width _ (commit_setup_registers state).2.2.2.2.1

private theorem sampled_witness {α β : Type} (coins : ProbComp α) (output : α → β)
    (result : β) (reachable : result ∈ support (coins >>= fun answer => pure (output answer))) :
    ∃ answer, result = output answer := by
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, equal⟩ := reachable
  exact ⟨answer, equal⟩

attribute [local irreducible] commitSetupState Submission.initialState submission
  CommittedState commitSaltCoins commitFinalResult

/-- Every returned result originates from an actual seed reply and deterministic body. -/
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

/-- The RANDOM syscall requests the 256-bit seed. -/
theorem commit_salt_width (message : Message) :
    8*((commitSetupState (submission.initialState .commit message)).getReg .x11).toNat =
      256 := setup_salt_width _

/-- Explicit nonce contents of the actual final state, for every possible seed reply: the
generated nonces. -/
theorem commit_final_nonce (oracle : Oracle) (message : Message)
    {bits : Nat} (answer : BitVec bits) (width : bits = 256) (index : Index) :
    committedNonce (commitFinalResult oracle message answer).1.state index =
      s4GenNonce oracle.permutation (answer.cast width) index := by
  rw [commit_final_state]
  subst width
  rw [BitVec.cast_eq]
  exact commit_body_nonce oracle message answer index

/-- Functional correctness together with the identity of the retained nonces. -/
theorem commit_final_contents (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) (width : bits = 256) :
    CommittedState oracle message (commitFinalResult oracle message answer).1.state ∧
    ∀ index : Index, committedNonce (commitFinalResult oracle message answer).1.state index =
        s4GenNonce oracle.permutation (answer.cast width) index :=
  ⟨commit_final_matches oracle message answer width,
    commit_final_nonce oracle message answer width⟩

end CommitGolfCandidate
