import CommitGolfCandidate.QuadNonceCommitMemory
import CommitGolfCandidate.QuadCommitMeaning
import CommitGolfCandidate.QuadNonceSpec

/-! The complete quad3 + NonceChain commit: execution of the actual image, exact resources,
the seed-keyed output distribution and the serialized trapdoor facts at the chain salts. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure fixedOracleRun
  fixed_oracle_run_map oracle_run_bind oracle_run_pure)
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local irreducible] image body checkEvaluation Leaves.groups Quads.groups Quad2s.groups Quad3s.groups packedParentGroups
  readBuffer rootPrefix Chain.expansion Chain.seedSetup Chain.seedWritten Chain.chainFinish

/-- Seed draw, generator, then the W3 tree phase from the generator's leaf-entry state. -/
def nonceCommitTrace (initial : MachineState) : OracleComp World Execution := do
  let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
  let last ← Chain.expansion initial k
  let state ← body (Chain.chainFinish last)
  return ⟨.success,state,493165594,40846847⟩

private theorem body_charge (s : MachineState) :
    (⟨.success,s,477889253,39321599⟩ : Execution).charge 15276324 Chain.nonceChainCount =
      ⟨.success,s,493165577,40846847⟩ := by
  have cost : 15276324+477889253=493165577 := by norm_num
  have calls : Chain.nonceChainCount+39321599=40846847 := by norm_num [Chain.nonceChainCount]
  simp only [Execution.charge,cost,calls]

private theorem seed_charge (s : MachineState) :
    ((⟨.success,s,493165577,40846847⟩ : Execution).charge 4 0).charge 13 0 =
      ⟨.success,s,493165594,40846847⟩ := by
  have cost : 13+(4+493165577)=493165594 := by norm_num
  simp only [Execution.charge,cost,Nat.zero_add]

private theorem seeded_execution (initial : MachineState) (entry : CommitEntry initial)
    (k : BitVec 192) (fuel : Nat) :
    execute image (4599588+(202638060+fuel)) (Chain.seedWritten initial k) true =
      (do let last ← Chain.expansion initial k
          let state ← body (Chain.chainFinish last)
          return ⟨.success,state,493165577,40846847⟩) := by
  rw [Chain.after_draw initial entry k (202638060+fuel)]
  apply bind_congr_of_forall_mem_support
  intro last reached
  have r := (Chain.expansion_post initial entry k last reached).2
  rw [execute_after_ready (Chain.chainFinish last) r fuel]
  simp only [bind_assoc,pure_bind,body_charge]

/-- The actual image runs the intended trace in 207237662 instruction steps. -/
theorem execute_nonce_commit (initial : MachineState) (entry : CommitEntry initial) (fuel : Nat) :
    execute image (207237662+fuel) initial true = nonceCommitTrace initial := by
  have clock : 207237662+fuel=13+(1+(4599588+(202638060+fuel))) := by omega
  rw [clock,Chain.seed_run initial entry.pc,Chain.seed_draw initial entry]
  simp only [nonceCommitTrace,bind_assoc,pure_bind]
  apply bind_congr
  intro k
  rw [seeded_execution initial entry k fuel]
  simp only [bind_assoc,pure_bind,seed_charge]

attribute [local irreducible] nonceCommitTrace

theorem program_nonce_commit_run (program : Submission) (code : program.image .commit=image)
    (enough : 207237662≤program.steps .commit) (message : Message)
    (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message=nonceCommitTrace (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit) (program.initialState .commit message) true=_
  rw [code,show program.steps .commit=207237662+(program.steps .commit-207237662) by omega]
  exact execute_nonce_commit _ entry _

theorem submission_nonce_commit_run (opening checker : Image) (message : Message) :
    (submission opening checker).run .commit message =
      nonceCommitTrace ((submission opening checker).initialState .commit message) := by
  exact program_nonce_commit_run (submission opening checker) rfl (by change 207237662≤1073807360;decide) message
    (abi_entry _ (abi opening checker) message)

theorem nonce_trace_resources (initial : MachineState) (run : Execution)
    (reached : run ∈ support (nonceCommitTrace initial)) :
    run.exit=.success ∧ run.cycles=493165594 ∧ run.oracleCalls=40846847 := by
  unfold nonceCommitTrace at reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨_,_,_,_,_,_,rfl⟩ := reached
  exact ⟨rfl,rfl,rfl⟩

/-- Exact resources of every reachable commit run. -/
theorem reachable_nonce_commit_resources (opening checker : Image) (message : Message) (run : Execution)
    (reached : run ∈ support ((submission opening checker).run .commit message)) :
    run.exit=.success ∧ run.cycles=493165594 ∧ run.oracleCalls=40846847 := by
  rw [submission_nonce_commit_run] at reached
  exact nonce_trace_resources _ run reached

/-- The resource fact in the form consumed by `quad_nonce_certificate`. -/
theorem nonce_commit_resources (opening checker : Image) :
    ∀ message run, run ∈ support ((submission opening checker).run .commit message) →
      run.exit = .success ∧ run.cycles = 493165594 ∧ run.oracleCalls ≤ COMMIT_BUDGET := by
  intro message run reached
  obtain ⟨exit,cycles,calls⟩ := reachable_nonce_commit_resources opening checker message run reached
  refine ⟨exit,cycles,?_⟩
  rw [calls]
  decide

/-! ### Distribution and serialized contents -/

theorem counted_ready_body (oracle : Oracle) (ready : MachineState) :
    RunPublic oracle (body ready) 39321599 := by
  unfold body
  apply run_bind_public _ _ _ 33554432 5767167 (Leaves.counted_groups ..)
  intro leaves
  apply run_bind_public _ _ _ 4194304 1572863 (Quads.counted_groups ..)
  intro quads
  apply run_bind_public _ _ _ 1048576 524287 (Quad2s.counted_groups ..)
  intro quad2s
  apply run_bind_public _ _ _ 262144 262143 (Quad3s.counted_groups ..)
  intro quad3s
  exact run_bind_public _ _ _ 262143 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

/-- The commit execution under a fixed oracle and seed. -/
def nonceOutput (oracle : Oracle) (initial : MachineState) (k : Key) : Execution :=
  ⟨.success,finalState oracle (Chain.chainFinalReady oracle.permutation initial k),493165594,40846847⟩

theorem nonce_counted_trace (oracle : Oracle) (initial : MachineState) :
    oracle.run (nonceCommitTrace initial) =
      (do let k ← $ᵗ Key
          return (nonceOutput oracle initial k,40846847)) := by
  unfold nonceCommitTrace
  rw [CommitGolfCandidate.oracle_run_coins_bind]
  apply bind_congr
  intro k
  have expand : oracle.run (Chain.expansion initial k) =
      pure (Chain.evalChain oracle.permutation 0 (Chain.chainInitial initial k) Chain.nonceChainCount,
        Chain.nonceChainCount) := by
    unfold Chain.expansion
    exact Chain.chain_fixed_run ..
  rw [oracle_run_bind,expand,pure_bind]
  simp only
  rw [oracle_run_bind,show oracle.run (body _) = _ from counted_ready_body oracle _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  rw [body_evaluated]
  rfl

noncomputable def nonceTrapdoor (opening checker : Image) (oracle : Oracle) (message : Message) (k : Key) :
    BitVec (8*(submission opening checker).sizes.trapdoor) :=
  ((submission opening checker).readCommit
    (nonceOutput oracle ((submission opening checker).initialState .commit message) k)).2

theorem nonce_physical_results (opening checker : Image) (oracle : Oracle) (message : Message) (k : Key) :
    let salts := actualNonces oracle.permutation k
    let output := (submission opening checker).readCommit
      (nonceOutput oracle ((submission opening checker).initialState .commit message) k)
    output.1=quad3PublicTree oracle message salts 1 ∧
    (∀ n, 0<n → n<2^19 → quadTrapdoorHeap output.2 n=quad3PublicTree oracle message salts n) ∧
    (∀ g, g<2^22 → quad2TrapdoorQuad output.2 g=quad2PublicQuads oracle message salts g) ∧
    (∀ h, h<2^20 → quad3TrapdoorQuad2 output.2 h=quad3PublicQuad2s oracle message salts h) ∧
    (∀ i : Index, quadTrapdoorLeaf output.2 i=quadPublicLeaves oracle message salts i) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=salts i) := by
  obtain ⟨regs,messages,nonces,zeros,quadZeros,quad3Zeros⟩ :=
    Chain.final_content oracle (submission opening checker) (abi opening checker) message k
  exact physical_results opening checker oracle message (actualNonces oracle.permutation k) _
    regs messages nonces zeros quadZeros quad3Zeros _ rfl

theorem nonce_commit_distribution (opening checker : Image) (oracle : Oracle) (message : Message) :
    fixedOracleRun oracle ((submission opening checker).scheme.commit message) =
      (do let k ← $ᵗ Key
          pure (quad3PublicTree oracle message (actualNonces oracle.permutation k) 1,
            nonceTrapdoor opening checker oracle message k)) := by
  let candidate := submission opening checker
  let initial := candidate.initialState .commit message
  change fixedOracleRun oracle (candidate.readCommit <$> candidate.run .commit message)=_
  rw [submission_nonce_commit_run,fixed_oracle_run_map]
  unfold fixedOracleRun
  rw [nonce_counted_trace oracle initial]
  simp only [map_bind,map_pure]
  apply bind_congr
  intro k
  have physical := nonce_physical_results opening checker oracle message k
  exact congrArg pure (Prod.ext physical.1 rfl)

/-- The commit-side deliverable of the quad3 + NonceChain certificate. -/
noncomputable def verifiedNonceTranscript (opening checker : Image) :
    Quad3NonceCommitTranscript (submission opening checker) where
  trapdoor := nonceTrapdoor opening checker
  distribution oracle message := by
    unfold EvalDistEq
    rw [nonce_commit_distribution]
    exact fun _ => rfl
  nonce oracle message k i := (nonce_physical_results opening checker oracle message k).2.2.2.2.2 i
  leaf oracle message k i := (nonce_physical_results opening checker oracle message k).2.2.2.2.1 i
  quad oracle message k g bound :=
    (nonce_physical_results opening checker oracle message k).2.2.1 g (by rw [length_value] at bound;exact bound)
  quad2 oracle message k h bound :=
    (nonce_physical_results opening checker oracle message k).2.2.2.1 h (by rw [length_value] at bound;exact bound)
  heap oracle message k n positive bound :=
    (nonce_physical_results opening checker oracle message k).2.1 n positive (by rw [length_value] at bound;exact bound)

end TwoPermutationPrototype.Quad.Commit
