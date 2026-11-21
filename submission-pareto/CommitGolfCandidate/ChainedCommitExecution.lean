import CommitGolfCandidate.ChainedParentRun

/-! Whole delivered commitment execution and exact native fuel/cycle/query accounting. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
attribute [local irreducible] execute chainedCommitBody Chain.expansion Chain.seedSetup Chain.seedWritten

def chainedCommitTrace (initial : MachineState) : OracleComp World Execution := do
  let seed ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
  let last ← Chain.expansion initial seed
  let state ← chainedCommitBody (Chain.chainFinish last)
  return ⟨.success,state,2353177256,102382335⟩

private theorem chained_seed_execution (initial : MachineState) (entry : CommitEntry initial)
    (seed : BitVec 192) (fuel : Nat) :
    execute chainedCommitImage (57028397+(1579472499+fuel)) (Chain.seedWritten initial seed) true =
      (do let last ← Chain.expansion initial seed
          let state ← chainedCommitBody (Chain.chainFinish last)
          return ⟨.success,state,2353177241,102382335⟩) := by
  rw [chained_image_packed,Chain.after_draw initial entry seed (1579472499+fuel),←chained_image_packed]
  apply bind_congr_of_forall_mem_support
  intro last reached
  have regs := (Chain.expansion_post initial entry seed last reached).2.2
  rw [chained_commit_body_execution (Chain.chainFinish last) regs fuel]
  simp only [bind_assoc,pure_bind,Execution.charge,Chain.nonceChainCount]

theorem chained_commit_execution (initial : MachineState) (entry : CommitEntry initial) (fuel : Nat) :
    execute chainedCommitImage (1636500908+fuel) initial true = chainedCommitTrace initial := by
  rw [show 1636500908+fuel = 11+(1+(57028397+(1579472499+fuel))) by omega,
    chained_image_packed,Chain.seed_run initial entry.pc,Chain.seed_draw initial entry,←chained_image_packed]
  simp only [chainedCommitTrace,bind_assoc,pure_bind]
  apply bind_congr
  intro seed
  rw [chained_seed_execution initial entry seed fuel]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem chained_commit_submission_run (program : Submission)
    (image : program.image .commit = chainedCommitImage) (enough : 1636500908 ≤ program.steps .commit)
    (message : Message) (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message = chainedCommitTrace (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit) (program.initialState .commit message) true = _
  rw [image,show program.steps .commit = 1636500908+(program.steps .commit-1636500908) by omega]
  exact chained_commit_execution _ entry _

theorem chained_commit_numeric_bounds : 1636500908 ≤ 2^31 ∧ 102382335 ≤ 100*2^24 := by decide

end CommitGolfCandidate.Chained.Native
