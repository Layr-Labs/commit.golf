import CommitGolfCandidate.QuartetCommitJoinRegs
import CommitGolfCandidate.QuartetChainSetup

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 1700000
attribute [local irreducible] execute image QuartetUpper.packedWideCommitImage qStartPrefix upStartPrefix qGroups qUnits QuartetLeaves.groups packedParentsTrace packedParentGroups rootPrefix

/-- Everything after the leaf-loop entry, from any ready state (the chain generator's output). -/
def commitBody (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← QuartetLeaves.groups 4096 0 ready
  let quad ← qGroups 8192 0 (qStartPrefix leaves 3)
  let upperStart ← packedParentsTrace 4194176 127 (upStartPrefix quad 6)
  let parents ← packedParentGroups QuartetUpper.loopBase 32767 128 upperStart
  return rootPrefix parents 10

private theorem same_image : image=QuartetUpper.packedWideCommitImage := exact_image.trans QuartetUpper.packed_manifest_image.symm

theorem commit_after_draw (s : MachineState) (ready : StartLeafRegs s) (fuel : Nat) :
    execute image (214524173+fuel) s true = (do
      let out ← commitBody s
      return ⟨.success,out,508125446,41943039⟩) := by
  rw [show 214524173+fuel=185147391+(3+(12599295+(6+(508+(16776959+(11+fuel)))))) by omega,
    QuartetLeaves.entire_leaf_phase _ ready]
  simp only [commitBody,bind_assoc]; apply bind_congr_of_forall_mem_support
  intro leaves path
  obtain ⟨lpc,qpc,qregs,carry⟩ := start_q _ ready path
  rw [qStart_run _ lpc,entire_quartet_phase _ _ qregs qpc]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro quad path
  obtain ⟨rpc,startpc,regs,out⟩ := start_upper _ qregs qpc carry path
  rw [upStart_run _ rpc,same_image,QuartetUpper.upper_prefix_run _ _ regs startpc]
  simp only [bind_assoc]; apply bind_congr_of_forall_mem_support
  intro upperStart path
  have ⟨last,loopPC⟩ := packed_parent_segment_post 191180 4194176 127 0 _ regs
    (by simpa [packedParentPC] using startpc) path
  have atLoop : upperStart.pc=QuartetUpper.loopBase := loopPC
  have outPrefix := (packed_sequence_keeps_output _ _ _ path).trans out
  rw [QuartetUpper.upper_loop_run upperStart _ last atLoop]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro parents path
  obtain ⟨last,rootPC⟩ := packed_groups_post QuartetUpper.loopBase 32767 128 _ (by decide) (fun _ => atLoop) last path
  have rootPos : parents.pc=717492 := rootPC (by decide)
  have outParent := (wide_parent_full_register _ _ _ _ path).trans outPrefix
  rw [QuartetUpper.execute_packed_root _ rootPos last.heap outParent]
  simp only [bind_assoc,pure_bind,Execution.charge]

attribute [local irreducible] QuartetChain.expansion QuartetChain.chainFinish QuartetChain.seedWritten prePrefix

/-- The commitment: a 24-byte seed, the permutation chain, then the unchanged Quartet body. -/
def commitTrace (s : MachineState) : OracleComp World Execution := do
  let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
  let last ← QuartetChain.expansion s k
  let out ← commitBody (QuartetChain.chainFinish last)
  return ⟨.success,out,523377606,43468241⟩

theorem commit_execution (s : MachineState) (entry : CommitEntry s) (fuel : Nat) :
    execute image (219099916+fuel) s true = commitTrace s := by
  rw [show 219099916+fuel=15+(1+(4575727+(214524173+fuel))) by omega,pre_run s entry.pc,
    QuartetChain.seed_draw s entry]
  simp only [commitTrace,bind_assoc,pure_bind]
  apply bind_congr
  intro k
  rw [QuartetChain.after_draw s entry k]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro last hit
  rw [commit_after_draw _ (QuartetChain.expansion_post s entry k last hit).2]
  simp only [bind_assoc,pure_bind,Execution.charge]
  apply bind_congr
  intro out
  congr 1

theorem submission_run (program : Submission) (hi : program.image .commit=image) (fuel : 219099916≤program.steps .commit)
    (msg : Message) (entry : CommitEntry (program.initialState .commit msg)) :
    program.run .commit msg=commitTrace (program.initialState .commit msg) := by
  change execute (program.image .commit) (program.steps .commit) (program.initialState .commit msg) true=_
  rw [hi,show program.steps .commit=219099916+(program.steps .commit-219099916) by omega]
  exact commit_execution _ entry _

theorem artifact_run (msg : Message) : Artifact.submission.run .commit msg =
    commitTrace (Artifact.submission.initialState .commit msg) :=
  submission_run Artifact.submission exact_image.symm (by decide) msg ⟨rfl,rfl,rfl,rfl⟩

end TwoPermutationPrototype.QuartetCommit
