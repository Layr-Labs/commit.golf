import CommitGolfCandidate.TwoPermutationPackedSetup
import CommitGolfCandidate.NonceChainSetup

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 60000
set_option maxHeartbeats 1700000
attribute [local irreducible] execute packed_wideReadyState parentSetup rootPrefix

structure PackedLeavesFinished (state : MachineState) : Prop where
  pc : state.pc=184784
  selector : state.getReg .x5=0
  heap : state.getReg .x9=4294971424
  stride : state.getReg .x19=536870912
  stop : state.getReg .x21=wordAddress (leafDest (2^24))
  output : state.getReg .x8=4294971392

structure PackedLeafExecution where
  trace : MachineState → OracleComp World MachineState
  executes : ∀ (ready : MachineState), Chain.BodyRegs ready → ∀ fuel : Nat,
    execute packedWideCommitImage (184950783+fuel) ready true =
      (do let leaves ← trace ready
          let out ← execute packedWideCommitImage fuel leaves true
          return out.charge 419831807 33554432)
  finished : ∀ (ready : MachineState), Chain.BodyRegs ready → ∀ out ∈ support (trace ready),
    PackedLeavesFinished out

def packed_wideCommitBody (leaf : PackedLeafExecution) (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← leaf.trace ready
  let parents ← packedParentGroups 184804 46995 357 (parentSetup leaves 5)
  return rootPrefix parents 10

theorem packed_wide_commit_after_draw (leaf : PackedLeafExecution) (ready : MachineState)
    (regs : Chain.BodyRegs ready) (fuel : Nat) :
    execute packedWideCommitImage (252060372+fuel) ready true =
      (do let result ← packed_wideCommitBody leaf ready
          return ⟨.success,result,604381901,50331647⟩) := by
  rw [show 252060372+fuel=184950783+(5+(67109573+(11+fuel))) by omega,
    leaf.executes ready regs]
  simp only [packed_wideCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := leaf.finished ready regs leaves reached
  have regs := packed_wide_parent_setup_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop
  rw [packed_execute_wide_parent_setup leaves fin.pc,packed_parent_phase _ _ regs.1 regs.2.1]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,pc,out⟩ := packed_parent_phase_post _ regs.1 regs.2.1 reached
  rw [execute_packed_root parents pc terms.heap (out.trans (regs.2.2.trans fin.output))]
  simp only [bind_assoc,pure_bind,Execution.charge]

def packed_wideCommitTrace (leaf : PackedLeafExecution) (initial : MachineState) :
    OracleComp World Execution := do
  let seed ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
  let last ← Chain.expansion initial seed
  let state ← packed_wideCommitBody leaf (Chain.chainFinish last)
  return ⟨.success,state,619658240,51856895⟩

attribute [local irreducible] Chain.expansion Chain.seedSetup Chain.seedWritten packed_wideCommitBody

private theorem complete_body_charge (s : MachineState) :
    (⟨.success,s,604381901,50331647⟩ : Execution).charge 15276324 Chain.nonceChainCount =
      ⟨.success,s,619658225,51856895⟩ := by
  have cost : 15276324+604381901=619658225 := by norm_num
  have calls : Chain.nonceChainCount+50331647=51856895 := by norm_num [Chain.nonceChainCount]
  simp only [Execution.charge,cost,calls]

private theorem complete_seed_charge (s : MachineState) :
    ((⟨.success,s,619658225,51856895⟩ : Execution).charge 4 0).charge 11 0 =
      ⟨.success,s,619658240,51856895⟩ := by
  have cost : 11+(4+619658225)=619658240 := by norm_num
  simp only [Execution.charge,cost,Nat.zero_add]

private theorem wide_seed_execution (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (k : BitVec 192) (fuel : Nat) :
    execute packedWideCommitImage (4599588+(252060372+fuel)) (Chain.seedWritten initial k) true =
      (do let last ← Chain.expansion initial k
          let state ← packed_wideCommitBody leaf (Chain.chainFinish last)
          return ⟨.success,state,619658225,51856895⟩) := by
  rw [Chain.after_draw initial entry k (252060372+fuel)]
  apply bind_congr_of_forall_mem_support
  intro last reached
  have r := (Chain.expansion_post initial entry k last reached).2
  rw [packed_wide_commit_after_draw leaf (Chain.chainFinish last) r fuel]
  simp only [bind_assoc,pure_bind,complete_body_charge]

theorem packed_wide_commit_execution (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (fuel : Nat) :
    execute packedWideCommitImage (256659972+fuel) initial true = packed_wideCommitTrace leaf initial := by
  have clock : 256659972+fuel=11+(1+(4599588+(252060372+fuel))) := by omega
  rw [clock,Chain.seed_run initial entry.pc,Chain.seed_draw initial entry]
  simp only [packed_wideCommitTrace,bind_assoc,pure_bind]
  apply bind_congr
  intro k
  rw [wide_seed_execution leaf initial entry k fuel]
  simp only [bind_assoc,pure_bind,complete_seed_charge]

theorem packed_submission_wide_commit_run (leaf : PackedLeafExecution) (program : Submission)
    (image : program.image .commit=packedWideCommitImage) (enough : 256659972≤program.steps .commit)
    (message : Message) (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message=packed_wideCommitTrace leaf (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit)
    (program.initialState .commit message) true=_
  rw [image,show program.steps .commit=256659972+(program.steps .commit-256659972) by omega]
  exact packed_wide_commit_execution leaf _ entry _

end TwoPermutationPrototype.RV64
