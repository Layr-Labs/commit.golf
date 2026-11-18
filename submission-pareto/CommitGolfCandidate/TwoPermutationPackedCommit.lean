import CommitGolfCandidate.TwoPermutationPackedSetup
import CommitGolfCandidate.NonceChainSetup
import CommitGolfCandidate.MixedWidthStopRun

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 60000
set_option maxHeartbeats 1700000
attribute [local irreducible] execute packed_wideReadyState parentSetup rootPrefix

structure PackedLeavesFinished (state : MachineState) : Prop where
  pc : state.pc=184608
  selector : state.getReg .x5=0
  heap : state.getReg .x9=4294971424
  stride : state.getReg .x19=536870912
  stop : state.getReg .x21=wordAddress (leafDest (2^24))
  output : state.getReg .x8=4294971392

structure PackedLeafExecution where
  trace : MachineState → OracleComp World MachineState
  executes : ∀ (ready : MachineState), Chain.BodyRegs ready → ∀ fuel : Nat,
    execute packedWideCommitImage (184754175+fuel) ready true =
      (do let leaves ← trace ready
          let out ← execute packedWideCommitImage fuel leaves true
          return out.charge 419635199 33554432)
  finished : ∀ (ready : MachineState), Chain.BodyRegs ready → ∀ out ∈ support (trace ready),
    PackedLeavesFinished out

def packed_wideCommitBody (leaf : PackedLeafExecution) (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← leaf.trace ready
  let full ← FullWidth.parentGroups 184640 32768 1048575 480
    (mixedStopSetup (parentSetup leaves 5))
  let parents ← packedParentGroups 577864 19065 55 full
  return rootPrefix parents 10

theorem packed_wide_commit_after_draw (leaf : PackedLeafExecution) (ready : MachineState)
    (regs : Chain.BodyRegs ready) (fuel : Nat) :
    execute packedWideCommitImage (236135482+fuel) ready true =
      (do let result ← packed_wideCommitBody leaf ready
          return ⟨.success,result,588457011,50331647⟩) := by
  rw [show 236135482+fuel=184754175+(5+(3+(47186879+(4194409+(11+fuel))))) by omega,
    leaf.executes ready regs]
  simp only [packed_wideCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := leaf.finished ready regs leaves reached
  have regs := packed_wide_parent_setup_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop
  let ready := parentSetup leaves 5
  have readyRegs : ParentRegs ready (2^24-1) := regs.1
  have fullRegs := mixed_stop_parent_regs ready (2^24-1) readyRegs
  have stop := mixed_stop_value ready (2^24-1) readyRegs
  have fullPC : (mixedStopSetup ready).pc=184640 := by
    rw [mixed_stop_pc,show ready.pc=184628 from regs.2.1]
    rfl
  rw [packed_execute_wide_parent_setup leaves fin.pc,execute_mixed_stop ready regs.2.1,
    mixed_full_phase _ _ fullRegs stop fullPC]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro full fullReached
  have fullPost := FullWidth.groups_post 184640 32768 1048575 480 (mixedStopSetup ready)
    (by decide) (fun _ => fullPC) fullRegs fullReached
  have projectedPC : full.pc=577864 := fullPost.2 (by decide)
  have fullOutput : full.getReg .x8=(mixedStopSetup ready).getReg .x8 :=
    FullWidth.groups_keep_register _ _ _ _ _ _ .x8 (by decide) (by decide) fullReached
  rw [mixed_projected_phase full _ fullPost.1 projectedPC]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,pc,out⟩ := mixed_projected_phase_post _ fullPost.1 projectedPC reached
  have output : parents.getReg .x8=4294971392 := out.trans
    (fullOutput.trans ((mixed_stop_register ready .x8 (by decide)).trans (regs.2.2.trans fin.output)))
  rw [execute_packed_root parents pc terms.heap output]
  simp only [bind_assoc,pure_bind,Execution.charge]

def packed_wideCommitTrace (leaf : PackedLeafExecution) (initial : MachineState) :
    OracleComp World Execution := do
  let seed ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
  let last ← Chain.expansion initial seed
  let state ← packed_wideCommitBody leaf (Chain.chainFinish last)
  return ⟨.success,state,603733354,51856895⟩

attribute [local irreducible] Chain.expansion Chain.seedSetup Chain.seedWritten packed_wideCommitBody

private theorem complete_body_charge (s : MachineState) :
    (⟨.success,s,588457011,50331647⟩ : Execution).charge 15276328 Chain.nonceChainCount =
      ⟨.success,s,603733339,51856895⟩ := by
  have cost : 15276328+588457011=603733339 := by norm_num
  have calls : Chain.nonceChainCount+50331647=51856895 := by norm_num [Chain.nonceChainCount]
  simp only [Execution.charge,cost,calls]

private theorem complete_seed_charge (s : MachineState) :
    ((⟨.success,s,603733339,51856895⟩ : Execution).charge 4 0).charge 11 0 =
      ⟨.success,s,603733354,51856895⟩ := by
  have cost : 11+(4+603733339)=603733354 := by norm_num
  simp only [Execution.charge,cost,Nat.zero_add]

private theorem wide_seed_execution (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (k : BitVec 192) (fuel : Nat) :
    execute packedWideCommitImage (4599592+(236135482+fuel)) (Chain.seedWritten initial k) true =
      (do let last ← Chain.expansion initial k
          let state ← packed_wideCommitBody leaf (Chain.chainFinish last)
          return ⟨.success,state,603733339,51856895⟩) := by
  rw [Chain.after_draw initial entry k (236135482+fuel)]
  apply bind_congr_of_forall_mem_support
  intro last reached
  have r := (Chain.expansion_post initial entry k last reached).2
  rw [packed_wide_commit_after_draw leaf (Chain.chainFinish last) r fuel]
  simp only [bind_assoc,pure_bind,complete_body_charge]

theorem packed_wide_commit_execution (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (fuel : Nat) :
    execute packedWideCommitImage (240735086+fuel) initial true = packed_wideCommitTrace leaf initial := by
  have clock : 240735086+fuel=11+(1+(4599592+(236135482+fuel))) := by omega
  rw [clock,Chain.seed_run initial entry.pc,Chain.seed_draw initial entry]
  simp only [packed_wideCommitTrace,bind_assoc,pure_bind]
  apply bind_congr
  intro k
  rw [wide_seed_execution leaf initial entry k fuel]
  simp only [bind_assoc,pure_bind,complete_seed_charge]

theorem packed_submission_wide_commit_run (leaf : PackedLeafExecution) (program : Submission)
    (image : program.image .commit=packedWideCommitImage) (enough : 240735086≤program.steps .commit)
    (message : Message) (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message=packed_wideCommitTrace leaf (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit)
    (program.initialState .commit message) true=_
  rw [image,show program.steps .commit=240735086+(program.steps .commit-240735086) by omega]
  exact packed_wide_commit_execution leaf _ entry _

end TwoPermutationPrototype.RV64
