import CommitGolfCandidate.ParentGroupComplete
import CommitGolfCandidate.CursorRootFrame

/-! Static scheduling data is separated from proofs of the delivered instruction bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

structure ParentSchedule where
  initialPlan : ParentPlan
  start : Word
  branchPC : Word
  branchOffset : BitVec 13
  exitOffset : BitVec 21
  width : Nat

structure ParentSchedule.Valid (schedule : ParentSchedule) : Prop where
  positive : 0<schedule.width
  endPC : parentSequenceEnd schedule.start schedule.width=schedule.branchPC
  loopJump : schedule.branchPC+signExtend13 schedule.branchOffset=schedule.start
  entry : schedule.initialPlan.finish=schedule.start
  rootJump : schedule.branchPC+4+signExtend21 schedule.exitOffset=4412

structure ParentSchedule.Fetched (image : Image) (schedule : ParentSchedule) : Prop where
  plan : ParentPlan.Fetched image schedule.initialPlan
  sequence : ParentSequenceFetched image schedule.start schedule.width
  branch : ParentGroupBranchFetched image schedule.branchPC schedule.branchOffset
  exit : ParentGroupExitFetched image (schedule.branchPC+4) schedule.exitOffset

def ParentSchedule.parents (schedule : ParentSchedule) (groups : Nat) : Nat :=
  schedule.initialPlan.parents+schedule.width*groups

def ParentSchedule.instructions (schedule : ParentSchedule) (groups : Nat) : Nat :=
  schedule.initialPlan.instructions+(3*schedule.width+1)*groups+1

def ParentSchedule.cycles (schedule : ParentSchedule) (groups : Nat) : Nat :=
  schedule.initialPlan.cycles+(10*schedule.width+1)*groups+1

/-- The schedule cost is derived from its fetched prefixes, loop and exit. -/
theorem parent_schedule_execute (image : Image) (schedule : ParentSchedule)
    (valid : schedule.Valid) (fetched : schedule.Fetched image)
    (state : MachineState) (groups : Nat) (positive : 0<groups)
    (bounded : schedule.parents groups<2^24)
    (pointers : ParentPointerInvariant state (schedule.parents groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (schedule.parents groups)) (fuel : Nat) :
    execute image (schedule.instructions groups+fuel) (state.setPC schedule.initialPlan.entry) true=
      (do let finished ← commitParents state (schedule.parents groups)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (schedule.cycles groups) (schedule.parents groups)) :=
  parent_group_complete image schedule.initialPlan fetched.plan schedule.start schedule.branchPC
    schedule.branchOffset schedule.exitOffset schedule.width valid.positive fetched.sequence
    fetched.branch valid.endPC valid.loopJump valid.entry fetched.exit valid.rootJump
    state groups positive bounded pointers constants buffers fuel

/-- Carry the same inactive-register frame used by the retained leaf and root proofs. -/
theorem parent_schedule_execute_framed (schedule : ParentSchedule)
    (valid : schedule.Valid) (fetched : schedule.Fetched (submission.image .commit))
    (state : MachineState) (groups : Nat) (messageBase : Word) (positive : 0<groups)
    (bounded : schedule.parents groups<2^24) (pc : state.pc=schedule.initialPlan.entry)
    (pointers : ParentPointerInvariant state (schedule.parents groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (schedule.parents groups)) (fuel : Nat) :
    execute (submission.image .commit) (schedule.instructions groups+fuel)
      (cursorBaseFrame state messageBase) true=
      (do let finished ← commitParents state (schedule.parents groups)
          let result ← execute (submission.image .commit) fuel
            ((cursorBaseFrame finished messageBase).setPC 4412) true
          return result.charge (schedule.cycles groups) (schedule.parents groups)) := by
  have framedPC : (cursorBaseFrame state messageBase).pc=schedule.initialPlan.entry := pc
  have run := parent_schedule_execute _ schedule valid fetched
    (cursorBaseFrame state messageBase) groups positive bounded pointers constants buffers fuel
  rw [← framedPC,hoist_pc_self] at run
  rw [cursor_base_parents_bind state (schedule.parents groups) messageBase
    (fun finished => do
      let result ← execute (submission.image .commit) fuel (finished.setPC 4412) true
      return result.charge (schedule.cycles groups) (schedule.parents groups))] at run
  exact run

end CommitGolfCandidate
