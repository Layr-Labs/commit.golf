import CommitGolfCandidate.CapCheckRecordLogical
import CommitGolfCandidate.CapCheckLowerCollected

/-! Fixed-oracle consistency handling agrees with the logical forward insert.
The digest premise is discharged by the actual byte/ABI theorem separately.
All-reply support supplies the runtime frames; no collision-freedom or
injectivity property of compression is used here. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_record_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (capCheckRecordRun state) =
      (capCheckRecordResult (checkEvaluation oracle (capCheckLowerRecord state)).1,
        (checkEvaluation oracle (capCheckLowerRecord state)).2) := by
  rw [capCheckRecordRun,check_evaluation_bind]
  simp only [check_evaluation_pure,Nat.add_zero]

theorem cap_check_record_insert_agreement (oracle : Oracle) (state : MachineState)
    (record : CapLowerRecord) (roots : CapRootMap)
    (collected : CapCheckCollected state roots)
    (loaded : state.getMem (state.getReg .x24)=BitVec.ofNat 64 record.index.val)
    (scratch : state.getReg .x21=256) (leaves : state.getReg .x19=128)
    (marks : state.getReg .x9=20480) (rootBase : state.getReg .x18=12288)
    (one : state.getReg .x31=1)
    (digest : readBuffer (checkEvaluation oracle (capCheckLowerRecord state)).1 256 32=
      record.root oracle.compression) :
    (checkEvaluation oracle (capCheckRecordRun state)).1.2=true ↔
      (capInsert roots (capGroup record.index).val (record.root oracle.compression)).isSome=true := by
  let lower := (checkEvaluation oracle (capCheckLowerRecord state)).1
  have reachable := check_evaluation_support oracle (capCheckLowerRecord state)
  have bounded : record.index.val<2^24 := record.index.isLt
  have ready := cap_check_lower_group_ready state lower record.index.val bounded loaded
    scratch leaves marks rootBase one reachable
  have lowerCollected := cap_check_lower_record_collected state lower
    scratch reachable roots collected
  rw [cap_check_record_evaluation,cap_check_record_result_passed,
    cap_check_group_insert lower roots lowerCollected (record.index.val/2^17)
      ready.bounded ready.index ready.leaves ready.marks ready.roots ready.scratch ready.one,
    digest]
  rfl

theorem cap_check_record_insert_result (oracle : Oracle) (state : MachineState)
    (record : CapLowerRecord) (roots next : CapRootMap)
    (collected : CapCheckCollected state roots)
    (loaded : state.getMem (state.getReg .x24)=BitVec.ofNat 64 record.index.val)
    (scratch : state.getReg .x21=256) (leaves : state.getReg .x19=128)
    (marks : state.getReg .x9=20480) (rootBase : state.getReg .x18=12288)
    (one : state.getReg .x31=1)
    (digest : readBuffer (checkEvaluation oracle (capCheckLowerRecord state)).1 256 32=
      record.root oracle.compression)
    (accepted : capInsert roots (capGroup record.index).val
      (record.root oracle.compression)=some next) :
    CapCheckCollected (checkEvaluation oracle (capCheckRecordRun state)).1.1 next := by
  let lower := (checkEvaluation oracle (capCheckLowerRecord state)).1
  have reachable := check_evaluation_support oracle (capCheckLowerRecord state)
  have bounded : record.index.val<2^24 := record.index.isLt
  have ready := cap_check_lower_group_ready state lower record.index.val bounded loaded
    scratch leaves marks rootBase one reachable
  have lowerCollected := cap_check_lower_record_collected state lower
    scratch reachable roots collected
  rw [cap_check_record_evaluation]
  apply cap_check_record_result_collected lower roots next (record.index.val/2^17)
    ready lowerCollected
  rw [digest]
  exact accepted

end CommitGolfCandidate
