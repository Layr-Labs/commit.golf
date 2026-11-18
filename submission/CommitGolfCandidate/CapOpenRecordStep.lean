import CommitGolfCandidate.CapOpenRecordStart
import CommitGolfCandidate.CapOpenPathFrame
import CommitGolfCandidate.CapOpenGroupControl

/-! One complete, checked opening record. It writes the salt field, copies the
three other leaf digests of the group and fourteen lower siblings, then sets the
corresponding cap leaf mark. The loaded index bounds identify the final heap
node; the macro charges exactly 284 cycles across 278 instructions and makes no
oracle query. Original input/serialized-byte refinements are proved separately
from this runtime composition. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def capOpenRecordGroupState (state : MachineState) : MachineState :=
  capCountedRun capOpenPathState 14 (capOpenRecordPathState state)

def capOpenRecordState (state : MachineState) : MachineState :=
  capOpenGroupPrefix (capOpenRecordGroupState state) 6

attribute [local irreducible] capOpenRecordGroupState capOpenRecordState

theorem cap_open_record_group_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x30 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28)
    {rootBase saltBase cursor limit position : Nat}
    (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordGroupState state).getReg reg = state.getReg reg := by
  obtain ⟨h1, h6, h7, h23, h30, h25, h20, h28⟩ := outside
  rw [capOpenRecordGroupState]
  exact (cap_open_path_loop_register 14 _ reg ⟨h6, h7, h23, h25, h20, h28⟩).trans
    (cap_open_record_path_register state reg ⟨h1, h6, h7, h23, h30, h20, h25, h28⟩ entry)

theorem cap_open_record_group_index {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordGroupState state).getReg .x20 =
      BitVec.ofNat 64 (256+position/65536) := by
  have bounded := entry.positionBound
  rw [capOpenRecordGroupState, cap_open_path_loop_index 14 _
    (4194304+position/4) (by omega) (cap_open_record_path_facts entry).2.1]
  have division : (4194304+position/4)/2^14 = 256+position/65536 := by
    norm_num
    omega
  rw [division]

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_open_record_execute {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (278+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordState state) allowCoins
          return result.charge 284 0) := by
  have ready := cap_open_record_path_ready entry
  have rootBound : rootBase + 1073741824 ≤ MEMORY_BYTES := by
    have := entry.heapBelow
    have := entry.space
    have := entry.limitBound
    omega
  have pathRun := cap_open_path_loop_execute rootBase limit rootBound entry.rootAligned
    entry.limitBound 14 (capOpenRecordPathState state) ready (6+fuel) allowCoins
  have groupPC : (capOpenRecordGroupState state).pc = 4340 := by
    rw [capOpenRecordGroupState]
    exact (cap_open_path_loop_finished rootBase limit entry.limitBound 14 _ ready).1
  have groupMark : (capOpenRecordGroupState state).getReg .x22 = 28672 :=
    (cap_open_record_group_register state .x22 (by decide) entry).trans entry.marks
  have groupIndex := cap_open_record_group_index entry
  have groupRun := cap_open_group_execute (capOpenRecordGroupState state)
    (256+position/65536) groupPC groupMark groupIndex
    (by have := entry.positionBound; omega) fuel allowCoins
  rw [show 278+fuel = 62+(15*14+(6+fuel)) by omega,
    cap_open_record_start_execute entry, pathRun]
  rw [← capOpenRecordGroupState, groupRun, ← capOpenRecordState]
  simp only [bind_assoc, pure_bind, charge_pair, Nat.reduceAdd]

end CommitGolfCandidate
