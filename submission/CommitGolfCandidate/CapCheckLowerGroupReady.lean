import CommitGolfCandidate.CapCheckGroupAdmission
import CommitGolfCandidate.CapCheckLowerRecordFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

structure CapCheckGroupReady (state : MachineState) (group : Nat) : Prop where
  bounded : group < 256
  pc : state.pc = 4420
  scratch : state.getReg .x21 = 256
  index : state.getReg .x20 = BitVec.ofNat 64 group
  leaves : state.getReg .x19 = 256
  marks : state.getReg .x9 = 28672
  roots : state.getReg .x18 = 12288
  one : state.getReg .x31 = 1

theorem cap_check_lower_group_ready (state finished : MachineState) (index : Nat)
    (bounded : index < 2^24)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index)
    (scratch : state.getReg .x21 = 256) (leaves : state.getReg .x19 = 256)
    (marks : state.getReg .x9 = 28672) (roots : state.getReg .x18 = 12288)
    (one : state.getReg .x31 = 1)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    CapCheckGroupReady finished (index/2^16) := by
  constructor
  · omega
  · exact (cap_check_lower_record_finished state finished reachable).1
  · rw [cap_check_lower_record_register state finished reachable .x21 (by decide),scratch]
  · exact cap_check_lower_record_node state finished index (by omega) loaded reachable
  · rw [cap_check_lower_record_register state finished reachable .x19 (by decide),leaves]
  · rw [cap_check_lower_record_register state finished reachable .x9 (by decide),marks]
  · rw [cap_check_lower_record_register state finished reachable .x18 (by decide),roots]
  · rw [cap_check_lower_record_register state finished reachable .x31 (by decide),one]

theorem cap_check_group_ready_admission (state : MachineState) (group : Nat)
    (ready : CapCheckGroupReady state group) :
    accessValid ((capCheckGroupStartPrefix state 5).getReg .x30) 8 = true ∧
    (∀ i < 4, accessValid
      (state.getReg .x21+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true) ∧
    (∀ i < 4, accessValid
      ((capCheckGroupStartPrefix state 6).getReg .x23+
        signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true) ∧
    accessValid ((capCheckGroupStartPrefix state 6).getReg .x30) 8 = true := by
  have bounded := ready.bounded
  have addresses := cap_check_group_start_addresses state group ready.bounded ready.index
    ready.leaves ready.marks ready.roots
  refine ⟨cap_check_group_mark_access state group ready.bounded ready.index
    ready.leaves ready.marks ready.roots,?_,?_,?_⟩
  · intro i inside
    rw [ready.scratch]
    exact cap_check_group_scratch_access ⟨i,inside⟩
  · intro i inside
    rw [addresses.2.2]
    exact cap_check_group_root_access group ready.bounded ⟨i,inside⟩
  · rw [addresses.2.1]
    exact (cap_mark_address_valid 256 (256+group) (by decide) (by omega)).1

end CommitGolfCandidate
