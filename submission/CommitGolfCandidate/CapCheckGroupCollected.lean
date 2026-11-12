import CommitGolfCandidate.CapCheckGroupOutcome
import CommitGolfCandidate.CapCheckStoreCollected

/-! The actual lookup identifies the same bounded group as the logical map.
Collected occupancy makes the zero branch exactly the first occurrence;
the duplicate branch compares the reconstructed digest with the stored value. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckGroupStartPrefix readBuffer

theorem cap_check_group_lookup_mark (state : MachineState) (group : Nat)
    (bounded : group < 256) (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (roots : state.getReg .x18 = 12288) :
    (capCheckGroupStartPrefix state 6).getReg .x6 =
      state.getMem (capMarkAddress (256+group)) := by
  have projected := cap_check_group_start_projection state
  have address := (cap_check_group_start_addresses state group bounded index leaves marks roots).2.1
  rw [projected.2.1] at address
  rw [projected.2.2.2,address]
  rfl

theorem cap_check_group_compared_collected (state : MachineState) (roots : CapRootMap)
    (ready : CapCheckCollected state roots) :
    CapCheckCollected (capCheckGroupCompared state) roots :=
  cap_check_collected_memory _ state roots (cap_check_group_compared_memory state) ready

theorem cap_check_group_compared_addresses (state : MachineState) (group : Nat)
    (bounded : group < 256) (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (roots : state.getReg .x18 = 12288) :
    (capCheckGroupCompared state).getReg .x23 =
      BitVec.ofNat 64 (capCheckRootAddress group) ∧
    (capCheckGroupCompared state).getReg .x30 = capMarkAddress (256+group) := by
  rw [cap_check_group_compared_register,cap_check_group_compared_register]
  have address := cap_check_group_start_addresses state group bounded index leaves marks roots
  exact ⟨address.2.2,address.2.1⟩

theorem cap_check_group_compared_scratch (state : MachineState)
    (scratch : state.getReg .x21 = 256) :
    (capCheckGroupCompared state).getReg .x21 = 256 := by
  rw [cap_check_group_compared_register,
    cap_check_group_start_register state 6 (by decide) .x21 (by decide),scratch]

theorem cap_check_group_duplicate_value (state : MachineState) (roots : CapRootMap)
    (ready : CapCheckCollected state roots) (group : Nat) (bounded : group < 256)
    (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (rootBase : state.getReg .x18 = 12288) (scratch : state.getReg .x21 = 256)
    (previous : Digest) (known : roots group = some previous) :
    (capCheckDuplicateLoop (capCheckGroupCompared state) 0 4).2 = true ↔
      readBuffer state 256 32 = previous := by
  have address := (cap_check_group_compared_addresses state group bounded index leaves marks rootBase).1
  rw [cap_check_duplicate_passed_digest _ (capCheckRootAddress group)
    (cap_check_group_compared_scratch state scratch)
    address (by unfold capCheckRootAddress; omega)]
  rw [read_buffer_memory_congr _ state (cap_check_group_compared_memory state) 256 32,
    read_buffer_memory_congr _ state (cap_check_group_compared_memory state)
      (capCheckRootAddress group) 32,ready.roots group bounded previous known]

end CommitGolfCandidate
