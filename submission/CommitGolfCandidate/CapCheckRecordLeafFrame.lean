import CommitGolfCandidate.CapCheckRecordLeaf

/-! Complete salt-and-leaf outcomes preserve the loaded sorted index and
advance the value cursor by one 256-byte entry. Low-workspace writes retain
high input bytes on every supported reply continuation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSaltState capCheckLeafCallState

theorem cap_check_record_leaf_start_memory (state : MachineState) :
    (capCheckRecordLeafStart state).mem = (capCheckSaltState state).mem := by
  unfold capCheckRecordLeafStart capCheckLeafCallState
  rfl

theorem cap_check_record_leaf_source (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    finished.getReg .x8 = state.getReg .x8 + 256 := by
  obtain ⟨body, bodyReachable, rfl⟩ := cap_check_record_leaf_support state finished reachable
  rw [MachineState.getReg_setPC, cap_check_leaf_source _ body bodyReachable,
    cap_check_record_leaf_start_register state .x8 (by decide)]

theorem cap_check_record_leaf_cursor (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    finished.getReg .x25 = state.getReg .x25 + 32 := by
  obtain ⟨body, bodyReachable, rfl⟩ := cap_check_record_leaf_support state finished reachable
  rw [MachineState.getReg_setPC,
    cap_check_leaf_register_frame _ body bodyReachable .x25 (by decide)]
  unfold capCheckRecordLeafStart
  rw [cap_check_leaf_call_register _ .x25 (by decide), cap_check_salt_cursor]

theorem cap_check_record_leaf_index (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    finished.getReg .x20 = state.getMem (state.getReg .x24) := by
  obtain ⟨body, bodyReachable, rfl⟩ := cap_check_record_leaf_support state finished reachable
  rw [MachineState.getReg_setPC,
    cap_check_leaf_register_frame _ body bodyReachable .x20 (by decide)]
  unfold capCheckRecordLeafStart
  rw [cap_check_leaf_call_register _ .x20 (by decide), cap_check_salt_index]

theorem cap_check_record_leaf_high_frame (state reference finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (frame : CapHighBytes state reference)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    CapHighBytes finished reference := by
  obtain ⟨body, bodyReachable, rfl⟩ := cap_check_record_leaf_support state finished reachable
  have startFrame : CapHighBytes (capCheckRecordLeafStart state) reference :=
    cap_high_bytes_memory _ _ _ (cap_check_record_leaf_start_memory state)
      (cap_check_salt_high_frame state reference scratch frame)
  have bodyFrame := cap_check_leaf_high_frame _ reference body bodyReachable startFrame
  exact cap_high_bytes_memory _ _ _ rfl bodyFrame

end CommitGolfCandidate
