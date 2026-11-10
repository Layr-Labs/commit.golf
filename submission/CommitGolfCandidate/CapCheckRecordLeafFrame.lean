import CommitGolfCandidate.CapCheckRecordLeaf
import CommitGolfCandidate.CapCheckLeafOutcome

/-! Complete salt-and-leaf outcomes preserve the loaded sorted index and
advance the value cursor by one 256-byte entry. Scratch-only writes retain
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
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  rw [MachineState.getReg_setPC,
    cap_check_leaf_loop_source _ 8 body bodyReachable,
    cap_check_record_leaf_start_register state .x8 (by decide)]
  rfl

theorem cap_check_record_leaf_cursor (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    finished.getReg .x25 = state.getReg .x25 + 32 := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  rw [MachineState.getReg_setPC,
    cap_check_leaf_loop_register_frame _ 8 body bodyReachable .x25 (by decide)]
  unfold capCheckRecordLeafStart
  rw [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x25),
    cap_check_leaf_call_register _ .x25 (by decide), cap_check_salt_cursor]

theorem cap_check_record_leaf_index (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    finished.getReg .x20 = state.getMem (state.getReg .x24) := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  rw [MachineState.getReg_setPC,
    cap_check_leaf_loop_register_frame _ 8 body bodyReachable .x20 (by decide)]
  unfold capCheckRecordLeafStart
  rw [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x20),
    cap_check_leaf_call_register _ .x20 (by decide), cap_check_salt_index]

theorem cap_check_record_leaf_high_frame (state reference finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (frame : CapHighBytes state reference)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    CapHighBytes finished reference := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  have startScratch :=
    (cap_check_record_leaf_start_register state .x21 (by decide)).trans scratch
  have startFrame : CapHighBytes (capCheckRecordLeafStart state) reference := by
    exact cap_high_bytes_memory _ _ _
      (cap_check_record_leaf_start_memory state)
      (cap_check_salt_high_frame state reference scratch frame)
  have bodyFrame := cap_check_leaf_loop_high_frame _ reference 8 startScratch
    body bodyReachable startFrame
  exact cap_high_bytes_memory _ _ _ rfl bodyFrame

end CommitGolfCandidate
