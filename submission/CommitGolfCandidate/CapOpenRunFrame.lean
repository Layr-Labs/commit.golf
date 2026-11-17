import CommitGolfCandidate.CapOpenInputFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

structure CapOpenReadReady (marked : Nat → Bool) (rootBase limit floor : Nat)
    (reference : MachineState) (control : CapDfsControl) (state : MachineState) : Prop where
  machine : CapDfsMachineReady false marked rootBase (CapOpenCursorWindow limit) control state
  cursorFloor : floor ≤ (state.getReg .x25).toNat
  inputFrame : CapOpenInputFrame floor reference state

theorem cap_open_read_ready_transport (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 16384 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (control : CapDfsControl) (state : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference control state)
    (next : MachineState) (reached : next ∈ support (capDfsStep false marked control state)) :
    CapOpenReadReady marked rootBase limit floor reference
      (capControlStep marked control) next := by
  refine ⟨?_, ?_, ?_⟩
  · apply cap_dfs_machine_transport false marked rootBase (CapOpenCursorWindow limit)
    · intro impossible
      contradiction
    · intro atControl atState atReady node atNode _absent
      exact cap_open_boundary_ready marked rootBase limit atControl atState
        atReady.valid atReady.cursor limitBound rootBound rootAligned node atNode
    · intro atControl atState atReady result supported
      exact cap_open_cursor_transport marked limit atControl atState result
        atReady.valid atReady.cursor supported
    · exact ready.machine
    · exact reached
  · exact cap_open_step_floor marked control state next limit floor ready.machine.valid
      ready.machine.cursor limitBound ready.cursorFloor reached
  · exact cap_open_step_input_frame marked control state next reference rootBase limit floor
      ready.machine.physical ready.machine.valid ready.machine.stable ready.machine.cursor
      limitBound ready.cursorFloor ready.inputFrame reached

theorem cap_open_run_input_frame (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 16384 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (count : Nat) (control : CapDfsControl) (state final : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference control state)
    (reached : final ∈ support (capDfsRun false marked count control state)) :
    CapOpenReadReady marked rootBase limit floor reference
      (capControlRun marked count control) final := by
  exact cap_dfs_run_support false marked
    (CapOpenReadReady marked rootBase limit floor reference)
    (cap_open_read_ready_transport marked rootBase limit floor reference
      limitBound rootBound rootAligned) count control state final ready reached

theorem cap_open_completed_input_frame (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 16384 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (state final : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference (.visit 1) state)
    (reached : final ∈ support (capDfsRun false marked 1022 (.visit 1) state)) :
    final.pc = capAdvanceDone false ∧ CapOpenInputFrame floor reference final ∧
      floor ≤ (final.getReg .x25).toNat := by
  have finished := cap_open_run_input_frame marked rootBase limit floor reference
    limitBound rootBound rootAligned 1022 (.visit 1) state final ready reached
  rw [cap_control_complete] at finished
  exact ⟨finished.machine.physical, finished.inputFrame, finished.cursorFloor⟩

end CommitGolfCandidate
