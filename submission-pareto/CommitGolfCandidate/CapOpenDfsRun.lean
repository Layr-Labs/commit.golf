import CommitGolfCandidate.CapOpenABIWindow
import CommitGolfCandidate.CapDfsCostBound

/-! Actual opening DFS with its cursor admission hook discharged from the
retained ABI. The caller still supplies the state reached after lower-record
emission and the mark pass; this file does not assume a decoded root theorem. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

abbrev capOpenOutputLimit : Nat :=
  capProgram.layout.proof + capProgram.sizes.proof

private noncomputable def open_access (positions : Positions) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (ready : CapDfsMachineReady false marked capProgram.layout.trapdoor
      (CapOpenCursorWindow capOpenOutputLimit) control state)
    (node : Nat) (atNode : control = .visit node) (_absent : marked node = false) :
    CapDfsBoundaryReady false state capProgram.layout.trapdoor node :=
  cap_open_boundary_ready marked _ _ control state ready.valid ready.cursor
    (cap_open_abi_output_space positions).2 cap_open_abi_root_space.1
    cap_open_abi_root_space.2 node atNode

private theorem open_transport (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (ready : CapDfsMachineReady false marked capProgram.layout.trapdoor
      (CapOpenCursorWindow capOpenOutputLimit) control state)
    (next : MachineState) (reached : next ∈ support (capDfsStep false marked control state)) :
    CapOpenCursorWindow capOpenOutputLimit (capControlStep marked control) next :=
  cap_open_cursor_transport marked _ control state next ready.valid ready.cursor reached

theorem cap_open_dfs_run_execute (positions : Positions) (marked : Nat → Bool)
    (state : MachineState)
    (physical : CapDfsStateControl false state (.visit 1))
    (stable : CapDfsStable false state capProgram.layout.trapdoor)
    (marks : CapMarksReady state 256 0 marked)
    (pointer : state.getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof + 576 * positions.card))
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage false)
        (capDfsInstructionTotal false marked 1022 (.visit 1) + fuel) state allowCoins =
      (do let final ← capDfsRun false marked 1022 (.visit 1) state
          let result ← execute (capWalkImage false) fuel final allowCoins
          return result.charge (capDfsCycleTotal false marked 1022 (.visit 1))
            (capDfsQueryTotal false marked 1022 (.visit 1))) := by
  apply cap_dfs_machine_run_execute false marked capProgram.layout.trapdoor
    (CapOpenCursorWindow capOpenOutputLimit)
  · intro impossible
    contradiction
  · exact open_access positions marked
  · exact open_transport marked
  · exact ⟨physical, by constructor <;> decide, stable, marks,
      cap_open_abi_cursor_window positions (.visit 1) state pointer⟩

theorem cap_open_dfs_run_done (positions : Positions) (marked : Nat → Bool)
    (state final : MachineState)
    (physical : CapDfsStateControl false state (.visit 1))
    (stable : CapDfsStable false state capProgram.layout.trapdoor)
    (marks : CapMarksReady state 256 0 marked)
    (pointer : state.getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof + 576 * positions.card))
    (reached : final ∈ support (capDfsRun false marked 1022 (.visit 1) state)) :
    final.pc = capAdvanceDone false ∧
      CapDfsStable false final capProgram.layout.trapdoor ∧
      CapMarksReady final 256 0 marked ∧
      CapOpenCursorWindow capOpenOutputLimit .done final := by
  apply cap_dfs_machine_run_done false marked capProgram.layout.trapdoor
    (CapOpenCursorWindow capOpenOutputLimit)
  · intro impossible
    contradiction
  · exact open_access positions marked
  · exact open_transport marked
  · exact ⟨physical, by constructor <;> decide, stable, marks,
      cap_open_abi_cursor_window positions (.visit 1) state pointer⟩
  · exact reached

end CommitGolfCandidate
