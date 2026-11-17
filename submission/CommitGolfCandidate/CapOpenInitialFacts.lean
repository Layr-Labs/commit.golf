import CommitGolfCandidate.CapOpenSetup
import CommitGolfCandidate.CapOpenInputFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_initial_root_base
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getReg .x9 =
      BitVec.ofNat 64 capProgram.layout.trapdoor := by
  exact (cap_open_setup_registers _).1

theorem cap_open_initial_index_pointer
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getReg .x24 =
      BitVec.ofNat 64 capProgram.layout.indices := by
  exact (cap_open_setup_registers _).2.1

theorem cap_open_initial_proof_pointer
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getReg .x25 =
      BitVec.ofNat 64 capProgram.layout.proof := by
  exact (cap_open_setup_registers _).2.2.1

theorem cap_open_initial_count
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getReg .x27 =
      BitVec.ofNat 64 positions.card := by
  exact (cap_open_setup_registers _).2.2.2.1

theorem cap_open_initial_salt_base
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getReg .x18 =
      BitVec.ofNat 64 (capProgram.layout.trapdoor + 64*LENGTH) := by
  have salt := (cap_open_setup_registers
    (capProgram.initialState .opening (trapdoor, positions))).2.2.2.2.2.1
  change _ = BitVec.ofNat 64 capProgram.layout.trapdoor + BitVec.ofNat 64 1073741824 at salt
  simpa only [← BitVec.ofNat_add, LENGTH, LOG_LENGTH, Nat.reducePow, Nat.reduceMul] using salt

theorem cap_open_initial_workspace_zero
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (address : Nat) (bounded : address+8 ≤ 32768) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getMem
      (BitVec.ofNat 64 address) = 0 := by
  have zero := cap_experimental_opening_workspace_zero trapdoor positions address bounded
  simpa only [MachineState.getMem, cap_open_setup_memory] using zero

theorem cap_open_initial_byte_frame
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) (floor : Nat) :
    CapOpenInputFrame floor
      (capProgram.initialState .opening (trapdoor, positions))
      (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))) := by
  intro address below
  simp only [MachineState.getByte, MachineState.getMem, cap_open_setup_memory]

end CommitGolfCandidate
