import CommitGolfCandidate.CapExperimentalABI
import CommitGolfCandidate.InputMemory

/-! Actual experimental loader reads the returned private heap byte-for-byte.
This specializes the published BufferRefinement loader/slice argument to the
new image; it does not identify the old and new whole machine states. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_input_trapdoor_byte (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (offset : Nat) (inside : offset < capProgram.sizes.trapdoor) :
    (capProgram.initialState .opening (trapdoor, positions)).getByte
      (BitVec.ofNat 64 (capProgram.layout.trapdoor+offset)) =
        trapdoor.extractLsb' (8*offset) 8 := by
  have size : capProgram.sizes.trapdoor = 1610612736 := rfl
  rw [initial_input_byte capProgram .opening (trapdoor, positions) _
    (by change 4294971424+offset < 2^64; rw [size] at inside; omega)]
  have selected : capProgram.layout.trapdoor ≤ capProgram.layout.trapdoor+offset ∧
      capProgram.layout.trapdoor+offset <
        capProgram.layout.trapdoor+(8*capProgram.sizes.trapdoor+7)/8 := by
    rw [size]
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    selected, and_self, decide_true, Nat.add_sub_cancel_left]

theorem cap_open_input_trapdoor_digest
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (offset : Nat) (inside : offset+32 ≤ capProgram.sizes.trapdoor) :
    readBuffer (capProgram.initialState .opening (trapdoor, positions))
      (capProgram.layout.trapdoor+offset) 32 = trapdoor.extractLsb' (8*offset) 256 := by
  apply read_serialized_slice
  intro byte small
  simpa only [Nat.add_assoc] using
    cap_open_input_trapdoor_byte trapdoor positions (offset+byte) (by omega)

theorem cap_open_input_trapdoor_roundtrip (state : MachineState)
    (positions : Positions) (offset : Nat) (inside : offset+32 ≤ capProgram.sizes.trapdoor) :
    readBuffer (capProgram.initialState .opening
      (readBuffer state capProgram.layout.trapdoor capProgram.sizes.trapdoor, positions))
      (capProgram.layout.trapdoor+offset) 32 =
        readBuffer state (capProgram.layout.trapdoor+offset) 32 := by
  rw [cap_open_input_trapdoor_digest _ positions offset inside,
    read_buffer_slice _ _ _ _ _ inside]

end CommitGolfCandidate
