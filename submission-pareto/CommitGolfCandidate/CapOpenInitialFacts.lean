import CommitGolfCandidate.CapOpenSetup
import CommitGolfCandidate.CapOpenInputFrame

/-! Opening setup specialized to the actual ABI loader. The unused stack pointer
is not equated with the old image. Low mark words stay zero until the record
pass writes the requested cap groups, and all input bytes remain unchanged. -/
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
      BitVec.ofNat 64 (capProgram.layout.trapdoor + 1811939584) := by
  have salt := (cap_open_setup_registers
    (capProgram.initialState .opening (trapdoor, positions))).2.2.2.2.2.1
  change _ = BitVec.ofNat 64 capProgram.layout.trapdoor + BitVec.ofNat 64 1811939584 at salt
  simpa only [← BitVec.ofNat_add] using salt

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

/-- The opening input buffers (trapdoor, then indices) end at the values base. -/
theorem cap_open_input_buffers_end
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    ∀ buffer ∈ capProgram.inputBuffers .opening (trapdoor, positions),
      buffer.address + buffer.length ≤ capProgram.layout.values := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  intro buffer member
  simp only [Submission.inputBuffers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp only [fixedBuffer]
    decide
  · simp only [positionsBuffer, Finset.length_sort]
    have values : capProgram.layout.indices + 8*LENGTH = capProgram.layout.values := by decide
    rw [← values]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 8 cardinal) _

/-- A word above every input buffer of an image without data is zero after loading. -/
private theorem initial_zero_word_after (candidate : Submission) (program : Program)
    (input : Input candidate.sizes program) (address : Nat)
    (bounded : address < 2^64) (noData : (candidate.image program).data = [])
    (afterInputs : ∀ buffer ∈ candidate.inputBuffers program input,
      buffer.address + buffer.length ≤ address) :
    (candidate.initialState program input).getMem (BitVec.ofNat 64 address) = 0 := by
  rw [initial_input_word candidate program input address bounded]
  have bytes (offset : Nat) (small : offset < 8) :
      inputByte candidate program input (address + offset) = 0 := by
    have noneSelected : (candidate.inputBuffers program input).find?
        (fun buffer => decide (buffer.address ≤ address + offset ∧
          address + offset < buffer.address + buffer.length)) = none := by
      apply List.find?_eq_none.mpr
      intro buffer member
      have last := afterInputs buffer member
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    unfold inputByte
    rw [noneSelected]
    simp [noData]
  have zero : (∑ offset ∈ Finset.range 8,
      (inputByte candidate program input (address + offset)).toNat * 2^(8*offset)) = 0 := by
    apply Finset.sum_eq_zero
    intro offset member
    rw [bytes offset (Finset.mem_range.mp member)]
    simp
  rw [zero]
  rfl

/-- Every proof-buffer word of the loaded opening state is zero: the proof buffer lies above
every opening input buffer and the image carries no data. -/
theorem cap_open_initial_proof_zero
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (address : Nat) (above : capProgram.layout.proof ≤ address)
    (bounded : address + 8 ≤ MEMORY_BYTES) :
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))).getMem
      (BitVec.ofNat 64 address) = 0 := by
  have small : address < 2^64 := by
    have memory : MEMORY_BYTES ≤ 2^64 := by decide
    omega
  have ordered : capProgram.layout.values ≤ capProgram.layout.proof := by decide
  have zero := initial_zero_word_after capProgram .opening (trapdoor, positions) address small rfl
    (fun buffer member => Nat.le_trans (cap_open_input_buffers_end trapdoor positions buffer member)
      (Nat.le_trans ordered above))
  simpa only [MachineState.getMem, cap_open_setup_memory] using zero

end CommitGolfCandidate
