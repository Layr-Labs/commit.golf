import CommitGolfCandidate.CapCheckRetainedIndex
import CommitGolfCandidate.BufferRefinement

/-! Opened values loaded by the experimental checker are unchanged ABI bytes.
The loader memory projection is equal because input buffers and embedded
data are identical; no old checker fetch or execution theorem is reused.
Later states use the established high-byte frame. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_loader_memory (input : CheckInput) :
    (capProgram.initialState .check input).mem =
      (submission.initialState .check input).mem := rfl

theorem cap_check_input_value_block (input : CheckInput) (ordinal block : Nat)
    (present : ordinal < input.positions.card) (inside : block < 8) :
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.values + 256*ordinal + 32*block) 32 =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present))).extractLsb' (256*block) 256 := by
  exact (read_buffer_memory_congr _ _ (cap_check_loader_memory input) _ 32).trans
    (check_input_value_block input ordinal block present inside)

theorem cap_check_retained_value_block (input : CheckInput) (state : MachineState)
    (ordinal block : Nat) (present : ordinal < input.positions.card) (inside : block < 8)
    (frame : CapHighBytes state (capProgram.initialState .check input)) :
    readBuffer state (capProgram.layout.values + 256*ordinal + 32*block) 32 =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present))).extractLsb' (256*block) 256 := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have high : 22528 ≤ capProgram.layout.values + 256*ordinal + 32*block := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  have bounded : capProgram.layout.values + 256*ordinal + 32*block + 32 ≤ 2^64 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  exact (cap_high_bytes_read state _ _ 32 high bounded frame).trans
    (cap_check_input_value_block input ordinal block present inside)

end CommitGolfCandidate
