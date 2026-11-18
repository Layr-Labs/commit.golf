import CommitGolfCandidate.CapOpenCursorWindow
import CommitGolfCandidate.CapExperimentalABI

/-! The retained opening ABI allocates 800 bytes per possible leaf. The cap
record prefix uses 576 bytes per requested leaf, leaving ample space for the
conservative traversal-rank window even at the maximum admitted cardinality.
This proves address admission, not the tighter serialized proof-size claim. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_abi_output_space (positions : Positions) :
    capProgram.layout.proof + 576 * positions.card + 32 * 1022 ≤
      capProgram.layout.proof + capProgram.sizes.proof ∧
    capProgram.layout.proof + capProgram.sizes.proof ≤ MEMORY_BYTES := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  norm_num [capProgram, capExperimental, candidate, sizes, layout, trapdoorBytes,
    openingBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES, MEMORY_BYTES]
    at cardinal ⊢
  omega

theorem cap_open_abi_root_space :
    capProgram.layout.trapdoor + 16384 ≤ MEMORY_BYTES ∧
      capProgram.layout.trapdoor % 8 = 0 := by
  norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
    LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES, MEMORY_BYTES]

theorem cap_open_abi_prefix_aligned (positions : Positions) :
    (capProgram.layout.proof + 576 * positions.card) % 8 = 0 := by
  norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
    LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES, Nat.add_mod, Nat.mul_mod]

theorem cap_open_abi_cursor_window (positions : Positions)
    (control : CapDfsControl) (state : MachineState)
    (pointer : state.getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof + 576 * positions.card)) :
    CapOpenCursorWindow (capProgram.layout.proof + capProgram.sizes.proof)
      control state := by
  apply cap_open_cursor_initial _ _ control state pointer
  · exact cap_open_abi_prefix_aligned positions
  · norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · exact (cap_open_abi_output_space positions).1

end CommitGolfCandidate
