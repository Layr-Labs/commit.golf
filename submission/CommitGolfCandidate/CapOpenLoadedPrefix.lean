import CommitGolfCandidate.CapOpenLowerBytes
import CommitGolfCandidate.CapOpenLoadedExecution
import CommitGolfCandidate.CapOpenEntryFrame
import CommitGolfCandidate.CapOpenReadDigest

/-! Exact lower-record bytes survive the actual mark pass, cap traversal and
success return. The frame is relative to the completed record state and only
claims the populated prefix, not equality of the growing output buffer. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_loaded_read_ready
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapOpenReadReady (capOpenRequestedMarks positions) capProgram.layout.trapdoor
      capOpenOutputLimit (capProgram.layout.proof+576*positions.card)
      (capOpenTraversalInitial trapdoor positions) (.visit 1)
      (capOpenTraversalInitial trapdoor positions) := by
  have window := cap_open_abi_cursor_window positions (.visit 1)
    (capOpenTraversalInitial trapdoor positions)
    (cap_open_traversal_initial_cursor trapdoor positions positive)
  refine ⟨⟨cap_open_traversal_initial_control trapdoor positions positive,
    by constructor <;> decide,
    cap_open_traversal_initial_stable trapdoor positions positive,
    cap_open_traversal_initial_marks trapdoor positions positive, window⟩, ?_, ?_⟩
  · have space := (cap_open_abi_output_space positions).1
    have limitBound := (cap_open_abi_output_space positions).2
    have bounded : capProgram.layout.proof+576*positions.card < 2^64 := by
      simp only [MEMORY_BYTES] at limitBound
      omega
    rw [cap_open_traversal_initial_cursor trapdoor positions positive,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
  · intro address inside
    rfl

theorem cap_open_loaded_prefix_bytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (final : MachineState)
    (reached : final ∈ support (capDfsRun false (capOpenRequestedMarks positions)
      510 (.visit 1) (capOpenTraversalInitial trapdoor positions)))
    (offset : Nat) (inside : offset < 576*positions.card) :
    (capOpenExitState final).getByte
        (BitVec.ofNat 64 (capProgram.layout.proof+offset)) =
      (capDigestEncoding (capOpenLowerDigests trapdoor positions))[offset]?.getD 0 := by
  have frame := (cap_open_completed_input_frame (capOpenRequestedMarks positions)
    capProgram.layout.trapdoor capOpenOutputLimit
    (capProgram.layout.proof+576*positions.card)
    (capOpenTraversalInitial trapdoor positions)
    (cap_open_abi_output_space positions).2 cap_open_abi_root_space.1
    cap_open_abi_root_space.2 _ final
    (cap_open_loaded_read_ready trapdoor positions positive) reached).2.1
  have high : 22528 ≤ capProgram.layout.proof+offset := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  have bound : capProgram.layout.proof+offset < 2^64 := by
    have space := (cap_open_abi_output_space positions).1
    have limitBound := (cap_open_abi_output_space positions).2
    simp only [MEMORY_BYTES] at limitBound
    omega
  have returned : (capOpenExitState final).getByte =
      final.getByte := by
    funext pointer
    simp only [MachineState.getByte, MachineState.getMem, cap_open_exit_memory]
  rw [returned, frame _ (by omega)]
  exact (cap_open_traversal_initial_high trapdoor positions positive
    _ high bound).trans (cap_open_lower_bytes trapdoor positions positive offset inside)

end CommitGolfCandidate
