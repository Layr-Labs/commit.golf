import CommitGolfCandidate.CapOpenLoadedSuffix
import CommitGolfCandidate.CapOpenProofBudget

/-! Complete header-free output bytes and reported length for the actual
nonempty opening. The list is read from the original ABI trapdoor; its honest
tree interpretation and checker acceptance remain distinct obligations. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenLoadedBytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : Proof :=
  capDigestEncoding (capOpenLowerDigests trapdoor positions) ++
    capDigestEncoding (capOpenBoundaryDigests trapdoor positions)

theorem cap_open_loaded_bytes_length
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenLoadedBytes trapdoor positions).length =
      576*positions.card+32*(capOpenBoundaryDigests trapdoor positions).length := by
  rw [capOpenLoadedBytes, List.length_append, cap_digest_encoding_length,
    cap_digest_encoding_length, cap_open_lower_digests_length]
  omega

theorem cap_open_loaded_bytes_byte
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (final : MachineState)
    (reached : final ∈ support (capDfsRun false (capOpenRequestedMarks positions)
      1022 (.visit 1) (capOpenTraversalInitial trapdoor positions)))
    (offset : Nat) (inside : offset < (capOpenLoadedBytes trapdoor positions).length) :
    (capOpenExitState final).getByte
        (BitVec.ofNat 64 (capProgram.layout.proof+offset)) =
      (capOpenLoadedBytes trapdoor positions)[offset]?.getD 0 := by
  by_cases lower : offset < 576*positions.card
  · rw [capOpenLoadedBytes, List.getElem?_append_left (by
      rw [cap_digest_encoding_length, cap_open_lower_digests_length]; omega)]
    exact cap_open_loaded_prefix_bytes trapdoor positions positive final reached offset lower
  · have suffix : offset-576*positions.card <
        32*(capOpenBoundaryDigests trapdoor positions).length := by
      rw [cap_open_loaded_bytes_length] at inside
      omega
    rw [capOpenLoadedBytes, List.getElem?_append_right (by
      rw [cap_digest_encoding_length, cap_open_lower_digests_length]; omega),
      cap_digest_encoding_length, cap_open_lower_digests_length]
    have emitted := cap_open_loaded_suffix_bytes trapdoor positions positive final reached
      (offset-576*positions.card) suffix
    have address : capProgram.layout.proof+576*positions.card+
        (offset-576*positions.card) = capProgram.layout.proof+offset := by omega
    have length : 32*(18*positions.card) = 576*positions.card := by omega
    simpa only [address, length] using emitted

theorem cap_open_loaded_bytes_report
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (final : MachineState)
    (reached : final ∈ support (capDfsRun false (capOpenRequestedMarks positions)
      1022 (.visit 1) (capOpenTraversalInitial trapdoor positions))) :
    ((capOpenExitState final).getReg .x11).toNat =
      (capOpenLoadedBytes trapdoor positions).length := by
  have pointer := cap_open_run_cursor_count (capOpenRequestedMarks positions)
    1022 (.visit 1) _ final (capProgram.layout.proof+576*positions.card)
    (cap_open_traversal_initial_cursor trapdoor positions positive) reached
  have base := (cap_open_run_base (capOpenRequestedMarks positions) 1022 (.visit 1)
    _ final reached).trans (cap_open_traversal_initial_proof_base trapdoor positions)
  have count := cap_control_boundaries_length (capOpenRequestedMarks positions) 1022 (.visit 1)
  have space := (cap_open_abi_output_space positions).1
  have limitBound := (cap_open_abi_output_space positions).2
  have noWrap : capProgram.layout.proof+
      (576*positions.card+32*(capOpenBoundaryDigests trapdoor positions).length) < 2^64 := by
    simp only [capOpenBoundaryDigests, List.length_map]
    simp only [MEMORY_BYTES] at limitBound
    omega
  rw [cap_open_loaded_bytes_length]
  apply cap_open_exit_report final capProgram.layout.proof _ base ?_ noWrap
  simpa only [capOpenBoundaryDigests, List.length_map, Nat.add_assoc] using pointer

end CommitGolfCandidate
