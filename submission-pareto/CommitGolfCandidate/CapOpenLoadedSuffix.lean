import CommitGolfCandidate.CapOpenLoadedPrefix
import CommitGolfCandidate.CapBoundaryNodes

/-! The emitted cap suffix consists exactly of the canonical unknown-node
digest sequence read from the original ABI trapdoor. This byte theorem applies
to arbitrary trapdoors; honest parent hash equations are a separate bridge. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem high_read (state reference : MachineState) (address count : Nat)
    (high : 32768 ≤ address) (bound : address+count ≤ 2^64)
    (frame : CapHighBytes state reference) :
    readBuffer state address count = readBuffer reference address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro offset member
  have small := Finset.mem_range.mp member
  rw [frame (address+offset) (by omega) (by omega)]

def capOpenBoundaryDigests
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : List Digest :=
  (capControlBoundaries (capOpenRequestedMarks positions) 1022 (.visit 1)).map
    (fun node => readBuffer (capProgram.initialState .opening (trapdoor, positions))
      (capProgram.layout.trapdoor+32*node) 32)

theorem cap_open_traversal_initial_root_read
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (node : Nat) (bounded : node < 512) :
    readBuffer (capOpenTraversalInitial trapdoor positions)
      (capProgram.layout.trapdoor+32*node) 32 =
      readBuffer (capProgram.initialState .opening (trapdoor, positions))
        (capProgram.layout.trapdoor+32*node) 32 := by
  have high : 32768 ≤ capProgram.layout.trapdoor+32*node := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  have below : capProgram.layout.trapdoor+32*node+32 ≤ capProgram.layout.proof := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  have outputBound : capProgram.layout.proof ≤ 2^64 := by decide
  have first : readBuffer (capOpenTraversalInitial trapdoor positions)
      (capProgram.layout.trapdoor+32*node) 32 =
      readBuffer (capOpenRecordsFinal trapdoor positions)
        (capProgram.layout.trapdoor+32*node) 32 :=
    high_read _ _ _ 32 high (by omega)
      (cap_open_traversal_initial_high trapdoor positions positive)
  exact first.trans (cap_open_retained_read capProgram.layout.proof _ _ _ 32 high below
    (cap_open_records_final_ready trapdoor positions positive).frame)

theorem cap_open_loaded_suffix_bytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (final : MachineState)
    (reached : final ∈ support (capDfsRun false (capOpenRequestedMarks positions)
      1022 (.visit 1) (capOpenTraversalInitial trapdoor positions)))
    (offset : Nat)
    (inside : offset < 32*(capOpenBoundaryDigests trapdoor positions).length) :
    (capOpenExitState final).getByte
        (BitVec.ofNat 64 (capProgram.layout.proof+576*positions.card+offset)) =
      (capDigestEncoding (capOpenBoundaryDigests trapdoor positions))[offset]?.getD 0 := by
  let nodes := capControlBoundaries (capOpenRequestedMarks positions) 1022 (.visit 1)
  have selected : nodes.map (fun node =>
      readBuffer (capOpenTraversalInitial trapdoor positions)
        (capProgram.layout.trapdoor+32*node) 32) =
      capOpenBoundaryDigests trapdoor positions := by
    apply List.map_congr_left
    intro node member
    have bounded := cap_control_boundaries_nodes
      (capOpenRequestedMarks positions) 1022 (.visit 1)
      (by constructor <;> decide) node member
    exact cap_open_traversal_initial_root_read trapdoor positions positive node bounded.2
  have emitted := cap_open_run_bytes (capOpenRequestedMarks positions)
    capProgram.layout.trapdoor capOpenOutputLimit
    (capProgram.layout.proof+576*positions.card)
    (capOpenTraversalInitial trapdoor positions)
    (cap_open_abi_output_space positions).2 cap_open_abi_root_space.1
    cap_open_abi_root_space.2 (cap_open_abi_heap_before_prefix positions)
    1022 (.visit 1) _ final
    (cap_open_loaded_read_ready trapdoor positions positive) reached offset
    (by simpa only [capOpenBoundaryDigests, List.length_map] using inside)
  have pointer := cap_open_traversal_initial_cursor trapdoor positions positive
  have bound : capProgram.layout.proof+576*positions.card < 2^64 := by
    have space := (cap_open_abi_output_space positions).1
    have limitBound := (cap_open_abi_output_space positions).2
    simp only [MEMORY_BYTES] at limitBound
    omega
  rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, selected] at emitted
  have returned : (capOpenExitState final).getByte = final.getByte := by
    funext address
    simp only [MachineState.getByte, MachineState.getMem, cap_open_exit_memory]
  rw [returned]
  exact emitted

end CommitGolfCandidate
