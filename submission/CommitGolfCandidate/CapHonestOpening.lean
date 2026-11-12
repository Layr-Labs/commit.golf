import CommitGolfCandidate.CapHonestParse
import CommitGolfCandidate.CapHonestView
import CommitGolfCandidate.CapCommitBridge
import CommitGolfCandidate.CapOpenProgramRun

/-! Honest proof bytes are the actual opening image's bytes, and their cap
suffix decodes against the duplicate-checked lower roots. This is the semantic
completeness connector; actual checker execution is still proved separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_honest_opening_bytes (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) (positive : 0 < positions.card) :
    capOpenLoadedBytes
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      capDigestEncoding
        (capLowerTranscript (capHonestLowerRecords message committed positions) ++
          capProof oracle.compression (capHeapTree (heapDigest committed 4294971424) 8 1)
            (capHeapView (heapDigest committed 4294971424) (capOpenRequestedMarks positions) 8 1)) := by
  rw [capOpenLoadedBytes, cap_honest_lower_loaded_transcript message committed positions,
    cap_open_honest_boundary_digests oracle message committed correct positions]
  simp only [capDigestEncoding, List.flatMap_append]

theorem cap_honest_cap_accepts (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) (roots : CapRootMap)
    (accepted : capLowerBatchRoots oracle.compression
      (capHonestLowerRecords message committed positions) (fun _ => none) = some roots)
    (agree : CapRootsAgree (fun group => heapDigest committed 4294971424 (256+group)) roots) :
    capDecode oracle.compression (capKnownView roots 8 0)
      (capOpenBoundaryDigests
        (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions) =
      some (readBuffer committed 4294971392 32, []) := by
  rw [cap_honest_known_view oracle message committed positions roots accepted agree,
    cap_open_honest_boundary_digests oracle message committed correct positions]
  have codec := cap_heap_codec oracle.compression (heapDigest committed 4294971424)
    (capOpenRequestedMarks positions) 8 1 []
  simp only [List.append_nil] at codec
  rw [codec, cap_heap_tree_root oracle.compression _ 
    (cap_open_committed_cap_parents oracle message committed correct) 8 1
    (by decide) (by decide)]
  rw [correct.1]

theorem cap_honest_lower_parses (message : Message) (committed : MachineState)
    (positions : Positions) (suffix : List Digest) :
    capParseLower message (capOpenRequestedIndices positions)
      (capLowerTranscript (capHonestLowerRecords message committed positions) ++ suffix) =
      some (capHonestLowerRecords message committed positions, suffix) := by
  have records : (capHonestLowerRecords message committed positions).map CapLowerRecord.index =
      capOpenRequestedIndices positions := by
    simp only [capHonestLowerRecords, List.map_map, capHonestLowerRecord]
    exact List.map_id _
  rw [← records]
  apply cap_parse_encoded_lower
  intro record member
  obtain ⟨index, requested, rfl⟩ := List.mem_map.mp member
  rfl

end CommitGolfCandidate
