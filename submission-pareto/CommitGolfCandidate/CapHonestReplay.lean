import CommitGolfCandidate.CapHonestOpening
import CommitGolfCandidate.CapBatchReplay

/-! Honest logical records are accepted by the paid lower-and-cap replay.
This connects semantic completeness to a real World query transcript; the
actual checker execution and its byte parser are still separate bridges. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem cap_honest_paid_replay (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    ∃ inputs : List (BitVec 512),
      oracle.run (capReplayBatch (capHonestLowerRecords message committed positions)
        (capOpenBoundaryDigests
          (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions)
        (readBuffer committed 4294971392 32)) =
        pure (some (capLowerBatchInputs oracle.compression
          (capHonestLowerRecords message committed positions) ++ inputs),
          25 * (capHonestLowerRecords message committed positions).length + inputs.length) := by
  obtain ⟨roots, accepted, agree⟩ :=
    cap_honest_lower_collection oracle message committed correct positions
  obtain ⟨inputs, capRun, batchRun⟩ := cap_replay_batch_run oracle
    (capHonestLowerRecords message committed positions)
    (capOpenBoundaryDigests
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions)
    (readBuffer committed 4294971392 32) roots accepted
    (cap_honest_cap_accepts oracle message committed correct positions roots accepted agree)
  exact ⟨inputs, batchRun⟩

end CommitGolfCandidate
