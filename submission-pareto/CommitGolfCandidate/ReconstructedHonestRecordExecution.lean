import CommitGolfCandidate.ReconstructedHonestRecordIteration
import CommitGolfCandidate.ReconstructedHonestRecordFragments00
import CommitGolfCandidate.ReconstructedHonestRecordFragments01
import CommitGolfCandidate.ReconstructedHonestRecordFragments02
import CommitGolfCandidate.ReconstructedHonestRecordFragments03
import CommitGolfCandidate.ReconstructedHonestRecordFragments04
import CommitGolfCandidate.ReconstructedHonestRecordFragments05
import CommitGolfCandidate.ReconstructedHonestRecordFragments06
import CommitGolfCandidate.ReconstructedHonestRecordFragments07
import CommitGolfCandidate.ReconstructedHonestRecordFragments08
import CommitGolfCandidate.ReconstructedHonestRecordFragments09
import CommitGolfCandidate.ReconstructedHonestRecordFragments10
import CommitGolfCandidate.ReconstructedHonestRecordFragments11
import CommitGolfCandidate.ReconstructedHonestRecordFragments12
import CommitGolfCandidate.ReconstructedHonestRecordFragments13
import CommitGolfCandidate.ReconstructedHonestRecordFragments14

namespace CommitGolfCandidate.Reconstruction.HonestRecordExecution
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open HonestRecordShapes HonestRecordIteration HonestRecordCheck

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem missing (i k : Nat) (outside : k∉points) : current i k=none := by
  unfold current
  split <;> first | rfl | (exfalso; apply outside; decide)

theorem all_checked : ValidChecks := by
  intro i k
  by_cases inside : k∈points
  · simp only [points,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact receipt111 i
    · exact receipt112 i
    · exact receipt128 i
    · exact receipt130 i
    · exact first_store i
    · exact receipt144 i
    · exact receipt149 i
    · exact receipt160 i
    · exact receipt176 i
    · exact receipt184 i
    · exact receipt192 i
    · exact receipt197 i
    · exact receipt208 i
    · exact receipt224 i
    · exact receipt240 i
    · exact receipt256 i
    · exact receipt272 i
    · exact receipt288 i
    · exact receipt304 i
    · exact receipt320 i
    · exact receipt336 i
    · exact receipt352 i
    · exact receipt368 i
    · exact receipt384 i
    · exact receipt400 i
    · exact receipt416 i
    · exact receipt432 i
    · exact receipt448 i
    · exact receipt464 i
    · exact receipt480 i
    · exact receipt496 i
    · exact receipt512 i
    · exact receipt528 i
    · exact receipt544 i
    · exact receipt560 i
    · exact receipt576 i
    · exact receipt592 i
    · exact receipt608 i
    · exact receipt624 i
    · exact receipt640 i
    · exact receipt656 i
    · exact receipt672 i
    · exact receipt688 i
    · exact receipt704 i
    · exact receipt720 i
    · exact receipt736 i
    · exact receipt752 i
    · exact receipt768 i
    · exact receipt784 i
    · exact receipt800 i
    · exact receipt816 i
    · exact receipt832 i
    · exact receipt848 i
    · exact receipt864 i
    · exact receipt880 i
    · exact receipt896 i
    · exact receipt912 i
    · exact receipt928 i
    · exact receipt944 i
    · exact receipt960 i
    · exact receipt976 i
    · exact receipt992 i
    · exact receipt1008 i
    · exact receipt1024 i
    · exact receipt1040 i
    · exact receipt1056 i
    · exact receipt1072 i
    · exact receipt1088 i
    · exact receipt1104 i
    · exact receipt1120 i
    · exact receipt1136 i
    · exact receipt1152 i
    · exact receipt1168 i
    · exact receipt1184 i
    · exact receipt1200 i
    · exact receipt1216 i
    · exact receipt1232 i
    · exact receipt1248 i
    · exact receipt1264 i
    · exact receipt1280 i
    · exact receipt1296 i
    · exact receipt1312 i
    · exact receipt1328 i
    · exact receipt1344 i
    · exact receipt1360 i
    · exact receipt1376 i
    · exact receipt1392 i
    · exact receipt1408 i
    · exact receipt1424 i
    · rfl
  · simp only [checked,missing i.val k inside]

/-- Exact ABI batch and the real RV64 record prologue, 128 iterations and cap entry. -/
theorem batch (trap : HonestInputs.Trapdoor) (ps : Positions) (batchSize : ps.card=128) (tail : Nat)
    (cap : ∀ t, t.pc=CommitBlocks.addr 1429 → HonestProtected.Holds HonestRecordMemory.context (capStart 128) t →
      HonestCapPrices.Budget t true tail) :
    HonestCapPrices.Budget (HonestInputs.initial trap ps) true (152718+tail) :=
  abi_records all_checked trap ps batchSize tail cap

end CommitGolfCandidate.Reconstruction.HonestRecordExecution
