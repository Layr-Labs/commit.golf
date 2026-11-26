import CommitGolfCandidate.ReconstructedHonestFlagTables00
import CommitGolfCandidate.ReconstructedHonestFlagTables01
import CommitGolfCandidate.ReconstructedHonestFlagTables02
import CommitGolfCandidate.ReconstructedHonestFlagTables03
import CommitGolfCandidate.ReconstructedHonestFlagTables04
import CommitGolfCandidate.ReconstructedHonestFlagTables05
import CommitGolfCandidate.ReconstructedHonestFlagTables06
import CommitGolfCandidate.ReconstructedHonestFlagTables07
import CommitGolfCandidate.ReconstructedHonestFlagTables08

namespace CommitGolfCandidate.Reconstruction.HonestFlagCheck
open HonestRecordShapes
set_option maxRecDepth 32768
private theorem missing (i k : Nat) (outside : k∉points) : current i k=none := by
  unfold current
  split <;> first | rfl | (exfalso; apply outside; decide)

theorem all_checked : ValidChecks := by
  intro i k
  by_cases inside : k∈points
  · simp only [points,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact flags111 i
    · exact flags112 i
    · exact flags128 i
    · exact flags130 i
    · exact flags143 i
    · exact flags144 i
    · exact flags149 i
    · exact flags160 i
    · exact flags176 i
    · exact flags184 i
    · exact flags192 i
    · exact flags197 i
    · exact flags208 i
    · exact flags224 i
    · exact flags240 i
    · exact flags256 i
    · exact flags272 i
    · exact flags288 i
    · exact flags304 i
    · exact flags320 i
    · exact flags336 i
    · exact flags352 i
    · exact flags368 i
    · exact flags384 i
    · exact flags400 i
    · exact flags416 i
    · exact flags432 i
    · exact flags448 i
    · exact flags464 i
    · exact flags480 i
    · exact flags496 i
    · exact flags512 i
    · exact flags528 i
    · exact flags544 i
    · exact flags560 i
    · exact flags576 i
    · exact flags592 i
    · exact flags608 i
    · exact flags624 i
    · exact flags640 i
    · exact flags656 i
    · exact flags672 i
    · exact flags688 i
    · exact flags704 i
    · exact flags720 i
    · exact flags736 i
    · exact flags752 i
    · exact flags768 i
    · exact flags784 i
    · exact flags800 i
    · exact flags816 i
    · exact flags832 i
    · exact flags848 i
    · exact flags864 i
    · exact flags880 i
    · exact flags896 i
    · exact flags912 i
    · exact flags928 i
    · exact flags944 i
    · exact flags960 i
    · exact flags976 i
    · exact flags992 i
    · exact flags1008 i
    · exact flags1024 i
    · exact flags1040 i
    · exact flags1056 i
    · exact flags1072 i
    · exact flags1088 i
    · exact flags1104 i
    · exact flags1120 i
    · exact flags1136 i
    · exact flags1152 i
    · exact flags1168 i
    · exact flags1184 i
    · exact flags1200 i
    · exact flags1216 i
    · exact flags1232 i
    · exact flags1248 i
    · exact flags1264 i
    · exact flags1280 i
    · exact flags1296 i
    · exact flags1312 i
    · exact flags1328 i
    · exact flags1344 i
    · exact flags1360 i
    · exact flags1376 i
    · exact flags1392 i
    · exact flags1408 i
    · exact flags1424 i
    · rfl
  · simp only [checked,missing i.val k inside]
end CommitGolfCandidate.Reconstruction.HonestFlagCheck
