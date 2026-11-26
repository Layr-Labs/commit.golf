import CommitGolfCandidate.ReconstructedHonestNameCases00
import CommitGolfCandidate.ReconstructedHonestNameCases01
import CommitGolfCandidate.ReconstructedHonestNameCases02
import CommitGolfCandidate.ReconstructedHonestNameCases03
import CommitGolfCandidate.ReconstructedHonestNameCases04
import CommitGolfCandidate.ReconstructedHonestNameCases05
import CommitGolfCandidate.ReconstructedHonestNameCases06
import CommitGolfCandidate.ReconstructedHonestNameCases07
namespace CommitGolfCandidate.Reconstruction.HonestNameKernel
open HonestWideShapes
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

attribute [local irreducible] checked

theorem all_checked : ∀ n∈points, checked n=true := by
  simp only [points,List.forall_mem_cons]
  exact ⟨at111,at112,at128,at130,at136,at139,at141,at142,at143,at144,at149,at150,at160,at176,at184,at192,at197,at208,at224,at240,at256,at272,at288,at304,at320,at336,at352,at368,at384,at400,at416,at432,at448,at464,at480,at496,at512,at528,at544,at560,at576,at592,at608,at624,at640,at656,at672,at688,at704,at720,at736,at752,at768,at784,at800,at816,at832,at848,at864,at880,at896,at912,at928,at944,at960,at976,at992,at1008,at1024,at1040,at1056,at1072,at1088,at1104,at1120,at1136,at1152,at1168,at1184,at1200,at1216,at1232,at1248,at1264,at1280,at1296,at1312,at1328,at1344,at1360,at1376,at1392,at1408,at1424,at1429,(by intro _ h; cases h)⟩

end CommitGolfCandidate.Reconstruction.HonestNameKernel
