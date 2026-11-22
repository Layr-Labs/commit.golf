import CommitGolfCandidate.Layout2V1EntryCheck
namespace CommitGolfCandidate.Layout2
open CommitGolf
open CommitGolfCandidate.Layout2Helpers (pget pget_get)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000
private theorem checked_1_0 : entriesCheck 1 0 2048=true := by decide +kernel
private theorem checked_1_2048 : entriesCheck 1 2048 2048=true := by decide +kernel
private theorem checked_1_4096 : entriesCheck 1 4096 176=true := by decide +kernel
theorem bank_1 (i : Nat) (hi : i<4272) : entryCheck 1 i=true := by
  by_cases hi0 : i<2048
  · exact entries_sound 1 0 2048 checked_1_0 i (by omega) (by omega)
  by_cases hi2048 : i<4096
  · exact entries_sound 1 2048 2048 checked_1_2048 i (by omega) (by omega)
  exact entries_sound 1 4096 176 checked_1_4096 i (by omega) (by omega)

end CommitGolfCandidate.Layout2
