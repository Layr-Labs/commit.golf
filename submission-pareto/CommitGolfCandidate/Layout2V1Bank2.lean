import CommitGolfCandidate.Layout2V1EntryCheck
namespace CommitGolfCandidate.Layout2
open CommitGolf
open TwoPermutationPrototype.GroupedOpening (pget pget_get)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000
private theorem checked_2_0 : entriesCheck 2 0 2048=true := by decide +kernel
private theorem checked_2_2048 : entriesCheck 2 2048 2048=true := by decide +kernel
private theorem checked_2_4096 : entriesCheck 2 4096 2048=true := by decide +kernel
private theorem checked_2_6144 : entriesCheck 2 6144 2048=true := by decide +kernel
private theorem checked_2_8192 : entriesCheck 2 8192 352=true := by decide +kernel
theorem bank_2 (i : Nat) (hi : i<8544) : entryCheck 2 i=true := by
  by_cases hi0 : i<2048
  · exact entries_sound 2 0 2048 checked_2_0 i (by omega) (by omega)
  by_cases hi2048 : i<4096
  · exact entries_sound 2 2048 2048 checked_2_2048 i (by omega) (by omega)
  by_cases hi4096 : i<6144
  · exact entries_sound 2 4096 2048 checked_2_4096 i (by omega) (by omega)
  by_cases hi6144 : i<8192
  · exact entries_sound 2 6144 2048 checked_2_6144 i (by omega) (by omega)
  exact entries_sound 2 8192 352 checked_2_8192 i (by omega) (by omega)

end CommitGolfCandidate.Layout2
