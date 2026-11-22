import CommitGolfCandidate.Layout2V1EntryCheck
namespace CommitGolfCandidate.Layout2
open CommitGolf
open TwoPermutationPrototype.GroupedOpening (pget pget_get)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000
private theorem checked_3_0 : entriesCheck 3 0 2048=true := by decide +kernel
private theorem checked_3_2048 : entriesCheck 3 2048 2048=true := by decide +kernel
private theorem checked_3_4096 : entriesCheck 3 4096 2048=true := by decide +kernel
private theorem checked_3_6144 : entriesCheck 3 6144 2048=true := by decide +kernel
private theorem checked_3_8192 : entriesCheck 3 8192 2048=true := by decide +kernel
private theorem checked_3_10240 : entriesCheck 3 10240 2048=true := by decide +kernel
private theorem checked_3_12288 : entriesCheck 3 12288 528=true := by decide +kernel
theorem bank_3 (i : Nat) (hi : i<12816) : entryCheck 3 i=true := by
  by_cases hi0 : i<2048
  · exact entries_sound 3 0 2048 checked_3_0 i (by omega) (by omega)
  by_cases hi2048 : i<4096
  · exact entries_sound 3 2048 2048 checked_3_2048 i (by omega) (by omega)
  by_cases hi4096 : i<6144
  · exact entries_sound 3 4096 2048 checked_3_4096 i (by omega) (by omega)
  by_cases hi6144 : i<8192
  · exact entries_sound 3 6144 2048 checked_3_6144 i (by omega) (by omega)
  by_cases hi8192 : i<10240
  · exact entries_sound 3 8192 2048 checked_3_8192 i (by omega) (by omega)
  by_cases hi10240 : i<12288
  · exact entries_sound 3 10240 2048 checked_3_10240 i (by omega) (by omega)
  exact entries_sound 3 12288 528 checked_3_12288 i (by omega) (by omega)

end CommitGolfCandidate.Layout2
