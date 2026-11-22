import CommitGolfCandidate.Layout2V1EntryCheck
namespace CommitGolfCandidate.Layout2
open CommitGolf
open CommitGolfCandidate.Layout2Helpers (pget pget_get)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000
private theorem checked_4_0 : entriesCheck 4 0 2048=true := by decide +kernel
private theorem checked_4_2048 : entriesCheck 4 2048 2048=true := by decide +kernel
private theorem checked_4_4096 : entriesCheck 4 4096 2048=true := by decide +kernel
private theorem checked_4_6144 : entriesCheck 4 6144 2048=true := by decide +kernel
private theorem checked_4_8192 : entriesCheck 4 8192 2048=true := by decide +kernel
private theorem checked_4_10240 : entriesCheck 4 10240 2048=true := by decide +kernel
private theorem checked_4_12288 : entriesCheck 4 12288 2048=true := by decide +kernel
private theorem checked_4_14336 : entriesCheck 4 14336 2048=true := by decide +kernel
private theorem checked_4_16384 : entriesCheck 4 16384 704=true := by decide +kernel
theorem bank_4 (i : Nat) (hi : i<17088) : entryCheck 4 i=true := by
  by_cases hi0 : i<2048
  · exact entries_sound 4 0 2048 checked_4_0 i (by omega) (by omega)
  by_cases hi2048 : i<4096
  · exact entries_sound 4 2048 2048 checked_4_2048 i (by omega) (by omega)
  by_cases hi4096 : i<6144
  · exact entries_sound 4 4096 2048 checked_4_4096 i (by omega) (by omega)
  by_cases hi6144 : i<8192
  · exact entries_sound 4 6144 2048 checked_4_6144 i (by omega) (by omega)
  by_cases hi8192 : i<10240
  · exact entries_sound 4 8192 2048 checked_4_8192 i (by omega) (by omega)
  by_cases hi10240 : i<12288
  · exact entries_sound 4 10240 2048 checked_4_10240 i (by omega) (by omega)
  by_cases hi12288 : i<14336
  · exact entries_sound 4 12288 2048 checked_4_12288 i (by omega) (by omega)
  by_cases hi14336 : i<16384
  · exact entries_sound 4 14336 2048 checked_4_14336 i (by omega) (by omega)
  exact entries_sound 4 16384 704 checked_4_16384 i (by omega) (by omega)

end CommitGolfCandidate.Layout2
