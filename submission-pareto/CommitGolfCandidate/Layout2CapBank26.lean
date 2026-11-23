import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 26 0 1024=true := by decide +kernel
private theorem part1024 : scan 26 1024 1024=true := by decide +kernel
private theorem part2048 : scan 26 2048 1024=true := by decide +kernel
private theorem part3072 : scan 26 3072 1024=true := by decide +kernel
private theorem part4096 : scan 26 4096 1024=true := by decide +kernel
private theorem part5120 : scan 26 5120 1024=true := by decide +kernel
private theorem part6144 : scan 26 6144 48=true := by decide +kernel
theorem bank26 (i : Nat) (bound : i<6192) : checkEntry 26 i=true := by
  by_cases lt0 : i<1024
  · exact in_scan 26 0 1024 part0 i (by omega) (by omega)
  by_cases lt1024 : i<2048
  · exact in_scan 26 1024 1024 part1024 i (by omega) (by omega)
  by_cases lt2048 : i<3072
  · exact in_scan 26 2048 1024 part2048 i (by omega) (by omega)
  by_cases lt3072 : i<4096
  · exact in_scan 26 3072 1024 part3072 i (by omega) (by omega)
  by_cases lt4096 : i<5120
  · exact in_scan 26 4096 1024 part4096 i (by omega) (by omega)
  by_cases lt5120 : i<6144
  · exact in_scan 26 5120 1024 part5120 i (by omega) (by omega)
  exact in_scan 26 6144 48 part6144 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
