import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 27 0 1024=true := by decide +kernel
private theorem part1024 : scan 27 1024 1024=true := by decide +kernel
private theorem part2048 : scan 27 2048 1024=true := by decide +kernel
private theorem part3072 : scan 27 3072 1024=true := by decide +kernel
private theorem part4096 : scan 27 4096 1024=true := by decide +kernel
private theorem part5120 : scan 27 5120 1024=true := by decide +kernel
private theorem part6144 : scan 27 6144 288=true := by decide +kernel
theorem bank27 (i : Nat) (bound : i<6432) : checkEntry 27 i=true := by
  by_cases lt0 : i<1024
  · exact in_scan 27 0 1024 part0 i (by omega) (by omega)
  by_cases lt1024 : i<2048
  · exact in_scan 27 1024 1024 part1024 i (by omega) (by omega)
  by_cases lt2048 : i<3072
  · exact in_scan 27 2048 1024 part2048 i (by omega) (by omega)
  by_cases lt3072 : i<4096
  · exact in_scan 27 3072 1024 part3072 i (by omega) (by omega)
  by_cases lt4096 : i<5120
  · exact in_scan 27 4096 1024 part4096 i (by omega) (by omega)
  by_cases lt5120 : i<6144
  · exact in_scan 27 5120 1024 part5120 i (by omega) (by omega)
  exact in_scan 27 6144 288 part6144 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
