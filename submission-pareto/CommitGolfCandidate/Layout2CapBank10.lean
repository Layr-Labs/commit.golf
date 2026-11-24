import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 10 0 1024=true := by decide +kernel
private theorem part1024 : scan 10 1024 1024=true := by decide +kernel
private theorem part2048 : scan 10 2048 336=true := by decide +kernel
theorem bank10 (i : Nat) (bound : i<2384) : checkEntry 10 i=true := by
  by_cases lt0 : i<1024
  · exact in_scan 10 0 1024 part0 i (by omega) (by omega)
  by_cases lt1024 : i<2048
  · exact in_scan 10 1024 1024 part1024 i (by omega) (by omega)
  exact in_scan 10 2048 336 part2048 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
