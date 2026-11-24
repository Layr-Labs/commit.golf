import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 8 0 1024=true := by decide +kernel
private theorem part1024 : scan 8 1024 880=true := by decide +kernel
theorem bank8 (i : Nat) (bound : i<1904) : checkEntry 8 i=true := by
  by_cases lt0 : i<1024
  · exact in_scan 8 0 1024 part0 i (by omega) (by omega)
  exact in_scan 8 1024 880 part1024 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
