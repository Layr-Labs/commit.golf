import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 7 0 1024=true := by decide +kernel
private theorem part1024 : scan 7 1024 656=true := by decide +kernel
theorem bank7 (i : Nat) (bound : i<1680) : checkEntry 7 i=true := by
  by_cases lt0 : i<1024
  · exact in_scan 7 0 1024 part0 i (by omega) (by omega)
  exact in_scan 7 1024 656 part1024 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
