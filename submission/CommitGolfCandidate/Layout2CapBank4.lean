import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 4 0 960=true := by decide +kernel
theorem bank4 (i : Nat) (bound : i<960) : checkEntry 4 i=true := by
  exact in_scan 4 0 960 part0 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
