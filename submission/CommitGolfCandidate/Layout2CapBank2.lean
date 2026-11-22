import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 2 0 480=true := by decide +kernel
theorem bank2 (i : Nat) (bound : i<480) : checkEntry 2 i=true := by
  exact in_scan 2 0 480 part0 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
