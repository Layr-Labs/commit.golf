import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 3 0 720=true := by decide +kernel
theorem bank3 (i : Nat) (bound : i<720) : checkEntry 3 i=true := by
  exact in_scan 3 0 720 part0 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
