import CommitGolfCandidate.Layout2CapEntry
namespace CommitGolfCandidate.Layout2.Cap
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
private theorem part0 : scan 1 0 240=true := by decide +kernel
theorem bank1 (i : Nat) (bound : i<240) : checkEntry 1 i=true := by
  exact in_scan 1 0 240 part0 i (by omega) (by omega)

end CommitGolfCandidate.Layout2.Cap
