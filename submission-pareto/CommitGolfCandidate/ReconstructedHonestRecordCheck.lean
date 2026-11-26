import CommitGolfCandidate.ReconstructedHonestRecordShapes

namespace CommitGolfCandidate.Reconstruction.HonestRecordCheck
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRanges HonestProtected HonestRegionStep
open HonestRecordMemory HonestRecordShapes
open CommitBlocks (addr)

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

def checked (i k : Nat) : Bool :=
  match current i k with
  | none => true
  | some a => HonestRegionBlocks.check context Artifact.openingCode stopAt (nextShape i) 64 (addr k) (a.model context)

theorem first_store (i : Fin 128) : checked i.val 143=true := by
  exact (by decide +kernel : ∀ j : Fin 128, checked j.val 143=true) i

end CommitGolfCandidate.Reconstruction.HonestRecordCheck
