import CommitGolfCandidate.Layout2Invariant
import CommitGolfCandidate.GroupOpenTable
import CommitGolfCandidate.TwoPermutationCheckLoader

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (pget pget_get halfword_bytes half_ext)
set_option maxRecDepth 32000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048
abbrev candidate := K1Artifact.submission

def multiplicity (k : Nat) :=
  if k<34176 then 4 else if k<42720 then 1 else if k<59808 then 2 else 3
def tableByte (τ : Tables) (k : Nat) : Nat :=
  let r:=multiplicity k
  let n:=τ r ((k-tableOffset r)/2)
  if k%2=0 then n%256 else n/256%256

end CommitGolfCandidate.Layout2
