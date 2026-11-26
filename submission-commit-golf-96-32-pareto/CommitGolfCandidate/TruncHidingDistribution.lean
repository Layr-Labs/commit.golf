import CommitGolfCandidate.HidingDistribution

import CommitGolfCandidate.TruncHidingTree

namespace CommitGolfCandidate.Trunc

open CommitGolf CommitGolf.Riscv OracleComp OracleComp.DeferredSampling

local instance hidingDistributionDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 12000

set_option maxHeartbeats 800000

def referenceTranscript (compress : Compression) (message : Message)
    (salt : Index → Salt) (positions : Positions) : Commitment × Proof :=
  let heap := saltedHeap compress message salt
  (heap 1, referenceOpening heap salt positions)

def hybridTranscript (compress : Compression) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) : Commitment × Proof :=
  let heap := hybridHeap compress positions message salt freshInit
  (heap 1, referenceOpening heap salt positions)

attribute [local irreducible] commitFinalResult submission readBuffer saltedHeap referenceOpening

def referenceHiding {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) : ProbComp Output := do
  let challenge ← fixedOracleRun oracle adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let salt ← $ᵗ (Index → Salt)
  let (root, proof) := referenceTranscript oracle.compression message salt challenge.positions
  fixedOracleRun oracle (adversary.observe challenge.aux root proof)

end CommitGolfCandidate.Trunc
