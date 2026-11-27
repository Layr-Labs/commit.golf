import CommitGolfCandidate.R1bCarrier
import CommitGolfCandidate.TwoPermutationHybridModel

namespace TwoPermutationPrototype.Hybrid
open CommitGolf CommitGolfCandidate Sampling
open CommitGolfCandidate.R1b

def wireProof (positions : Positions) (xs : Proof) : Proof :=
  if positions.card=BATCH then Carry.batchEncode xs else xs

def wideProof (positions : Positions) (xs : Proof) : Proof :=
  if positions.card=BATCH then Carry.batchDecode xs else xs

def wireBuilder : TranscriptBuilder := fun compress positions salts leaves =>
  let view := builder compress positions salts leaves
  (view.1, wireProof positions view.2)

theorem wireBound (positions : Positions) (xs : Proof) (batch : positions.card=BATCH) :
    (wireProof positions xs).length≤67489 := by
  rw [wireProof,if_pos batch]
  exact Carry.encoded_bound xs

end TwoPermutationPrototype.Hybrid
