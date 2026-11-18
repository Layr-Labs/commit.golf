import CommitGolfCandidate.NonceChainSecurity
import CommitGolfCandidate.TwoPermutationPackedOpeningTranscript

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf OracleComp CommitGolfCandidate TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Opening (trapdoorHeap trapdoorSalt)
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
local instance chainDiscrete {α : Type} : MeasurableSpace α := ⊤

/-- Only the serialized trapdoor passes from commitment to opening. Each seed
determines the salt sequence for the fixed permutation used by both machines. -/
structure ChainRepresentation (s : Submission) where
  trapdoorOf : Oracle → Message → Key → BitVec (8*s.sizes.trapdoor)
  distribution : ∀ o m, fixedOracleRun o (s.scheme.commit m) =ᵈ
    (do let k ← $ᵗ Key
        let r := actualNonces o.permutation k
        let leaves := pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r
        pure (mixedTranscriptHeap o.compression leaves 1, trapdoorOf o m k))
  nonce : ∀ o m k i, trapdoorSalt (s := s) (trapdoorOf o m k) i = actualNonces o.permutation k i
  heap : ∀ o m k n, 0<n → n<2*LENGTH → trapdoorHeap (s := s) (trapdoorOf o m k) n =
    mixedTranscriptHeap o.compression (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (actualNonces o.permutation k)) n

theorem chain_transcript (s : Submission) (abi : OpeningABI s) (commit : ChainRepresentation s) :
    ChainTranscriptRefines s.scheme mixedTranscriptBuilder := by
  intro o m p
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((commit.distribution o m).bind_left _).trans
  simp only [bind_assoc,pure_bind]
  apply EvalDistEq.bind_right
  intro k
  rw [scheme_open_bytes s abi,pure_bind,fixed_oracle_run_pure]
  rw [proof_from_trapdoor_matches s (commit.trapdoorOf o m k) p o.compression
    (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (actualNonces o.permutation k))
    (actualNonces o.permutation k) (commit.heap o m k) (commit.nonce o m k)]
  rfl

end TwoPermutationPrototype.PackedOpening
