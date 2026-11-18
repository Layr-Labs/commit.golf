import CommitGolfCandidate.QuartetRVTranscript
import CommitGolfCandidate.QuartetChainSecurity

/-! Adapted from submission c28dd9ca (dadon), `NonceChainRepresentation`, for the Quartet opening:
only the serialized trapdoor passes from commitment to opening, and each key determines the salt
array for the fixed permutation used by both machines. -/
namespace TwoPermutationPrototype.QuartetRV
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp Sampling
open Opening (trapdoorHeap)
open Sampling.Quartet (upperHeap quartetLookup builder ChainQuartetRefines)
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
local instance quartetChainRepresentationDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem chain_transcript_refines (s : Submission) (abi : OpeningABI s)
    (trapdoorOf : Oracle → Message → Key → BitVec (8*s.sizes.trapdoor))
    (distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          let p := BiPermutation.equiv Block oracle.permutation
          let leaves := pinnedFullLeafDigests p message (actualNonces oracle.permutation k)
          pure (upperHeap (quartetLookup p) oracle.compression leaves 1, trapdoorOf oracle message k)))
    (nonce : ∀ oracle message k i, trapdoorSalt (s:=s) (trapdoorOf oracle message k) i = actualNonces oracle.permutation k i)
    (leaf : ∀ oracle message k (i : Index), trapdoorLeaf (s:=s) (trapdoorOf oracle message k) i.val =
      pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message (actualNonces oracle.permutation k) i)
    (heap : ∀ oracle message k node, 0<node → node<2*(LENGTH/4) →
      trapdoorHeap (s:=s) (trapdoorOf oracle message k) node =
      upperHeap (quartetLookup (BiPermutation.equiv Block oracle.permutation)) oracle.compression
        (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message (actualNonces oracle.permutation k)) node) :
    ChainQuartetRefines s.scheme := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((distribution oracle message).bind_left _).trans
  simp only [bind_assoc,pure_bind]
  apply EvalDistEq.bind_right
  intro k
  rw [scheme_open_bytes s abi,pure_bind,fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (trapdoorOf oracle message k) positions
    (quartetLookup (BiPermutation.equiv Block oracle.permutation)) oracle.compression
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message (actualNonces oracle.permutation k))
    (actualNonces oracle.permutation k) (heap oracle message k) (leaf oracle message k) (nonce oracle message k)
  rw [proof]
  rfl

end TwoPermutationPrototype.QuartetRV
