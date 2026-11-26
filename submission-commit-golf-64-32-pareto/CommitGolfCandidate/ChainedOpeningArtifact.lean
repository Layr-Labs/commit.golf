import CommitGolfCandidate.ChainedCachedOpening

/-! The official artifact's delivered opener is exactly the relocated chained image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem opening_manifest_code : ArtifactEncoding.decode 32 Artifact.openingCode=cachedControllerImage.code := by
  decide +kernel

theorem opening_manifest_image : Artifact.submission.image .opening=cachedControllerImage := by
  change Image.mk (ArtifactEncoding.decode 32 Artifact.openingCode) (ArtifactEncoding.decode 8 Artifact.openingData)=
    Image.mk cachedControllerImage.code cachedControllerImage.data
  exact congrArg₂ Image.mk opening_manifest_code (by rfl)

theorem artifact_cached_opening (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    let trapdoor := (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    let packet := cachedEncodedPacket heap (deliveredSalts oracle key) positions
    ∃ after cycles, (∀ fuel coins, execute (Artifact.submission.image .opening)
        (TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles+fuel)
        (Artifact.submission.initialState .opening (trapdoor,positions)) coins=
        pure ⟨.success,after,TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 proofBase) packet ∧
      (after.getReg .x11).toNat=packet.length ∧
      cycles≤2273*positions.card+66460+13*(openingNodes positions).length := by
  simpa only [opening_manifest_image] using delivered_cached_opening oracle message key positions

end CommitGolfCandidate.Chained.Native
