import CommitGolfCandidate.ChainedCachedPacket
import CommitGolfCandidate.TwoPermutationPackedOpeningProofBytes

/-! Readback of canonical raw fields at the cached opener's postpass boundary. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 8192

theorem bytes_at_proof_bytes (before : MachineState) (count : Nat) (bytes : Proof)
    (readback : TwoPermutationPrototype.PackedOpening.proofBytes before count=bytes) :
    BytesAt before (BitVec.ofNat 64 proofBase) bytes := by
  have length : bytes.length=count := by
    rw [←readback,TwoPermutationPrototype.PackedOpening.proof_bytes_length]
  intro index inside
  rw [←readback,TwoPermutationPrototype.PackedOpening.proof_bytes_getD before count index (by omega),
    ←BitVec.ofNat_add]

theorem delivered_cached_source_view (oracle : Oracle) (message : Message) (key : Key)
    (positions : Positions) (before : MachineState)
    (sourceReadback : TwoPermutationPrototype.PackedOpening.proofBytes before
      (TwoPermutationPrototype.PackedOpening.proofLength positions)=
      TwoPermutationPrototype.PackedOpening.proofFromTrapdoor (s := Artifact.submission)
        (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 positions) :
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    BytesAt before (BitVec.ofNat 64 proofBase)
      (rawRecordStream (cachedRecords heap (deliveredSalts oracle key) positions)++
        rawFieldsBytes (footerRawFields (openingNodes positions) (cachedFooter (openingNodes positions) heap))) := by
  apply bytes_at_proof_bytes before (TwoPermutationPrototype.PackedOpening.proofLength positions)
  exact sourceReadback.trans (delivered_cached_packet oracle message key positions).symm

theorem delivered_cached_source_of_completed (oracle : Oracle) (message : Message) (key : Key)
    (positions : Positions) (before : MachineState) (layout : OpeningLayout Artifact.submission)
    (lowerDone : TwoPermutationPrototype.PackedOpening.CompletedRecords Artifact.submission
      (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 positions before positions.card)
    (footerDone : ∀ i (inside : i < (openingNodes positions).length),
      readBuffer before (TwoPermutationPrototype.PackedOpening.recordBase positions.card+30*i) 30 =
        ((Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2.extractLsb'
          (256*(openingNodes positions)[i]) 256).extractLsb' 0 240) :
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    BytesAt before (BitVec.ofNat 64 proofBase)
      (rawRecordStream (cachedRecords heap (deliveredSalts oracle key) positions)++
        rawFieldsBytes (footerRawFields (openingNodes positions) (cachedFooter (openingNodes positions) heap))) := by
  apply delivered_cached_source_view oracle message key positions before
  exact TwoPermutationPrototype.PackedOpening.unpacked_opening_proof_layout Artifact.submission layout _
    positions before lowerDone footerDone

end CommitGolfCandidate.Chained.Native
