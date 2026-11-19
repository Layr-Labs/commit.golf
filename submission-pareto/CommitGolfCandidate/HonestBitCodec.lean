import CommitGolfCandidate.HonestCodec
import CommitGolfCandidate.ProofCodecBits

/-! Honest projected-leaf transcripts round-trip through the legacy seven-bit head stream. -/
namespace TwoPermutationPrototype.Sampling.HonestCodec
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

theorem honest_bit_unpack_pack (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (heads : HeadFacts compress positions salts leaves) :
    let proof := (transcriptBuilder true compress positions salts leaves).2
    ProofCodec.BitPacked.unpack positions.card (ProofCodec.BitPacked.pack positions.card proof)=some proof := by
  intro proof
  obtain ⟨b,len,hb,top,headBytes⟩ := honest_codec_shape compress positions salts leaves
  obtain ⟨salt,leaf,leafTop⟩ := headBytes heads
  have card : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  change positions.card≤16777216 at card
  exact ProofCodec.BitPacked.unpack_pack positions.card b proof len
    (by unfold ProofCodec.packedLength ProofCodec.bodyLength;omega) top salt
    (fun r hr => (leaf r hr).trans_le (by decide)) leafTop

theorem honest_bit_length_le (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (scored : positions.card≤128) :
    (ProofCodec.BitPacked.pack positions.card
      (transcriptBuilder true compress positions salts leaves).2).length≤66800 := by
  obtain ⟨b,len,hb,_⟩ := honest_codec_shape compress positions salts leaves
  rw [ProofCodec.BitPacked.pack_length,len,
    show ProofCodec.unpackedCount positions.card (498*positions.card+30*b)=15*positions.card+b by
      unfold ProofCodec.unpackedCount;omega]
  exact ProofCodec.BitPacked.packed_length_le _ _ scored hb

end TwoPermutationPrototype.Sampling.HonestCodec
