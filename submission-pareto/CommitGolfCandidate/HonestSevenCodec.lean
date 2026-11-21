import CommitGolfCandidate.HonestCodec
import CommitGolfCandidate.HeadStreamSeven

namespace TwoPermutationPrototype.Sampling.HonestCodec
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

theorem salt_byte121 (x : BitVec 128) (small : x.toNat<2^121) :
    ((saltBytes x)[15]?.getD 0).toNat<2 := by
  have value : ((saltBytes x)[15]?.getD 0).toNat=x.toNat/2^(8*15)%2^8 := by
    simp only [saltBytes,List.getElem?_ofFn,show 15<16 by decide,Option.getD_some]
    simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [value]
  have q : x.toNat/2^(8*15)<2 := by
    apply Nat.div_lt_of_lt_mul
    norm_num
    omega
  exact lt_of_le_of_lt (Nat.mod_le _ _) q

theorem honest_record_salt121 (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape)
    (small : ∀ index, (salts index).toNat<2^121) :
    ∀ r<positions.card,
      (((transcriptBuilder true compress positions salts leaves).2).getD (498*r+15) 0).toNat<2 := by
  let proof := (transcriptBuilder true compress positions salts leaves).2
  let heap := transcriptHeap true compress leaves
  let ordered := positions.attach.sort (fun i j => i.val≤j.val)
  let groups := ordered.map (capGroup ∘ Subtype.val)
  let path := ordered.flatMap (fun index => lowerRecord true heap index.val (salts index))
  have hproof : proof=path++frontierProof true heap groups := rfl
  have hord : ordered.length=positions.card := by simp [ordered]
  have hrec : ∀ index∈ordered, (lowerRecord true heap index.val (salts index)).length=498 := by
    intro index _
    simp [lower_record_length]
  have hpath : path.length=498*positions.card := by
    simp only [path,List.length_flatMap]
    rw [List.map_congr_left (fun index h => hrec index h)]
    simp [hord,Nat.mul_comm]
  intro r hr
  change (proof.getD (498*r+15) 0).toNat<2
  rw [hproof,List.getD_eq_getElem?_getD,List.getElem?_append_left (by rw [hpath];omega),
    getElem?_flatMap_uniform ordered _ 498 hrec r (by rw [hord];exact hr) 15 (by decide),
    lower_record_salt]
  exact salt_byte121 _ (small _)

theorem honest_seven_unpack_pack (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape)
    (small : ∀ index, (salts index).toNat<2^121) :
    let proof := (transcriptBuilder true compress positions salts leaves).2
    ProofCodec.HeadStreamSeven.unpack positions.card
      (ProofCodec.HeadStreamSeven.pack positions.card proof)=some proof := by
  intro proof
  have heads := head_facts_of_small_salts compress positions salts leaves
    (fun index => lt_trans (small index) (by norm_num))
  obtain ⟨b,len,hb,top,headBytes⟩ := honest_codec_shape compress positions salts leaves
  obtain ⟨_,leaf,tail,leafTop⟩ := headBytes heads
  have card : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  change positions.card≤16777216 at card
  exact ProofCodec.HeadStreamSeven.unpack_pack positions.card b proof len
    (by unfold ProofCodec.packedLength ProofCodec.bodyLength;omega) top
    (honest_record_salt121 compress positions salts leaves small) leaf tail leafTop

end TwoPermutationPrototype.Sampling.HonestCodec
