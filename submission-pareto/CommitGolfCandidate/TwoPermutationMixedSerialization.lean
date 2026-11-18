import CommitGolfCandidate.TwoPermutationMixedTranscript
import CommitGolfCandidate.TwoPermutationMixedWidthParameters

/-! Serialization for the mixed-width heap. The first three path siblings
are full-width; the remaining thirteen and the cap footer use thirty bytes. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate

def mixedLowerRecord (heap : Nat → BitVec 256) (index : Index)
    (salt : BitVec 128) : List Byte :=
  saltBytes salt ++ (List.range 16).flatMap fun level =>
    proofDigestBytes (decide (4 < level))
      (heap (((LENGTH + index.val) / 2 ^ level) ^^^ 1))

theorem mixed_lower_record_length (heap : Nat → BitVec 256) (index : Index)
    (salt : BitVec 128) : (mixedLowerRecord heap index salt).length = 506 := by
  unfold mixedLowerRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap]
  simp [proof_digest_length, List.range_succ]

def mixedTranscriptBuilder : TranscriptBuilder :=
  fun compress positions salts leaves =>
    let heap := mixedTranscriptHeap compress leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let path := ordered.flatMap (fun index => mixedLowerRecord heap index.val (salts index))
    let footer := frontierProof true heap (ordered.map (capGroup ∘ Subtype.val))
    (heap 1, path ++ footer)

theorem mixed_transcript_128_size (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (count : positions.card = 128) :
    (mixedTranscriptBuilder compress positions salts leaves).2.length ≤ 68608 := by
  let sorted := positions.attach.sort (fun i j => i.val ≤ j.val)
  let heap := mixedTranscriptHeap compress leaves
  have footer := frontier_proof_bound true heap (sorted.map (capGroup ∘ Subtype.val))
  have ordered : sorted.length = 128 := by simp [sorted, count]
  change ((sorted.flatMap (fun index => mixedLowerRecord heap index.val (salts index))) ++
    frontierProof true heap (sorted.map (capGroup ∘ Subtype.val))).length ≤ _
  simp only [List.length_append, List.length_flatMap]
  simp [Function.comp_def, mixed_lower_record_length, ordered] at footer ⊢
  omega

end TwoPermutationPrototype.Sampling
