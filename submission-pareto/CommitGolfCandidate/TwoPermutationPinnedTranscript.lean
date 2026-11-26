import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationTranscript

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp

def pinnedHonestView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun index => salts index.val) (pinnedFullLeafDigests p message salts)

/-- The honest view at masked salts, as a function of the raw salts drawn by the hiding game. -/
def pinnedMaskedView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun index => salts index.val) (hidingLeafDigests p message salts)

/-- Clear the top salt bits of every opened salt before building the transcript. -/
def maskBuild (build : TranscriptBuilder) : TranscriptBuilder :=
  fun compress positions salts leaves => build compress positions (fun index => maskSalt (salts index)) leaves

theorem masked_view_honest (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    pinnedHonestView build compress p message positions (fun i => maskSalt (salts i)) =
      pinnedMaskedView (maskBuild build) compress p message positions salts := rfl

abbrev PinnedTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) :=
  TranscriptRefinesView scheme (pinnedHonestView build)

end TwoPermutationPrototype.Sampling
