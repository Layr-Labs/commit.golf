import CommitGolfCandidate.OverlapInputs
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.TwoPermutationWideParentImage
import CommitGolfCandidate.TwoPermutationOpeningTranscript

namespace TwoPermutationPrototype.Overlap
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open CommitGolfCandidate (fixedOracleRun splitBlocks)

/-- The untruncated second reply is useful for reasoning about the output spill. -/
def blockReply (perm : Block → Block) (index : Nat) (salt : Words 2) (message : Words 32) : Block :=
  perm (packBuffer (secondInput index salt (replyWords (perm (packBuffer (firstInput message)))) message))

def leafDigests (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i => outputDigest (blockReply oracle.permutation i.val (saltWords (salts i)) (messageWords message i))

def tree (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  transcriptHeap false oracle.compression (leafDigests oracle message salts)

/-- The check image is read from the delivered manifest; commitment semantics only uses the
commit branch and the serialization layout. -/
def program : Submission where
  sizes := ⟨1610612736, 8858378240⟩
  layout := ⟨4096, 4294971392, 4294971424, 5905584160, 6039801952, 10334769248⟩
  steps
    | .commit => 1073807360
    | .opening => 8590000128
    | .check => 17179934720
  image
    | .commit => wideCommitImage
    | .opening => Opening.openingImage
    | .check => Artifact.submission.image .check

structure CommitTranscript (candidate : Submission) where
  trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*candidate.sizes.trapdoor)
  distribution : ∀ oracle message, fixedOracleRun oracle (candidate.scheme.commit message) =ᵈ
    (do let salts ← sampleCompleteSaltTape
        pure (tree oracle message salts 1, trapdoorOf oracle message salts))
  nonce : ∀ oracle message salts index,
    Opening.trapdoorSalt (s := candidate) (trapdoorOf oracle message salts) index = salts index
  heap : ∀ oracle message salts n, 0<n → n<2*LENGTH →
    Opening.trapdoorHeap (s := candidate) (trapdoorOf oracle message salts) n = tree oracle message salts n

noncomputable def CommitTranscript.ofPacked (candidate : Submission)
    (trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*candidate.sizes.trapdoor))
    (dist : ∀ oracle message, fixedOracleRun oracle (candidate.scheme.commit message) =ᵈ
      (do let packed ← $ᵗ BitVec (128*LENGTH)
          let salts := splitBlocks 128 LENGTH packed
          pure (tree oracle message salts 1, trapdoorOf oracle message salts)))
    (nonce : ∀ oracle message salts index,
      Opening.trapdoorSalt (s := candidate) (trapdoorOf oracle message salts) index = salts index)
    (heap : ∀ oracle message salts n, 0<n → n<2*LENGTH →
      Opening.trapdoorHeap (s := candidate) (trapdoorOf oracle message salts) n = tree oracle message salts n) :
    CommitTranscript candidate :=
  ⟨trapdoorOf,fun oracle message => (dist oracle message).trans
    (packed_salt_tape_uniform (fun salts => pure (tree oracle message salts 1,trapdoorOf oracle message salts))),
    nonce,heap⟩
end TwoPermutationPrototype.Overlap
