import CommitGolfCandidate.OverlapWindowRows
import CommitGolfCandidate.TwoPermutationCheckerPaths
import CommitGolfCandidate.PlbBindingBridge
import CommitGolfCandidate.PlbHidingBridge

namespace TwoPermutationPrototype.Overlap
open CommitGolf TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

abbrev fullLeafDigests := Sampling.plbLeafDigests
abbrev honestView := Sampling.plbHonestView

/-- Evidence from an accepted path, including both recorded forward evaluations. -/
structure RecordedOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : Words 2
  first : let a := firstRow oracle.permutation (entryWords entry)
          PublicRow.permutation a.1 a.2 ∈ rows
  second : let m := entryWords entry
           let b := secondRow oracle.permutation index nonce m (firstRow oracle.permutation m).2
           PublicRow.permutation b.1 b.2 ∈ rows
  path : let m := entryWords entry
         let b := secondRow oracle.permutation index nonce m (firstRow oracle.permutation m).2
         RecordedPath rows (LENGTH+index.val) LOG_LENGTH (outputDigest b.2) root

end TwoPermutationPrototype.Overlap
