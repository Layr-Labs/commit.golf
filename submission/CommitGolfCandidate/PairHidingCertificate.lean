import CommitGolfCandidate.PairHidingQuartetFinalSharp

/-!
# Pair-heads hiding: the security-side target

`pair_iid_hiding : Quartet.PairIidHiding` (PairLeafModel.lean): the pair-leaf analog of
`Quartet.final_reference_hiding_sharp`, with the same error `(t+1)/2^121`. The proof is the pinned one, run on the
pair seeds of PairHidingSeeds.lean through the `PairH` copies of the leaf-dependent declarations
(PairHidingCommon … PairHidingQuartetFinalSharp); the frame hypothesis is discharged by the pair `global_frame`.
-/

namespace TwoPermutationPrototype.Sampling.Quartet

theorem pair_iid_hiding : PairIidHiding := by
  intro State Output openingSize adversary build compress budget bounded small
  exact PairH.final_reference_hiding_sharp PairH.global_frame adversary build compress budget bounded small

end TwoPermutationPrototype.Sampling.Quartet
