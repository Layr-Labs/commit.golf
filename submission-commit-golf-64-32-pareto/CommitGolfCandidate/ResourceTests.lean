import CommitGolfCandidate.Resources

/-! Regression checks for this candidate's resource helpers, not additional challenge rules. -/

namespace CommitGolfCandidate.ResourceTests
open CommitGolf OracleComp OracleSpec

-- Eight actual compression queries cannot satisfy a seven-call budget, even when the handler
-- always returns zero. This exercises the merged all-paths-to-fixed-handler bound.
example : ¬ WorstCaseCostBound (Resources.leaf (0, 0)) Resources.compressCost 7 := by
  intro h
  have impossible := worstCaseCostBound_runAdd_withAddCost_le h
    (Resources.compressionAnswer (fun _ => 0))
  change 8 ≤ 7 at impossible
  omega

-- Noncommuting state updates distinguish low-to-high block order from reversal or omission.
private def orderedCompression (input : BitVec 512) : Resources.Digest :=
  ((input.extractLsb' 256 256 + (3 : BitVec 256) * input.extractLsb' 0 256) :
    BitVec 256).cast (by decide)
#guard Resources.referenceLeaf orderedCompression (0, 1) == 2187

end CommitGolfCandidate.ResourceTests
