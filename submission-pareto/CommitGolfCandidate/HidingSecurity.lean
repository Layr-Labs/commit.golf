import CommitGolfCandidate.HidingGameIntegration

/-! Statistical hiding of the reference game with generated nonces: the complete
two-stage oracle-adaptive game over the tree with tagged permutation leaves, whose
nonces are generated from a uniform seed, for every opening size, including zero.
This file is independent of the commit machine; the transfer to the submitted images
uses `hiding_distance_reference`. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingSecurityDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

/-- The reference games for the two selector bits are within the contract's
hiding error, for the shared two-stage public-query budget. -/
theorem reference_hiding_bound {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS :=
  reference_hiding_distance adversary bounded

end CommitGolfCandidate
