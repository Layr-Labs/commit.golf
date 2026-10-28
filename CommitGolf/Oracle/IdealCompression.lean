import CommitGolf.Parameters
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType

/-! # Ideal compression functions

A uniformly random function on fixed-width bit strings. Unlike a permutation it need not be
injective and exposes no inverse query. The family declaration requires `0 < outputBits <
inputBits`. Sampling the entire finite function is a mathematical definition, not a practical
implementation; every party observes the same function throughout a game. -/
namespace CommitGolf.IdealCompression
open OracleComp OracleSpec

abbrev Spec (inputBits outputBits : Nat) : OracleSpec (BitVec inputBits) :=
  BitVec inputBits →ₒ BitVec outputBits

abbrev Function (inputBits outputBits : Nat) := BitVec inputBits → BitVec outputBits

/-- Each input has an independent uniform output; repeated queries use the same function. -/
def sample (inputBits outputBits : Nat) : ProbComp (Function inputBits outputBits) :=
  $ᵗ (Function inputBits outputBits)

end CommitGolf.IdealCompression
