import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate

/-! # Checker facts of the final submission

The check image of `K1Manifest.lean` (K3-lite + L21 + T238 + chain) terminates, spends at most 100 public calls per
opened position, accepts every honest opening (534-byte records, packed 238-bit siblings and cap frontier), and is
binding with the T238 replay bound (`k1_peer_leaf_layout_sharp`). -/
namespace CommitGolf.K1Check

theorem checker_facts : TwoPermutationPrototype.QuartetCertificate.CheckerFacts CommitGolf.K1Artifact.submission :=
  TwoPermutationPrototype.Packed.Checker.executable_checker_facts

end CommitGolf.K1Check
