import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf
-- The textbook Merkle tree, the baseline scheme, and the proof of its certificate.
lean_lib CommitGolfBaseline
-- Kernel-checked constants, runs of the baseline on small trees, and the certificate's axioms.
lean_lib CommitGolfTests
-- Namespace for submitted proofs; the verifier copies a submission's CommitGolfCandidate/ here.
lean_lib CommitGolfCandidate
