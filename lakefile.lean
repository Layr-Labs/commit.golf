import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf
-- Historical baseline sources are retained but excluded until adapted to the fixed oracles.
-- Fixed-oracle execution and security-definition regression tests.
lean_lib CommitGolfTests
-- Namespace for submitted proofs; the verifier copies a submission's CommitGolfCandidate/ here.
lean_lib CommitGolfCandidate
