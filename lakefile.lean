import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

require «riscv-zkvm» from git
  "https://github.com/Verified-zkEVM/riscv-zkvm" @ "4634e41b229da4256e4a1f1688b94133fffa4af0"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf
-- Historical baseline sources are retained unchanged; no baseline build target is registered.
-- Fixed-oracle execution and security-definition regression tests.
lean_lib CommitGolfTests
-- Verifier-only namespace: candidate modules are copied here during submission checking.
-- The default contract build does not build or check a submission.
lean_lib CommitGolfCandidate
