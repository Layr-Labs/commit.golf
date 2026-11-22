import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «riscv-zkvm» from git
  "https://github.com/Verified-zkEVM/riscv-zkvm" @ "4634e41b229da4256e4a1f1688b94133fffa4af0"

require Arklib from git
  "https://github.com/Verified-zkEVM/ArkLib" @ "608f550b89b881cc1c9c6c32825fcc61b53c96ab"

require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "afb9b1363984a70f10e24bd597f6ff40ebc8afbb"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "f1e63c780de398fb62206dd5890f27e1ad64e0e6"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf
-- Historical baseline sources are retained unchanged; no baseline build target is registered.
-- Fixed-oracle execution and security-definition regression tests.
lean_lib CommitGolfTests
-- Verifier-only namespace: candidate modules are copied here during submission checking.
-- The default contract build does not build or check a submission.
lean_lib CommitGolfCandidate
