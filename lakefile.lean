import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «riscv-zkvm» from git
  "https://github.com/Verified-zkEVM/riscv-zkvm" @ "4634e41b229da4256e4a1f1688b94133fffa4af0"

require Arklib from git
  "https://github.com/Verified-zkEVM/ArkLib" @ "3b2ff0cc6938d7a8032afde7502b6080b5420eea"

require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "e28da34817c3775cfb935376acf5d416f555d64f"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "9054989327a7185ff19ef9ff0f119cccea479501"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf
-- Historical baseline sources are retained unchanged; no baseline build target is registered.
-- Fixed-oracle execution and security-definition regression tests.
lean_lib CommitGolfTests
-- Verifier-only namespace: candidate modules are copied here during submission checking.
-- The default contract build does not build or check a submission.
lean_lib CommitGolfCandidate

-- Separate execution/resource contracts for the new depth-aware tracks.
lean_lib CommitGolfDepth
