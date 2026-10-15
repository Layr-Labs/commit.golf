import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf
-- The textbook Merkle tree, the baseline scheme.
lean_lib CommitGolfBaseline
-- Kernel-checked constants and runs of the baseline on small trees.
lean_lib CommitGolfTests
