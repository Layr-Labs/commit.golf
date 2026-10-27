import Lake
open Lake DSL

package CommitGolf where
  leanOptions := #[⟨`autoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

-- The contract: parameters, oracle, scheme syntax, games, and the statements a certificate proves.
@[default_target] lean_lib CommitGolf

-- Submission builds (the verifier supplies its own candidate library below this boundary).
-- Kernel-checked constants, small-tree executions, and certificate axioms.
lean_lib CommitGolfTests

lean_lib PermutationCandidate where
  srcDir := "submissions/ideal-permutation"
  roots := #[`CommitGolfCandidate.Permutation]
  globs := #[.andSubmodules `CommitGolfCandidate.Permutation]

lean_lib CompressionCandidate where
  srcDir := "submissions/ideal-compression"
  roots := #[`CommitGolfCandidate.Compression]
  globs := #[.andSubmodules `CommitGolfCandidate.Compression]

lean_lib RandomOracleCandidate where
  srcDir := "submissions/random-oracle-fixed-output"
  roots := #[`CommitGolfCandidate.RandomOracle]
  globs := #[.andSubmodules `CommitGolfCandidate.RandomOracle]

lean_lib XofCandidate where
  srcDir := "submissions/ideal-xof"
  roots := #[`CommitGolfCandidate.Xof]
  globs := #[.andSubmodules `CommitGolfCandidate.Xof]

-- Compile each submitted baseline independently, including its track certificate.
lean_lib IdealPermutation where
  roots := #[`submissions.«ideal-permutation».Solution]
lean_lib IdealCompression where
  roots := #[`submissions.«ideal-compression».Solution]

-- Check the oracle models independently of the Merkle baselines.
-- This target is model regression coverage, not a certified submission.
lean_lib RandomOracleFixedOutputModel where
  roots := #[`CommitGolf.Oracle.Tests]

lean_lib IdealXofModel where
  roots := #[`CommitGolf.Oracle.Tests]

lean_lib RandomOracleFixedOutput where
  roots := #[`submissions.«random-oracle-fixed-output».Solution]

lean_lib IdealXof where
  roots := #[`submissions.«ideal-xof».Solution]
