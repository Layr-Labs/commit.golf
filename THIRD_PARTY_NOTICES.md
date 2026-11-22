# Dependencies and reuse

The Lean project uses [VCVio](https://github.com/Verified-zkEVM/VCVio) for probabilistic oracle computations. Its version and transitive dependencies are pinned in `lake-manifest.json`; their licenses remain in the dependency repositories.

The repository layout and the style of the rules and statements follow [sig.golf](https://github.com/leanEthereum/sig.golf-submissions).

`verifier/`, `scripts/` and `.github/workflows/benchmark.yml` are adapted from sig.golf's verifier (Apache-2.0). The verifier runs `lake comparator`, which ships with the Lean release in `lean-toolchain` and succeeds the standalone [comparator](https://github.com/leanprover/comparator). On Linux, it sandboxes the build with the distribution's [bubblewrap](https://github.com/containers/bubblewrap).

`CommitGolf/Riscv.lean` restores and adapts the sig.golf-derived RV64IM interpreter
from commit.golf's own history. Instruction semantics and decoding use the pinned
[riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm) dependency; its licenses
and those of its dependencies remain in their repositories.
