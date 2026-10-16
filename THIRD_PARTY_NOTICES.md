# Dependencies and reuse

The Lean project uses [VCVio](https://github.com/Verified-zkEVM/VCVio) for probabilistic oracle computations. Its version and transitive dependencies are pinned in `lake-manifest.json`; their licenses remain in the dependency repositories.

The repository layout and the style of the rules and statements follow [sig.golf](https://github.com/leanEthereum/sig.golf-submissions).

`verifier/`, `scripts/` and `.github/workflows/benchmark.yml` are adapted from sig.golf's verifier (Apache-2.0). The verifier builds Lean's [comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and, on Linux, [landrun](https://github.com/Zouuup/landrun) at pinned revisions; their licenses remain in those repositories.
