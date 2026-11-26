# Upstream needs demonstrated by the depth clients

The depth tracks add no dependency or pin update. The six existing tracks retain
their pinned semantics. This is a planning handoff, not a request to merge an
upstream API into the live challenge without compatibility review and replays.

| Need | Concrete local evidence | Suggested owner and scope |
| --- | --- | --- |
| Reusable work/span traces with separate sequential and fork composition | `CommitGolfDepth/Span/Trace.lean` sums work but takes max only between independent children; [archived scoring tests](https://github.com/Layr-Labs/commit.golf/blob/d45f94302f2c36881f34f4c4bb455321f64d4325/DepthPrototype/test_compare_scores.py) distinguish equal-work/equal-span computations with different finite-worker times | PolyFun/VCVio: an executed dependency-trace interface and cost-preserving interpretation theorem. An additive resource vector alone does not define span. |
| Explicit conditions for parallel effect interpretation | `Span/Memory.lean`, `Descriptors.lean`, and `Machine.lean` prove frame, sibling read-view independence and disjoint write reconciliation for this fixed memory/oracle model | PolyFun/VCVio: reusable ownership/noninterference hypotheses and distributional coupling for independent coins with one fixed oracle. Do not add arbitrary-handler interchange. |
| Nonadaptive batches preserving oracle correlations | `Rounds/Batch.lean` and `RoundMachine.lean` snapshot inputs and prove each captured request is counted; tests cover repeats, inverses and overwritten descriptors | VCVio: a public batch-to-sequential refinement interface preserving shared sampled functions, with query count equal to batch length and separately priced preparation. |
| Resource-proof transport to actual machines | Both `Legacy.lean` clients prove whole image-derived scheme equality before transporting complete security certificates; the rounds support bridge uses actual execution support; the opt-in `Rounds.Proofs` and `Span.Proofs` APIs now compose symbolic interpreter steps and support bounds | VCVio/ArkLib: stable bridges between measured-program counts, machine traces and fixed-oracle distributions. For forked execution, a reusable trace-to-actual-World-counter bridge must require cost-compatible child runners: an arbitrary runner can make a query and return a zero-query trace. Typed extractor paths are useful design precedent, but are not a binding/hiding or CPU-depth theorem. |
| API stability for accepted solver proofs | Each new serial bootstrap copies the existing 81 proof modules at the exact pins; the full verifier replays them against the selected contract | All upstream libraries: deprecation periods or compatibility aliases for public resource/probability lemmas. A future repin needs an explicit solver replay matrix. |

[PolyFun at the current pin](https://github.com/Verified-zkEVM/PolyFun/blob/4181c82238142d9b73403fbf4c4b13e1a801e400/PolyFun/PFunctor/Free/Parallel.lean)
already provides parallel syntax and deliberately fixes left-before-right handler
order. Its documented counterexample excludes unrestricted handler interchange.
The [quantitative API](https://github.com/Verified-zkEVM/PolyFun/blob/4181c82238142d9b73403fbf4c4b13e1a801e400/PolyFun/Realizability/Quantitative.lean)
tracks work, queries, traffic and peak represented sizes. Neither replaces the
local proof that a particular machine's dependencies and prices match these metrics.

Two further items belong outside ArkLib: efficient kernel equality between large
independently encoded artifacts (Lean/Mathlib), and a reviewed implementation of
this fork machine on physical processors (execution backend). The current generated
artifact alias mitigates the first. The abstract span specification and explicit
exclusions avoid making an unsupported hardware claim for the second.

Expected-time extraction, security-parameter families and extractor self-computation
budgets are not required by these two binding/hiding tracks. Revisit them only when
an extractability or asymptotic track has a concrete specification and client.
