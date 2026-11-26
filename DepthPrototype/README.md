# Depth-model research implementations

These frozen research modules motivated the two separate production depth tracks. They are not imported by `CommitGolf`; solvers cannot
import this namespace under the current policy. They are not production certificate definitions; the separate implementations live
in `CommitGolfDepth/`.

| Module | Implemented and proved | Remaining boundary |
| --- | --- | --- |
| `Batch.lean`, `BatchTests.lean` | Pre-state query snapshots, fixed-oracle refinement, exact query/primitive-cost counts, PC and byte-write correspondence | Helper fee quote alone is not instruction dispatch |
| `BatchMachine.lean`, `BatchMachineTests.lean` | Actual RAM descriptor parser and RISC-V batch selector, bounded count/addresses/fuel, charged macro work and rounds, exact legacy projection | No whole commitment scheme, artifact admission or full security certificate |
| `WorkSpan.lean`, `WorkSpanTests.lean` | Actual private RISC-V kernels, serialized work bounds, structured span algebra and concrete examples | No task-launch implementation, parallel scheduler, whole-message preparation or full commitment certificate |
| `compare_scores.py`, `test_compare_scores.py` | Synthetic Pareto/scalar tradeoffs and finite-worker counterexamples | No measured live-entry metrics or verified scheduler |

Build the prototypes with the repository's exact pinned Lean toolchain:

```sh
lake build CommitGolf CommitGolfTests
lake build DepthPrototype
python3 -m unittest discover -s DepthPrototype -p test_compare_scores.py
python3 DepthPrototype/compare_scores.py
```

These are ordinary Lean builds and Python tests. They are not official supported
verifier acceptance of a new submission. No `sorry`, new axiom, native decision
procedure or disabled kernel checking is used in the prototype sources.

## Batch instruction

In the prototype's **batched** mode, `ECALL` with `t0=3` uses `a0` as the descriptor
base and `a1` as the count. Each descriptor is four little-endian 64-bit words:
primitive kind, input address, input-byte length, output address. The count cap is
`2^24`. The aligned descriptor array must fit in the 64-GiB model without wrapping.
The existing per-primitive width/alignment/address checks still apply.

All descriptors and query inputs are captured before the first answer/write.
Replies share one fixed oracle and are written in descriptor order. Repeats still
consume multiple queries; forward/inverse calls are not resampled. Overlapping
outputs have ordered last-writer semantics, so they must not be assumed to be
independent writes in a future parallel-span model.

The fixed experimental macro price is `1 + 5*k + sum(primitive prices)`: one entry
unit, four descriptor-word units and one bookkeeping unit per request. Caller
preparation remains ordinary charged program work. These are declared abstract
prices, not a microcode or hardware-runtime measurement. A nonempty batch uses
one oracle round, an empty batch zero; both consume one instruction of fuel.

The tests execute a five-word image with two compression queries: success,
31 total cycles, two calls and one round, including actual reply bytes. Another
test overwrites a later descriptor with the first reply and proves that the
second query still uses its captured original descriptor/input.

**Legacy** mode delegates exactly to the old interpreter and counts one round
per old public call. The same new-selector image fails in legacy mode. Thus the
prototype makes no blanket compatibility claim for old images under new semantics.
The production `CommitGolf.Artifact.depthSubmission` binds that mode to the
delivered artifact; a solver-supplied abstract mode claim is insufficient.

## Work and span

Each kernel executes real RV64IM code on private state with a supplied read-only
input word. The model sums work and uses addition for serial dependencies and
maximum for forked branches. Its LD/MUL/HALT example has five instructions and
eight cycles, including the four-cycle multiply.

Two such leaves plus two three-cycle control kernels yield work 22 in either
plan and declared spans 22 versus 14. Both actual canonical serializations use
22 cycles, make zero oracle calls and return `(49,49)`. The entry/exit kernels
are HALT padding, not implementations of task launch or synchronization. Plan
construction, task input loading and output inspection are outside this bounded
model; no arbitrary free host computation of commitment data is authorized.

The separate production work supplies executable fork semantics, actual-image
security/resource certificates and artifact linkage in `CommitGolfDepth/Span`.
An optimized parallel commitment baseline, physical scheduler refinement and
aggregate physical context-storage bounds remain separate improvements.

The [design note](../docs/depth-track-design.md) records both scoring options,
the upper-bound versus exact-cost distinction, and release gates.
