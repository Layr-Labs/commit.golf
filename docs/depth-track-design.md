# Depth-aware commitment tracks: design and validation

Status: both models selected as separate production tracks; implementation and release validation in progress.
Base: production commit `1a8a66f3609ac24a19e6fbded3a5d26b4d3b9909` (26 November 2026).
Yukon supports adding both tracks. The six existing tracks, their certificates and pins
remain the compatibility boundary. The prototypes are not accepted submissions.

Implemented checkpoints:

- The batch helper and bounded-RAM batch instruction compile, including actual
  fixed-oracle query/count proofs, fuel handling and snapshot-alias regressions.
  A five-word test image uses two queries, one round and 31 abstract cycles.
- The structured work/span model compiles with real RISC-V kernel bounds. Its
  concrete plans have equal work 22 and declared spans 22/14; both canonical
  serializations execute 22 cycles. This is not a parallel-backend theorem.
- Seven synthetic scoring regressions distinguish the competing objectives.

See [archived prototype sources and build instructions](https://github.com/Layr-Labs/commit.golf/blob/d45f94302f2c36881f34f4c4bb455321f64d4325/DepthPrototype/README.md).

The track contracts and artifact/claim interfaces are specified in [depth rules](depth-rules.md).
Initial baselines preserve the complete serial certificate through exact legacy bridges.
They establish an admission path, not an optimized parallel construction.

## Goal and common workload

Reward lower sequential dependence alongside total prover work and opening-proof
bytes. Preserve one commitment to `2^24` logical 256-byte leaves followed by one
opening of 128 positions. Record commitment and opening costs separately. Their
resource bounds must cover the same fixed-oracle/message/position/private-coin
quantifiers as the existing honest bounds. Checking remains outside the objectives; adding it requires a separately certified
bound and an explicit policy choice.

The security games can be reused only for the scheme derived from the new
executable semantics. A certificate for the old interpreter does not certify a
new batch instruction: old failure on a selector can become execution in the new
interpreter, including on adversarial inputs.

## Candidate A: batched oracle-round depth

One batch supplies a finite collection of nonadaptive public queries. Every
descriptor and every input byte is captured before the first oracle answer or
output write. Answers use the same fixed compression/permutation pair as the
rest of the experiment. Repeated queries and forward/inverse calls retain their
correlations: nonadaptivity does not mean statistical independence.

- Count every underlying call in query budgets, including repeats and inverses.
- A nonempty batch consumes one round; an empty batch consumes zero rounds.
- Ordinary single oracle calls consume one round each. Randomness and local
  instructions contribute work but are not public oracle rounds.
- Charge total primitive work, descriptor processing and required memory work;
  batching is not a free bulk-data instruction.
- Bound descriptor count, byte sizes, alignment and addresses without overflow.
  Define/restrict output overlap and snapshot input/output aliases explicitly.
- Specify behavior on malformed requests, faults, exhaustion and checker coins.

A serial evaluation of the captured query list is a valid implementation of this
ideal round semantics. It is not a proof of physical simultaneous evaluation.
Resource reporting is `(total prover cycles, proof bytes, total oracle rounds)`.
The round count does not bound sequential local work, randomness generation,
memory bandwidth, or actual multicore makespan.

For the preserved binary salted-Merkle baseline, leaf hashing makes eight chained
compression calls and the tree has 24 internal levels. Level-wise batching would
therefore need 32 commitment rounds, not the 25 obtained by assuming a one-call
leaf. This statement assumes all required private salts are already available;
their generation is still charged work. A working baseline must prove these
bounds for its actual images, including descriptor preparation and output layout.
The batch-width limit is part of the model: splitting a layer across batches
increases its rounds. The 32-round estimate assumes the limit can accommodate
the `2^24`-query leaf stages. It is not a bound for an arbitrary smaller limit.

## Candidate B: executable work and span

Use an explicit structured fork/join plan over delivered RISC-V kernels. Kernel
costs come from execution; ownership/dependency conditions justify concurrency.
Work sums all computation, while span adds along sequencing and takes the maximum
over parallel branches, including declared preparation and fork/join costs.

The prototype must keep the following boundaries visible:

- Input-dependent control, register dependencies, memory aliases and output
  assembly cannot be dropped from the dependency relation without proof.
- Kernel input views, wiring, copies, randomness, scheduling and readout are not
  arbitrary free Lean functions. State exactly which interface work is excluded.
- Specify oracle latency, throughput and worker occupancy, rather than converting
  query count to processor time by an assumed constant.
- Specify shared versus private memory and aggregate storage limits. A sequential
  peak-state bound is not aggregate memory for concurrently live workers.
- Prove semantic correspondence for each fixed oracle, with a coupling of private
  coins, to the scheme whose security and completeness are certified.

The first prototype compares concrete sequential and independent kernel tasks.
It does not itself establish a full commitment certificate or scheduling theorem.
Production supplies a specified fork interpreter, actual-image security/resource
certificate and delivered-artifact linkage. A physical scheduler refinement is
separate from this abstract span contract.
At full vector size, the plan must also have a compact executable representation
or generator. A giant proof-side list of leaf tasks cannot replace delivered
code, evade image-size admission or hide plan construction and wiring costs.

## Scoring alternatives to compare

For either depth model, three-objective Pareto ranking is possible:

`[commitWork + openingWork, proofBytes, commitDepth + openingDepth]`.

The depth label identifies oracle rounds or weighted executable span; their
numbers are not interchangeable. Work for a parallel plan includes its overhead
and is not automatically bounded by the old serial program's cycle certificate.
The submitted values are upper bounds. Their ratio is not certified parallelism:
inflating a work bound can make `workBound / spanBound` arbitrarily impressive.
Pareto minimization of the bounds does not give that inflation a ranking benefit.

A scalar rule must make its tradeoff explicit. `proofBytes * rounds` ignores work
unless accompanied by a work limit. A weighted work/rounds score is a benchmark
preference, not an elapsed-time prediction. In particular,
`cycles / P + c * oracleRounds` is not a certified parallel runtime when local
computation and its dependencies remain unmeasured.

For executable work/span, a fixed-worker objective can instead multiply proof
bytes by a *proved upper bound* on the two phase schedules. The familiar
`max(work / P, span)` is only a lower bound. Scheduling and communication costs
require explicit assumptions or additional charges.
Here `work` and `span` denote actual DAG costs. Substituting independently
certified upper bounds does not establish a lower bound on actual execution time.
For example, six unit tasks in two layers of three with a barrier have work six
and span two, but need four ticks on two workers. Three independent two-task
chains have the same work/span and finish in three ticks. Neither the maximum
formula nor the pair of metrics determines exact finite-worker time.

## Implementation gates

1. Build bounded Lean prototypes for both models, including nonvacuous concrete
   executions and counterexamples to misleading metrics.
2. Independently review snapshots, aliases, counting, private coins, executable
   correspondence, and ranking tradeoffs. Record unresolved bridges.
3. Selection: develop both models as separate tracks, each with three-objective Pareto ranking. Scalar comparisons remain research tools, not runtime claims.
4. Add an isolated machine/resource certificate and trusted comparator template,
   strict claim schema, artifact representation, track configuration and reports.
   Existing templates and track semantics remain unchanged.
5. Supply a fully certified baseline. A legacy-execution bootstrap is acceptable
   only when explicitly identified; it does not demonstrate a parallel baseline.
6. Run unit, kernel, linkage, maximum-image and supported full-certificate checks;
   obtain independent review before publishing implementation commits.

## Upstream reuse and references

The [upstream handoff](depth-upstream-needs.md) ties requests to these concrete
clients and distinguishes reusable APIs from missing machine refinement proofs.


The current PolyFun pin `4181c82238142d9b73403fbf4c4b13e1a801e400` already has
`FreeM.parallel` and quantitative execution/resource contracts. Its sequential
handler interprets joint calls left-before-right; the syntax does not supply a
machine work/span theorem. Current import policy does not allow direct PolyFun
imports. A reviewed public bridge or alternate-track policy would be needed.
Ark extractor-stage path length is a different resource from parallel span.

- [Current rules](https://github.com/Layr-Labs/commit.golf/blob/1a8a66f3609ac24a19e6fbded3a5d26b4d3b9909/RULES.md).
- [Current certificate](https://github.com/Layr-Labs/commit.golf/blob/1a8a66f3609ac24a19e6fbded3a5d26b4d3b9909/CommitGolf/Statements.lean).
- [PolyFun parallel syntax and handler caveats](https://github.com/Verified-zkEVM/PolyFun/blob/4181c82238142d9b73403fbf4c4b13e1a801e400/PolyFun/PFunctor/Free/Parallel.lean).
- [PolyFun quantitative execution](https://github.com/Verified-zkEVM/PolyFun/blob/4181c82238142d9b73403fbf4c4b13e1a801e400/PolyFun/Realizability/Quantitative.lean).
- [OpenCilk work/span concepts](https://www.opencilk.org/doc/tutorials/opencilk-concepts/).
- [Blelloch on work, depth, scheduling and communication](https://www.cs.cmu.edu/~scandal/cacm/node3.html).
