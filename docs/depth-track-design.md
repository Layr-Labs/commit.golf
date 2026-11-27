# Depth-aware commitment tracks: design

The challenge has separate oracle-round and CPU work/span tracks. Both use
three-objective Pareto ranking, preserving total prover work and proof bytes as
objectives. The [depth rules](depth-rules.md) specify their execution, artifact and
claim interfaces and record [validation and launch requirements](depth-rules.md#validation-and-launch).

The six existing tracks, their certificates and dependency pins retain their
semantics. The depth design started from production commit
`1a8a66f3609ac24a19e6fbded3a5d26b4d3b9909` (26 November 2026).

## Research prototypes

The [archived prototypes](https://github.com/Layr-Labs/commit.golf/blob/d45f94302f2c36881f34f4c4bb455321f64d4325/DepthPrototype/README.md)
compared the models before the production interpreters:

- A five-word batch image uses two queries, one round and 31 abstract cycles.
- Two structured work/span plans have equal work 22 and declared spans 22/14.
  Both canonical serializations execute 22 cycles. This is not a parallel-backend theorem.
- Seven synthetic scoring tests distinguish Pareto/scalar tradeoffs and finite-worker
  scheduling costs. They do not measure live submissions.

The current serial baselines preserve the complete certificate through exact
legacy bridges. They establish an admission path, not an optimized parallel construction.

## Goal and common workload

Reward lower sequential dependence alongside total prover work and opening-proof
bytes. Preserve one commitment to `2^24` logical 256-byte leaves followed by one
opening of 128 positions. Record commitment and opening costs separately. Their
resource bounds must cover the same fixed-oracle/message/position/private-coin
quantifiers as the existing honest bounds. Checking remains outside the objectives.
Adding it requires a separately certified bound and an explicit policy choice.

The security games can be reused only for the scheme derived from the new
executable semantics. A certificate for the old interpreter does not certify a
new batch instruction: old failure on a selector can become execution in the new
interpreter, including on adversarial inputs.

## Oracle-round depth

One batch supplies a finite collection of nonadaptive public queries. Every
descriptor and every input byte is captured before the first oracle answer or
output write. Answers use the same fixed compression/permutation pair as the
rest of the experiment. Repeated queries and forward/inverse calls retain their
correlations: nonadaptivity does not mean statistical independence.

- Every underlying call counts in query budgets, including repeats and inverses.
- A nonempty batch consumes one round; an empty batch consumes zero rounds.
- Ordinary single oracle calls consume one round each. Randomness and local
  instructions contribute work but are not public oracle rounds.
- The macro charges primitive work and descriptor overhead. Caller preparation
  remains ordinary machine work.
- The parser checks descriptor count, byte sizes, alignment and addresses without
  wraparound. Inputs use a common snapshot; overlapping outputs use array order.
- Malformed requests reject before any query. Faults reject, exhaustion remains
  unfinished, and the checker cannot obtain private coins.

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

## Executable work and span

The [fork/join interpreter](../CommitGolfDepth/Span/Machine.lean) executes delivered
RV64 images. Guest-memory descriptors select child entry points, owned regions and
reserved instruction budgets. The interpreter constructs the dependency trace from
those executions. Work sums all computation; span adds sequential costs and takes
the maximum over child spans, including the declared launch and join costs.

Each task executes its input-dependent control flow and register operations in order.
The [memory policy](../CommitGolfDepth/Span/Memory.lean) guards shared-memory accesses.
The children cannot read or write each other's owned regions. Snapshot inputs and
disjoint writes justify the logical shared-memory join. Task inputs, copies and
output assembly must follow the specified ABI and execution, rather than an arbitrary
unpriced Lean function.

Canonical evaluation keeps the same fixed oracle and private-coin sampling effects
as the scheme whose security the certificate proves. A physical scheduler refinement
is separate from this abstract span contract. Predicting elapsed time also requires
an oracle latency/throughput model, worker occupancy and memory communication costs.
A sequential peak-state bound does not bound aggregate storage for concurrent workers.

At full vector size, the plan must also have a compact executable representation
or generator. A giant proof-side list of leaf tasks cannot replace delivered
code, evade image-size admission or hide plan construction and wiring costs.

## Scoring and scalar alternatives

Both depth models use three-objective Pareto ranking:

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

## Remaining proof work

The opt-in [rounds](../CommitGolfDepth/Rounds/Proofs.lean) and
[span](../CommitGolfDepth/Span/Proofs.lean) APIs compose symbolic interpreter steps
and bounds over every supported result. A parallel commitment still needs proofs
of table preparation, data layout, complete execution, actual oracle-query budgets
and security. The serial bootstrap does not discharge those obligations for new modes.

For an arbitrary child runner, the span API's query coordinate counts trace annotations.
A runner can make an actual oracle query and return a zero-query trace. A theorem
relating those annotations to the independent `Oracle.run` counter therefore needs
cost-compatible child runners. The full certificate's query-budget field remains
an independent obligation.

## Upstream reuse and references

The [upstream handoff](depth-upstream-needs.md) ties requests to these concrete
clients and distinguishes reusable APIs from missing machine refinement proofs.
The current PolyFun pin `4181c82238142d9b73403fbf4c4b13e1a801e400` already has
`FreeM.parallel` and quantitative execution/resource contracts. Its sequential
handler interprets joint calls left-before-right; the syntax does not supply a
machine work/span theorem. Current import policy does not allow direct PolyFun
imports. A reviewed public bridge or alternate-track policy would be needed.
ArkLib extractor-stage path length is a different resource from parallel span.

- [Rules at the design base](https://github.com/Layr-Labs/commit.golf/blob/1a8a66f3609ac24a19e6fbded3a5d26b4d3b9909/RULES.md).
- [Certificate at the design base](https://github.com/Layr-Labs/commit.golf/blob/1a8a66f3609ac24a19e6fbded3a5d26b4d3b9909/CommitGolf/Statements.lean).
- [PolyFun parallel syntax and handler caveats](https://github.com/Verified-zkEVM/PolyFun/blob/4181c82238142d9b73403fbf4c4b13e1a801e400/PolyFun/PFunctor/Free/Parallel.lean).
- [PolyFun quantitative execution](https://github.com/Verified-zkEVM/PolyFun/blob/4181c82238142d9b73403fbf4c4b13e1a801e400/PolyFun/Realizability/Quantitative.lean).
- [OpenCilk work/span concepts](https://www.opencilk.org/doc/tutorials/opencilk-concepts/).
- [Blelloch on work, depth, scheduling and communication](https://www.cs.cmu.edu/~scandal/cacm/node3.html).
