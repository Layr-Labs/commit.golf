# Depth tracks

The two depth tracks minimize prover work, proof size and either oracle rounds or
weighted CPU span. They use separate execution contracts from the six existing tracks.
Oracle rounds and weighted span measure different resources.

| Track | Pareto objectives, minimized in this order of reporting | Claim fields |
| --- | --- | --- |
| `commit-golf-oracle-rounds-pareto` | `[commitCycles + openingCycles, proofBytes, commitRounds + openingRounds]` | `proofBytes`, `commitCycles`, `openingCycles`, `commitRounds`, `openingRounds` |
| `commit-golf-work-span-pareto` | `[commitWork + openingWork, proofBytes, commitSpan + openingSpan]` | `proofBytes`, `commitWork`, `openingWork`, `commitSpan`, `openingSpan` |

Pareto domination means no objective is worse and at least one is better. The
reporting order does not give any objective priority. Every claim and each summed
objective is an integer between zero and `2^53 - 1`. There is no unranked product
admission cap on these tracks. The older tracks retain their numeric rules.

The workload, oracle model, input/output ABI, admission, completeness, termination,
query budgets and binding/hiding games remain those in [RULES.md](../RULES.md).
Both depth tracks use **64→32-byte compression at 8 cycles** and forward/inverse
permutations at **8 cycles**. Each public call consumes one query, including repeats.
Scored resource bounds concern one full commitment and one opening of 128 leaves, without
amortization, under the existing fixed-oracle and private-coin quantifiers.

Each certificate proves all security properties for the scheme derived from its
actual images and selected interpreter, and adds its resource bounds. An old
certificate alone does not certify a new instruction. Exact all-legacy transport
lemmas are supplied; they do not establish equivalence of batched or fork mode.

## Oracle rounds

[The rounds contract](../CommitGolfDepth/Rounds.lean) gives each phase either
`legacy` or `batched` mode. Legacy uses the original interpreter exactly and counts
each public call as one round. Batched mode adds ECALL selector `t0=3`:

- `a0`: base address of an 8-byte-aligned descriptor array; `a1`: its count, at most `2^24`.
- Each 32-byte descriptor holds four little-endian 64-bit words: primitive selector,
  input address, input byte length, output address. Selectors match the existing
  compression/forward/inverse syscall interface: 0/1/2. Input and output addresses
  must be 8-byte aligned. Compression reads exactly 64 bytes and writes 32; either
  permutation reads and writes exactly 200 bytes.
- The entire descriptor array and all query input bytes are read from the same
  pre-call memory state. Invalid descriptors reject the batch before any query.
- Answers use the same sampled primitives as every other call. Outputs are written
  in array order; if they overlap, the last write wins. An answer cannot influence
  another query in this batch, even if an output overwrites an input or descriptor.
- A nonempty batch contributes one round; an empty batch contributes zero. Each
  underlying query still counts separately and incurs its primitive price.
- The macro costs `1 + 5*k + sum(primitive prices)` cycles for `k` requests and
  consumes one instruction of fuel. It preserves registers and advances PC by four.
  Caller-side preparation is ordinary charged machine work. Malformed arrays cost
  one cycle; valid arrays with malformed
  requests incur preparation cost. Fuel exhaustion remains unfinished.

The five-cycle request overhead is an explicit benchmark macro price, not an RV64
implementation theorem for descriptor parsing. Fixed-size oracle I/O retains the
existing flat price. Private randomness and local instructions cost cycles but do
not contribute public oracle rounds. The checker still cannot obtain private coins.

Rounds measure oracle dependency stages, including public-oracle chains used to
generate salts. They do not measure local CPU/private-coin generation depth,
physical bandwidth or elapsed multicore time.

## CPU work and span

[The span contract](../CommitGolfDepth/Span.lean) gives each phase `legacy` or
`forkJoin` mode. Legacy runs the original interpreter exactly, with span equal to
cycles. Fork mode adds ECALL selector `t0=3`; it does not add the batch syscall.

`a0` points to an 8-byte-aligned 128-byte table containing two 64-byte child records.
Each record holds eight little-endian 64-bit words: entry PC, positive instruction
fuel at most `2^48`, owned memory base, owned byte length, and child `a0`–`a3`.
After consuming the FORK instruction, both child fuel allowances must fit within
the parent’s remaining fuel. They are reserved before either child runs; unused
reservations are not refunded, and the continuation receives only unreserved fuel.
Thus the root instruction allowance bounds the whole fork computation, rather than
giving every descendant a fresh full allowance.

Both descriptors are captured before either child runs. Children execute the same
immutable image, with private zeroed registers except these arguments and inherited
`sp`. On successful join their registers are discarded; the parent retains its registers
and resumes at PC+4.

Child entry PCs are 4-byte aligned and at least `0x1000`; fetch enforces the image boundary.
Owned bases and lengths must be multiples of eight, within parent ownership, and disjoint. A child may
read the shared parent snapshot except sibling-owned regions and inherited forbidden
regions. It may write only its own region. Guards cover ordinary loads/stores,
subword read/modify/write words, oracle inputs/outputs, randomness outputs, and nested
descriptor tables. Children inherit the checker's coin prohibition and cannot switch
to the legacy interpreter. Nested forks are limited to 32 levels.

Both bounded child executions contribute work even if one fails. Exhaustion of
either child dominates failure; it cannot be hidden by a fault in the other child.
The parent continues only after two successful children. A successful join makes
disjoint child writes visible in shared memory and preserves other memory.

The executed trace, built by the interpreter rather than supplied by the solver,
determines the metrics:

- Ordinary work and span add the existing instruction/syscall cost.
- Fork work adds launch, **both** child works, join and continuation work.
- Fork span adds launch, the **maximum** child span, join and continuation span.
- Query counts add across both children and the continuation.
- Launch costs 81 abstract cycles (16 descriptor words, 64 register-context writes,
  one launch). Join costs one synchronization cycle. Caller preparation costs work.

Constant join is logical shared-RAM visibility, not free copying between private
64-GiB memories. Permission enforcement is an explicit machine primitive; frame,
read-view and disjoint overlay lemmas justify the ownership model. The canonical
interpreter evaluates children left then right using the same fixed oracle and
private random draws. These definitions do not assert commutation for arbitrary
stateful effects or supply a physical parallel backend.

## Artifacts, development and validation

Edit only the selected `submission-<track>/` directory. Depth manifests have
`schemaVersion: 2` and all existing artifact fields plus exactly:

```json
"executionModes": {"commit": "legacy", "opening": "legacy", "check": "legacy"}
```

Each value may instead select that track's `batched` or `forkJoin` mode. Unknown,
missing, mixed-profile or extra modes reject. The generated
`CommitGolf.Artifact.depthSubmission` binds the modes and core bytes together.
`submission_matches_artifact` must prove equality with that value; the comparator
also checks the **full** selected certificate with all five bounds.

Generate a local artifact from the selected manifest:

```sh
python3 scripts/generate_artifact.py submission-commit-golf-oracle-rounds-pareto/programs.json --resource-model oracle-rounds --refresh
# Or use the work/span manifest and --resource-model work-span.
lake build CommitGolfDepth.Rounds CommitGolfDepth.Span
python3 scripts/run.py --track commit-golf-oracle-rounds-pareto
```

The last command requires the supported Linux verifier and checks the full
certificate; an ordinary Lean build is not official verification. For large
images, alias the generated artifact definition and prove linkage by `rfl`.
Equality between independently encoded maximum-size images is not known to be
practical. The verifier regenerates the artifact and invalidates cached copies.

The initial baselines are **serial bootstraps**, preserving the old salted-Merkle
bytes and complete proof. Rounds are 150,994,943 for commitment and zero for
opening; legacy span equals work. They do not demonstrate parallel optimization.

Separate [resource-only clients](../verifier/tests/fixtures/README.md) exercise
batched and fork/join images on a fixed zero message, for every fixed oracle. They
check resource proofs and artifact linkage, without supplying security certificates.
The [rounds](../submission-commit-golf-oracle-rounds-pareto/README.md#symbolic-proof-helpers)
and [span](../submission-commit-golf-work-span-pareto/README.md#symbolic-proof-helpers)
READMEs describe opt-in symbolic proof APIs. These helpers leave certificate imports
unchanged. They do not discharge table preparation, actual oracle-query budgets or
complete construction/security proofs.

A level-wise version of that tree would need eight leaf-hash stages plus 24 tree
levels (32 rounds), assuming a whole layer fits one batch and salts are already
available without extra oracle dependencies; this is a design estimate,
not a bound proved for the bootstrap images.

## Limits

Security is query-dependent: binding error is at most `q/2^120` for `q≥1`, and
hiding error at most `min(1,(t+1)/2^120)`. The inherited hiding definition fixes an
opening size and positions before commitment; it covers one opening, not adaptive
or repeated openings. Timing/memory side channels and efficient extraction are not
certified. These depth tracks do not strengthen those security definitions.

Unscored resources include checker work/span, trapdoor capacity, initial input
loading and interface decoding. The 64-GiB bound is shared guest RAM, not a bound
on physical aggregate register contexts or interpreter metadata. Fork depth and
per-task fuel are capped, but peak parallel context storage is not an objective.
Memory operations and oracle I/O use abstract prices without bandwidth/cache costs.
In the rounds track, one batch consumes one instruction allowance while doing up
to `2^24` primitive calls; its full work is charged, but unscored checker work can
therefore be much larger than for the old ISA. A separate checker-work cap would
be a further resource-policy improvement, requiring its own baseline proof.

Work/span follows the usual [fork/join DAG interpretation](https://www.opencilk.org/doc/tutorials/opencilk-concepts/).
Relating it to finite-processor elapsed time requires scheduling and communication
assumptions, as [Blelloch explains](https://www.cs.cmu.edu/~scandal/cacm/node3.html).
Ratios of independently certified upper bounds do not prove actual parallelism;
`max(work/P, span)` is not a certified runtime upper bound. Scalar scoring options
remain [research comparisons](depth-track-design.md), not production scoring policies.

## Validation and launch

[CI run 45911609582](https://github.com/Layr-Labs/commit.golf/actions/runs/45911609582)
at [636d294](https://github.com/Layr-Labs/commit.golf/commit/636d294b7780ad03b34b5f5bc14614120e689d86)
passed 151 Python tests, 19 resource-client cases, full-certificate verification for
all eight tracks, and the `contract-regressions` gate. These results apply to that
commit. Source review or ordinary Lean compilation alone does not establish
supported-verifier acceptance.

Launch still requires the pre-sandbox bounded-read/staging fixes in
[PR #31](https://github.com/Layr-Labs/commit.golf/pull/31), administrator enforcement
of `contract-regressions`, and Yukon approval of the three-objective tracks and their
abstract prices. Future execution or verifier changes need independent review and
verification of the affected certificates at the new commit.
