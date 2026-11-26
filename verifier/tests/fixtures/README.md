# New-mode resource clients

These small delivered images exercise the two new interpreters through
`Submission.run .commit`, including normal ABI initialization. Each Lean client
proves artifact equality, image admission and resource behavior for the fixed
zero message and **every fixed oracle**. Neither implements a secure commitment
scheme, supplies a production certificate or earns a score.

| Client | Mode | Work | Depth | Public queries | Checked outputs |
| --- | --- | --- | --- | --- | --- |
| `RoundsResources.lean` | batched | 33 cycles | 1 round | 2 | Last byte of each compression reply |
| `SpanResources.lean` | fork/join | 103 work | 95 span | 0 | Child squares 49 and 81 |

The batch has two compression requests. Its first output overlaps the second
input: both must nevertheless hash the original zero input. This checks snapshot
semantics with oracle-dependent outputs. The fork client runs actual MUL and SD
instructions in two disjoint child regions and proves span strictly below work.
Descriptor tables are embedded image data; their initial loading is unscored under
the existing ABI. Machine setup and the specified macro prices are charged.

The same clients import the protected, opt-in `Rounds.Proofs`/`Span.Proofs` libraries and
export general-input batch/fork and ordinary-instruction step and continuation-bound
theorems. Their trusted expected
types spell out the live interpreter, RAM, fuel and resource fields directly;
they do not import proof-library predicates as specifications. The shared libraries
remain available even when a later submission replaces its candidate modules. This checks
symbolic counts and child/continuation bounds in addition to concrete reductions.
It does not prove table construction or an entire parallel commitment.

Run on the supported Linux verifier after setup:

```sh
python3 verifier/tests/check_depth_resources.py
```

This maintainer regression creates a private trusted project with an explicit
resource-only theorem template. It preserves the production axiom and kernel
policies. For each client it checks a positive resource proof and rejects an
understated work bound, an understated depth bound, a changed execution mode and
a changed code byte. It also checks that the resource client is rejected by the
original full-security certificate contract. A further negative changes the
symbolic round/span bound at `symbolic_bounds`; two others remove an ordinary
instruction's work charge at `ordinary_bounds`. There are 16 cases in total.
Negative cases require the expected
linkage or theorem-mismatch diagnostic; timeouts and unrelated failures do not pass.

The CI setup explicitly builds both `Proofs` modules. The contract-regression
workflow calls `scripts/blacksmith.sh test-linkage`, which runs this compile harness
after the Python and linkage tests.

The harness never changes production templates, comparator policy or score files.
It records source, helper-library, manifest, template and configuration hashes in its case results.
An ordinary Lean compile is useful feedback; only a successful supported-verifier
run establishes acceptance by that verifier.
