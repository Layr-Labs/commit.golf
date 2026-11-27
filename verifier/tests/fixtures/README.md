# New-mode resource clients

These small delivered images exercise the two new interpreters through
`Submission.run .commit`, including normal ABI initialization. Each Lean client
proves artifact equality, image admission and resource behavior for the fixed
zero message and **every fixed oracle**. Neither implements a secure commitment
scheme, supplies a production certificate or earns a score.

| Client | Mode | Work | Depth | Public queries | Checked outputs |
| --- | --- | --- | --- | --- | --- |
| [RoundsResources.lean](RoundsResources.lean) | batched | 33 cycles | 1 round | 2 | Last byte of each compression reply |
| [SpanResources.lean](SpanResources.lean) | fork/join | 103 work | 95 span | 0 | Child squares 49 and 81 |

The batch has two compression requests. Its first output overlaps the second
input: both must nevertheless hash the original zero input. This checks snapshot
semantics with oracle-dependent outputs. The fork client runs actual MUL and SD
instructions in two disjoint child regions and proves span strictly below work.
Descriptor tables are embedded image data; their initial loading is unscored under
the existing ABI. Machine setup and the specified macro prices are charged.

The clients also check the opt-in
[rounds](../../../CommitGolfDepth/Rounds/Proofs.lean) and
[span](../../../CommitGolfDepth/Span/Proofs.lean) proof libraries. They export symbolic
batch/fork and ordinary-instruction step equations and continuation bounds. The trusted
[rounds](RoundsResources.lean.in) and [span](SpanResources.lean.in) templates state these
theorems with the live interpreter, RAM, fuel and resource fields directly. They do
not use proof-library predicates as specifications. The libraries belong to the
protected source tree, so replacing a submission's candidate modules does not remove them.

Span targets also check oracle, HALT and RANDOM dispatch, including argument rejection,
actual sampling effects and resource bounds. With an arbitrary child runner, the
query coordinate counts trace annotations, not the independent `Oracle.run` counter.
The full certificate's actual query budget remains a separate obligation. Neither
client proves table construction or a complete parallel commitment.

From the repository root, run on the supported Linux verifier after setup:

```sh
python3 verifier/tests/check_depth_resources.py
```

The [harness](../check_depth_resources.py) creates a private trusted project with an explicit
resource-only theorem template. It preserves the production axiom and kernel
policies. For each client it checks a positive resource proof and rejects an
understated work bound, an understated depth bound, a changed execution mode and
a changed code byte. It also checks that the resource client is rejected by the
original full-security certificate contract.

For each model, further negatives change the round/span bound at `symbolic_bounds`
or remove an ordinary instruction's work charge at `ordinary_bounds`. Three Span-only
negatives remove the oracle query increment, HALT work or RANDOM work at their
respective bound targets. There are 19 cases in total. Each negative requires its
expected linkage or theorem-mismatch diagnostic. Timeouts and unrelated failures do not pass.

The [CI setup](../../../scripts/setup.sh) explicitly builds both `Proofs` modules.
The contract-regression workflow calls
[`scripts/blacksmith.sh test-linkage`](../../../scripts/blacksmith.sh), which runs
this verifier harness after the Python and linkage tests.

The harness never changes production templates, comparator policy or score files.
It records source, helper-library, manifest, template and configuration hashes in its case results.
An ordinary Lean compile is useful feedback; only a successful supported-verifier
run establishes acceptance by that verifier.
