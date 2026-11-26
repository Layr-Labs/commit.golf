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

Run on the supported Linux verifier after setup:

```sh
python3 verifier/tests/check_depth_resources.py
```

This maintainer regression creates a private trusted project with an explicit
resource-only theorem template. It preserves the production axiom and kernel
policies. For each client it checks a positive resource proof and rejects an
understated work bound, an understated depth bound, a changed execution mode and
a changed code byte. It also checks that the resource client is rejected by the
original full-security certificate contract. Negative cases require the expected
linkage or theorem-mismatch diagnostic; timeouts and unrelated failures do not pass.

The harness never changes production templates, comparator policy or score files.
It records source, manifest, template and configuration hashes in its case results.
An ordinary Lean compile is useful feedback; only a successful supported-verifier
run establishes acceptance by that verifier.
