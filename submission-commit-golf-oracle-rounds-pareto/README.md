# oracle-rounds-pareto bootstrap

This is a serial bootstrap for the new Rounds execution contract. All three
images use `legacy` mode, exactly preserving the original baseline's security
proof and bytes. It is not a parallel optimization: rounds count every public oracle call.

The five bounds in claim.json are proved by the full certificate in Solution.lean.
Generate the matching local artifact before compiling:

```sh
python3 scripts/generate_artifact.py submission-commit-golf-oracle-rounds-pareto/programs.json --resource-model oracle-rounds --refresh
```

Large images should define submission from the generated artifact where practical;
this historical small baseline retains its existing definitional byte equality.
The production verifier regenerates the artifact and clears its build cache.
See [the depth rules](../docs/depth-rules.md) for the execution ABI and exclusions.

## Symbolic proof helpers

Import `CommitGolfDepth.Rounds.Proofs` to use the protected, opt-in proof API. It is not
imported by the contract or the serial bootstrap certificate.

`loadDescriptors_formula` proves decoding of a table of arbitrary admitted length
from four RAM-word invariants per index. `executeBatched_regular` combines those
invariants and pointwise pre-state captures into an actual interpreter step for a
symbolic count; it covers zero requests without expanding a literal descriptor list.
`executeBatched_batch_bounds` composes worst-case continuation bounds over every
possible reply and outcome. `executeBatched_batch_counted` preserves the fixed
oracle and its independent call counter.

For a binary-tree level, describe the descriptor and captured request as functions
of the index, prove alignment/range and RAM contents, then use `snapshot_compression`
and `executeBatched_regular`. `compression_quote` gives `1 + 13*k` macro cycles
for `k` compression requests; descriptor/input preparation is additional machine
work. Empty batches pay one entry cycle and zero rounds. The helpers neither build
the table for free nor prove a complete tree construction or its security.

For setup and loop instructions, `executeBatched_nonbatch` exposes the real
one-instruction `Riscv.execute` computation. Deterministic unfinished/terminal
corollaries reuse existing one-tick proofs; `executeBatched_nonbatch_bounds`
composes support bounds. This branch includes ordinary ORACLE/RANDOM calls,
HALTs and faults. It enters the continuation only for an unfinished tick and
charges public calls as rounds. Terminal paths retain their actual costs.
