# work-span-pareto bootstrap

This is a serial bootstrap for the new Span execution contract. All three
images use `legacy` mode, exactly preserving the original baseline's security
proof and bytes. It is not a parallel optimization: span equals serial work.

The five bounds in claim.json are proved by the full certificate in Solution.lean.
Generate the matching local artifact before compiling:

```sh
python3 scripts/generate_artifact.py submission-commit-golf-work-span-pareto/programs.json --resource-model work-span --refresh
```

Large images should define submission from the generated artifact where practical;
this historical small baseline retains its existing definitional byte equality.
The production verifier regenerates the artifact and clears its build cache.
See [the depth rules](../docs/depth-rules.md) for the execution ABI and exclusions.

## Symbolic proof helpers

Import `CommitGolfDepth.Span.Proofs` to use the protected, opt-in proof API. It is not
imported by the contract or the serial bootstrap certificate.

`runBody_fork_val` exposes one actual fork step: reserved child executions, guarded
shared-memory merge and the parent's continuation. `runBody_fork_bounds` composes
bounds over all reachable child and continuation results. Work adds both children;
span takes their maximum; launch, join and continuation costs remain charged.
Zero fuel, disabled or malformed forks, insufficient reservations, child failure
and exhaustion have separate rules or remain explicit in the continuation.

For an induction, instantiate the child runner with the smaller-depth
`executeBudgeted` interpreter, prove the two child bounds and reservation invariant,
then bound the actual merged-state continuation. `executeBudgeted_succ_bounds`
provides this transport. A successful pair of children does not guarantee a
successful parent: the continuation may exhaust its remaining fuel. These lemmas
do not by themselves prove a complete parallel commitment or its security.

With an arbitrary child runner the query coordinate bounds **trace queries**.
It does not prove that runner's actual `Oracle.run` call count. The full
certificate's actual oracle-query budget remains a separate obligation.
