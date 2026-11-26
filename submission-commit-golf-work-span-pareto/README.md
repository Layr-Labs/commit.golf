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
