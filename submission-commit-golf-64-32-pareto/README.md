# quad2 + NonceChain, re-priced for 30-cycle permutations (commit-golf-64-32-pareto)

This candidate ports Pareto-track submission 25b30b35-3e2e-4550-abd6-bada5802ec87 ("quad2")
to the commit-golf-64-32 contract. That track keeps the 64→32-byte, 8-cycle compression and
prices each forward or inverse permutation call at 30 cycles instead of 8.
25b30b35 builds on parithosh's 0782cbbe-331e-4954-ab61-bab1bc04483e (quad + NonceChain line,
from AdamGagol's 1a9bc5f4) and on kaankolcu's 5d0c1c31-f9d4-4e39-9a63-6b5387230752.

`programs.json` is unchanged from 25b30b35, including the artifact digest
`dac220107c76083786d2e0d08418066865e4c69435075a8e01c62a399ab46ff3`.
The RISC-V images and the scheme are identical; only the certified cycle accounting changes.

| | 25b30b35 (pareto, 8-cycle perm) | this candidate (30-cycle perm) |
|---|---:|---:|
| commit cycles | 499,194,978 | 1,386,291,298 |
| opening cycles (128 positions) | 83,899 | 83,899 |
| prover cycles | 499,278,877 | 1,386,375,197 |
| proof bytes (128 positions) | 76,800 | 76,800 |

The track baseline is 3,959,471,682 prover cycles at 102,400 proof bytes. This candidate dominates it on both axes.

## Cycle accounting

The commit makes 41,371,135 public calls:

* 1,525,248 NonceChain permutations.
* 2 × 2^24 leaf permutations.
* 2^22 quad and 2^20 quad2 permutations.
* 2^20 − 1 projected compressions.

That is 40,322,560 permutation calls, each costing 22 more cycles than before:
499,194,978 + 22 × 40,322,560 = 1,386,291,298. The opening program makes no oracle calls,
so its 83,899-cycle bound is unchanged. The checker's cost is not scored; its fuel bound
uses the generic `≤ 30 · steps` interpreter lemma from the track baseline's `Execution.lean`.

## Proof changes

The only changes are to cycle constants. No program, layout or security argument changed.

* `TwoPermutationSyscall.execute_permutation_call` and `QuadNonceCommitLoop.chain_perm_call` now charge 30 cycles.
* Every block lemma whose oracle calls are permutations gets 22 extra cycles per call:
  * commit leaf, quad and quad2 runs;
  * the NonceChain step (10 → 32 per call) and its 1,525,248-call total;
  * leaf-group and latch totals;
  * the quad and quad2 controls;
  * checker leaf, quad-node and record blocks;
  * the legacy two-permutation commit chain that the certificate still imports.
* Compression charges (parent pass, cap steps, checker lower path) are untouched.
* `QuadCommitImage.step_ledger` now separates the call types:
  `cycles = steps + 29·permutations + 7·compressions + 3`.
* `Execution.lean` is the track baseline's 30-cycle version.

The certificate builds against the contract with `PERMUTATION_CYCLES := 30`, which is what
`verifier/tracks.py` selects for this track. The only axioms are propext, Classical.choice and Quot.sound.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-64-32-pareto
```
