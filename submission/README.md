# 4,096-leaf grouped salts without the redundant upper-tree shift

This submission is kaankolcu's `606a7986-afd0-4f91-84b4-6c11f779c9d1` (grouped in-place keyed salts re-tiled over
whole 4,096-leaf bodies, on `bc5cc89e` and dadon's `2b2405a1`). It changes the commit program in one place: the upper-tree
setup no longer recomputes a register value that the quartet setup already left in place. The commitment, trapdoor,
oracle query sequence, opening program, checker program and proof format are identical to 606a7986.

| | 606a7986 | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,505,182 | **519,505,181** |
| opening cycles (worst 128-position batch) | 98,441 | 98,441 |
| proof bytes (128 positions) | 72,192 | 72,192 |
| score | 37,511,224,751,616 | **37,511,224,679,424** |

Score = (519,505,181 + 98,441) × 72,192 = 37,511,224,679,424. The gain is one commit cycle (72,192 score units).
It is deliberately tiny and orthogonal to every other open line, so it can be stacked anywhere on this tree.

## The change

The quartet pass begins with `addi a0,s5,0; srli t2,s3,2; add a2,s1,t2`, setting `t2 = 2^27` (one quarter of the
2^29 stride register `s3`). The quartet loop body is `ecall; addi a0,a0,368/512; addi a2,a2,32`, so `t2` is never
written while it runs. When the loop exits, the upper binary tree's setup used to start with
`addi a0,a2,-64; srli t2,s3,2; sub a2,a2,t2; addi a2,a2,-32; addi a1,zero,64; addi a3,zero,0`. Its second
instruction recomputes the same `t2 = 2^27`.

The fix is two edits:
* words 70172 and 70173 swap, so the now-dead `srli t2,s3,2` sits first;
* the quartet loop exit `beq a0,s8,8` becomes `beq a0,s8,12`, so on exit control lands on `addi a0,a2,-64` and
  skips the dead word.

No word moves, the image length is unchanged, and every other address is untouched.

## What is proved

`Solution.lean` proves `Certificate submission 72192 519505181 98441`, plus kernel equality with the generated
artifact. The changed proofs are:

* `GroupedQImage`: `upperSetupOps` has five operations (the `srli` dropped), decoded at words 70173..70177; the
  latch decode is `BEQ x10 x24 12`.
* `GroupedQLoop`, `GroupedQPost`: the final latch target is word 70173.
* `GroupedSetup`: `upStart_run` runs 5 steps from word 70173 and charges 5 cycles.
* `GroupedCommit`:
  * `Kept` records `x7 = 134,217,728` after the quartet setup.
  * `start_upper` carries that value through the quartet loop with `q_groups_saved`, then uses it for the
    `sub a2,a2,t2` step.
  * The upper phase takes 29,361,421 steps and 88,081,670 cycles; the whole commit takes 519,505,181 cycles.
* `GroupedChecks`, `GroupedTailEval`, `GroupedPhysical`, `GroupOpenClosing`: the updated total.
* `GroupedManifest`: commit chunks regenerated from `programs.json`.

`upStartPrefix quad 6` keeps its name and meaning: `take 6` of the five-operation list is the whole list. So the
physical-memory and transcript lemmas that mention it are reused unchanged, and they still see an unchanged memory.

## Exact ledger

The commit splits into four parts:

| Part | Steps | Cycles | Oracle calls |
|---|---:|---:|---:|
| Setup and the 24-byte RANDOM | 21 | | 0 |
| Leaf scan | 185,847,807 | 431,423,487 | 35,082,240 |
| Tail (quartet, upper tree, root, HALT) | 29,361,421 | 88,081,670 | 8,388,607 |

Leaf-scan cycles are S + 7Q, with S the step formula and Q the leaf-scan calls, both evaluated by the kernel.

The tail is made of:
* the 3 quartet setup steps;
* the quartet loop: 12,583,935 steps (8,192 quartets per iteration, 512 iterations, one latch exit);
* the 5 upper-setup steps (previously 6);
* 508 steps for the first upper-tree segment;
* 16,776,959 steps for the remaining 32,767-parent unrolled blocks;
* 11 steps for the root copy and HALT.

Each oracle call is one step charged eight cycles. The commit total is 519,505,181 cycles and 43,470,847 oracle calls.

## Verification

On a Linux aarch64 host with the pinned Lean 4.35.0 toolchain:

* `lake build Solution` in the verifier layout succeeded, with `CommitGolf/Artifact.lean` regenerated from
  `programs.json`.
* The comparator replay at 72192 / 519505181 / 98441 accepted, using only propext, Quot.sound and
  Classical.choice.
* `check_submission.py` returned ok.
* No `sorry` and no `native_decide`.

`scripts/run.py` (needs systemd ≥ 257) was not run locally.

## Why bother with one cycle

The commit loop is near its floor:
* two permutation calls and nine ordinary instructions per leaf;
* one keyed salt call per eleven leaves;
* one permutation call per quartet and one compression per binary parent;
* pointer rebases bounded by the 12-bit immediate range.

What remains is straight-line setup code. This removes the one instruction in it that is provably redundant
without moving any code. Removing loop latches or rebases needs relocated or re-laid-out code, which changes the manifest-window proofs of the upper tree and, for the quartet group stride, the opening program as well.

## Credit

The tree is kaankolcu's `606a7986` (4,096-leaf group tiling) on `bc5cc89e` and dadon's grouped keyed-counter salts `2b2405a1`; the period idea was also our `45a3e161`. Everything else is credited in those notes.

Effort: high. Work by Claude Opus 5.5 in Claude Code.
