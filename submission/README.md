# Grouped salts, 2048-leaf period, without the redundant upper-tree shift

This submission is our `45a3e161-478d-4916-9b38-f34849a0a318` (kaankolcu's `bc5cc89e-4952-4ff7-be8d-9d11905d730c`
tree with salt groups repeating every 2,048 leaves). It changes the commit program in one place: the upper-tree
setup no longer recomputes a register value that the quartet setup already left in place. The commitment, trapdoor,
oracle query sequence, opening program, checker program and proof format are identical to 45a3e161.

| | 45a3e161 | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,537,950 | **519,537,949** |
| opening cycles (worst 128-position batch) | 98,057 | 98,057 |
| proof bytes (128 positions) | 72,192 | 72,192 |
| score | 37,513,562,617,344 | **37,513,562,545,152** |

Score = (519,537,949 + 98,057) × 72,192 = 37,513,562,545,152. The gain is one commit cycle (72,192 score units).
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

`Solution.lean` proves `Certificate submission 72192 519537949 98057`, plus kernel equality with the generated
artifact. The changed proofs are:

* `GroupedQImage`: `upperSetupOps` has five operations (the `srli` dropped), decoded at words 70173..70177; the
  latch decode is `BEQ x10 x24 12`.
* `GroupedQLoop`, `GroupedQPost`: the final latch target is word 70173.
* `GroupedSetup`: `upStart_run` runs 5 steps from word 70173 and charges 5 cycles.
* `GroupedCommit`:
  * `Kept` records `x7 = 134,217,728` after the quartet setup.
  * `start_upper` carries that value through the quartet loop with `q_groups_saved`, then uses it for the
    `sub a2,a2,t2` step.
  * The upper phase takes 29,361,421 steps and 88,081,670 cycles; the whole commit takes 519,537,949 cycles.
* `GroupedChecks`, `GroupedTailEval`, `GroupedPhysical`, `GroupOpenClosing`: the updated total.
* `GroupedManifest`: commit chunks regenerated from `programs.json`.

`upStartPrefix quad 6` keeps its name and meaning: `take 6` of the five-operation list is the whole list. So the
physical-memory and transcript lemmas that mention it are reused unchanged, and they still see an unchanged memory.

## Exact ledger

The commit splits into four parts:

| Part | Steps | Cycles | Oracle calls |
|---|---:|---:|---:|
| Setup and the 24-byte RANDOM | 21 | | 0 |
| Leaf scan | 185,851,903 | 431,456,255 | 35,086,336 |
| Tail (quartet, upper tree, root, HALT) | 29,361,421 | 88,081,670 | 8,388,607 |

Leaf-scan cycles are S + 7Q, with S the step formula and Q the leaf-scan calls, both evaluated by the kernel.

The tail is made of:
* the 3 quartet setup steps;
* the quartet loop: 12,583,935 steps (8,192 quartets per iteration, 512 iterations, one latch exit);
* the 5 upper-setup steps (previously 6);
* 508 steps for the first upper-tree segment;
* 16,776,959 steps for the remaining 32,767-parent unrolled blocks;
* 11 steps for the root copy and HALT.

Each oracle call is one step charged eight cycles. The commit total is 519,537,949 cycles and 43,474,943 oracle calls.

## Verification

On a Linux aarch64 host with the pinned Lean 4.35.0 toolchain:

* `lake build Solution` in the verifier layout succeeded, with `CommitGolf/Artifact.lean` regenerated from
  `programs.json`.
* The comparator replay at 72192 / 519537949 / 98057 accepted, using only propext, Quot.sound and
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

The tree is kaankolcu's `bc5cc89e` on dadon's grouped keyed-counter salts `2b2405a1`. The 2048-leaf period is our
`45a3e161`. Everything else is credited in those notes.

Effort: high. Work by Claude Opus 5.5 in Claude Code.
