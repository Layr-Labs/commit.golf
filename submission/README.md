# 512-leaf blocks for the two-permutation leaf phase

**Claim:** `proofBytes = 72704`, `commitCycles = 688456169`, `openingCycles = 92441`.
Product `(688456169 + 92441) * 72704 = 50,060,238,141,440`. This is **196,604 fewer commitment
cycles** than the two-permutation stack it builds on (`4836e7c0`, 688,652,773 / 92,441,
product 50,074,532,038,656; −0.0285%). Pareto point: [688,548,610 prover cycles, 72,704 bytes].
The opening and checking programs, the proof format and every security argument are unchanged.

## What this builds on

* **Base tree:** kaankolcu's `4836e7c0-8676-4244-b647-5eae7e884027`. It combines kshitij-hash's
  two-permutation leaf commitment and checker (`24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`) with
  kaankolcu's fixed-offset opener and fixed nonce copy (`13891b40-3297-43a7-b8c3-ab241605d25e`).
  It descends from spariev's packed cap multiproof `c283c35a-98fc-4898-a64d-f586abfcee44` (a
  restore of the `243b0d14` record lineage) and from the grouped leaf loop of `bb74fbfa`.
  The leaf function, the stage-3 reference model (`s3Leaves`, `s3Groups`), all memory and
  security proofs, the parent schedule, the nonce repair and the opener/checker are theirs.
* **Ours:** the physical 512-leaf block layout and its proof modules: `UnrollShift.lean`
  (a generic pointer-displacement simulation, written earlier for a compression-tree variant),
  `S4Image`, `S4Exec`, `S4Loop`, `S4Block`, `S4Leaves`. Also the rewiring of `S3TreeExec`,
  `CommitRuntime` and `Commit` (entry jump), and the extended image words. Finally, a cheaper
  appended-code check in `CapPackedImageEquality`: one kernel list comparison per 512-word chunk,
  where the earlier proof did per-element `fin_cases`. Its peak elaboration memory fell from
  about 20 GB to 4 GB.

## Mechanism

The base leaf phase runs 2^18 groups of 64 leaves. Each leaf costs 28 cycles: twelve ordinary
instructions plus two permutation calls. Every group ends with a three-instruction latch
(`ADDI x18,1536; ADD x23,x23,x7; BLTU`), so the overhead is 3 cycles per 64 leaves.

Word 54 now jumps to a new block appended after the base code (pc 1015200). The block opens with
a copy of the five stage-3 entry instructions and two bias instructions (`ADDI x18,1536;
ADD x23,x23,x7`). Then come four identical 128-leaf windows. Each window holds two 64-leaf
halves; leaf `u` of half `h` is the base leaf with immediates `24u+1536h−1536` (nonce loads)
and `32u+2048h−2048` (heap slot). Every immediate fits in 12 bits because the live x18/x23 are
biased into the middle of the window. Four rebase instructions follow each window:
`ADDI x18,1536` twice and `ADD x23,x23,x7` twice. The block ends with

```
BGEU x23,x22,+8 ; JAL x0,block ; ADDI x18,-1536 ; ADDI x23,-2048 ; JAL x0,repair
```

The biased x23 can be compared directly with the heap end because blocks are 16 KiB granular.
The exit path removes the bias and jumps to the retained nonce-repair and exit code, so the state
there is exactly the reference state.

Each block of 512 leaves costs 14,336 cycles for the leaves, 16 for the rebases and 2 for the
branch and jump; that is 18 overhead cycles against 24 for eight 64-leaf latches. Over 2^15
blocks the leaf phase drops from `1795·2^18+50` to `14354·2^15+54` cycles. The image grows to
1,039,888 bytes (< 2^20).

## Proof structure

* The base group code (64 leaves at pc 1011424) stays in the image as the reference window. In
  `S4Exec`, `unroll_shift_execute` (from `UnrollShift`) shows that running a physical half on the
  displaced state equals mapping the displacement over the reference group's exact-step run. That
  run comes from `s3_group_leaves_execute` via `execute_add`. Each related instruction pair (zero
  stores, nonce loads/stores, x10/x12 setup, heap ADDI, ECALL) commutes with the displacement,
  for every fault, reply and private-coin branch.
* `S4Loop`: the reference latch only changes the displacement of the physical frame
  (`s4_frame_latch`). The rebase run shifts it back, and one window is two reference groups.
* `S4Block`: four windows, then the block-end dispatch. The branch is decided from the reference
  heap pointer, and the exit path returns the exact reference state at the repair pc.
  `S4Leaves`: all blocks by induction, then the entry, then the retained repair
  (`s3_finish_execute`). The result is `s3Leaves state 2^18`, the same distribution the base
  proves everything else about.
* `S3TreeExec`/`CommitRuntime` keep the base support facts (from `s3_leaves_execute`) and swap
  only the execution equation and the cycle constants.

## Verification performed

* Regenerated `CommitGolf/Artifact.lean` from this `programs.json` with
  `scripts/generate_artifact.py --refresh` (manifest SHA-256
  `6b9b96c1606ea6cb106365c6d310b6fbcbfb6d9e21ef00498a57f571dfcb690d`), then ran
  `lake build Solution` (Lean 4.35.0).
* Comparator replay with the pinned comparator/lean4export tools and `verifier/comparator.json`,
  with `CommitGolf/Challenge.lean` filled from `claim.json`. The kernel accepts the solution.
* `scripts/run.py` was not run: its sandbox needs systemd ≥ 257 and the development host has 255.
  The manual pipeline follows the same steps.

## Limitations and next steps

* The gain is only the latch overhead (6 of 24 cycles per 512 leaves). Holding x7 = 4096
  physically would save one more instruction per rebase (about 131K cycles), but the frame would
  then have to cover x7.
* Per-leaf work in the two-permutation leaf looks tight. The bigger levers are proof bytes:
  narrower internal digests, or shorter nonces under the 120-bit hiding bound.
