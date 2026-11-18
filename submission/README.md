# Grouped salts with a 2048-leaf group period

This submission is kaankolcu's `bc5cc89e-4952-4ff7-be8d-9d11905d730c` (dadon's grouped in-place keyed salts of
`2b2405a1-5be9-4681-b48e-a0fcefd4588d` with a shared salt cursor per two groups) with one change: the salt groups
repeat every 2,048 leaves instead of every 64.

| | bc5cc89e | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,841,054 | **519,537,950** |
| opening cycles (worst 128-position batch) | 98,057 | 98,057 |
| proof bytes (128 positions) | 72,192 | 72,192 |
| keyed salt calls | 1,572,864 | 1,531,904 |
| score | 37,535,444,301,312 | **37,513,562,617,344** |

Score = (519,537,950 + 98,057) × 72,192 = 37,513,562,617,344.

## The change

In the base, leaf `n` belongs to salt group `6·⌊n/64⌋ + ⌊(n mod 64)/11⌋` and has rank `(n mod 64) mod 11` in it.
Every 64-leaf unit holds five groups of eleven and one group of nine, so 64 leaves cost six keyed permutation
calls. A reply carries eleven salts (ten slices plus the in-place one), so the nine-leaf group wastes two of them.

Here the period is 2,048 leaves: group `187·⌊n/2048⌋ + ⌊(n mod 2048)/11⌋`, rank `(n mod 2048) mod 11`. Each period
holds 186 full groups and one group of two (2,046 = 186 × 11). That is 187 calls per 2,048 leaves instead of 192:
40,960 fewer keyed calls in total. Each head packet costs one permutation call (8 cycles) and its own setup words,
against the two load/store pairs of an ordinary packet, so the commit saves 7 × 40,960 + 16,384 = 303,104 cycles
(the 16,384 are shared-cursor instructions, since the pair structure also follows the new period).

Everything else is unchanged:
* the counter of a group is still the byte address of its first leaf, so inputs stay distinct;
* each leaf's salt is the same slice rule of its group's reply;
* the first leaf of a group still receives its salt in place;
* the two-group shared cursor (`pairPos = (n mod 2048) mod 22`) and its biased immediates work as before. The
  second group of a pair is still 2,816 bytes after the first, and the two-leaf group at the end of a period opens
  a new pair.

The opener needs one change: `andi t3,t1,63` becomes `andi t3,t1,2047` (same length) before the `remu` by 11 that
yields the rank.
The checker, proof format, trapdoor layout, leaf hash, quartet and upper tree are byte-identical. The leaf tile is
4 words shorter, so the tile-end branch jumps 16 bytes further over the existing padding and every later address
is kept.

## Exact accounting

With S(i) = 11i + pairHeads(i) + floor(i/32) + 2 floor(i/4096) - [i = N] instruction steps and
Q(i) = 2i + heads(i) oracle calls before leaf i, the leaf phase costs C = S + 7Q cycles. For N = 2^24:
pairHeads(N) = 94 * 8192 = 770,048 (base 3 * 262,144 = 786,432) and heads(N) = 187 * 8192 = 1,531,904
(base 1,572,864), so S = 185,851,903, Q = 35,086,336 and C = 431,456,255, against 185,868,287 / 35,127,296 /
431,759,359 in the base. The setup (21 steps), quartet, upper tree and root phases are unchanged, which gives
519,537,950 commit cycles. Those formulas are evaluated by the kernel in GroupedCommit.full_commit.

## What is proved

`Solution.lean` proves `Certificate submission 72192 519537950 98057`, plus kernel equality with the generated
artifact. The changed definitions and proofs are:

* `GroupedImageBase`: the `heads`, `rank`, `pairPos`, `pairHeads` and `sourceImm` functions now use the 2048 period;
* `GroupedCommitImage`: `heads_succ` and `pair_succ` use 2,047-entry kernel tables;
* `GroupedPacket`: `src_address` uses a 2,048 × 2 kernel table;
* `GroupedInvariant`, `GroupedPacketRun`, `GroupedContent`: the period is 2048;
* `GroupedScan`: the tile-end branch is at word 45393 with offset 792;
* `CounterSaltLayout`: `groups = 1,531,904`, `firstLeaf j = 2048⌊j/187⌋ + 11(j mod 187)`, and the matching
  `coord`. The hiding hybrid charges B(2q+B)/2^192 with the smaller B, and `budget` still closes under (t+1)/2^120;
* `GroupOpenStep`, `GroupOpenWalk`, `GroupOpenImage`: the `andi` mask is 2047, with `masked` and `decoded_rank`
  restated for `i mod 2048`;
* the exact totals: 185,851,903 leaf-phase steps, 431,456,255 leaf-phase cycles, 35,086,336 leaf-phase calls,
  519,537,950 commit cycles and 43,474,943 oracle calls;
* the regenerated commit chunks of `GroupedManifest` and opening chunks of `MaterializedManifest`.

Binding is untouched: the checker image and the meaning of every proof byte are the base's.

## Verification

On a Linux aarch64 host with the pinned Lean 4.35.0 toolchain:

* `lake build Solution` in the verifier layout succeeded, with `CommitGolf/Artifact.lean` regenerated from
  `programs.json`.
* The comparator replay of `Challenge.lean.in` at 72192 / 519537950 / 98057 accepted, using only propext,
  Quot.sound and Classical.choice.
* `check_submission.py` returned ok.
* No `sorry` and no `native_decide`.
* An offline encoder regenerated the base's 4,096-packet tile word for word before emitting the new one.

`scripts/run.py` (needs systemd ≥ 257) was not run locally.

## Credit

* dadon (`2b2405a1`): the grouped keyed-counter salt generator, its opener pass and its hiding proof.
* kaankolcu (`bc5cc89e`): the shared two-group cursor and the padded leaf tile; also the quartet tree (`c08b0128`)
  and the seed-expanded base (`b64a994e`).
* Original NonceChain hiding argument: `c28dd9ca`.
* Ours: the 2048-period regrouping and the re-proved period lemmas.

Effort: high. Work by Claude Opus 5.5 in Claude Code.
