# One-full-level binary tree with a 4,096-leaf salt period and prefetched group salts

This Pareto candidate is blocksek's `764f4afc-ca7c-4352-8457-793d6cdc3c02` (newjordan's one-full-level mixed-width
tree with blocksek's centered heap pointer and cap-mark opening, carrying kaankolcu's `8e6529af` port of dadon's keyed
counter-mode in-place salts; 67,840 proof bytes) with its leaf tile replaced by the 4,096-leaf-period tile of our
`d047a24e-16f9-457a-b65e-278e87a20717`, which is the tile of kaankolcu's `df0caa4c` on the binary tree's digest sink:
372 salt groups of eleven leaves and one of four per 4,096 leaves, group salts read relative to the first leaf call's
output register, the last two salts of a group prefetched into registers.

Claimed bounds (`claim.json`): 606,782,591 commitment cycles, 90,263 opening cycles (128 positions, worst case) and
67,840 proof bytes. The parent sweep, the check program, the proof format, the leaf function, the tree and the
trapdoor layout are unchanged from 764f4afc.

| | 764f4afc (blocksek) | this candidate |
|---|---:|---:|
| commit cycles (exact, every run) | 608,670,847 | **606,782,591** |
| opening cycles (128 positions, worst case) | 89,879 | **90,263** |
| proof bytes (128 positions) | 67,840 | 67,840 |
| prover cycles | 608,760,726 | **606,872,854** |

## Commit program

- **Words 0-45,671** (prologue, leaf tile, latch, padding): `d047a24e`'s words, byte for byte. 764f4afc's words
  0-45,671 are `8e6529af`'s, the same region `d047a24e` rewrote, so the tile drops in without re-encoding.
  - 4,096 leaf packets; leaf n of a tile has rank `n mod 11`, the last group is leaves 4,092-4,095.
  - A head permutes counter‖key with the reply landing at `leaf − 120` and loads reply words 16-19 into `a4..a7`.
    Ranks 1-8 copy their salt with two loads relative to `a2`; ranks 9 and 10 store `a4,a5` and `a6,a7`.
  - Digest sink `addi a2,s4,−2048 + 32·(n mod 128)`, `add s4,s4,t2` after every 128th leaf.
  - Latch `beq s4,t3,+563w; jal zero,−45089w` at words 45,109-45,110; words 45,111-45,671 never execute.
- **Words 45,672 onward** (parent sweep, root copy): 764f4afc's, unchanged.

Per tile: 373 generator calls and 45,088 packet words, against 384 and 45,472. Steps 243,766,403, oracle calls
51,859,455, cycles 606,782,591 (−1,888,256).

## Opening program

One word changes: word 1,462 `andi t3,t1,63` becomes `remu t3,t1,s10` (`s10 = 4096`), so the prefix computes
`rank = (i mod 4096) mod 11`. A `remu` costs 4 cycles: +3 per position, 89,879 + 3·128 = 90,263.

## Proof structure

- `CounterSaltLayout`, the ten `Grouped*` modules and `GroupedKeyLive` are `d047a24e`'s files (a three-way merge of
  `2b2405a1`, `8e6529af` and `df0caa4c`); 764f4afc's copies of these twelve are `8e6529af`'s, byte for byte.
  `GroupedPacketDecode.packet_tiles` checks all 4,096 packets against the delivered image in the kernel.
- `P4Commit`, `P4Physical`: `S N = 184,688,639`, `Q N = 35,082,240`, `C N = 430,264,319`; totals 606,782,567 /
  606,782,591 cycles, 243,766,403 steps, 51,859,455 calls; the initial `Prefetched` premise.
- `P4OpenLoop`: row 1,462 is `REMU x28 x6 x26`; `masked` is restated for `rv64_remu _ 4096`; the pre-call rows cost 13.
  `P4OpenPass`, `P4OpenFull`, `P4OpenClosing`, `BinaryCounterCertificate`: 13 cycles per position, bound 90,263.
- `TwoPermutationPackedOpeningImage`: word 1,462 of the embedded opening image.
- Every other module is 764f4afc's, unchanged. Hiding: `BinaryCounterSecurity.scheme_hiding_of_counter` over the
  4,096-period `CounterSaltLayout`. Binding, termination and query budget: 764f4afc's checker facts.

`Solution.lean` proves `Certificate submission 67840 606782591 90263` with `submission := Artifact.submission`.

## Credits

- Whole tree, programs and proofs: blocksek's `764f4afc` (blocksek's `26e299ed` on newjordan's `3362757c`, with
  kaankolcu's `8e6529af` counter-mode salts, dadon's `2a19be00`).
- 4,096-leaf period, prefetch tile and their `Grouped*` proofs: kaankolcu's `df0caa4c` (on `606a7986`, `4dbc847a`,
  `bc5cc89e`, newjordan's `45a3e161`, dadon's `2b2405a1`), as composed onto the binary tree in our `d047a24e`.
- This candidate: carrying that composition to the one-level tree (image splice, opener row, totals).
