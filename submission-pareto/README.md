# Three-full-level binary tree with a 4,096-leaf salt period and prefetched group salts

This Pareto candidate is kaankolcu's `8e6529af-51e2-4d13-bd42-31b674a0ed3d` (blocksek's `04680e02` binary mixed-width
tree with three full-width parent levels, centered heap pointer and cap-mark opening, with dadon's keyed counter-mode
in-place salts of `2a19be00`; 68,352 proof bytes) with its leaf tile replaced by the 4,096-leaf-period tile of
kaankolcu's `df0caa4c-f611-49a4-b148-9c3f1f994bb0`: 372 salt groups of eleven leaves and one of four per 4,096 leaves,
group salts read relative to the first leaf call's output register, the last two salts of a group prefetched into
registers.

Claimed bounds (`claim.json`): 600,134,811 commitment cycles, 90,775 opening cycles (128 positions, worst case) and
68,352 proof bytes. The check program, the proof format, the leaf function, the tree and the trapdoor layout are
unchanged from 8e6529af.

| | 8e6529af | this candidate |
|---|---:|---:|
| commit cycles (exact, every run) | 602,023,067 | **600,134,811** |
| opening cycles (128 positions, worst case) | 90,391 | **90,775** |
| proof bytes (128 positions) | 68,352 | 68,352 |
| prover cycles | 602,113,458 | **600,225,586** |

## Commit program

- **Prologue (words 0-20)**: unchanged (24-byte key drawn into the key block at trapdoor offset 80·2^24 + 8).
- **Leaf tile (words 21-45,108)**: 4,096 leaf packets. Leaf n of a tile has rank `n mod 11`; rank 0 is a head, except
  that the last group of a tile is leaves 4,092-4,095.
  - A head writes its message address into the counter word, permutes counter‖key with the reply landing at
    `leaf − 120` (its last 16 bytes are the head's own salt slot), and, unless it is leaf 4,092, loads reply words
    16-19 into `a4..a7`.
  - Ranks 1-8 copy their 16-byte salt with two loads at `−(104 + 240·rank)` and `+8` from `a2` (which holds
    `leaf − 32` after the leaf's first call).
  - Ranks 9 and 10 store `a4,a5` and `a6,a7`.
  - Every leaf then makes 8e6529af's second call, writing the digest through the centered heap pointer `s4` at
    `−2048 + 32·(n mod 128)`; `add s4,s4,t2` follows every 128th leaf.
- **Latch (words 45,109-45,110)**: `beq s4,t3,+563w; jal zero,−45089w`. Words 45,111-45,671 are never-executed `nop`s,
  so the parent sweep and root copy (words 45,672 onward) keep 8e6529af's addresses and bytes.

Per tile: 45,088 packet words and 373 generator calls, against 45,472 and 384. Steps 237,118,623, oracle calls
51,859,455, cycles 600,134,811 (−1,888,256).

## Opening program

One word changes: word 1,466 `andi t3,t1,63` becomes `remu t3,t1,s10` (`s10 = 4096`), so the prefix computes
`rank = (i mod 4096) mod 11`. A `remu` costs 4 cycles: +3 per position, 90,391 + 3·128 = 90,775.

## Proof structure

- The eleven `Grouped*`/`CounterSaltLayout` modules shared with 2b2405a1 are a three-way merge (base 2b2405a1, 8e6529af,
  df0caa4c): df0caa4c's period, `cacheCredit`/`bodyLen` accounting, `Prefetched` register invariant and a2-relative
  `src_address` table, in 8e6529af's vocabulary (`leafDest`, `keyWord`, stride register `x7`, stop register `x28`),
  with `slotOff n = 32·n` (so `rb n = n/128`, 32 rebases per tile).
  - `GroupedPacketDecode.packet_tiles` checks all 4,096 packets against the delivered image in the kernel.
  - `GroupedScan`: latch at word 45,109 (`BEQ x20 x28 2252`, `JAL x0 −180356`).
  - `GroupedInvariant.fixed_packet_good` carries `Good` and `Prefetched`; `CounterSaltLayout` has
    `groups = 1,527,808`, `firstLeaf j = 4096⌊j/373⌋ + 11(j mod 373)`.
- `P4Commit`, `P4Physical`: `S N = 184,688,639`, `Q N = 35,082,240`, `C N = 430,264,319`; total 237,118,623 steps.
- `P4OpenLoop`: row 1,466 is `REMU x28 x6 x26`; `masked` is restated for `rv64_remu _ 4096`; the pre-call rows cost 13.
  `P4OpenPass`, `P4OpenFull`: 13 cycles per position on top of the row steps; bound 90,775.
- `TwoPermutationPackedOpeningImage`: word 1,466 of the embedded opening image.
- Hiding: `BinaryCounterSecurity.scheme_hiding_of_counter` over the 4,096-period `CounterSaltLayout`
  (df0caa4c's layout; fewer generator calls than the 64-period one). Binding, termination and query budget:
  8e6529af's unchanged checker facts.

## Credits

- Whole tree, programs and proofs: kaankolcu's `8e6529af`, which is blocksek's `04680e02` (on newjordan's
  `cdb98559`, Th0rgal's `ddb6bf80`, blocksek's `746ff19e`, and the two-permutation lineage of `a6b5adf3`) with dadon's
  `2a19be00` counter-mode salts.
- 4,096-leaf period, prefetch tile and their `Grouped*` proofs: kaankolcu's `df0caa4c` (on `606a7986`, `4dbc847a`,
  `bc5cc89e`, newjordan's `45a3e161`, dadon's `2b2405a1`).
- This candidate: the composition of the two (image generator, three-way merge of the proofs, opener row).
