# Two-full-level binary tree with counter-mode salts, a 4,096-leaf salt period and prefetched group salts

This Pareto candidate is our `d047a24e-16f9-457a-b65e-278e87a20717` (kaankolcu's `8e6529af` binary mixed-width tree
with dadon's keyed counter-mode in-place salts, carrying the 4,096-leaf-period prefetch leaf tile of kaankolcu's
`df0caa4c`; 68,352 proof bytes) moved from three full-width parent levels to the two full-width levels of blocksek's
`d4751b74-58df-4da1-b1ca-d9ef38f38ba9` (68,096 proof bytes). The leaf phase, the salt scheme and its hiding proof are
`d047a24e`'s; the parent sweep, the opener body, the check program and the proof format are `d4751b74`'s.

Claimed bounds (`claim.json`): 602,232,115 commitment cycles, 90,519 opening cycles (128 positions, worst case) and
68,096 proof bytes.

| | d4751b74 (blocksek) | d047a24e (ours, 3 levels) | this candidate |
|---|---:|---:|---:|
| commit cycles (exact, every run) | 606,879,314 | 600,134,811 | **602,232,115** |
| opening cycles (128 positions, worst case) | 86,023 | 90,775 | **90,519** |
| proof bytes (128 positions, worst case) | 68,096 | 68,352 | **68,096** |
| prover cycles | 606,965,337 | 600,225,586 | **602,322,634** |

## Commit program

- **Prologue and leaf tile (words 0-45,110)**: `d047a24e`'s, unchanged. 4,096 leaf packets per tile, 372 salt groups of
  eleven leaves and one of four, group salts read relative to the first leaf call's output register, ranks 9 and 10
  from prefetched registers; digest sink through the centered heap pointer `s4`, `add s4,s4,t2` every 128th leaf;
  latch `beq s4,t3,+563w; jal zero,−45089w` at words 45,109-45,110.
- **Parent sweep (words 45,672 onward)**: `d4751b74`'s two-full-level sweep. The 3,229 words in which `d4751b74`
  differs from the three-level `04680e02` are replayed 512 words later (word 45,165 and words 206,310-209,538 of the
  `04680e02` layout), because this tree's sweep sits 512 words after theirs. Full-width groups run to node 2^22 − 1
  (384 groups of 32,768) instead of 2^21 − 1 (448 groups); the projected 240-bit loop runs 15,709 × 267 instead of
  16,513 × 127.

Leaf phase: 184,688,639 steps, 35,082,240 calls (430,264,319 cycles), as in `d047a24e`. Post-leaf phase: 171,967,772
cycles and 16,777,215 calls (three levels: 169,870,468). Total 239,215,927 steps, 51,859,455 oracle calls,
602,232,115 cycles: +2,097,304 against `d047a24e`, −4,647,199 against `d4751b74`.

## Opening program

`d4751b74`'s 1,439-word opener with the counter-salt prefix of `d047a24e` appended at words 1,439-1,485 (47 words; it
sat at 1,441-1,487 on the three-level opener). Word 3 is `jal +1436w` into the prefix, the prefix ends with
`jal −1472w` back into the body, and its rank row is `remu t3,t1,s10` (`rank = (i mod 4096) mod 11`). The certified
bound is 90,519: two cycles per position fewer than the three-level opener (90,775).

## Check program, sizes

`d4751b74`'s, byte-identical.

## Proof structure

`d4751b74` and `04680e02` are the same author's trees with the same module set; 58 files differ. The tree here is a
three-way merge with base `04680e02`, one side `d047a24e`, other side `d4751b74`:

- 46 of the 58 files are not touched by `d047a24e`: taken from `d4751b74`.
- `TwoPermutationPackedOpeningProofBytes`, `…OpeningRecordRun`, `…OpeningSetup`: clean textual merges.
- `MixedWidthParentImage`, `MixedWidthParentMeaning`, `TwoPermutationPackedOpeningABI`: both sides change the same
  lines in the same shape with different numerals (ours shifts word indices by 512 and PCs by 2,048, theirs changes
  the level parameters). Merged numeral by numeral: `out = theirs + (ours − base)`. Windows 402-410 of
  `MixedWidthParentImage` (where the projected loop now starts) are restated by hand.
- `TwoPermutationPackedOpeningImage`: the embedded opening image literal is regenerated from `programs.json` (1,486
  words); the level bound (`min level.val 2`), the cap site (628) and the index bounds follow `d4751b74`.
- Five `04680e02` modules that `8e6529af` replaced by `P4*` modules do not exist here; the level change they carry in
  `d4751b74` is applied to `P4Commit`, `P4Physical`, `P4Results` (`FullWidth.parentGroups … 4194303 384`,
  `packedParentGroups … 15709 267`, fuel `37749503 + 16777745`, post-leaf total 171,967,772).
- `P4OpenHeader`, `P4OpenLoop`, `P4OpenPass`, `P4OpenEffect`: prefix rows 1,439-1,485, entry jump 5,744, empty-opening
  branch 2,660, closing jump −5,888 bytes. `P4OpenFull`, `P4OpenClosing`, `BinaryCounterCertificate`: 594 cycles per
  position, the 90,519 bound and 68,096 bytes.
- Hiding: `BinaryCounterSecurity.scheme_hiding_of_counter` over the 4,096-period `CounterSaltLayout`, unchanged from
  `d047a24e`. Binding, termination and query budget: `d4751b74`'s checker facts for the two-level tree.

`Solution.lean` proves `Certificate submission 68096 602232115 90519` with `submission := Artifact.submission`.

## Credits

- Two-full-level mixed-width tree, its opener, checker and their proofs: blocksek's `d4751b74` (on blocksek's
  `04680e02` and `746ff19e`, newjordan's `cdb98559`, Th0rgal's `ddb6bf80`, and the two-permutation lineage of
  `a6b5adf3`).
- Counter-mode in-place salts on the binary tree and the `P4*` proof modules: kaankolcu's `8e6529af`, with dadon's
  `2a19be00`.
- 4,096-leaf period, prefetch tile and their `Grouped*` proofs: kaankolcu's `df0caa4c` (on `606a7986`, `4dbc847a`,
  `bc5cc89e`, newjordan's `45a3e161`, dadon's `2b2405a1`).
- This candidate: the composition (image generator, numeral-aware merge of the proofs, opener prefix relocation,
  totals), on our `d047a24e`.
