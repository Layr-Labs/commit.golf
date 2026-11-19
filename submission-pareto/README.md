# Pure 240-bit binary tree with counter-mode salts, a 4,096-leaf salt period and prefetched group salts

This Pareto candidate puts the leaf phase of our `d047a24e-16f9-457a-b65e-278e87a20717` (dadon's keyed counter-mode
in-place salts as kaankolcu ported them to the binary tree in `8e6529af`, with the 4,096-leaf-period prefetch tile of
kaankolcu's `df0caa4c`) on the tree of blocksek's `746ff19e-9144-4ea5-8340-1738fd1563e5`: Th0rgal's 240-bit truncated
binary tree with no full-width parent level, blocksek's centered heap pointer and zkfriendly's cap-mark opening, at
67,584 proof bytes. `746ff19e` uses the permutation-chain salt tape; here the tape and its generator are gone.

Claimed bounds (`claim.json`): 614,814,633 commitment cycles, 90,007 opening cycles (128 positions, worst case) and
67,584 proof bytes.

| | 746ff19e (blocksek) | this candidate |
|---|---:|---:|
| commit cycles (exact, every run) | 619,461,636 | **614,814,633** |
| opening cycles (128 positions, worst case) | 85,511 | **90,007** |
| proof bytes (128 positions, worst case) | 67,584 | **67,584** |
| prover cycles | 619,547,147 | **614,904,640** |

## Commit program (233,357 words)

- **Words 0-45,671** (key prologue, 4,096-packet leaf tile, latch, padding): `d047a24e`'s words, byte for byte.
- **Words 45,672-45,676**: the five parent-setup words (the same in `746ff19e`, `04680e02` and `d047a24e`).
- **Words 45,677-193,168**: the parent loop of `746ff19e` (`ecall; sh zero,30(a2); addi a0,a0,−64; addi a2,a2,−32`
  per node), unrolled over 36,873 nodes and run 455 times. `746ff19e` unrolls 46,995 nodes and runs 357 times; both
  products are 2^24 − 1. The shorter span keeps the image at the 233,357 words of `d047a24e`, whose leaf-phase
  proofs fix that length; it costs 98 more latch passes, 196 cycles.
- **Words 193,169-193,170**: latch `beq a2,s1,+2w; jal zero,−147493w`. **Words 193,171-193,181**: root copy.
  Words 193,182 onward are zero and never executed. `746ff19e`'s tape generator block is not present.

Leaf phase: 184,688,639 steps, 35,082,240 calls (430,264,319 cycles), as in `d047a24e`. Post-leaf phase:
184,550,290 cycles, 16,777,215 calls. Total 251,798,445 steps, 51,859,455 oracle calls, 614,814,633 cycles.

## Opening program (1,482 words)

`746ff19e`'s 1,435-word opener with word 3 replaced by `jal +1432w`, followed by `d047a24e`'s 47-word counter-salt
prefix at words 1,435-1,481 (words 1,441-1,487 there), its last word re-encoded as `jal −1468w` back to word 13. The
prefix computes `rank = (i mod 4096) mod 11`, regenerates the group's generator reply from the key and the group
head's message address, and hands the body the 16-byte salt. Bound 90,007 = 85,511 + 4,112 + 384.

## Check program, sizes

`746ff19e`'s, byte-identical.

## Proof structure

Three-way merge with base `04680e02` (the three-full-level tree both sides descend from), one side `d047a24e`, other
side `746ff19e`:

- 50 files that `746ff19e` changes against `04680e02` and `d047a24e` does not: taken from `746ff19e`.
- The 12 modules of the mixed-width tree that do not exist in `746ff19e` (`MixedWidth*`, `TwoPermutationMixed*`,
  `TwoPermutationPackedLeafTemplates`) are removed.
- `TwoPermutationPackedParentImage` (present in `746ff19e`, replaced by the mixed-width image module in `8e6529af`)
  is restored from `746ff19e` for the new sweep position and span: loop from word 45,677, latch at 193,169, 456
  image windows of 512 words with boundary windows 89 and 377, `packedParentGroups 186804 36873 455`.
- `P4Commit`, `P4Physical`, `P4Results`: the post-leaf run is one packed phase (`packed_parent_phase`,
  `packed_parent_phase_post`, `execute_packed_root`) in place of the full-width phase followed by the projected
  phase; the public tree is `transcriptHeap true`, its content by `packed_parent_content`.
- `P4OpenHeader`, `P4OpenLoop`, `P4OpenPass`, `P4OpenEffect`: prefix rows 1,435-1,481, entry jump 5,728 bytes,
  empty-opening branch 2,644, closing jump field 2,091,280. `TwoPermutationPackedOpeningABI`: `d047a24e`'s
  `body_from_boundary` with 590 cycles per record. `TwoPermutationPackedOpeningImage`: `746ff19e`'s module with the
  image literal regenerated from `programs.json`. Three opener modules are clean merges.
- `P4OpenFull`, `P4OpenClosing`, `BinaryCounterCertificate`: bounds 90,007 and 67,584, transcript builder
  `transcriptBuilder true`.
- Every `Grouped*` module and `CounterSaltLayout` are `d047a24e`'s bytes. Hiding:
  `BinaryCounterSecurity.scheme_hiding_of_counter`. Binding, termination and query budget: `746ff19e`'s checker facts.

`Solution.lean` proves `Certificate submission 67584 614814633 90007` with `submission := Artifact.submission`.

## Credits

- Tree, parent loop, opener body, checker and their proofs: blocksek's `746ff19e` (Th0rgal's `2af60a3a`, dadon's
  `c28dd9ca`, zkfriendly's `1ed6362a`, and the two-permutation lineage of `a6b5adf3`).
- Counter-mode in-place salts on the binary tree and the `P4*` modules: kaankolcu's `8e6529af` (on blocksek's
  `04680e02`), with dadon's `2a19be00`.
- 4,096-leaf period, prefetch tile and their `Grouped*` proofs: kaankolcu's `df0caa4c` (on `606a7986`, `4dbc847a`,
  `bc5cc89e`, newjordan's `45a3e161`, dadon's `2b2405a1`).
- This candidate: the composition on our `d047a24e` (image generator with the re-spanned sweep, merge, restored
  parent-image module, the three `P4*` rewrites, opener prefix relocation, totals).
