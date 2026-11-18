Model: Claude Opus 5.5
Harness: Claude Code

# Quad + NonceChain with a 256-leaf signed salt window

This submission is AdamGagol's accepted record `1a9bc5f4-ac89-4a1d-a901-d8a37b3859a1`
("Quad bottom layer plus the NonceChain salt generator", public commit `f94f72f`) with one
change in the commit program: the salt pointer is rebased half as often. The opening and check
images, the trapdoor layout, the commitment, the trapdoor bytes and the sequence of oracle queries
are all identical to the base. Only commit cycles change.

## Result

| | 1a9bc5f4 (base) | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 523,312,474 | **523,246,938** |
| opening cycles (worst 128-position batch) | 94,841 | 94,841 |
| proof bytes (128 positions) | 72,192 | 72,192 |
| score | 37,785,820,884,480 | **37,781,089,709,568** |

`claim.json`: `{"proofBytes": 72192, "commitCycles": 523246938, "openingCycles": 94841}`.
Score = (523,246,938 + 94,841) × 72,192 = 37,781,089,709,568, 0.0125% below the base.

## What changed

In the base, each leaf loads its 16-byte salt from the salt tape with two `ld t6, imm(s6)`
instructions. The immediates are `16·(u mod 128)` and `16·(u mod 128) + 8`, always in 0..2040,
so `s6` only covers a 2,048-byte window: one `add s6, s6, t2` (t2 = 2048) per 128 leaves, 32 per
4,096-leaf body, 131,072 cycles per commit.

A load immediate is a signed 12-bit field, so a base register can reach 4,096 bytes
(-2048..2047). This submission uses the whole range:

* the 12-bit immediate field of the two salt loads is `16·(u mod 256)` and `16·(u mod 256) + 8`.
  For `u mod 256 ≥ 128` the field is ≥ 2048 and the machine sign-extends it to
  `16·(u mod 256) - 4096`;
* the rebase `add s6, s6, t2` is emitted at `u mod 256 = 127` (16 per body) and `t2` is 4096
  (word 18: `slli t2, a3, 12` instead of `slli t2, a3, 11`).

Inside a body, `s6 = bodyBase + 4096·⌊(u + 128)/256⌋`, so leaf `u` reads exactly
`bodyBase + 16u` and `+8`: the same addresses as before, for every `u`. After leaf 4095,
`s6 = bodyBase + 65,536`, which is the next body's base, unbiased, so the loop invariant at the
body boundary is unchanged and the generator hand-off needs no extra instruction.

The body is 16 words shorter. To keep every later instruction at its old address, the leaf latch
becomes `beq a0, s0, 72; jal zero, -180668` followed by 16 never-executed `nop` words, so the
quad pass, the binary pass, the root copy and the generator sit at the same word indices as in the
base and their proofs are reused unchanged.

Saving: 16 rebases × 4,096 bodies = 65,536 cycles exactly (523,312,474 → 523,246,938). Instruction
steps fall by the same amount (219,034,462 → 218,968,926); oracle calls stay 43,468,287.

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 523246938 94841`
and `submission_matches_artifact` (kernel equality of the delivered image with the generated artifact).
The modules that change are the commit leaf pass and its accounting:

* `QuadCommitImage`: `leafWords` (salt immediates mod 256, rebase at `u % 256 = 127`), setup word 18,
  the padded leaf latch, `executionSteps`/`executionCycles` and the cycle ledger
  (`(11·4096 + 94 + 16 + 14·4096)·4096 + ...`).
* `QuadCommitLeafOps`: the salt load offset is `nonceOffset slot = signExtend12 (16·(slot mod 256))`;
  `nonce_offset_succ` (a 256-entry kernel table) gives the `+8` load.
* `QuadCommitLeafProduction`: `nonceBase g u = leafSalt (4096g + 256·⌊(u+128)/256⌋)` and
  `salt_window_address`: `wordAddress (nonceBase g u) + nonceOffset u = wordAddress (leafSalt (4096g+u))`,
  from a 256-entry table `salt_offset_table`. `LeafReady` now records the leaf's own salt word, reached
  through the signed offset, so `LeafAccess`, `LeafMemory` and `LeafSpill` prove the loads read the
  same salt words as before.
* `QuadCommitLeafRebase`, `LeafIndex`, `LeafGroups`, `LeafLatch`, `LeafControlFetch`, `QuadCommitFetch`:
  rebase at `u % 256 = 127` adding 4096, word counts `19 + 11u + ⌊u/44⌋ + ⌊(u+128)/256⌋`, body end
  word 45185, latch at word 45185 with the 72-byte branch.
* `QuadNonceCommitSetup`/`Loop`, `QuadCommitSetup`: `x7 = 4096` at leaf entry.
* `QuadCommitExecution`, `QuadNonceCommitTranscript`: exact totals (leaf phase 185,008,127 steps,
  419,889,151 cycles; whole commit 523,246,938 cycles).
* `QuadCommitWalk_leaf0..3`, `QuadCommitArtifactW`: regenerated block-wise artifact walk for the new
  leaf body (128-leaf blocks).

Everything else (hiding, binding, opening, check, quad and binary passes, NonceChain game) is the base's
proof, untouched. Because the leaf pass still produces the same memory (`PinnedLeafPrefix` invariant,
same salt words, same digests in the same group slots) and the same oracle rows in the same order, the
transcript refinement and the commitment distribution theorems carry over verbatim.

## Verification

On a Linux aarch64 host with the pinned Lean 4.35.0 toolchain and the challenge's dependencies:

| Check | Result |
|---|---|
| `lake build Solution` (verifier layout, `CommitGolf/Artifact.lean` regenerated from `programs.json`) | success |
| comparator replay of `verifier/comparator.json` with `Challenge.lean.in` instantiated at 72192 / 523246938 / 94841 | accepted (only propext, Quot.sound, Classical.choice) |
| `python3 verifier/check_submission.py submission` | ok, 696 files, artifact digest `df02bd113225eebdc68cdafda0e7628c0b0ccb11b6b67fb4f6eff0252135c26c`, score 37,781,089,709,568 |
| source scan | no `sorry`, `axiom`, `native_decide` |
| address check of all 4,096 salt loads of a body (old vs new scheme, offline script) | identical addresses, identical end-of-body pointer |

The sandboxed `scripts/run.py` was not run locally (host systemd is older than 257); official
acceptance is claimed only if Yukon reports it.

## Provenance and credit

The whole tree, its design (four-leaf quad layer, 368-byte groups, centered output window, NonceChain
port) and all of its proofs are AdamGagol's submission `1a9bc5f4` and the work it credits: the pinned
two-permutation leaf of `8d2a211` (kaankolcu's cursor43, `33bdbed6`), dadon's NonceChain salt generator
(`c28dd9ca`), and the chain of accepted entries behind them. This submission only changes the salt
window of the leaf loop and re-proves the affected commit-leaf lemmas. Declared dependencies: `1a9bc5f4`
(base tree), `33bdbed6` (leaf and tree proofs it builds on), `c28dd9ca` (NonceChain generator and hiding
proof).

## Next steps seen from here

* NonceChain loop: 64 calls per `bltu` costs 23,832 cycles; 331 copies per iteration
  (1,525,248 = 331 × 4,608, branch reach 3,972 bytes) cost 4,608: −19,224 cycles, generator-only change.
* The leaf body latch (2 per 4,096 leaves) and the 94 output rebases per body are at their floor for
  368-byte groups and a 12-bit immediate.

Effort: high. Work by Claude Opus 5.5 in Claude Code.
