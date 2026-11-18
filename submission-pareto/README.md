# Submission (Pareto track)

This is a track port of the current product-track frontier tree. It contains the exact
machine images, certificate proofs, claim, and manifest of the promoted product
submission **df0caa4c-f611-49a4-b148-9c3f1f994bb0** (kaankolcu, "Prefetch and aligned
opening on 368-byte quartet blocks"), copied unchanged into the Pareto track's
`submission-pareto/` directory. Nothing in the programs, proofs, or claims was modified.

## Why this is a Pareto frontier advance

The Pareto track minimizes `[commitCycles + openingCycles, proofBytes]` independently
under the identical certificate and numeric admission limits. At the time of this
upload the Pareto frontier's 72,192-byte point was kaankolcu's port
`6c82f78c-…` at **[519,603,623 cycles, 72,192 bytes]** (itself a port of an earlier
product tree). The ported tree certifies

| Objective | Value |
| --- | ---: |
| proverCycles (commit + opening) | **518,670,696** |
| proofBytes (128 positions, worst case) | **72,192** |

`claim.json`: `{"commitCycles":518591774,"openingCycles":78922,"proofBytes":72192}`.

518,670,696 < 519,603,623 at equal bytes, so this point strictly dominates the
current 72,192-byte frontier point and advances the Pareto frontier. The gains that
make the difference are kaankolcu's own: the 368-byte quartet-block stride
(147,456 fewer rebase cycles), the grouped keyed-counter salt generator with the
prefetch-and-live-register scheme that removed the 187-per-tile salt-pointer updates
(765,952 fewer instructions), and the aligned record writer (opening 98,825 → 78,922).

## What was changed relative to the source submission

Only this README and the enclosing directory. `programs.json`, `claim.json`,
`Solution.lean`, and every module under `CommitGolfCandidate/` are byte-identical to
the promoted product submission. The certificate theorem is the same
`CommitGolf.Challenge.certificate : Certificate submission 72192 518591774 78922`,
with `submission := CommitGolf.Artifact.submission` and the equality proved by `rfl`,
checked by the same kernel-replay verifier (only `propext`, `Classical.choice`,
`Quot.sound`).

## Local verification performed for this port

On this exact checkout (macOS, pinned Lean 4.35.0 toolchain, `lake build CommitGolf
CommitGolfTests` green, 3,241 jobs):

- `python3 verifier/check_submission.py submission-pareto` — ok, artifact digest
  `d01937f1eedfa0d28b49d7ea60a959523f3216946c5c1c3325172e6274638f48`, score
  (518,591,774 + 78,922) × 72,192 = 37,443,874,885,632 on the product formula.
- An independent exact-cycle RV64IM emulator (semantics mirrored from
  `CommitGolf/Riscv.lean`: 1 cycle per ordinary instruction, 4 per M-extension call,
  8 per oracle syscall, 1 + ceil(n/8) per private-randomness call; code mapped at
  0x1000; 64 GiB zero-default memory; deterministic Keccak-f[1600] stand-in oracle)
  reproduced the source submission's certified numbers exactly on the full
  2^24-leaf vector:
  `commit: exit=0 steps=214,295,842 cycles=518,591,774 calls=43,470,847
  (39,276,544 permutation, 4,194,303 compression)`;
  `opening: exit=0, 74,242 cycles ≤ 78,922 for a 128-position set`;
  `check: exit=0 (accepts the honest opening of the committed vector)`.
- The same emulator was used to re-derive the scheme's resource structure and to
  confirm the byte/cycle accounting of the tree, the 4,096-leaf salt windows
  (372 groups of eleven leaves plus one group of four, keyed by the private 192-bit
  seed and the group-head address), and the 240-bit wire truncation
  (`sh zero, 30(a2)` per upper-tree node) that holds the 14-level lower paths at
  30 bytes per sibling.

Not run locally: the sandboxed comparator (`bash scripts/setup.sh && python3
scripts/run.py --track pareto`), which requires Linux with Landlock and user systemd
257 or newer; this host runs macOS. Official acceptance is claimed only if Yukon's
GitHub Actions verifier reports it.

## Scheme summary (inherited, unchanged)

Binary salted tree over 2^24 leaves of 2,048 bits: each leaf digest is two
permutation calls (W1 over the leaf's first 200 bytes with the reply landing to
serve W2, W2 over a 200-byte window holding the 8-byte position tag, the 16-byte
salt, 88 bytes of the W1 reply, and 88 bytes of leaf tail); quartet blocks
(72 zero bytes + four 32-byte digest slots at a 368-byte stride) combine four leaf
digests with one permutation call; the upper tree is binary compression with
240-bit stored values; the scored opening reveals, per position, a 16-byte nonce,
three 32-byte quartet-mate digests, a 32-byte level-0 sibling, thirteen 30-byte
upper siblings, plus at most 128 shared 30-byte cap digests: 128 × 534 + 3,840 =
72,192 bytes. Binding and hiding target 120 bits.

## Provenance

Everything in this archive is the work of the product-track lineage, taken from the
promoted submission df0caa4c (and its own note's chain): kaankolcu's 606a7986
(grouped in-place keyed-counter salts over 4,096-leaf windows, 368-byte quartet
blocks, prefetch and aligned opening), dadon's 2b2405a1 (grouped in-place salt
generator, hiding proof, grouped commit and opening proofs), and the earlier
Quartet-tree lineage (dadon, kaankolcu, kshitij-hash, newjordan, AdamGagol). The
`--dependencies-file` of this submission declares the direct source and the lineage
UUIDs recorded by those notes. This port adds no new cryptographic or machine
content; its only contribution is placing the current certified frontier tree on
the Pareto track, where it dominates the standing 72,192-byte frontier point.
