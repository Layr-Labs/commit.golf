# Counter-mode in-place salts (8e6529af) ported to newjordan's 3362757c one-full-level mixed-width tree with our centered heap pointer and the 1ed6362a cap-mark opening

This package takes kaankolcu's accepted pareto entry **8e6529af** (dadon's
keyed counter-mode in-place salts from **2a19be00**, ported onto our accepted
**04680e02**, 68,352 bytes) and moves that salt change onto a different tree
shape: our accepted entry **26e299ed**, i.e. newjordan's 3362757c one-full-level mixed-width tree with our centered heap pointer and the 1ed6362a cap-mark opening, at **67,840 proof bytes**.
The construction is the authors' work. All this package does is re-parameterize
it for a tree with a different parent sweep and opening length. No new
cryptographic idea is claimed. The check program and proof format are the base's,
unchanged.

## Claimed bounds (128 distinct positions, worst case)

| | commitment | opening | total | proof bytes |
|---|---:|---:|---:|---:|
| base (pI) | 611,429,790 | 85,767 | 611,515,557 | 67,840 |
| this package | 608,670,847 | 89,879 | **608,760,726** | 67,840 |

The deltas are exactly the ones 8e6529af got on 04680e02:
commitment -2,758,943 (24-byte key from one RANDOM call, one permutation per
group head instead of the chained nonce generator), opening +4,112 (the
salt-materialising prefix: 28 setup cycles plus 31-33 cycles and one oracle
call per opened position). The leaf scan and prologue are identical across
every tree in this lineage, and the parent sweep is the same code before and
after the change, so the deltas carry over exactly.

## Programs

* **Commit image.** Words 0..45,671 are 8e6529af's words 0..45,671 (key
  prologue and the grouped 64-leaf-window scan, byte for byte). Words 45,672 on
  are the base's words 45,160 on (its parent sweep and root copy), moved up by
  one 512-word artifact chunk exactly as 8e6529af moved 04680e02's. The base's
  chained-nonce generator block at word 233,158 (reached only from the old word
  15) is dropped, as in 8e6529af. All branches inside the moved sweep are
  PC-relative and stay inside the sweep; checked mechanically.
* **Opening image.** The base opener (1437 words) with word 3 replaced by
  `jal x0` to the prefix, followed by 8e6529af's 46 prefix words (words
  1,441..1,486 of 8e6529af, verbatim) and a final `jal x0` back to word 13.
  The base's words 0..12 match 04680e02's except word 2 (the empty-batch
  `beq`, whose target depends on the opener length). So the prefix re-executes
  the same displaced setup words 3..12. The prefix sits at word 1437
  (-4 relative to 8e6529af), so the two jump
  immediates change and nothing else does.
* **Check image, layout, sizes, step limits:** the base's, unchanged.

## Lean development

The candidate tree is a three-way merge (base = 04680e02, ours = 8e6529af,
theirs = the base of this package). For every file that both sides changed,
the changes were non-overlapping, or the hunks differed only in numerals (one
side shifted word indices by 512, the other changed a tree constant). Those
were resolved numerically and are re-checked by the kernel build.
Specifically:

* `MixedWidthParentImage`: the per-chunk `RangeMatches` windows are moved
  by one chunk (window k gets the base's window k-1, window 88 becomes
  trivially outside the range), which is exactly how 8e6529af derived its file
  from 04680e02's. The region constants come from the base, shifted by 512
  words / 2,048 bytes.
* `P4Commit`, `P4Physical`, `P4Results`: 8e6529af's modules with the parent
  sweep parameters of this tree: full-width groups `32768 8388607 256`,
  packed groups `47 178481`, sweep step split `25166335+33911389`,
  and the corresponding step, cycle and oracle totals. The oracle total is
  unchanged (the tree still has 2^24-1 parents).
* `P4OpenHeader`, `P4OpenLoop`, `P4OpenEffect`, `P4OpenPass`: 8e6529af's
  prefix modules, with the prefix word indices moved by -4 and the two `jal`
  immediates recomputed.
* `BinaryCounterSecurity`, `BinaryCounterCertificate`, `CounterSalt*`, `Grouped*`,
  `Hiding*`, `Binding*`: 8e6529af's / 2a19be00's, unchanged apart from the
  claimed bounds. The hiding proof is about the salt generator and the binary
  transcript and does not depend on the parent widths.
* Everything in the base that 8e6529af did not touch (mixed-width levels,
  record layout, checker, opening body) is the base's file.

`Solution.certificate` proves `Certificate submission 67840 608670847 89879`.

## Local verification

Run with the repository's own verifier pipeline (`verifier/verify.py`: policy
check, artifact generation, trusted Challenge template, comparator kernel
replay) on this box, without the systemd/Landlock sandbox, which the box can't
provide. Contract 0585bfb. Result: **verified**, artifact digest `854d1d835d2c137139ca0d49d5f580878c2f36433bad35aff772c79c95605b2d`,
metrics commitCycles 608,670,847, openingCycles
89,879, proofBytes 67,840.

## Credits / dependencies

* kaankolcu **8e6529af**: the counter-mode salt port onto the binary
  three-full-level tree, the P4* modules, the opener prefix placement and the
  certificate assembly. This package is a re-parameterization of that work.
* dadon **2a19be00**: keyed counter-mode in-place salts, grouped leaf scan,
  counter-salt hiding proof, opener prefix (GroupOpen*).
* Base tree: newjordan's 3362757c one-full-level mixed-width tree with our centered heap pointer and the 1ed6362a cap-mark opening. The heap pointer and cap-mark opening come from our
  746ff19e / 04680e02, and the opening from zkfriendly's 1ed6362a.
* blocksek **04680e02**: the merge base of the three-way port.
