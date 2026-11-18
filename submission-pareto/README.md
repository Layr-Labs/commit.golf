<<<<<<< ours
# Counter-mode in-place salts on the three-full-level binary tree

This Pareto candidate is blocksek's `04680e02-1baf-49bd-9c6e-fe02d839de05` (binary mixed-width tree with three
full-width parent levels, centered heap pointer, cap-mark opening; 68,352 proof bytes) with its salt generator replaced
by dadon's keyed counter-mode in-place salts from `2a19be00-0516-4bca-be0d-6d5f20f9d5d9`.

Claimed bounds (`claim.json`): 602,023,067 commitment cycles, 90,391 opening cycles (128 positions, worst case) and
68,352 proof bytes. The check program and the proof format are unchanged from 04680e02.

## Commit program
||||||| base
# Three full-width parent levels (Pareto variant of the mixed-width chained-salt tree)

This candidate is the tree described below with the width threshold moved by one level: the bottom
three internal levels (nodes 2^21 .. 2^24 - 1) keep all 256 bits, higher internal levels keep 240 bits.
The full-width parent phase runs 448 groups of 32,768 parents and stops at node 2^21 - 1; the projected
phase runs 127 groups of 16,513 parents. Records carry four 32-byte and twelve 30-byte siblings
(504 bytes). Claimed bounds: 68,352 proof bytes, 604,913,082 commitment cycles, 89,079 opening cycles.

## Base tree (two full-width levels)

# Mixed-width vector commitment with chained salts
=======
# Mixed-width vector commitment with chained salts
>>>>>>> theirs

- **Prologue (words 0-20).** One `RANDOM` call draws a 24-byte key into words 1-3 of the salt tape (trapdoor offset
  80·2^24 + 8). Word 0 of the tape later holds the last counter. All other tape words stay zero; no salt is stored.
- **Leaf scan (words 21-45,494).** The scan runs 64-leaf windows in six groups (11, 11, 11, 11, 11, 9 leaves), as in
  2a19be00. A group's first leaf (the head) writes the counter, i.e. the message address of the head leaf, into tape
  word 0 and permutes counter‖key. The reply's last 16 bytes are the head's salt, and its first 160 bytes are the other
  ten salts of the group. Non-heads copy their 16-byte salt from that block. Every leaf is 04680e02's
  two-permutation tagged leaf. The digest is written through the centered heap pointer, rebased every 128 leaves.
- **Parents, root.** 04680e02's parent sweep and root copy, unchanged except that every word moves by 512 (one artifact
  chunk). Words 45,672 onward are 04680e02's words 45,160 onward.

So salt *i* is a 16-byte slice, chosen by *i*'s rank in its group, of the permutation of (message address of *i*'s
group head ‖ key). The hiding proof for these salts is 2a19be00's (`CounterSalt*`), applied here to the binary
transcript in `BinaryCounterSecurity`.

## Opening program

Word 3 jumps to a prefix at words 1,441-1,487:
- It re-executes the displaced setup words 3-12 and copies the key from the tape into the permutation input block.
- For each opened position, in sorted order, it recomputes the group's counter-mode reply with one permutation call and
  writes the position's 16-byte salt into its tape slot in the in-memory trapdoor.
- It then jumps back to word 13, where 04680e02's unchanged record writer and cap walk run.

The proof bytes are therefore 04680e02's serialization of a *virtual* trapdoor: the in-memory trapdoor after the
prefix. It has the original heap and the counter-mode salt of every opened position. The prefix costs 28 setup cycles
plus 31-33 cycles and one oracle call per position.

## Proof structure

- Commit execution:
  - `GroupedKeySetup` and `GroupedKeyLive` cover the prologue and key draw.
  - `GroupedScan`, `GroupedPacketDecode` and `GroupedInvariant` give the exact 2^24-leaf scan with its leaf contents.
  - `P4Commit` adds the shifted parent sweep (`MixedWidthParentImage`, `MixedWidthStopRun`).
  - `P4Physical` gives the full commit trace and oracle count.
  - `P4Results` shows that the serialized root and heap are the mixed-width tree over the counter-salted leaves, and
    that the trapdoor carries the key.
- Opening execution:
  - `P4OpenLoop`, `P4OpenEffect`, `P4OpenPass` and `P4OpenHeader` cover the prefix rows, the per-position effect, the
    whole pass and the header.
  - `P4OpenFull` shows that the prefix ends at 04680e02's record-loop boundary with the virtual trapdoor, and that the
    opener outputs `proofFromTrapdoor` of it.
  - 04680e02's body proofs are reused. Their input frame `SameOpeningInput` now covers aligned words only: the prefix's
    aligned stores leave the unaligned `getMem` keys stale. The body's loads all go through `alignToDword`.
- Certificate:
  - `P4OpenClosing` shows the executable transcript is the pinned honest view with counter-mode salts (`p4_refines`).
  - Hiding: `BinaryCounterSecurity.scheme_hiding_of_counter`.
  - Binding, termination and query budget: 04680e02's unchanged checker facts.
  - `BinaryCounterCertificate` assembles these, as 2a19be00's `QuartetCounterCertificate` does for its quartet tree.

## Credits

- Base tree and all its programs and proofs: blocksek's `04680e02`. That tree in turn builds on:
  - newjordan's `cdb98559`;
  - Th0rgal's `ddb6bf80`;
  - blocksek's `746ff19e` (heap pointer, cap-mark opening);
  - the two-permutation lineage of `a6b5adf3`.
- Counter-mode in-place salts, grouped leaf scan, counter-salt hiding proof, opener prefix and certificate assembly:
  dadon's `2a19be00`. The P4Open* modules are ports of its GroupOpen* prefix modules to this opener.
