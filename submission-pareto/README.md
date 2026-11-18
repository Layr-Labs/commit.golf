# A full 5-ary permutation tree on the quad + NonceChain design (Pareto track)

This Pareto-track candidate starts from submission 1a9bc5f4-ac89-4a1d-a901-d8a37b3859a1
(AdamGagol, commit f94f72f7, 523,312,474 commit cycles, 94,841 opening cycles, 72,192 proof bytes).
It keeps that design's leaves, NonceChain salts and in-place zero-prefixed groups. Everything above
the leaves becomes one 5-ary permutation tree, built in 11 levels. The quad layer, the binary
projected-compression tree and the cap footer are gone.

| | 1a9bc5f4 (base) | quad2 | quad3 | this candidate (penta) |
|---|---:|---:|---:|---:|
| commit cycles | 523,312,474 | 499,194,978 | 493,165,594 | 477,166,575 |
| opening cycles (128 positions) | 94,841 | 101,371 | 107,901 | 112,654 |
| prover cycles | 523,407,315 | 499,296,349 | 493,273,495 | 477,279,229 |
| proof bytes (128 positions) | 72,192 | 76,800 | 81,408 | 182,272 |
| oracle calls per commit | 43,468,287 | 41,371,135 | 40,846,847 | 39,273,988 |

The quad2 and quad3 columns are this author's intermediate candidates, which add one and two more
4-ary quad levels. This candidate cuts prover cycles by 46.1M (8.8%) and costs proof bytes.
Bytes do not matter for a cycle-axis frontier point on the Pareto track.

## The node

    pentaInput(c0..c4) = 0^320 || c0 || c1 || c2 || c3 || c4      (low bits first)

The node is the low 256 bits of one permutation reply. Its domain is D5, the blocks whose low
320 bits are zero.

* **Binding.** An adversary with q queries finds an output collision inside D5 with probability at
  most q²/2^257. An inverse query lands in D5 with probability at most 2^-320 per query.
* **Width.** Five 32-byte children plus 40 zero bytes fill the 200-byte block. The ECALL destination
  must be 8-aligned, so 32-byte slots are the narrowest usable children. A 6-ary node would leave only
  64 bits of capacity, which is too little for binding.

## Tree and memory

Level 0 has the 2^24 leaves. Level k+1 has ⌈n_k / 5⌉ nodes, giving
16777216, 3355444, 671089, 134218, 26844, 5369, 1074, 215, 43, 9, 2 and 1 (the root at level 11).
Missing children of a ragged last group count as 0.

Level-k nodes live in 368-byte groups at `pentaGroupBase k`: 40 never-written zero bytes, then five
32-byte slots.
* The leaf pass writes each leaf's 200-byte second reply into its slot.
* Level k+1 node j is one permutation call directly on level-k group j. Its reply is written ascending
  into its own slot, with destination strides +32, +32, +32, +32, +240.
* A reply only overwrites later slots of its own group, or ends exactly at the next group.
* After each level, the commit clears the ragged slots of the last group, so the trapdoor holds
  exactly the specification's zeros there.
* The root is copied to the commitment.

The trapdoor size, salts and buffer layout are those of the quad base. All groups fit below the salt
area, inside the space the old heap and leaf groups used.

**Leaf pass.** 4096 unrolled leaf bodies with 45-leaf centred output windows (nine groups).
* The first pass covers leaves 0..4095.
* The loop then re-enters at leaf 1 for 4096 passes of 4095 leaves.
* 4095 = 45 · 91, so each re-entered pass is a whole number of windows. The per-leaf instructions are
  those of the base.

**Level passes.** Levels 1..4 use an unrolled loop body plus a tail; levels 5..10 are fully unrolled.

**Commit.** 477,166,575 cycles, exact for every reachable run, with 39,273,988 oracle calls:
1,525,248 for the generator, 2 · 2^24 for the leaves and 4,194,308 for the nodes.

## Proof format, opener, checker

Each opened position contributes one 1,424-byte record: the salt (16), then for each level
k = 0..10 the four other children of its level-(k+1) node, in rotation order r+1..r+4 (mod 5) with
r = (i / 5^k) mod 5 (4 × 32). There is no footer.

* **Opener.** It uses DIVU/MUL/REMU for the group and rotation, with doubleword copies. A record
  costs 880 cycles, so every 128-position opening costs exactly 14 + 880 · 128 = 112,654 cycles.
* **Checker.** It recomputes the pinned leaf, then loops 11 times: 40 zero bytes, the digest at slot
  r, the four record siblings at r+1..r+4, one ECALL. Finally it compares the result with the
  commitment. It makes 13 public queries per position and rejects unless the proof length is exactly
  1,424 · card.

## Security

* **Binding.** Walking the D5 path down from the root, at each level either the two node inputs
  differ with equal outputs, or they are equal and the opened children agree. So two accepted
  openings of one position with different values give one of:
  * a D5 collision;
  * an inverse hit of D5;
  * the pinned-leaf event at the bottom.

  The bound is q/2^122 for D5 plus q/2^123 for pinned leaves, within q/2^120. Ragged groups need no
  special case, because siblings are unconstrained.
* **Hiding.** The base's quad hiding argument carries over to D5 (`PentaHiding*`, `PentaNonceFinal`).
  * Programming a hidden second-call row changes a node evaluation only if its preimage lies in D5.
    The nonzero position tag in word 0 keeps hidden inputs out of D5.
  * The freeze term becomes 2^24 / 2^319 per side.
  * For the NonceChain step, the public view tabulates the honest inputs level by level
    (`PentaNonceView`: 4,194,308 node queries), and `PentaBuildLocal` says the builder needs nothing
    else.
  * The chain error is evaluated at 2t + 2L + 4,194,308 queries and still fits: the bound is
    min(1, (t+1)/2^120).

Everything is proved in Lean on the challenge's RISC-V machine model, for the exact delivered
images: commit 236,749 words, opening 696 words, check 460 words. The only axioms are propext,
Classical.choice and Quot.sound.

## Credits

* 1a9bc5f4-ac89-4a1d-a901-d8a37b3859a1 (AdamGagol): the direct base. This candidate reuses its
  leaf pass, NonceChain integration and the whole proof lineage, adapted.
* c08b0128-14a7-48dd-a745-070c3a77d754 (kaankolcu, f53bbbf): the zero-capacity permutation node
  over in-place 368-byte groups, generalized here from 4 to 5 children and applied at every level.
* c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492 (dadon, 31727a8): the NonceChain salt generator.
* 33bdbed6-b605-43fc-b808-348ea3c87e3b (kaankolcu, 8d2a211): the pinned two-permutation leaf
  and the opener and checker lineage.
* 4cc16abc-b408-4852-9f59-1a7df894509e and 362ba8b2-d91c-400b-8b3a-cb4ffee99f9c (kshitij-hash):
  the cycle-budget analysis that pointed at the tree.
* The base README below credits further work in this lineage.

## Main new modules

* **Spec:** `TwoPermutationPentaSpec`, the frozen interface.
* **Commit:** `QuadCommitPenta*` and the regenerated leaf, walk and nonce modules.
* **Opening:** `QuadOpeningRun`, `QuadOpeningLevel(s)` and `QuadOpeningRecord`.
* **Checker:** `QuadCheckPenta*` and `QuadBindingPaths` (`binding_of_penta_trace`).
* **Hiding:** `PentaHiding*`, `PentaNonceFinal`, `PentaNonceView` and `PentaNonceSecurity`.
* **Assembly:** `PentaNonceCertificate` and `PentaNonceAssembly`.

---

# Base design (README of 1a9bc5f4, unchanged)

# Quad bottom layer plus the NonceChain salt generator

This note describes a candidate for the product track of commit.golf. It
starts from the pinned two-permutation design accepted at 8d2a211 and stacks
two independent changes on it: a quad bottom layer (one permutation node per
four leaves, this note's main idea) and the NonceChain salt generator of
31727a8. The score is (commit cycles + opening cycles) × proof bytes, and
lower is better.

| | 8d2a211 | 31727a8 | quad only | this candidate (quad + NonceChain) |
|---|---:|---:|---:|---:|
| commit cycles | 637,936,351 | 619,658,240 | 541,590,584 | 523,312,474 |
| opening cycles (worst 128-position batch) | 88,311 | 88,311 | 94,841 | 94,841 |
| proof bytes (128 positions) | 67,584 | 67,584 | 72,192 | 72,192 |
| score | 43,120,258,756,608 | 41,884,950,902,784 | 39,105,354,201,600 | 37,785,820,884,480 |

When this was written, the record was f8612ed (03:06 UTC on 18 Nov) at
523,377,606 / 93,945 / 72,192 = 37,790,458,209,792. It reached the same
combination (a four-leaf bottom layer plus a permutation-chain salt generator)
through its own route. This candidate is 0.012% below f8612ed: its commit is
65,132 cycles cheaper and its opening 896 cycles dearer. The two earlier
records of the same night were 432cfe6 (37,886,886,580,224, the same
generator with a 168,725-cycle opening) and f53bbbf (quad alone,
39,111,737,418,240). This candidate is 0.27% and 3.4% below them.

## NonceChain on the quad image

31727a8 replaced the bulk RANDOM draw of 2^28 salt bytes (33,554,433 cycles)
with a 24-byte seed and a chain of 1,525,248 forward permutation calls. Each
call outputs 200 bytes, keeps 176 bytes (eleven 16-byte salts) and leaves the
last 24 bytes hidden, because the next call's output overwrites them. On the
quad image the generator is the same code, appended after the root copy:

* RANDOM draws the 24-byte seed at QUAD_SALT_BASE - 176. That address lies in
  the spill area of the last leaf group (offsets 264..288), outside its
  72-byte zero prefix. The spill of leaf 4g+3 overwrites it later.
* Word 17 jumps to the generator. The generator returns to word 18, and on the
  way it restores x12 (one extra cycle), so the state at the leaf entry equals
  the bulk-RANDOM ready state with the drawn bytes replaced by the chain output.
  The leaf, quad, parent and root proofs of the quad image are reused as they
  are.
* Commit cycles: 541,590,584 - 18,278,111 + 1 = 523,312,474. Oracle calls:
  41,943,039 + 1,525,248 = 43,468,287.

Hiding with chain salts uses the 31727a8 triangle argument. The quad builder
reads the whole quad function, so the public view is re-expressed as a bounded
computation: it queries the 2^22 honest group inputs and tabulates them. The
query bound becomes t + 2L + L/4 + t. A sharp restatement of the quad final
bound, (q+1)/2^121, leaves room for both chain-error terms, and the total
stays at min(1, (q+1)/2^120).

## The idea

In 8d2a211 every leaf costs two permutation calls. The first absorbs 200 bytes
of the message entry. The second absorbs the position tag, the salt, part of
the first reply and the rest of the entry. Its low 32 bytes are the leaf
digest. Above the leaves sits a binary tree of compression calls, 2^24 - 1 of
them, and each internal output is masked to 240 bits.

The permutation block is wide: 1,600 bits. Four 256-bit leaf digests (1,024
bits) fit in one block with 576 zero bits to spare. This candidate keeps the
leaf function exactly as in 8d2a211. It changes only the two lowest tree
levels: instead of 3 compressions per group of four leaves (two at the bottom
level, one above), there is one permutation call on

    quadInput(c0, c1, c2, c3) = 0^576 || c0 || c1 || c2 || c3

(low bits first). The quad node is the low 256 bits of the reply. Above the
quad layer, the binary compression tree of 8d2a211 continues unchanged, mask
included. It covers heap nodes 1 .. LENGTH/4 - 1, over the LENGTH/4 quad
nodes.

Oracle calls per commit: 2·2^24 (leaves) + 2^22 (quad nodes) + (2^22 - 1)
(compressions) = 41,943,039. In 8d2a211 it was 50,331,647. A permutation
ECALL and a compression ECALL cost the same, so the cycle saving comes from
removing 2^23 compressions and their loop instructions. In this image a
quad node costs 10 cycles and a binary parent 11, in batched unrolled loops.

## Memory layout

The commit writes each leaf's second reply (200 bytes) into a padded group of
four digest slots:

* groups of 368 bytes starting at QUAD_GROUP_BASE = 2^28 + 4096 - 72;
* inside a group, 72 zero bytes, then slots k = 0..3 at offsets 72 + 32k;
* a reply written from slot 3 ends exactly at the start of the next group.
  So the 72-byte zero prefix of every group survives, and the group is
  already a valid quadInput block in memory: no copying.
* salts from QUAD_SALT_BASE = 0x6C001000 (one `lui`), 16 bytes per leaf,
  filled by the NonceChain generator (by one bulk RANDOM syscall in the
  quad-only variant).

The trapdoor is 2,080,378,880 bytes. It holds the binary heap, the groups and
the salt tape. The geometry modules prove the separation facts (replies never
reach an earlier digest; prefixes stay zero) for the full 200-byte replies,
not just the 32 retained bytes.

The leaf loop keeps the unrolled 4,096-leaf body of 8d2a211. Only the signed
destination immediate and the occasional base rebases change (94 destination
and 32 salt rebases per body). The body repeats 4,096 times.

## Opening and proof format

Each opened position contributes one 534-byte record:

* the 16-byte salt;
* the three other leaf digests of its group, 32 bytes each. They come in
  rotation order r+1, r+2, r+3 (mod 4), where r = index mod 4. The opener
  then copies three slots that are contiguous modulo the group, with no
  index-dependent permutation;
* the quad node's binary sibling, a full 32 bytes (quad nodes are not
  masked);
* 13 binary siblings above that, 30 bytes each (the masked 240-bit outputs).

The cap footer of 8d2a211 is unchanged. For 128 positions the proof is
72,192 bytes, 4,608 more than 8d2a211: each record grows from 498 bytes
(16 + 32 + 15 × 30) to 534 bytes (16 + 3 × 32 + 32 + 13 × 30), 36 bytes per position.
The opener's worst 128-position batch costs 94,841 cycles. The checker
rebuilds each quad node with one extra permutation query per opened position.

## Security argument

Binding. A collision of the quad layer means two distinct D2 inputs (the quad
domain: 576 zero low bits) whose replies agree in the low 256 bits among the
recorded oracle rows. The replay bound pays q/2^123 for it, next to the
existing compression and pinned-leaf terms, and the total stays at q/2^120.
Raw first-call leaf inputs may themselves lie in D2; the argument does not
assume the leaf and quad domains are disjoint.

Hiding. The reduction follows 8d2a211's pinned proof
(adaptive programming of the hidden leaf rows). The observer may now also
evaluate the quad function over the same permutation. Programming a hidden
row changes a quad-node evaluation only if the row's preimage falls into D2.
A freeze hybrid charges ≤ 2^24 · 2^-575 per side for that. The final bound is
still min(1, (q+1)/2^120) per fixed compression function.

Everything is proved in Lean on the challenge's RISC-V machine model, for the
exact delivered images: commit (157,424 words), opening (720 words) and check
(432 words). The images are tied to the generated Artifact module by kernel
equality. The only axioms are propext, Classical.choice and Quot.sound.

## How the work was split

* The shared interface `TwoPermutationQuadSpec.lean` was frozen first: the
  quad function, the heap, the 534-byte record, the transcript builder, the
  layout constants, and the `QuadCommitTranscript` structure that the commit
  side hands to the opening side.
* The commit image and its whole-run proof: the leaf pass, the quad pass,
  the binary pass, and resource facts (exact cycles and oracle calls).
* The opening image: a splice of the 8d2a211 opener, with a new group/leaf
  copy block and the quad sibling copy. Its proofs reuse the 8d2a211 record
  loop, with new record geometry.
* The checker image (8d2a211's checker plus a quad assembly block) and
  binding.
* Hiding.

## Honest caveats

* The opening cycle count is the proven worst case over 128-position
  batches. An emulator against the reference record format agreed with it.
* The commit cycle count is exact: every reachable run has exactly the
  claimed number of cycles (541,590,584 for quad only, 523,312,474 with the
  generator).
* The design adds proof bytes (+6.8%) to save commit cycles (-15.1%). It is
  only a net gain because commit cycles dominate the sum. If later records
  shrink the commit far enough, the trade-off reverses.

## Next steps

The leaf pass is now the dominant cost: 2^24 leaves at 25 cycles each. Nine of
those cycles are plain instructions: the position tag, the salt copy (two
load/store pairs) and pointer updates. Removing the salt copy would need the
generator to write each salt directly into the leaf window. The in-place leaf
windows overlap the previous leaf's message tail, so that is not a simple
reordering.

## Commands and results

From the project root, with the pinned Lean 4.35.0 toolchain, and with
`CommitGolf/Artifact.lean` regenerated from `programs.json`
(`scripts/generate_artifact.py submission/programs.json --refresh`):

- `lake build Solution`: build completed successfully (9,848 jobs).
- `#print axioms CommitGolf.Challenge.certificate`: [propext, Classical.choice, Quot.sound].
  `submission_matches_artifact`: [propext, Quot.sound].
- `python3 verifier/check_submission.py submission`: ok, artifact digest
  `1bb237f2a1b0e4ff3fccc7d1a03d4d552182a7ee6a90f1e57b9cf7c52e9da7b5`, score 37,785,820,884,480.
- With the candidate cache purged and the build pinned to two CPUs, the
  pre-commit-proof part of the tree builds in about 30 minutes, peaking at
  about 16 GiB proportional memory.

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 523312474 94841`.
Here `submission` is the generated `CommitGolf.Artifact.submission`, and
`submission_matches_artifact` holds by `rfl`. The pieces are:

- `QuadCertificate.artifact_is_quad`: the generated artifact equals
  `Quad.Commit.submission QuadOpening.openingImage Quad.Checker.quadCheckImage`.
  It is proved by kernel equality, in per-block walks over the commit image.
- `Quad.Commit.verifiedNonceTranscript` and `Quad.Commit.nonce_commit_resources`:
  every commit run succeeds in exactly 523,312,474 cycles with 43,468,287 calls.
  The commitment and trapdoor are those of the quad tree on the chain salts.
- `Quad.Checker.checker_facts`: the checker facts for the delivered check image.
- `QuadNonceCertificate.quad_nonce_certificate`: assembles these with the
  opening ABI, quad binding and the NonceChain hiding bound.

Two reused modules from the packed lineage (`TwoPermutationPackedTrustedInput`
and the packed commit image modules) were written against the earlier packed
artifact. They now read frozen copies of it (`PackedCheckArtifact`,
`PackedCommitArtifact`), which serve only as reference images for those
reused lemmas. Nothing about the delivered submission is derived from them.
