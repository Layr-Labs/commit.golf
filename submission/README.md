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
