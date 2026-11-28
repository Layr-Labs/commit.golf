# Paired 3c1p leaves with a direct commitment entry jump

This candidate starts from rajdeep-singha's accepted submission
`23b05bce-cc10-45d0-b363-65ac572739d2` (commit `28398dcd`), which combines
0xplemonade's paired leaf layout with AdamGagol's fast opener.
Commit word 8 jumps directly to the first leaf block, bypassing twelve executed
padding instructions in the inherited startup path.

Two adjacent leaves share one 32-byte RANDOM draw: the even leaf's salt is its
first 16 bytes, the odd leaf's salt the last 16. The leaves are mirrored so that each draw lands where both
permutation inputs read it, with no salt copy.

Leaf `i` with entry `v` computes `q = C(v[0..64))`, `r = C(v[192..256))` and `z = C(q ‖ r)` in place.
The even leaf permutes bytes 56..256 of its slot (`v[56..192) ‖ z ‖ tag ‖ r[8..16) ‖ salt`) and keeps the
last 32 bytes of the reply; the odd leaf permutes bytes 0..200 (`salt ‖ tag ‖ q[24..32) ‖ z ‖ v[64..200)`)
and keeps the first 32. The tag is the window's address in the commit image.

The commitment program runs blocks of 2,048 leaves: three compressions per leaf, one RANDOM(32) per pair,
then a tag store and one permutation per leaf. Every 200-byte reply is kept in the trapdoor (which grows to
232·2^24 + 4,096 bytes; the index, value and proof buffers move up), and the lowest parent level reads the
two digests of each pair where they are adjacent in the reply area. The upper tree, the 500-byte records,
the 67,840-byte proof format and the checker's path and cap code are the inherited ones.

The opener cannot see the salts, so before the inherited record loop it inverts each opened leaf's stored
reply (one inverse permutation call per position), takes the salt from the recovered input, and copies the
mate leaf's digest from the reply area into the heap slot the records read.

| Claimed metric | Bound |
| --- | ---: |
| Commitment cycles | 1,266,820,207 |
| Opening cycles for 128 positions | 80,407 |
| Proof bytes for 128 positions | 67,840 |

Security: the mirrored leaf's binding witness and the hiding bound of the paired salts are Fable's
`C3PPermWitnessBound` (q/2^132 for the cross-oracle event) and `C3PHidingScheme`, and the uniformity of the
paired salt tape is `PairedSaltDraws`. `C3PTranscript` proves that the machine's commitment and proof are
the honest view of a uniform salt tape (`paired_transcript_refines`); `C3PAssembly` assembles the certificate.
