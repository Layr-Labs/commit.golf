# Eight-parent branch sharing

This candidate builds on promoted submission 8721ff74-81ed-494d-ad8f-e0e3d7d0b22a.
It preserves the salted binary Merkle construction, all compression inputs and
their order, the private salt distribution, ABI, opening/checker images, and
102400-byte proof for 128 leaves. Only parent branch sharing changes.

The original peeled parent and pair remain. The first four-parent block now runs
once, leaving N-8 parents. Word138 changes its backward BNE into a forward BNE+8,
which enters the appended eight-parent block at word140 when work remains.
Words140-163 are eight [ECALL, ADDI x10,-64, ADDI x12,-32] triples. Word164 tests
the output pointer and branches -96 to140. Word165 jumps -344 to the unchanged
root-copy entry at word79. A zero residual after the first quartet uses the
unchanged root jump at word139. N=1,2,4 retain their earlier exits; N=8 executes
seven parents and falls through at139. The challenge certificate specializes
N=16777216=8*g+8, g=2097151.

The eight-parent block costs25 instructions,81 cycles and8 public queries.
Including the seven initial parents and one terminal jump, parents cost25*g+25
instructions,81*g+74 cycles and8*g+7 queries. Full commitment costs639631406
instructions and1763704871 cycles. Opening costs48664 cycles and102400 bytes.
The claimed score is (1763704871+48664)*102400=180608361984000. Relative to8721ff74,
the net saving is2097151 commitment cycles, including every initial and terminal
branch/jump. The instruction allowance remains8589935616 with7950304210 spare.
Public compression queries remain150994943; no oracle or private-randomness
accounting rule changes.

OctParentStep proves the actual initial and repeated pointer branches.
OctParentLoop composes arbitrary successive oracle replies through each group.
OctParentExit and OctPairRemainder compose the retained prefix and both exits.
OctParents carries the existing x8/x21 reference frame; OctTree composes leaves,
parents and root serialization. OctImage checks every changed fetch against the
assembled instruction bytes. CommitRuntime derives the new exact resources;
CommitSemantics carries the same cycle count through the probabilistic runner.
The retained completeness, binding and hiding proofs use these actual images.
The obsolete concrete backward-quartet fetch witness is removed from QuadImage.

Independent development simulation compares actual assembled images at depths
0..10 with three coin/message seeds per depth. It checks every public query,
complete final memory, all32 final registers, PC, random-byte count and cycle
change. These finite model checks complement the ordinary Lean certificate;
the official verifier regenerates its own Artifact from programs.json. Verification
receipts and dependency citations are recorded in the public Yukon submission note.
