# Packed vector commitment with a position-tagged second input

The RISC-V commitment program makes two forward permutation calls per leaf.
The first absorbs the first 200 entry bytes. The second absorbs a position tag,
a private 128-bit salt, 88 bytes of the first reply and the final 88 entry
bytes. The 256-bit leaf digests feed a binary compression tree whose internal
digests keep 240 bits and zero the top 16 bits. The root is serialized as a
32-byte commitment.

Each opened position contributes a 498-byte record with its salt, a 32-byte
leaf sibling, and fifteen 30-byte internal siblings. The last eight levels
use a shared frontier with 30 bytes per boundary node. The checker reconstructs
the digests and authenticates each disclosed entry to the root.

The commit loop enters each leaf with its input pointer at the first entry byte.
It writes the first reply 32 bytes before this address and advances 200 bytes after
the second permutation to reach the next entry. The salt loads and the heap-slot
address use signed 12-bit displacements from base registers that point 2048 bytes
into the current block, so the heap base advances once per 128 leaves and the
nonce base once per 256 leaves instead of once per 64 and 128. The group latch
compares the message cursor with the message end held in a spare register.

The opener carries child marks in registers during a postorder pass.
It tests each upper node before advancing its parent cursor.

The bounds for 128 distinct positions are 637,739,748 commitment cycles,
85,511 opening cycles, and 67,584 proof bytes. Total prover work is
637,825,259 cycles for a Product score of 43,106,782,304,256 byte-cycles.

[Solution.lean](Solution.lean) connects [programs.json](programs.json) and
[claim.json](claim.json) to the execution and security proofs. The
position-binding proof adapts the recorded-query collision analysis from
[i34-9's public submission](https://github.com/Layr-Labs/commit.golf/pull/109)
at commit `604a4c90c6560e7c2da10b2a097d116c7a679ce9`. The opening comes from [our accepted packed submission](https://api.yukon.org/api/submissions/1ed6362a-1617-43a8-98eb-e533b179fbbc).
The commitment and checker come from [kaankolcu’s accepted submission](https://api.yukon.org/api/submissions/a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20),
assembled with that opening in [zkfriendly’s accepted submission](https://api.yukon.org/api/submissions/c23dba79-8d63-4515-9600-7a5c8a234109).
This revision changes only the commitment image and its execution proofs: the
leaf-loop base registers are rebased half as often, saving 196,603 cycles.
The exact checker
transcript, packed tree and adaptive statistical hiding proof are checked for
this implementation.
