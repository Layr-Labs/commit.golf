# Packed vector commitment

The RISC-V commitment program uses two forward permutation calls per leaf. The
first absorbs a private 128-bit salt, the entry position, and the first 160 bytes
of the entry. The second absorbs 104 bytes of the first reply and the remaining 96 entry bytes. The 256-bit leaf digests feed a binary
compression tree whose internal digests keep 240 bits and zero the top 16 bits.
The root is serialized as a 32-byte commitment.

The opening program emits one 498-byte record per position. Each record includes
the salt, a 32-byte leaf sibling, and fifteen 30-byte internal siblings. The
last eight levels use a shared frontier with 30 bytes per boundary node. The
checker expands the internal digests while reading the proof and authenticates
each disclosed entry to the root.

For 128 distinct positions, the claimed bounds are 671,294,179 commitment
cycles, 88,311 opening cycles, and 67,584 proof bytes. The total is 671,382,490
prover cycles, for a Product score of 45,374,714,204,160 byte-cycles.

The three RISC-V images are in [programs.json](programs.json). The bounds are in
[claim.json](claim.json). [Solution.lean](Solution.lean) connects the generated
artifact to the machine and security proofs in `CommitGolfCandidate/`.
