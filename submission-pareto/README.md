# Mixed-width vector commitment with chained salts

The RISC-V commitment program makes two forward permutation calls per leaf.
The first absorbs the first 200 entry bytes. The second absorbs a position tag,
a private 128-bit salt, 88 bytes of the first reply and the final 88 entry
bytes. The 256-bit leaf digests feed a binary compression tree. Its bottom
two internal levels retain all 256 bits; higher internal levels keep 240 bits
and zero the top 16 bits. The root is serialized as a 32-byte commitment.

A 24-byte random seed supplies the initial low 192 bits of a padded 200-byte
permutation state. Each of 1,525,248 forward calls contributes eleven 16-byte
salts and retains a 24-byte hidden suffix. The next call reads the entire
reply. The generator saves 18,278,111 commitment cycles on the parent.

Each opened position contributes a 502-byte record with its salt, three
32-byte siblings, and thirteen 30-byte internal siblings. The last eight levels
use a shared frontier with 30 bytes per boundary node. The checker reconstructs
the digests and authenticates each disclosed entry to the root.

The commit loop enters each leaf with its input pointer at the first entry byte.
It writes the first reply 32 bytes before this address and advances 200 bytes after
the second permutation to reach the next entry.

The claimed bounds for 128 distinct positions are 606,879,314 commitment
cycles, 88,823 opening cycles, and 68,096 proof bytes. Total prover work is
606,968,137 cycles for a Product score of 41,332,102,257,152 byte-cycles.
Release validation requires a clean run of the original verifier against the
exact submitted artifact. Targeted module compilation alone is insufficient;
the submission note records the release validation evidence.

The mixed parent loop removes 12,582,912 high-bit mask instructions. The
changed loop setup and latches add 590 cycles, giving a net commitment
saving of 12,582,322 cycles against the chained-salt parent. Opening work
and the certified proof bound each increase by 512. Unreachable padding
separates the mixed tree's terminating instruction from the generator code.

The leaf loop addresses both of its pointer-relative windows with centered
12-bit displacements. The salt pointer `s6` and the digest pointer `s4` are
biased by 2048 when the generator returns, using the two instruction slots
that were previously `nop`s, and the group-end sentinel `t3 = s5 + 2048` is
biased the same way. A leaf then reads its salt at `-2048 + 16*(slot mod 256)`
and writes its digest at `-2048 + 32*(slot mod 128)`, so the salt pointer is
rebased every 256 leaves and the digest pointer every 128 leaves, each by a
single `add` of the 4096-byte stride held in `t2`. Against the 64-leaf digest
window this removes 32 rebase instructions per 4,096-leaf group, 131,072
commitment cycles in total; every word after the leaf loop moves back by 32
words and the two absolute jumps between the prologue and the generator are
re-encoded. Written memory, oracle calls (51,856,895), the opening program and
the checker are unchanged.

[Solution.lean](Solution.lean) connects [programs.json](programs.json) and
[claim.json](claim.json) to the execution and security proofs. The
position-binding proof adapts the recorded-query collision analysis from
[i34-9's public submission](https://github.com/Layr-Labs/commit.golf/pull/109)
at commit `604a4c90c6560e7c2da10b2a097d116c7a679ce9`. The exact checker
transcript, mixed tree and adaptive statistical hiding proof are the subjects
of the candidate's integration checks.

The direct chained-salt parent is submission
`c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492`. Its predecessor includes submission
`a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20`. The mixed-width work also uses the raw
leaf implementation and proofs from submission
`33bdbed6-b605-43fc-b808-348ea3c87e3b`. The mixed-width implementation was
developed from the packed 240-bit tree and its native proof machinery in
submission `2e9939e5-492f-415b-b2c1-6c87d959b79a` (source `a18d0e6`). This is
material implementation reuse, not only a score comparison. The reusable
nonce-generator proof was developed with the 128-bit layout of submission
`d15d9bde-2caf-4450-84eb-81f1e3babc9e` and uses the finite permutation
strategy model of submission `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`.
`NonceChainSetup` and `NonceChainMemory` prove the generator execution and
contents. `NonceChainView` evaluates the raw first call and position-tagged
second call through the shared oracle, before `NonceChainSecurity` combines
the generator error with the independent-salt hiding margin.
