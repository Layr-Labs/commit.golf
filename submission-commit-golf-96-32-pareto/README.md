# Binary-top chain over one ternary level

This certificate is for the reviewed `late1_bias_chain_bin` image. The commit hashes paired late 24-byte salts into one ternary bottom level. Every parent above that level is binary. Eight levels, L9 through L16, are variable-width chains. The top of the tree is binary. There is no ternary node above the chain.

`claim.json` is `{"proofBytes": 69396, "commitCycles": 860276380, "openingCycles": 191023}`. The product is 59,712,995,898,588.

Unchained nodes at L6–L8 and L17–L23 keep 238 bits. The eight chained levels keep 230–236 bits. L2–L5 keep 240 bits. The ternary level and the root keep 256 bits. A 128-position opening is 128 records of 4,030 bits and 171 cap slots. The last cap slot stores 230 bits. The checker recovers the two omitted bits by recomputing the root for each of the four candidates. Openings of any other cardinality send an ordinary record per position.

The binding argument for this shape is the one in `cg-team/neon10/SECURITY-fable.md`. Two separate conditions carry it. Input-domain separation: ordinary binary parent inputs have a zero third block, chain stages carry nonzero stage tags, and all untagged binary heights share one work class, so a chain call cannot also serve as an unchained node (the full-width ternary bottom level and the leaf calls are handled as full-output exceptions). Density: every chained level has ρ ≥ 1, the condition of the weighted counting argument, which gives the binding ratio 0.9025. Density alone would not give separation; the rejected ternary-top family shows why. The same note clears the four-trial restoration of the two unsent bits. Hiding is the fixed-oracle bound of the paired late-salt tree.

`CommitGolf.Challenge.certificate` assembles that statement for this image: the commit and opening machine proofs, the batch checker (128 records, the cap, and the four-trial search), and the ordinary checker for every other cardinality.
