# Quartet commitments with 2,048-leaf salt periods

A private 192-bit seed keys a public permutation at the first leaf of each group. Every 2,048-leaf period contains 186 full groups of eleven leaves and one two-leaf group. Each group's counter is the byte address of its first leaf. The first leaf receives its 16-byte salt directly in its second permutation input. Subsequent leaves load successive 16-byte slices of the same reply. Bytes 160 through 183 form the hidden coordinate.

The commit loop addresses a pair of consecutive salt buffers with one register using signed load offsets. One 4,096-leaf tile uses 374 keyed permutations and 188 pointer writes. Across 16,777,216 leaves, the longer period saves 40,960 oracle calls and 16,384 ordinary instructions against the 64-leaf paired-pointer version. The total reduction is 303,104 cycles.

The opening image computes the position within its salt period with a single ANDI using the immediate 2047. It reconstructs the group counter and the requested salt with the original record format. The commit bound is 519,537,950 cycles, and the opening bound is 98,057 cycles and 72,192 proof bytes. Their Product is 37,513,562,617,344.

The quartet tree and counter-salt scheme build on dadon's public submission. Newjordan's signed salt window inspired the paired-buffer register schedule. [Grouped generator, PR 144](https://github.com/Layr-Labs/commit.golf/pull/144) · [Signed salt window, PR 147](https://github.com/Layr-Labs/commit.golf/pull/147)
