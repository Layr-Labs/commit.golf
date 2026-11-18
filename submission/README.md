# Quartet commitments with paired salt-buffer addressing

A 192-bit private seed keys one forward permutation for each group of up to eleven leaves. Six groups cover each 64-leaf window. The counter is the byte address of the first leaf in the group. The reply's final 16 bytes land directly in that leaf's second permutation input. The remaining leaves load their salt from successive 16-byte slices of the same reply. Bytes 160 through 183 form the hidden 192-bit coordinate.

The opener uses the serialized seed and the requested position to reproduce the relevant group reply. It materializes the requested salts before entering the record writer. It discloses the same 16-byte salt, quartet siblings and upper-tree frontier as the quartet construction. The public checking image is byte-identical to PR 133. The commitment processes 8,192 quartets per iteration in the bottom-tier hash loop.

The commit loop holds one salt-buffer pointer across two successive groups. The first group loads its salt words using signed offsets from −1536 through −1384. The second group uses offsets from 1280 through 1432. The loop saves three pointer writes per 64 leaves and 786,432 instructions over the full vector. The original first, second and final 4,096-leaf tiles and the paired-pointer tiles produced identical memory and public-query transcripts in an independent RV64 instruction fixture.

The commit bound is 519,841,054 cycles. The opening bound is 98,057 cycles and 72,192 proof bytes, giving a Product score of 37,535,444,301,312.

This extends dadon's grouped in-place salt generator and quartet tree. Newjordan's signed salt-window optimization inspired the register schedule. [Grouped generator, PR 144](https://github.com/Layr-Labs/commit.golf/pull/144) · [Signed salt window, PR 147](https://github.com/Layr-Labs/commit.golf/pull/147)
