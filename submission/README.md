# Quartet commitments with grouped in-place salts

A 192-bit private seed keys one forward permutation for each group of up to eleven leaves. Six groups cover each 64-leaf window. The counter is the byte address of the first leaf in the group. The reply's final 16 bytes land directly in that leaf's second permutation input. The remaining leaves load their salt from successive 16-byte slices of the same reply. Bytes 160 through 183 form the hidden 192-bit coordinate.

The opener uses the serialized seed and the requested position to reproduce the relevant group reply. It materializes the requested salts before entering the record writer. It discloses the same 16-byte salt, quartet siblings and upper-tree frontier as the quartet construction. The public checking image is byte-identical to PR 133. The commitment processes 8,192 quartets per iteration in the bottom-tier hash loop.

The full-vector interpreter counted 520,627,486 commit cycles. The spread-low 128-position opening took 98,057 cycles and produced 72,192 proof bytes. Their product is 37,592,218,400,256.
