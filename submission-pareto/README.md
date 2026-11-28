# Five 5-ary levels, a 3-ary level 5 and three binary levels (pareto track)

Shape: radix 5 at levels 0-4, radix 3 at level 5, radix 2 at levels 6-8, radix 5 at levels 9-12
(13 levels; counts 16777216, 3355444, 671089, 134218, 26844, 5369, 1790, 895, 448, 224, 45, 9, 2, 1).
Every internal node is one permutation call on `0^320 || c0 || ... || c4`; a radix-`r` level uses
slots `5-r ... 4` of its group.

Opening proof: per opened position an 816-byte record (16-byte salt, 5 x 128 bytes of 5-ary rotation
slots, 2 x 32 bytes of 3-ary siblings, 3 x 32 bytes of binary siblings), then the 224 level-9 nodes
(7,168 bytes). At 128 positions: 816 * 128 + 7168 = 111,616 bytes.

Certified: commit 472,473,324 cycles; opening 52,738 cycles (364k + 1892 plus the salt pass);
proof 111,616 bytes.

The opener's record writer dispatches each 5-ary level (and the 3-ary level) into a per-digit copy
variant with fixed load offsets (`jalr` on `x25 = digit`), instead of computing every sibling's
rotation offset with a `REMU`: 364 instead of 488 cycles per record. The proof bytes, the trapdoor,
the commitment image and the checker are unchanged from f4571c54.

Derived from submission d981758b (the same tree with a 4-ary level 5) with the 3-ary construction of
88953167 / 5eab30a3. The checker wraps the unchanged 13-level donor checker; the wrapper expands each
compact record into a 1,688-byte donor record and recomputes levels 10-12 from the table
(45 + 9 + 2 = 56 permutation calls).
