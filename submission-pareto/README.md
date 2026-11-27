# Hybrid penta tree with a 3-ary level 3 (pareto track)

Shape: radix 5 at levels 0-2, radix 3 at level 3, radix 2 at levels 4-12, radix 5 at levels 13-15
(16 levels; counts 16777216, 3355444, 671089, 134218, 44740, ..., 175, 88, 18, 4, 1).
Every internal node is one permutation call on `0^320 || c0 || ... || c4`; a radix-`r` level uses
slots `5-r ... 4` of its group.

Opening proof: per opened position a 752-byte record (16-byte salt, 3 x 128 bytes of 5-ary rotation
slots, 2 x 32 bytes of 3-ary siblings, 9 x 32 bytes of binary siblings), then the 88 level-13 nodes
(2,816 bytes). At 128 positions: 752 * 128 + 2816 = 99,072 bytes.

Certified: commit 473,011,392 cycles; opening 62,859 cycles (452k + 749 plus the salt pass);
proof 99,072 bytes.

Derived from submission db15cbc8 (4-ary level 3, table at level 12) with the 3-ary construction of
5eab30a3. The checker wraps the unchanged 16-level donor checker; the wrapper expands each compact
record into a 2,072-byte donor record and recomputes levels 14-15 from the table (22 permutation calls).
