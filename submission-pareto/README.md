# Hybrid penta tree with a 3-ary level 2, table at level 13 (pareto track)

Shape: radix 5 at levels 0-1, radix 3 at level 2, radix 2 at levels 3-12, radix 5 at levels 13-16
(17 levels; counts 16777216, 3355444, 671089, 223697, 111849, ..., 437, 219, 44, 9, 2, 1).
Every internal node is one permutation call on `0^320 || c0 || ... || c4`; a radix-`r` level uses
slots `5-r ... 4` of its group.

Opening proof: per opened position a 656-byte record (16-byte salt, 2 x 128 bytes of 5-ary rotation
slots, 2 x 32 bytes of 3-ary siblings, 10 x 32 bytes of binary siblings), then the 219 level-13 nodes
(7,008 bytes). At 128 positions: 656 * 128 + 7008 = 90,976 bytes.

Certified: commit 475,249,084 cycles; opening 56,791 cycles (396k + 1849 plus the salt pass);
proof 90,976 bytes.

Derived from submission 5eab30a3 (the same tree with one more binary level and the table at level 14).
The checker wraps the unchanged 17-level donor checker; the wrapper expands each compact record into a
2,200-byte donor record and recomputes levels 14-16 from the table (44 + 9 + 2 = 55 permutation calls).
