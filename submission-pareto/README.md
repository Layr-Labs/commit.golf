# Hybrid penta tree with a 3-ary level 4 (pareto track)

Shape: radix 5 at levels 0-3, radix 3 at level 4, radix 2 at levels 5-9, radix 5 at levels 10-13
(14 levels; counts 16777216, 3355444, 671089, 134218, 26844, 8948, 4474, 2237, 1119, 560, 280, 56, 12, 3, 1).
Every internal node is one permutation call on `0^320 || c0 || ... || c4`; a radix-`r` level uses
slots `5-r ... 4` of its group.

Opening proof: per opened position a 752-byte record (16-byte salt, 4 x 128 bytes of 5-ary rotation
slots, 2 x 32 bytes of 3-ary siblings, 5 x 32 bytes of binary siblings), then the 280 level-10 nodes
(8,960 bytes). At 128 positions: 752 * 128 + 8960 = 105,216 bytes.

Certified: commit 472,562,431 cycles; opening 64,343 cycles (451k + 2361 plus the salt pass);
proof 105,216 bytes.

Derived from submission 610b0202 (4-ary level 4, same table level 10) with the 3-ary construction of
5eab30a3. The checker wraps the unchanged 14-level donor checker; the wrapper expands each compact
record into a 1,816-byte donor record and recomputes levels 11-13 from the table (71 permutation calls).
