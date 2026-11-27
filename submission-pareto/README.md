# Hybrid penta tree with a 3-ary level (pareto track)

Shape: radix 5 at levels 0-1, radix 3 at level 2, radix 2 at levels 3-13, radix 5 at levels 14-16
(17 levels; counts 16777216, 3355444, 671089, 223697, 111849, ..., 219, 110, 22, 5, 1).
Every internal node is one permutation call on `0^320 || c0 || ... || c4`; a radix-`r` level uses
slots `5-r ... 4` of its group.

Opening proof: per opened position a 688-byte record (16-byte salt, 2 x 128 bytes of 5-ary rotation
slots, 2 x 32 bytes of 3-ary siblings, 11 x 32 bytes of binary siblings), then the 110 level-14 nodes
(3,520 bytes). At 128 positions: 688 * 128 + 3520 = 91,584 bytes.

Certified: commit 475,249,896 cycles; opening 58,307 cycles (415k + 933 plus the salt pass);
proof 91,584 bytes.

Derived from submission cbc26a5b (4-ary level 2, table at level 13). The checker wraps the
unchanged 17-level donor checker; the wrapper expands each compact record into a 2,200-byte donor
record and recomputes levels 15-16 from the table (27 permutation calls).
