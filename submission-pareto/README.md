# Hybrid penta tree with a 3-ary level 3, table at level 12 (pareto track)

Shape: radix 5 at levels 0-2, radix 3 at level 3, radix 2 at levels 4-11, radix 5 at levels 12-15
(16 levels; counts 16777216, 3355444, 671089, 134218, 44740, 22370, ..., 350, 175, 35, 7, 2, 1).
Every internal node is one permutation call on `0^320 || c0 || ... || c4`; a radix-`r` level uses
slots `5-r ... 4` of its group.

Opening proof: per opened position a 720-byte record (16-byte salt, 3 x 128 bytes of 5-ary rotation
slots, 2 x 32 bytes of 3-ary siblings, 8 x 32 bytes of binary siblings), then the 175 level-12 nodes
(5,600 bytes). At 128 positions: 720 * 128 + 5600 = 97,760 bytes.

Certified: commit 473,010,732 cycles; opening 61,157 cycles (433k + 1479 plus the salt pass);
proof 97,760 bytes.

Derived from submission a196d858 (the same tree with one more binary level and the table at level 13),
itself from db15cbc8 and the 3-ary construction of 5eab30a3. The checker wraps the unchanged 16-level
donor checker; the wrapper expands each compact record into a 2,072-byte donor record and recomputes
levels 13-15 from the table (35 + 7 + 2 = 44 permutation calls).
