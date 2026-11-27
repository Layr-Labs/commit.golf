# Five 5-ary levels below the binary levels (109,824 proof bytes)

The hybrid tree of `9e495a40` with one more 5-ary level at the bottom: 5-ary levels 0-4, binary levels 5-9,
5-ary levels from the table (level 10) up (`PENTA_LOW = 5`, `PENTA_HIGH = 10`, 14 levels:
`3355444, 671089, 134218, 26844, 5369, 2685, 1343, 672, 336, 168, 34, 7, 2, 1`).

- Proof: 816-byte records (salt, `5 × 128` rotation slots, 5 binary siblings), then the 168 level-10 nodes
  (5,376 bytes): `816 · 128 + 5376 = 109,824` bytes.
- Commitment: 472,491,696 cycles, 39,280,826 calls. Opener: 480 cycles per record plus 1,421, **67,115**.
- Checker: donor with 14 levels on 1,816-byte records; wrapper words 464-3478; `816(k + 6) + 480`;
  43 hash calls for levels 11-13; 547 words cleared. At most `16k + 43` calls (`k = 1`: 59).

# 5-ary levels above the table, four 5-ary levels below (102,976 proof bytes)

`17a1ef1d` (levels 0-3 5-ary, binary above, table at level 13) with every level from the table up
5-ary again (`PENTA_HIGH = 11`): `radix k = 5` for `k < 4` or `k ≥ 11`, else 2. 15 levels
(`3355444, 671089, 134218, 26844, …, 420, 210, 42, 9, 2, 1`), root = node 0 of level 15. The table
moves from level 13 (53 nodes) to level 11 (210 nodes) within the 100-call budget of one position.

- Proof: per position a 752-byte record (salt, `4 × 128` rotation slots, 7 binary siblings for
  levels 4-10), then the 210 level-11 nodes (6,720 bytes): `752 · 128 + 6720 = 102,976` bytes.
- Commitment: 472,652,448 cycles (level passes 11-14 write 5-ary groups; root at level 15).
- Opener: 443 cycles per record plus 1,773, **62,731** cycles at 128 positions (42 full table groups).
- Checker: donor runs 15 levels on 1,944-byte records (`x29 = 15`, `x6 = 1944`); the wrapper
  (words 464-4017) checks the length `752k + 6720`, copies the table into 5-ary scratch groups,
  makes 53 calls for levels 12-14, expands 243-word records and clears 691 words past them.
  At most `17k + 53` calls (`k = 1`: 70).

# Four 5-ary levels, then binary (106,144 proof bytes)

The hybrid tree with `PENTA_LOW = 4`: levels 0-3 are 5-ary, every level above is the binary penta
node `penta(0, 0, 0, c₀, c₁)`; 19 levels (`3355444, 671089, 134218, 26844, …, 2, 1` nodes).

- Proof: per position an 816-byte record (salt, `4 × 128` rotation slots, 9 binary siblings for
  levels 4-12), then the 53 level-13 nodes (1,696 bytes): `816 · 128 + 1696 = 106,144` bytes.
- Commitment: 472,654,062 cycles (fewer binary nodes than with two or three 5-ary levels).
- Opener: 481 cycles per record plus 487, **66,309** cycles at 128 positions (26 full table groups
  and a half group for node 52).
- Checker: the donor runs 19 levels on 2,456-byte records (`x29 = 19`, `x6 = 2456`); the wrapper
  (words 464-2141) makes 55 calls for levels 14-19. At most `21k + 55` calls (`k = 1`: 76).
- Lean: the same modules as the two previous hybrid entries, re-parameterised
  (`PENTA_LOW`/`PENTA_LEVELS`/`CAP_LEVEL` = 4/19/13).

# Two 5-ary levels, then binary (93,472 proof bytes; previous entry)

The hybrid tree of the previous entry with `PENTA_LOW = 2`: levels 0 and 1 are 5-ary, every level
above is the binary penta node `penta(0, 0, 0, c₀, c₁)`. With 2^24 leaves there are 22 levels
(`3355444, 671089, 335545, 167773, …, 2, 1` nodes).

- Proof: per position a 720-byte record (salt, `2 × 128` rotation slots, 14 binary siblings for
  levels 2-15), then the 41 level-16 nodes (1,312 bytes): `720 · 128 + 1312 = 93,472` bytes.
- Commitment: 477,488,172 cycles (more binary nodes than with three 5-ary levels).
- Opener: 426 cycles per record plus 379, **59,161** cycles at 128 positions; the table copy has
  20 full groups and a half group for node 40.
- Checker: the donor runs 22 levels on 2,840-byte records (`x29 = 22` from the trampoline,
  `x6 = 2840`); the wrapper (words 464-2069) makes 44 calls for levels 17-22 and expands 355-word
  records. At most `24k + 44` calls (`k = 1`: 68).
- Lean: the same modules as the previous entry, re-parameterised (`HybWrapTable.table_half`,
  `TableDone`, level offsets, hash levels 17-22, `PENTA_LOW`/`PENTA_LEVELS`/`CAP_LEVEL` = 2/22/16).

# Hybrid tree: three 5-ary levels, then binary (98,368 proof bytes; previous entry)

The commitment tree changes shape. Levels `k < 3` stay 5-ary; every level above is binary, hashed
as the penta node `penta(0, 0, 0, c₀, c₁)` (children in slots 3 and 4), so the same permutation
domain separation and hiding argument apply. With 2^24 leaves there are 21 levels
(`3355444, 671089, 134218, 67109, …, 2, 1` nodes) and the root is node 0 of level 21.

- **Proof format** (`PentaCapSpec.capTranscriptBuilder`): per opened position, in ascending order,
  a 752-byte record (16-byte salt, the four other slots of each 5-ary group in rotation order
  `3 × 128`, then one 32-byte binary sibling for levels 3-13), then once the 66 level-14 nodes
  (2,112 bytes). At 128 positions: `752 · 128 + 2112 = 98,368` bytes. Levels 15-21 are recomputed
  by the checker.
- **Commitment**: 473,459,618 cycles (`PentaGroupedCommit.commit_resources`); the binary levels
  use the 368-byte group stride of the 5-ary levels, so every node is still one `ECALL`.
- **Opener** (words 527-1476): per record the salt, 12 rotation slots and 11 siblings are copied
  with doubleword loads/stores from the trapdoor (94 pairs, `QuadOpeningHyb`); then the 66-node
  table. Bound at 128 positions: **61,689** cycles (`PentaOpenFull.all_resources`).
- **Checker**: a new wrapper (check-image words 464-2369, `HybWrapCode`) in front of the unchanged
  donor checker, which now walks 21 levels on a virtual index whose base-5 digits are the hybrid
  slots (`virtIndex`; the donor's level counter and record stride are 21 and 2,712 bytes). The
  wrapper rejects any length other than `752k + 2112`, copies the table to scratch memory, makes the
  70 calls for levels 15-21, expands the records in place from last to first into donor records
  (salt, virtual index, 21 × 4 group slots; binary levels get their sibling in slot 3 or 4 and zeros
  elsewhere), clears 20 words past them, restores the loader registers and jumps to word 1. At most
  `25k + 70` calls (`k = 1`: 95 ≤ 100).
- **Lean**: the wrapper is verified instruction by instruction through the `CheckActions` kernel
  (new `alu` action): `HybWrapKit`/`HybWrapBlocks` (observed runs, copy/clear blocks),
  `HybWrapEntry` (empty, reject, entry), `HybWrapTable`, `HybWrapHash` (`HashInv`: slot words are
  `upNode`), `HybWrapLevel`/`HybWrapRecord` (one record, `RecMem` loop invariant), `HybWrapTail`
  (`wrap_positive`: `HeaderStart` for `expandInput` plus the memory frame). `HybWrapSpec` defines
  the expansion word by word and `HybWrapHonest.expand_honest` proves that expanding an honest
  compact proof gives exactly the donor's honest proof. `QuadCheckerObservation` assembles the
  checker facts; binding goes through the donor's accepted-trace argument unchanged.

# Full-group records copied through the permutation

The proof format changes: each record is the salt and, for levels `k = 0 … 6`, all five slots of the
record's level-`k` group (`16 + 7 · 160 = 1136` bytes), followed by the 215 level-7 slots as before
(`1136 k + 6880` bytes, 152,288 at 128 positions). With whole groups, every level is one contiguous
160-byte trapdoor range, so the opener copies it with `P` then `P⁻¹`:

- Record writer (opening words 11-105): setup (27 cycles), then per record the index and salt (7),
  seven forward blocks `DIVU x6, x6, 5; MUL x10, x6, 368; ADD x10, x10, base_k; ECALL; ADDI x12, 200`
  writing `P(group k)` into a 1,400-byte scratch area, three switch instructions, seven inverse blocks
  writing `P⁻¹(P(group k)) = group k` to `16 + 160 k` of the record, and the latch: 211 cycles and
  14 permutation calls per record (the old variant writer took 297 cycles).
- Footer: 42 of the 43 level-7 groups by `P`/`P⁻¹`, the last one by 20 load/store pairs, so that an
  opening of one position stays within its 100-call budget (`1 + 14 + 84 = 99`): 898 cycles, 84 calls.
- Opening bound at 128 positions: 29 + 4,225 + 27 + 211 · 128 + 898 = **32,187** cycles.
- Checker: the wrapper's record step (offset 115) now jumps to a body at offsets 3470-4465 that doubles
  the seven groups into scratch memory, copies the salt, writes the four other slots of each level in
  rotation order (`32 (d + 1)` into the doubled group, `d` the record's digit), clears the scratch and
  returns; the rest of the wrapper (table doubling, levels 8-10 hash phase, top-level fills, donor
  checker) is unchanged apart from the 1136-byte stride. Hiding uses the new `capTranscriptBuilder`
  (its record reads only penta nodes, so it is local); binding and completeness go through the
  unchanged donor checker.

# Level-7 table through the permutation

The opener's footer (words 527-799) copies the 43 level-7 groups with `P⁻¹ ∘ P`: 43 forward calls
write `P(group g)` into a scratch area 8,192 bytes past the table start, then 43 inverse calls write
`P⁻¹(P(group g)) = group g` to the table at `160 g`. Each 200-byte reply also covers the next 40 bytes,
which the following group overwrites. Footer: 274 steps, 876 cycles (was 1,812), 86 calls. Opening bound
at 128 positions: 29 + 4,225 + 297 * 128 + 23 + 876 = **43,169** cycles; proof bytes, records, checker and
commitment unchanged. Lean: `QuadOpeningFooter` (`fwdTrace`/`invTrace`, `footer_exec`, `footer_fixed`,
`footer_output`, `footer_length_reg`), `QuadOpeningABI.body_from_record_at`, `PentaOpenFull`.

# Inlined group heads

Each pair variant now ends with the next group's head (`pairPrep 1` after pair 0, `triplePrep` after
pair 1) and its `JALR`, instead of a `JAL` back to the head at words 59/77 (now dead). A pair costs
83 cycles (74 steps), a record 297 cycles. Opening bound at 128 positions:
29 + 4,225 + 297 * 128 + 1,835 = **44,105** cycles. `LevelAt` takes the head's word as a parameter;
`pair_level_step` and `triple_level_step` take the head's location and code facts as hypotheses.

# Salt pass: end-pointer latch and a shorter salt-offset select

The opener's salt-materializing loop (now words 505-525) ends each position with
`addi x14, x14, 8; bne x14, x17, <loop>` against an end pointer `x17 = indices + 8 k` computed once
in the header (`slli x17, x18, 3; add x17, x17, x8`, one more header word, so the header is 29
cycles), instead of decrementing a counter. The salt source is selected as
`x7 = 16 rank (+ 200 if rank = 0) + 1536` and loaded at `x7 - 16`, `x7 - 8`, which takes four
instructions instead of five. Each position costs 2 cycles less (at most 20 steps and 33 cycles
plus the final jump), so at 128 positions the pass costs at most 4,225 cycles (was 4,481). Opening
bound: 29 + 4,225 + 40,107 = **44,361** cycles; proof bytes, checker and commitment unchanged.
Changed modules: `PentaOpenLoop` (rows, `selAt`, `sel_lo`/`sel_hi`, end-pointer `next_ok`),
`PentaOpenHeader`, `PentaOpenPass`, `PentaOpenEffect`, `PentaOpenFull`.

# Grouped record levels: pairs (0,1), (2,3) and the triple (4,5,6)

The opener's record writer no longer divides by 5 at every level. Levels `(0,1)` and `(2,3)` are
handled as pairs and levels `(4,5,6)` as one triple; the proof format, the checker and the
commitment are unchanged (every emitted byte is the same).

- **Pair head** `p` (words `41 + 18p`): `REMU x25, x6, 25; DIVU x6, x6, 25; MUL x10, x6, 368`,
  `x11 = base(2p+1) + 368 Q`, `x30 = base(2p) + 1840 Q`, `x7 = 512 (x6 % 25) + table(p)`, `JALR`.
  Variant `v = 5 r1 + r0` (words `6144 + 4096 p + 128 v`) copies the four level-`2p` siblings of child
  `r0` from `x30 + 368 r1` and the four level-`2p+1` siblings of child `r1` from `x11`, then jumps on.
  A pair costs 84 cycles instead of 2 x 48.
- **Triple head** (words 77-89): `REMU x25, x6, 125; DIVU x24, x6, 125; MUL x10, x24, 368`,
  `x27 = base 6 + 368 Q`, `x11 = base 5 + 1840 Q`, `x30 = base 4 + 9200 Q`, `JALR` into variant
  `v = x6 % 125` (words `14336 + 128 v`). The variant first adds `4096 * tripleHi v` to `x30`
  (`LUI x10; ADD`) so that every level-4 load offset `368 (v/5) + vo` fits a signed 12-bit immediate,
  then copies levels 4, 5 and 6 (48 load/store pairs), advances `x21` by 912 and jumps to the latch.
  A triple costs 122 cycles instead of 84 + 49.
- Registers: `x5, x17, x20` hold the variant tables, `x26 = 25`, `x28 = 125` (loaded once at words
  25-31). The old single-level code and variants are left in the image but are no longer executed.

A record costs 299 cycles (was 346). At 128 positions the certified bounds are 472,452,327 commitment
cycles, **44,616** opening cycles (was 50,632) and 123,616 proof bytes. The opening image has 30,336
words. New Lean modules: `QuadOpeningPair` (generalized copy blocks `genPairs`/`gen_block` with
arbitrary register base and wrapped 12-bit offsets, `pair_level_step`) and `QuadOpeningTriple`
(`triple_level_step`); `QuadOpeningLevels` composes them. `quad_opening_image` now compares the
delivered image by `decide +kernel` on the code list.

# Level-7-only cap table: the checker recomputes levels 8-10

The proof is the 912-byte records followed by the 215 level-7 slots only (`912k + 6880` bytes,
123,616 at 128 positions). The check wrapper copies the 43 level-7 groups into its doubled scratch
table, then a hash phase (check words 775-3929) recomputes the 54 nodes of levels 8, 9 and 10 with the
permutation (40 zero bytes, then the five children, low 256 bits of the reply), restores its scratch
memory and registers, and continues with the unchanged record expansion and donor checker. The
opener copies only level 7 and exits at word 2334. At 128 positions: 472,452,327 commitment cycles,
50,632 opening cycles, 123,616 proof bytes. See `PentaWrapHash`, `PentaWrapExtend`, `PentaWrapHonest`.

# Level-specialized copy variants, alternating node registers, end-pointer latch

The record writer has 35 copy variants (one per level `k = 0..6` and rank `r = 0..4`) at words
3072-5311, after the table copy and 251 padding words. Variant `(k, r)` stores at fixed offsets
`16 + 128k + 8m` from the record start and ends with `jal` to the next level (the level-6 variants
first advance `x21` by 912 bytes). The levels jump in with `jalr x0` through seven table registers
(`x5, x17, x20, x26, x27, x28, x29` = `16384 + 1280k`, loaded once at words 25-31) and alternate
the node register between `x6` and `x24`. Words 32-33 turn `x18` into the end of the index buffer
and the latch is `addi x8, x8, 8; bne x8, x18, <record>`. A record costs 346 cycles (b2a0e62d: 375).
At 128 positions the bounds are 472,452,327 commitment cycles, 51,115 opening cycles and 125,440
proof bytes. Every emitted proof byte is unchanged.

# Level-specialized copy variants and alternating node registers

The record writer now has 35 copy variants (one per level `k = 0..6` and rank `r = 0..4`) appended
after the table copy at words 2821-5060. Variant `(k, r)` stores at fixed offsets `16 + 128k + 8m`
from the record start and ends with `jal` to the next level (the level-6 variants first advance
`x21` by 912 bytes). The levels jump in with `jalr x0` through seven table registers
(`x5, x17, x20, x26, x27, x28, x29` = `15380 + 1280k`, loaded once at words 25-32), and alternate
the node register between `x6` and `x24`. This removes the per-level `addi x21, x21, 128`, the
per-level `addi x6, x24, 0` and the salt `addi`, so a record costs 347 cycles (was 361). At
128 positions the bounds are 472,452,327 commitment cycles, 51,242 opening cycles and 125,440
proof bytes. Every emitted proof byte is unchanged.

# Preloaded level bases in the record writer

The seven per-level group bases (`trapdoor + pentaGroupBase k + 40`, k = 0..6) are loaded once into
`x2, x3, x4, x12, x13, x14, x16` at the formerly dead words 11-24. Each record level head then uses
`add x30, x10, baseReg k` instead of `lui x11, page; add x11, x11, x9; add x30, x10, x11`, two cycles
less per level. A record costs 361 cycles (was 375); the record loop starts at word 25 and every
address from the latch (103) onwards is unchanged. At 128 positions the bounds are 472,452,327
commitment cycles, 53,026 opening cycles (was 54,804) and 125,440 proof bytes. Proof format,
checker and commitment are inherited from `b2a0e62d`.

# Copy only the two occupied slots of the root group

The proof still omits the three root padding slots. This opener also omits
their loads and stores. The root group copies eight doublewords, then advances
the cursor by 64 bytes. All earlier groups use their original 20 doublewords.

At 128 positions, the bounds are 472,452,327 commitment cycles, 54,804 opening
cycles, and 125,440 proof bytes. The proof format and the checker are inherited
from the preceding short-cap variant.

## Inherited short-cap format

With 16,777,216 leaves, level 10 has two real digests. Its five-slot table group
therefore ends with three zero digests. The opener reports a length that excludes
those 96 bytes, and the checker accepts the shorter length. The checker's
loader supplies zeros beyond the proof, so its table copy and record expansion
still reconstruct the same reference paths. The certificate proves the padding
identity for every honest set of positions.

At 128 positions the proof has 125,440 bytes. The certified commitment and
opening bounds are 472,452,327 and 54,828 cycles, respectively. The cap format
retains the source pointer optimization and all of the other table and record
execution from the preceding entry. The final group still copies all five slots
into memory. Its destination cursor advances only by the 64 bytes reported in
the proof.

## Inherited pointer schedule

This entry builds on `6f7af826-0a98-4c80-811a-0808e9204019`.
Each of the four cap-table levels initializes its own source pointer, so the final
group in each level skips the source increment. All groups still advance the
output pointer and copy the same 20 doublewords. The commitment and checker
images, proof bytes, and ABI are inherited.

The certified bounds are 472,452,327 commitment cycles and 54,828 opening cycles
at 125,536 proof bytes. The opener deletes four instructions from the previous
2,849-word image. The following sections describe the inherited format and its
original cycle accounting.

## Inherited entry: One table for the top four levels of 865ff261's proof: 472,507,159 cycles at 125,536 bytes

This entry is steph4n-gh's accepted Pareto entry `865ff261` with a smaller proof format. Each 1,424-byte record of the base carries a salt and four siblings at each of the eleven levels of its 5-ary tree. At the top of the tree there are few distinct nodes: levels 7 to 10 have 275 slots in all (215 + 45 + 10 + 5, ragged zero slots included), yet 128 records carry 65,536 bytes of siblings there. Here each record stops at level 6, and one table with every slot of levels 7 to 10 follows the records. The check image starts with a wrapper that rebuilds the base's records from the records and the table, then runs the base's checker unchanged. The commitment image and the salts are unchanged.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes |
| --- | ---: | ---: | ---: | ---: |
| `865ff261` by steph4n-gh (base) | 472,452,327 | 77,601 | 472,529,928 | 182,272 |
| This entry | 472,452,327 | 54,832 | 472,507,159 | 125,536 |

`claim.json` is `{"proofBytes": 125536, "commitCycles": 472452327, "openingCycles": 54832}`.

## Proof format

- Records: for each opened position in ascending order, the base record's first 912 bytes (the salt and the four siblings at each of levels 0 to 6, in the base's rotation order).
- Table, after the records: every slot of levels 7, 8, 9 and 10 in trapdoor order, as 55 groups of five 32-byte slots, ragged zero slots included. It is the same for every set of positions.
- Length `912k + 8,800` for k ≥ 1 positions and 0 for the empty opening: 125,536 bytes at k = 128, against `1,424k` for the base.

## Images

- Opening, 2,849 words: the record loop keeps the base's code up to level 6 (words 0–102) and gets a new latch (words 103–105). Word 106 jumps to an appended copy of the table (words 527–2,848), which ends with the base's exit sequence. Words 107–147, which wrote levels 7 to 10, are now no-ops; words 148–526 are unchanged.
- Check, 775 words: word 0 jumps to the wrapper at words 460–774; words 1–459 are the base's checker. The wrapper rejects any length other than `912k + 8,800` (k = 0: empty), parks the table in scratch memory, expands the records from the last one down into the base's 1,424-byte layout, clears the leftover bytes, restores the loader's registers and jumps to word 1. It makes no oracle calls. Check fuel is `2^40` steps; the wrapper needs at most `851k + 5,000`.
- Commitment: byte-identical to the base's.

## Security

- Binding: the base's binding theorem uses the oracle calls of an accepting check run (`PentaAcceptedTrace`), not the proof bytes. The wrapper makes no oracle calls and keeps the commitment, positions and values, so an accepting run on this format is an accepting run of the base checker on the expanded proof.
- Hiding: the base's hiding theorem (`penta_counter_hiding_of_transcript`) holds for any transcript builder that is local in its sense (`PentaBuildLocal`). The new builder (`capTranscriptBuilder`), which also outputs the level 7–10 table, is proved local (`cap_transcript_builder_local`): its proof part reads only nodes of levels up to 10, and the commitment remains the level-11 root.

## Lean changes

New modules: `PentaCapSpec`, `PentaCapRoundtrip`, `PentaCapFacts`, `PentaWrapCode`, `PentaWrapMemory`, `PentaWrapLoader`, `PentaWrapTable`, `PentaWrapRecord`, `PentaWrapRunA`, `PentaWrapRunB`, `PentaWrapRunC`, `PentaWrapCheckImage`, `QuadOpeningFooter`. Changed base modules: `QuadCommitImage` (check fuel), `QuadCheckImage`, `QuadCheckLoader`, `QuadCheckerMeasure`, `QuadHeaderAssembly`, `QuadCheckerObservation`, `QuadCheckerComplete`, `QuadOpeningImage`, `QuadOpeningLevel`, `QuadOpeningLevels`, `QuadOpeningRecord`, `QuadOpeningABI`, `QuadOpeningModel`, `QuadOpeningProofBytes`, `PentaOpenFull`, `PentaCounterCertificate`, and `Solution.lean`. The 28 base modules that nothing reachable from `Solution.lean` imports are not included.

## Credits

- Base: `865ff261-6a95-400c-a4cd-5dee6b1e699e` by steph4n-gh, which joins valproate-acid's 5-ary tree, record writer and checker (`f5ae28bd-8f22-4693-9071-c777c40e2419`) with mitchuski's counter-mode salts (`076b6f1a-c099-4993-8b98-fc3b92c112a3`). The record writer and checker this entry changes are valproate-acid's.
- steph4n-gh's note lists "pruned top caps on the 5-ary tree" as a next step; this entry is one such cap.
- The base's README follows unchanged. Its figures describe the base, not this entry.

---

# 5-ary Penta Permutation Tree with 4,095-Leaf Counter-Mode In-Place Salts

This Pareto-track candidate combines:

1. **5-ary (penta) permutation tree, record writer, and checker** from accepted submission
   `f5ae28bd-8f22-4693-9071-c777c40e2419` (commit `966f29e9b709833d23f67ffc27a4124b7a672628`),
   preserving levels 1..10, the root node, the 1424-byte proof record format, and the 460-word
   checker image verbatim.
2. **Counter-mode in-place salt generation with register prefetching** adapted from accepted
   submission `076b6f1a-c099-4993-8b98-fc3b92c112a3` (commit `fda8496ea3b71ba2a364c5ec8679fe18983b7580`),
   eliminating the upfront 15.26M-cycle `NonceChain` tape pass and all per-leaf salt tape loads.

## Key Design Changes

- **4,095-leaf counter-mode loop period (`1 + 4097 * 4095 = 2^24`)**:
  Each pass of the unrolled commit leaf body processes `4,095 = 91 * 45 = 372 * 11 + 3` leaves
  (`372` full 11-leaf salt groups with 4-word register prefetch into `x14..x17` for ranks `9` and `10`,
  plus one short 3-leaf group at slots `4092..4094`). Every 45 leaves (9 penta groups),
  `ADDI x20, x12, 1776` rebases the centered 12-bit destination window directly from `x12`.
- **Trailing final leaf (`i = 2^24 - 1 = 4097 * 4095`)**:
  Placed after the loop latch (words `45,190..45,200`) as a standalone 1-leaf counter-mode group,
  so `rank(i) = (i % 4095) % 11` has no index-shift special case across all `2^24` leaves and
  leaves `x12 = wordAddress (leafWord (2^24 - 1))` directly ready for `leafZeroWords` at word `45,201`.
- **On-the-fly salt materialization in the opener (48 appended words, 527 words total)**:
  On non-empty openings, word `2` jumps to word `479`, executes the displaced setup, copies the
  24-byte key from `nonceBase + 8..24` into scratch `1032..1048`, regenerates each opened leaf's
  16-byte salt via `P(4096 + 256 * (i - rank(i)) || key || 0)` into `nonceBase + 16 * i`, and
  jumps to word `11` to run the unchanged penta record loop and exit.

## Resource Comparison

| Metric | Prior lowest-cycle frontier (`f5ae28bd`) | This submission | Delta |
|---|---:|---:|---:|
| Commit cycles | 477,082,487 | **472,452,327** | **-4,630,160** |
| Opening cycles (128 positions) | 73,103 | **77,601** | +4,498 |
| Total prover cycles | 477,155,590 | **472,529,928** | **-4,625,662** |
| Opening proof bytes | 182,272 | **182,272** | 0 |

## Lean Proof Architecture (`CommitGolfCandidate/`)

- **Counter-mode security**: `CounterSaltLayout.lean` (4,095-leaf period, `groups = 1,528,182`),
  `CounterSalt{Replay,Game,Oracle,Windows}.lean`, and `PentaCounterSecurity.lean` proving
  120-bit statistical hiding (`penta_counter_hiding`).
- **Commit machine proof**: `PentaGrouped{Base,Decode,CommitImage,Packet,PacketRun,Scan,Eval,Content,Frame,Invariant,KeySetup,Commit}.lean`
  proving exact commit execution (197,513,870 steps, 39,276,922 oracle calls, 472,452,327 cycles)
  and handing off directly to the unchanged `QuadCommitPenta{Pass,Level,Layouts,Content,Root}` and
  `QuadCommit{Execution,Meaning}` modules at word `45,201`.
- **Opening machine proof**: `QuadOpeningImage.lean` (527 words), `QuadOpeningABI.lean`
  (`body_from_record_at`), and `PentaOpen{Loop,Effect,Pass,Header,Full}.lean` proving exact
  opening execution (`≤ 77,601` cycles, `128` oracle calls, `182,272` proof bytes) and virtual
  trapdoor equivalence to the honest penta transcript.
- **Certificate assembly**: `PentaCounterCertificate.lean` and `Solution.lean` proving
  `CommitGolf.Certificate submission 182272 472452327 77601` and `submission_matches_artifact`.
