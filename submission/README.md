# Product: shifted 32-byte copies

Stacked on `9b3cd204` (`devin/copy30`). The four 32-byte writer sites use
aligned dword loads and shifted halfword/word stores when the destination is
2 mod 4. The alignment dispatch branches directly into the site's old copy slots.
The paths cost 14 cycles (8-aligned), 22 (4 mod 8), or 28 (2 mod 4),
instead of 12, 22, or 38. Across 128 records this saves **2,304 opening cycles**.
Proof serialization, commit/check images, embedded data, image lengths and ABI
are unchanged.

The certified claim is **504,594,887 commit cycles**, **128,437 opening cycles**
and **72,160 proof bytes**. Product:
**504,723,324 × 72,160 = 36,420,835,059,840**,
an improvement of **166,256,640** over the copy30/head certificate.

## Previous entry: common rebuilt-block destination

Stacked on the shifted-copy certificate (`e2f859f`). Compute `B_g` from the quartet index
already in `x28`, and set the inverse-call destination `B_g+512` before selecting parity.
Each parity arm now needs only two address selections. Fresh-quartet heads save one cycle
(36 even, 35 odd); repeated-quartet heads remain three cycles. This saves another **128**
worst-case opening cycles without changing serialized proof bytes, commit/check images,
embedded data, image lengths or ABI.

The certified claim is **504,594,887 commit cycles**, **130,741 opening cycles** and
**72,160 proof bytes**. Product: **504,725,628 × 72,160 = 36,421,001,316,480**, improving
by **9,236,480** over copy30 and **364,840,960** over `devin/next-trim`.

## Previous entry: shifted 30-byte copies

Stacked on `a2b726ec` (`devin/next-trim`). The 2-mod-4 path of the shared 30-byte writer
copy uses aligned dword loads, shifts and mixed-width stores instead of fifteen halfword
load/store pairs. Each slow copy falls from 34 to 27 cycles. Across 128 records, 704 such
copies save **4,928 opening cycles**, with identical proof serialization and length.
The added 23-word stub brings the opening image to **7,560 bytes**. Commit/check images,
embedded data and ABI are unchanged. The byte-copy refinement includes the final six-byte
chunk: the high two bytes of its aligned load are never stored.

Commit cycles remain **504,594,887**, opening falls to **130,869**, and proof bytes remain
**72,160**. Product: **504,725,756 × 72,160 = 36,421,010,552,960**, improving by **355,604,480**.

## Previous entry: double the level-21 loop span

Stacked on the two-cycle startup trim (`8fe651cd`, submitted as `bf616286`). Double the unrolled
level-21 compression body from 16,384 to 32,768 nodes, reducing its passes from 128 to 64 and
removing 128 latch instructions. Compression order, inputs, destinations, commitment, trapdoor,
opening/check images, ABI and proof encoding are unchanged. Later commit code is relocated by
49,152 words. The commit image is **1,047,880 bytes**, 696 bytes below the 1 MiB limit.

Commit cycles fall from **504,595,015** to **504,594,887**; opening remains **135,797** cycles
and the proof bound remains **72,160** bytes. The Product score is
**504,730,684 × 72,160 = 36,421,366,157,440**, an improvement of 9,236,480.

## Previous entry: two-cycle startup trim

Based on `a33961ff-408d-482b-88a2-fc4ff48b45d3`. Remove the dead initial commitment-pointer save
and compute the generator key-block address directly in its final register, eliminating a copy.
The prologue executes two fewer words; unreachable padding keeps every word from index 21 onward,
all later PCs, opening/check images, ABI and proof encoding unchanged.

Commit cycles fall from **504,595,017** to **504,595,015**. Opening remains **135,797** cycles
and the proof bound remains **72,160** bytes. The Product score is
**504,730,812 × 72,160 = 36,421,375,393,920**, an improvement of 144,320.

## Base entry: shorter special-rank salt selection

This candidate ports `552a6b9d` and replaces opener words 796..802 in place. Commit and checker images,
image lengths, ABI, proof encoding and all other opener words are unchanged.

```text
word  before                       after
796   addi x7,x28,-1                slli x7,x28,4
797   slli x7,x7,4                  beq x28,x23,+16
798   bne x28,x0,+8                 beq x28,x0,+16
799   addi x7,x7,16                 addi x7,x7,1520
800   bne x28,x23,+8                jal x0,+12
801   addi x7,x0,184                addi x7,x0,184
802   add x7,x7,x12                 add x7,x7,x12
```

At entry `x28` is the salt rank, `x23 = 1`, and `x12 = 1536`. Rank 0 branches to word 802 and
rank 1 branches to word 801; both paths take four selection instructions instead of six.
Ranks at least 2 form `16*rank + 1520 = 1536 + 16*(rank-1)` and jump over the special cases,
still taking five instructions. All paths reach word 803 with the same source address as before.

The maximum post cost falls from 15 to 14 cycles (plus the final exit jump), giving
`31 + (37 + 299 + 14)*128 + 1 + (90980 - 15) = 135797` opening cycles.
The claim is **504595017 commit cycles, 135797 opening cycles, 72160 proof bytes**;
the Pareto point is **[504730814, 72160]**, 128 cycles below the ported entry.

RV64IM differential emulation with identity permutation and zero compression gives byte-identical
proofs on empty, singleton, consecutive, random, and separated 128-position inputs, with zero and
patterned trapdoor fixtures. The zero fixtures' proofs are accepted by the unchanged checker.
For `131072*k + 363` (`k = 0..127`), cycles drop from 135925 to 135669. The new worst-case witness
`131072*k + 739` takes 135797 cycles with 72160 proof bytes. Emulation is a regression check;
the Lean certificate proves the bounds and correctness for every permitted oracle and honest input.

## Ported entry's lineage

# One opening step less per position: the rank→salt-offset map re-encoded in place

Built on the current master `74e3f693-ac71-48cc-81de-21897463800a` (Bome2017, public commit
`165be01526586c7a7a74416ff0a03b84d44377af`), which is `5d0c1c31` plus one shared 30-byte wide-copy stub
for writer levels 2..12 (rows 1062..1096; 1,867 opening words). This entry changes one 7-word block of
the opener and nothing else.

The master's own lineage, unchanged here: our odd-quartet entry `750657ae` (kaankolcu), itself kshitij-hash's
`cfad3d49-5038-4850-be68-98a1ee7d4f48` (public commit `34159694b89006446e2eaf6a3f7584fb47a73b04`) with the odd
quartet blocks moved 200 bytes below the even ones. Three changes on top (our `804b758d`):

- **Level-21 setup, 11 → 7 words** (the trim of patternrecognition9-del's `ffa6a198-899f-406b-818d-95dd3c9ea2b6`,
  public commit `10e21ee11e7e0b62972ab550d496b83f7444c080`, applied to this layout): the first level-21 input
  pointer is taken from `x24 = Q + 2^32`, which the body already holds, instead of rebuilding `Q + 2^32` from
  `x21`: `addi x7,x21,-1912; addi x10,x24,-1912`. The six post-body words move four words up so that they still run
  straight into it. −4 commit cycles.
- **Opener link chain, straight line** (the opener of patternrecognition9-del's `42ccb0c2-770b-47da-89be-0c846a629cb2`,
  public commit `40eb3d880edd79e4c2fea0241e790de5f8d28ed4`, withdrawn by its author before grading, on this tree): the `k = g mod 34` in-place generator links are a
  computed jump into 33 appended `ecall`s (opening rows 790–794 and 896–929). −7,936 on the certified worst set.
- **Word-wide record copies.** The four 32-byte halfword copies of each opening record (three sibling digests and the
  level-0 sibling, rows 43, 79, 115, 153) jump to stubs (rows 930–1061) that copy with
  `ld/sd` or `lw/sw` when the destination allows it. −2,304 on the certified worst set.

The master (on our `804b758d`, the tree above) changes only the opener, in two places:

- **374-based link counter** (pepedesigner's `ca54b35f-af11-4644-8031-a6d8b9e6fef6`, public commit
  `9d9b1e75ed5a76bc9185efb3ea9826a621d1423e`, taken over unchanged, image words and Lean): the per-position counter
  of the link chain uses three `mul/div` instead of five. −7 cycles per position, −896 on the certified worst set.
- **30-byte wide copies.** The eleven 30-byte halfword copies of writer levels 2..12 (rows 225, 260, …, 575) jump to
  one shared stub (rows 1062–1096; 1,097 opening words) that copies with `ld/sd`, `lw/sw` and a final `lhu/sh` when
  the destination allows it. −4,928 on the certified worst set.

## This entry: the rank→salt-offset map

The opener copies each position's 16-byte salt into the record at `x12 + off(rank)`, where
`off(0) = 0`, `off(1) = 184` and `off(r) = 16 (r-1)` for `r ≥ 2`. The map sits in the seven words
796..802 and was four instructions on the common path (rank ≥ 2), six for rank 0 and seven for rank 1:

```
796 addi x7,x28,-1   797 slli x7,x7,4   798 bltu x23,x28,+16
799 addi x7,x0,0     800 bne x28,x23,+8  801 addi x7,x0,184   802 add x7,x7,x12
```

Both words 798 and 799 are re-encoded in place, so the image length, every other word, every PC outside the
block and the phase layout are unchanged (the master's rank-map words are byte-identical to the ones this
trim was first built on):

```
796 addi x7,x28,-1   797 slli x7,x7,4   798 bne x28,x0,+8
799 addi x7,x7,16    800 bne x28,x23,+8  801 addi x7,x0,184   802 add x7,x7,x12
```

`x7` is `16 (r-1)` after 797; rank 0 falls through 798 and 799 adds 16 back (giving 0), rank ≥ 1 jumps over
799, and 800/801 keep rank 1 at 184 while rank ≥ 2 keeps `16 (r-1)`. The salt address is identical for every
rank (simulated for `r = 0..10`), so every record byte, proof byte and digest is unchanged; only the path
lengths move, from 4/6/7 to 5/6/6. The worst case is now rank 1 at 6 steps instead of 7, which is the only
rank-dependent term in the certified opening bound: `postSteps` becomes `13 + (2 for rank 0, 2 for rank 1,
1 for rank ≥ 2) + [last]` and the per-position cycle bound 352 → 351. The opening bound drops by 128 cycles:
`31 + (37 + 299 + 15)·128 + 1 + (90,980 − 15) = 135,925`.

Proofs: `GroupOpenWalk.selectRows` carries the new row list per rank class (including the word-800 branch for
rank ≥ 2); `GroupOpenSelect.choose_legal`/`chosen` re-prove the branch outcomes and `x7 = readAt i`, with
`rank_ne_zero`/`rank_ne_one` matching the post-`simp` `BitVec.ofNat` form; `GroupOpenLatch.postSteps`/
`post_length` re-count; `GroupOpenPass.pass_cycles_bound` is 351·n+1; `GroupOpenFull.per_steps_le`/
`pass_steps_bound` are 167·n; the claim sites (`GroupOpenClosing`, `GroupOpenFull.all_resources`,
`Solution.lean`, `claim.json`) carry 135,925.

## Result

| | `cfad3d49` | `750657ae` | `74e3f693` (master) | This entry |
| --- | ---: | ---: | ---: | ---: |
| proof bytes | 72,160 | 72,160 | 72,160 | 72,160 |
| commitment cycles | 506,688,062 | 504,595,021 | 504,595,017 | 504,595,017 |
| opening cycles (128 positions, proved bound) | 154,669 | 153,901 | 136,053 | **135,925** |
| score | 36,573,771,468,960 | 36,422,682,211,520 | 36,421,394,011,200 | **36,421,384,774,720** |

## The level-21 setup

`750657ae`'s six post-body words rebuild `x8` (commitment), `x21 = Q` and `x9` (trapdoor) and then run the 11-word
level-21 setup, which built `x10 = Q + 2^32 + 136 − 2048` from `x21` with `1 << 32`. The body already holds
`x24 = Q + 2^32` (the key-block counter base), so the setup becomes `addi a1,zero,64; addi a3,zero,0;
addi t2,s5,-1912; addi a0,s8,-1912; lui a2,0x8000; add a2,a2,s1; addi a2,a2,-32` (words 45,666..45,672). The post
words move to 45,660..45,665 (the latch jump now targets 45,660; 45,656..45,659 are never executed). `TailEntry`
gains `x24 = Q + 2^32`; the tail is 14,942,749 steps and 44,302,870 cycles.

## The link chain (opener)

`750657ae`'s opener runs the `k = g mod 34` salt links of a position as a loop, `ecall; addi t5,t5,-1; bne` per link.
Here rows 790–794 compute a jump into a run of 33 appended `ecall`s (rows 896–928) so that exactly `k` of them run,
and row 929 jumps back to row 795: `addi, slli, auipc, sub, jalr` to row `929 − k`. Each call has the same arguments
and comes in the same order, so calls, memory and proofs are unchanged. Per position the chain costs `42 + 8k`
cycles for `k ≤ 33` links (306 at the worst case `k = 33`, against 368).

## The 374-based link counter (opener)

pepedesigner's change (`ca54b35f`), unchanged here. Rows 777–788 of `804b758d` computed the position's salt offset
and its link count `k = (g mod 4096)/11 mod 34` with `remu, divu, remu, remu, mul` (20 cycles). Rows 777–793 now take
`r = (g mod 4096) mod 374` (`slli/srli` by 52 and one `remu` by 374 = 34·11), then `k = r/11` and `g mod 11 = r mod 11`,
and subtract `r` in one step; the jump into the call run is rebuilt at row 793 (row 794 is no longer reached). Per
position the chain costs `35 + 8k` cycles (299 at `k = 33`, against 306).

## Word-wide record copies (opener)

Each opening record copies four 32-byte fields with 16 `lhu/sh` pairs (32 cycles). The four sites now `jal x29` to a
33-word stub that tests the destination `x21 & 7`: 8-aligned, four `ld/sd` and `jalr 124(x29)` (12 cycles);
4-aligned, eight `lw/sw` (22 cycles); 2-aligned, the first `lhu/sh` and a return into the site's own pairs 1..15 (38
cycles). Record `o`'s destinations are `≡ 6o (mod 8)`, so a record costs `673 − 80, + 24, − 40, + 24` cycles for
`o mod 4 = 0..3`; the writer term over 128 records goes from 99,996 to 97,692. Proof bytes are unchanged.

## 30-byte wide copies (opener)

Writer levels 2..12 copy a 30-byte heap node from `x7` (32-byte aligned) to `0(x21)` with 15 `lhu/sh` pairs (30
cycles), followed by `addi x21,x21,30`. The first word of each of these eleven sites is now `jal x29,<1062>`, into one
shared 35-word stub:

```
1062  andi t6,s5,3 ; beq t6,zero,+16      destination 2 mod 4:
1064  lhu/sh 0 ; jalr zero,4(t4)          first halfword, back to the site's pairs 1..14       34 cycles
1067  andi t6,s5,7 ; beq t6,zero,+72      destination 4 mod 8:
1069  7 x lw/sw 0..24, lhu/sh 28, jalr zero,116(t4)   back to the site's addi            22 cycles
1086  3 x ld/sd 0..16, lw/sw 24, lhu/sh 28, jalr zero,116(t4)   (destination 0 mod 8)   16 cycles
```

Level `l` of record `o` starts at `proofBase + 534o + 176 + 30(l−2) ≡ 6o + 6(l−2) (mod 8)`, so a record's eleven
copies cost 284, 302, 284 and 296 cycles for `o mod 4 = 0..3`, against 330. `x29` and `x31` are dead at these sites
(`x29` already carries the 32-byte stubs' return address; the counter's divisor in `x29` is set before the position
pass and the writer runs after it). Proof bytes are unchanged.

## The odd-quartet layout (as in `750657ae`)

In cfad3d49 each quartet's permutation call runs right after its fourth leaf. The even quartet `2u` writes its
200-byte reply from that leaf's output pointer `a2` over its own block, and the odd quartet `2u+1`, whose block is
1,024 bytes higher, first spends `addi a2,a0,-656` so that its reply lands next to the even one and the two kept
32-byte nodes abut as the level-21 input.

Here the odd block sits **200 bytes below** the even block of its octet (`Be` = even block start):

```
odd reply   O = P(0^72 | d0..d3 of quartet 2u+1)   at [Be-32,  Be+168)   node_odd  = O[168..200)  at Be+136
even reply  E = P(0^72 | d0..d3 of quartet 2u)     at [Be+168, Be+368)   node_even = E[0..32)     at Be+168
level-21 input of unit u                           at [Be+136, Be+200)   = node_odd | node_even
```

Both quartets now write their reply from `a2` as left by their fourth leaf, so the odd rebase is gone: −512 words
and −512 cycles per 4,096-leaf tile, −2,097,152 cycles in all.

- **Commit.** Ten new constants (the four odd slot gaps and four odd A-slot gaps, 1,224 bytes below the even ones,
  and the two odd advance registers) take `s0..s3`, `s5`, `s6`, `tp`, `t2`, `t6` and `t1`. `t6` is freed by moving
  the 10,424 salt-copy temporaries to `a2` (dead there); `t1` is freed by making the tile latch absolute:
  `srli a2,a0,32; bne a2,zero,exit` (one extra word per tile, +4,096 cycles). The pre-loop setup grows by nine
  words and six words after the body rebuild the commitment, `Q` and trapdoor registers the upper stage reads; the
  level-21 pass starts at `Be + 136`. Net −2,093,041 cycles against cfad3d49 (504,595,021 in `750657ae`; here
  504,595,017 cycles, 200,299,085 steps), 43,470,847 oracle calls (unchanged), 212,818 words.
- **Tree.** The heap leaves are permuted, `heap(2^22 + g) = node(g xor 1)`, so the level-21 parent of groups `2k`,
  `2k+1` is `C(node(2k+1) | node(2k))` in the generic "right child high" form; even groups keep reply bytes 0..32,
  odd groups bytes 168..200. Levels 21 and up are unchanged.
- **Opening (every word index kept).** Every leaf digest is read from the inverse-rebuilt block at
  `Q + 512 + 1024 g` (words 42, 78, 114), never from the original slots (the replies overwrite them). The prefix rows
  747..764 make one `P⁻¹` call per newly opened quartet: even, `P⁻¹(E)` to `Be + 512` with sibling `node_odd`; odd,
  `P⁻¹(O)` to `Be + 1536` with sibling `node_even`. Proof bytes are identical to cfad3d49's for every position set.
- **Check (in place).** Words 489..490 become `xori t1,t1,4; jal 567`: the quartet reply slice flips with the group
  parity and the first combine uses the flipped leaf index. One more check step per position.

## Bounds

- Commitment: exact, 504,595,017 cycles (Lean: `GroupedChecks.resources`; `budget_q` and a full-size RV64IM
  emulation give the same number and the same commitment as `750657ae`).
- Opening: at most 135,925 cycles for 128 positions, `31 + (37 + 299 + 15)·128 + 1 + (90,980 − 15)` (the
  master's per-term bound with the rank map at 15 instead of 16 cycles per position; the writer term is 90,980
  with the 32- and 30-byte wide copies, each record costing `215 + 4·c32(o) + c30(o)`).
  A full-size RV64IM emulation against `804b758d`'s opener, on the certified worst set and on positions 0..127 for
  1..9, 13, 64, 127 and 128 positions, gives exactly `−7 − 46, −7 − 28, −7 − 46, −7 − 34` cycles per record for
  `o mod 4 = 0..3` (worst set, 128 positions: 143,661 → 137,837), byte-identical proofs, honest acceptance and every
  tamper rejected.
- Proof: 72,160 bytes, unchanged.

## What is proved

`Solution.lean` states `Certificate submission 72160 504595017 135925`. As in cfad3d49 it rests on the checker
facts (termination, query budget, binding, honest acceptance), the linked hiding hybrid, the exact commit run, the
opening resource bound and the opened-proof correspondence; here every statement that mentions the quartet layout
or the heap leaf order is re-proved for the new images. `#print axioms CommitGolf.Challenge.certificate` shows only
`propext`, `Classical.choice`, `Quot.sound`.

## Provenance and credits

The master `74e3f693` is Bome2017's (public commit `165be01`); the 30-byte shared stub for writer levels
2..12 and its proofs (`GroupOpenWideCopy30` and cost plumbing) are Bome2017's. Below it the tree is
kshitij-hash's `cfad3d49-5038-4850-be68-98a1ee7d4f48` and, through it, its lineage as credited in that
entry: kaankolcu `606a7986-afd0-4f91-84b4-6c11f779c9d1`, `bc5cc89e-4952-4ff7-be8d-9d11905d730c`,
`c08b0128-14a7-48dd-a745-070c3a77d754`, `b64a994e-6d0b-46e0-8c37-b6e642e3828a`, `33bdbed6-b605-43fc-b808-348ea3c87e3b`,
`4dbc847a-414f-41f2-854d-79e6c80f26fc`; dadon `2b2405a1-5be9-4681-b48e-a0fcefd4588d`,
`20182e74-9879-4c56-a5d1-7a65b83f03aa`, `c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492`; i34-9
`95bf06c1-0ec6-4bf5-b6cc-6b6315f204be`. The odd-block placement, the register reallocation, the absolute latch, the
image builder and the re-proofs of the layout-dependent modules are ours (`750657ae`). The level-21 setup trim is
patternrecognition9-del's `ffa6a198-899f-406b-818d-95dd3c9ea2b6` (public commit
`10e21ee11e7e0b62972ab550d496b83f7444c080`), re-derived for this layout; no file of it is used. The straight-line link chain
is the opener of patternrecognition9-del's `42ccb0c2-770b-47da-89be-0c846a629cb2` (public commit
`40eb3d880edd79e4c2fea0241e790de5f8d28ed4`; withdrawn before grading), re-proved on this tree; its proof modules here
are ours. The word-wide copy stubs and their proofs are ours (`804b758d`).

The 374-based link counter is pepedesigner's `ca54b35f-af11-4644-8031-a6d8b9e6fef6` (public commit
`9d9b1e75ed5a76bc9185efb3ea9826a621d1423e`). Its opening words 777–793 and its Lean files `K3OpenChainRows`,
`K3OpenChainLink`, `K3OpenChainRun`, `K3OpenChainPost`, `K3OpenChainExit`, `K3OpenChainReply` and `GroupOpenPass` are
used here unchanged, and its `packed_fetch_base_any` lemma is kept in `GroupOpenImage` (stated as there, for rows
below 1062). The 30-byte copy stub, its image builder and its proofs (`GroupOpenWideCopy30` and the cost plumbing) are
ours.

Relative to our `804b758d`, these files of `CommitGolfCandidate/` differ (one new, `GroupOpenWideCopy30`):

- image and manifest: `K1Manifest` (re-rendered from `programs.json`), `GroupOpenImage` (1,097-word literal, the
  `CopySite.wide30` sites, fetch bounds);
- the counter (pepedesigner's files, unchanged): `K3OpenChainRows`, `K3OpenChainLink`, `K3OpenChainRun`,
  `K3OpenChainPost`, `K3OpenChainExit`, `K3OpenChainReply`, `GroupOpenPass`;
- the 30-byte copies: `GroupOpenWideCopy30` (new), `GroupOpenWideCopy` (fetch bounds raised to 1,097 words),
  `GroupOpenCopy`, `GroupOpenSiblingRun`, `GroupOpenUpperRun`, `GroupOpenRecordData`, `GroupOpenRecordRun`,
  `GroupOpenRecordsAPI`, `GroupOpenABI`;
- the claim: `GroupOpenFull`, `GroupOpenClosing`.

`804b758d` itself differs from cfad3d49 in these files (two new, `K3OpenReply` and `GroupOpenWideCopy`):

- images and manifests: `K1Manifest`, `GroupedUpperImage`, `TwoPermutationPackedImage`;
- commit body and setup: `GroupedImageBase`, `GroupedCommitImage`, `GroupedPacket`, `GroupedPacketRun`, `GroupedScan`,
  `GroupedContent`, `GroupedFrame`, `GroupedInvariant`, `GroupedSetup`, `GroupedSeed`, `GroupedSeededLeaves`,
  `QuartetCommitRanges`, `QuartetCommitInput`, `QuartetCommitUpperMeaning`, `K3CBDefs`, `K3CBQuad`;
- upper stage and totals: `GroupedQImage`, `GroupedQMeaning`, `GroupedTailEval`, `GroupedCommit`, `GroupedChecks`,
  `K3CUUnits`;
- tree and physical bridge: `K3GQModel`, `QuartetConcrete`, `QuadReplay`, `QuadBinding`, `QuartetWordBridge`,
  `QuartetPhysicalInputs`, `K3CUSerial`, `GroupedPhysical`;
- checker: `QuartetCheckBlock`, `QuartetCheckBlockCode`, `QuartetCheckHeap`, `TwoPermutationPackedCheckRecordData`,
  `TwoPermutationPackedCollectTable`, `TwoPermutationPackedHonestInput`, `TwoPermutationPackedHonestSibling`,
  `TwoPermutationPackedLeafAdapter`, `TwoPermutationPackedLeafComplete`, `TwoPermutationPackedRecordComposition`,
  `TwoPermutationPackedRecordLeafPhysical`;
- opener: `GroupOpenClosing`, `GroupOpenEffect`, `GroupOpenFixed`, `GroupOpenFull`, `GroupOpenImage`, `GroupOpenLatch`,
  `GroupOpenLeafFields`, `GroupOpenMemory`, `GroupOpenModel`, `GroupOpenPass`, `GroupOpenResume`, `GroupOpenStep`,
  `GroupOpenWalk`, `K3GRBridge`, `K3OpenFacts`, `K3OpenReply` (new), `K3OpenChainRows`, `K3OpenChainLink`,
  `K3OpenChainRun`, `K3OpenChainPost`, `K3OpenChainExit`, `K3OpenChainReply`, `GroupOpenABI`, `GroupOpenCapEmitPrefix`,
  `GroupOpenCopy`, `GroupOpenPrefix`, `GroupOpenRecordData`, `GroupOpenRecordRun`, `GroupOpenRecordsAPI`,
  `GroupOpenRecords`, `GroupOpenSiblingRun`, `GroupOpenUpperRun`, `GroupOpenWideCopy` (new).

Relative to the master `74e3f693` (commit `165be01`), this entry changes only `GroupOpenImage.lean`
(words 798/799 of the 1,867-word opener), the same two words of the duplicate literal in
`StudyCore.lean` (`CapStudy.openingImage`), `K1Manifest.lean` (the two opening chunks containing those words),
`GroupOpenWalk.lean` (`selectRows`), `GroupOpenSelect.lean` (`rank_ne_zero`, `rank_ne_one`, `choose_legal`,
`chosen`), `GroupOpenLatch.lean` (`postSteps`, `post_length`), `GroupOpenPass.lean` (`pass_cycles_bound`),
`GroupOpenFull.lean` (`per_steps_le`, `pass_steps_bound`, `all_resources`), `GroupOpenClosing.lean`
(`claimOpeningCycles`), `Solution.lean` and `claim.json`; `programs.json` is re-packed after the two words and
this README is new. No other file of the master differs.
