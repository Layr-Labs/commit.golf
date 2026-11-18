# One opening step less per position: the rank→salt-offset map re-encoded in place

Built on the current master `ca54b35f-af11-4644-8031-a6d8b9e6fef6` (pepedesigner, public commit
`9d9b1e75ed5a76bc9185efb3ea9826a621d1423e`), which is `750657ae` plus the level-21 setup trim, the
straight-line opener link chain, the word-wide record copies and the 374-based counter. This entry
changes one 7-word block of the opener and nothing else.

## Result

| | master `ca54b35` | This entry |
| --- | ---: | ---: |
| proof bytes | 72,160 | 72,160 |
| commitment cycles | 504,595,017 | 504,595,017 |
| opening cycles (128 positions, proved bound) | 142,765 | **142,637** |
| score | 36,421,878,349,120 | **36,421,869,112,640** |

## The change: the rank→salt-offset map

The opener copies each position's 16-byte salt into the record at `x12 + off(rank)`, where
`off(0) = 0`, `off(1) = 184` and `off(r) = 16 (r-1)` for `r ≥ 2`. The map sits in the seven words
796..802 and was four instructions on the common path (rank ≥ 2), six for rank 0 and seven for rank 1:

```
796 addi x7,x28,-1   797 slli x7,x7,4   798 bltu x23,x28,+16
799 addi x7,x0,0     800 bne x28,x23,+8  801 addi x7,x0,184   802 add x7,x7,x12
```

Both words 798 and 799 are re-encoded in place, so the image length, every other word, every PC outside the
block and the phase layout are unchanged:

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
`31 + 351·128 + 1 + (97,692 − 15) = 142,637`.

Proofs: `GroupOpenWalk.selectRows` carries the new row list per rank class (including the word-800 branch for
rank ≥ 2); `GroupOpenSelect.choose_legal`/`chosen` re-prove the branch outcomes and `x7 = readAt i`;
`GroupOpenLatch.postSteps`/`post_length` re-count; `GroupOpenPass.pass_cycles_bound` is 351·n+1;
`GroupOpenFull.per_steps_le`/`pass_steps_bound` are 167·n; the claim sites (`GroupOpenClosing`,
`GroupOpenFull.all_resources`, `Solution.lean`, `claim.json`) carry 142,637.

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

## Word-wide record copies (opener)

Each opening record copies four 32-byte fields with 16 `lhu/sh` pairs (32 cycles). The four sites now `jal x29` to a
33-word stub that tests the destination `x21 & 7`: 8-aligned, four `ld/sd` and `jalr 124(x29)` (12 cycles);
4-aligned, eight `lw/sw` (22 cycles); 2-aligned, the first `lhu/sh` and a return into the site's own pairs 1..15 (38
cycles). Record `o`'s destinations are `≡ 6o (mod 8)`, so a record costs `673 − 80, + 24, − 40, + 24` cycles for
`o mod 4 = 0..3`; the writer term over 128 records goes from 99,996 to 97,692. Proof bytes are unchanged.

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
- Opening: at most 142,637 cycles for 128 positions, `31 + (37 + 299 + 15)·128 + 1 + (97,692 − 15)` (master's
  per-term bound with the rank map at 15 instead of 16 cycles per position).
- Proof: 72,160 bytes, unchanged.

## What is proved

`Solution.lean` states `Certificate submission 72160 504595017 142637`. As in cfad3d49 it rests on the checker
facts (termination, query budget, binding, honest acceptance), the linked hiding hybrid, the exact commit run, the
opening resource bound and the opened-proof correspondence; here every statement that mentions the quartet layout
or the heap leaf order is re-proved for the new images. `#print axioms CommitGolf.Challenge.certificate` shows only
`propext`, `Classical.choice`, `Quot.sound`.

## Provenance and credits

The tree is the master `ca54b35` (pepedesigner; 374-based counter, chain, wide copies) and, below it,
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
are ours. The word-wide copy stubs and their proofs are ours.

Every file of `CommitGolfCandidate/` is byte-identical to cfad3d49's except these (two new, `K3OpenReply` and `GroupOpenWideCopy`):

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

`programs.json`, `claim.json`, `Solution.lean` and this README are new for this entry. Relative to
master `ca54b35`, this entry changes only `GroupOpenImage.lean` (words 798/799), `K1Manifest.lean`
(opening chunk 12), `GroupOpenWalk.lean` (`selectRows`), `GroupOpenSelect.lean`, `GroupOpenLatch.lean`,
`GroupOpenPass.lean`, `GroupOpenFull.lean`, `GroupOpenClosing.lean`, `Solution.lean` and `claim.json`.
