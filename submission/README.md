# Odd quartets reuse a2, with a shorter level-21 setup and a 4-unrolled opener link loop

Built on our odd-quartet entry `750657ae` (kaankolcu), itself kshitij-hash's
`cfad3d49-5038-4850-be68-98a1ee7d4f48` (public commit `34159694b89006446e2eaf6a3f7584fb47a73b04`) with the odd
quartet blocks moved 200 bytes below the even ones. Two small changes on top:

- **Level-21 setup, 11 → 7 words** (the trim of patternrecognition9-del's `ffa6a198-899f-406b-818d-95dd3c9ea2b6`,
  public commit `10e21ee11e7e0b62972ab550d496b83f7444c080`, applied to this layout): the first level-21 input
  pointer is taken from `x24 = Q + 2^32`, which the body already holds, instead of rebuilding `Q + 2^32` from
  `x21`: `addi x7,x21,-1912; addi x10,x24,-1912`. The six post-body words move four words up so that they still run
  straight into it. −4 commit cycles.
- **Opener link loop unrolled by four.** The `k = g mod 34` in-place generator links run as groups of four ecalls
  with a 0..3 remainder (opening rows 4–14, which were unreachable, and 790–794; still 896 words). −4,352 on the
  certified worst set.

## Result

| | `cfad3d49` | `750657ae` | This entry |
| --- | ---: | ---: | ---: |
| proof bytes | 72,160 | 72,160 | 72,160 |
| commitment cycles | 506,688,062 | 504,595,021 | 504,595,017 |
| opening cycles (128 positions, proved bound) | 154,669 | 153,901 | 149,549 |
| score | 36,573,771,468,960 | 36,422,682,211,520 | 36,422,367,882,560 |

## The level-21 setup

`750657ae`'s six post-body words rebuild `x8` (commitment), `x21 = Q` and `x9` (trapdoor) and then run the 11-word
level-21 setup, which built `x10 = Q + 2^32 + 136 − 2048` from `x21` with `1 << 32`. The body already holds
`x24 = Q + 2^32` (the key-block counter base), so the setup becomes `addi a1,zero,64; addi a3,zero,0;
addi t2,s5,-1912; addi a0,s8,-1912; lui a2,0x8000; add a2,a2,s1; addi a2,a2,-32` (words 45,666..45,672). The post
words move to 45,660..45,665 (the latch jump now targets 45,660; 45,656..45,659 are never executed). `TailEntry`
gains `x24 = Q + 2^32`; the tail is 14,942,749 steps and 44,302,870 cycles.

## The link loop (opener)

The opener's salt-link loop runs its generator calls four per pass. Rows 4–14, which no path reached in
`750657ae`, now hold a group of four in-place calls, and row 792 jumps there; 0–3 remaining links run singly
through rows 13, 14, 793 and 794. Each call has the same arguments and comes in the same order, so calls, memory and
proofs are unchanged. Per position, the link cycles change from `2 + 10k` to `7 + 35⌊k/4⌋ + 11(k mod 4)` for
`k ≥ 1` links. The worst case, `k = 33`, is 34 cycles cheaper: 4,352 cycles less over 128 positions.

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
- Opening: at most 149,549 cycles for 128 positions (`750657ae`'s per-term bound with the link chain at 334 instead
  of 368 cycles per position).
- Proof: 72,160 bytes, unchanged.

## What is proved

`Solution.lean` states `Certificate submission 72160 504595017 149549`. As in cfad3d49 it rests on the checker
facts (termination, query budget, binding, honest acceptance), the linked hiding hybrid, the exact commit run, the
opening resource bound and the opened-proof correspondence; here every statement that mentions the quartet layout
or the heap leaf order is re-proved for the new images. `#print axioms CommitGolf.Challenge.certificate` shows only
`propext`, `Classical.choice`, `Quot.sound`.

## Provenance and credits

The tree is kshitij-hash's `cfad3d49-5038-4850-be68-98a1ee7d4f48` and, through it, its lineage as credited in that
entry: kaankolcu `606a7986-afd0-4f91-84b4-6c11f779c9d1`, `bc5cc89e-4952-4ff7-be8d-9d11905d730c`,
`c08b0128-14a7-48dd-a745-070c3a77d754`, `b64a994e-6d0b-46e0-8c37-b6e642e3828a`, `33bdbed6-b605-43fc-b808-348ea3c87e3b`,
`4dbc847a-414f-41f2-854d-79e6c80f26fc`; dadon `2b2405a1-5be9-4681-b48e-a0fcefd4588d`,
`20182e74-9879-4c56-a5d1-7a65b83f03aa`, `c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492`; i34-9
`95bf06c1-0ec6-4bf5-b6cc-6b6315f204be`. The odd-block placement, the register reallocation, the absolute latch, the
image builder and the re-proofs of the layout-dependent modules are ours (`750657ae`). The level-21 setup trim is
patternrecognition9-del's `ffa6a198-899f-406b-818d-95dd3c9ea2b6` (public commit
`10e21ee11e7e0b62972ab550d496b83f7444c080`), re-derived for this layout; no file of it is used. The 4-unrolled
opener link loop and its proof are ours.

Every file of `CommitGolfCandidate/` is byte-identical to cfad3d49's except these (one new, `K3OpenReply.lean`):

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
  `K3OpenChainRun`, `K3OpenChainPost`, `K3OpenChainExit`, `K3OpenChainReply`.

`programs.json`, `claim.json`, `Solution.lean` and this README are new for this entry.
