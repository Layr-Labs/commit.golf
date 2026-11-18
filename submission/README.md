# Quartet with pair heads, prefetched group salts and 368-byte quartet blocks

This submission is our 606a7986 tree (A′: grouped in-place counter salts over 4,096-leaf windows, `remu` opener row)
with the leaves processed in **pairs** that share their salt generator call, and with the table salts of each group
read relative to the leaf pointer (no salt cursor), the far ones prefetched into registers by the heads, and with the
quartet blocks of the trapdoor packed at a 368-byte stride (our b368 / 4dbc847a layout). The proof format, quartet tree, salt
generator and opener record writer are A′'s; the leaf function of even positions changes shape, the commit leaf body,
the opener salt loop and the checker leaf run change accordingly.

## What changed against A′

**Leaf function.** Leaves come in pairs (even position e = 2p, odd o = 2p+1, entries M and M′ = M + 256).
- Odd leaves are A′'s pinned leaf unchanged: call 1 `P(v[0..200))`, call 2 `P(tag | salt | R1[112..200) | v[168..256))`
  with `tag = M′ + 56` at word 0.
- Even leaves use a mirrored shape so that both leaves' salt slots lie next to one generator reply: call 1
  `P(v[56..256))`, call 2 `P(tag | R1[160..200) | v[0..136) | salt)` with `tag = M − 48` at word 0
  (`PairLeafModel.evenLeafDigest`; even tags ≡ 208, odd tags ≡ 56 mod 256, so tags never collide).

**Commit.** The leaf body runs 2,048 pair packets per 4,096-leaf body. Pairs p with p mod 2048 mod 11 ∈ {0, 5} are
heads (373 per body): the head writes the counter `M′` into the key block, calls the generator once and the reply lands
so that its words 0-1 are the even leaf's salt slot and words 23-24 the odd leaf's (both in place) and words 2-19 a
table of nine salts for the following four (or five) pairs of its group, which copy them with 8 loads/stores. A head
packet is 19 words, a non-head packet 22, plus one quartet rebase per 16 pairs; the latch is
`beq s4,s9,+8; jal zero,21; jal zero,45591` at words 44,086-44,088, and never-executed `nop`s keep every later word at
A′'s address. Setup word 20 becomes `addi a0,s2,-200`. Calls are unchanged (43,470,847).

**Prefetched group salts.** The pairs of a group load their table salts relative to `a2` (the odd leaf's entry − 32
bytes, set by the odd leaf's first call), so the heads no longer write a salt cursor: the copy immediates are
`−(512k + 72 − 16c)` for the pair k places after its head and table salt c. Only pair 11m+10 is out of 12-bit range
(its even salt is table salt 8 of head 11m+5, its odd salt, the 12th leaf of the group, table salt 8 of head 11m):
head 11m (m ≤ 185) loads that salt into `a6,a7` and head 11m+5 into `a4,a5` right after the generator call, and pair
11m+10 stores the four registers instead of loading. Packets: prefetching heads 20 words, pairs 11m+10 and the last
head of a body (2,046) 18, other pairs 22; the latch moves to words 43,713-43,715. Against plain pair heads this saves
the 373 cursor writes per body.

**368-byte quartet blocks** (as in our b368, 4dbc847a). Each quartet block holds 72 zero bytes and four 32-byte leaf
digests, and the fourth digest's 200-byte reply ends exactly at the next block, so blocks are 368 bytes instead of 512:
a body's 1,024 blocks fill 92 windows of 4,096 bytes and the quartet pointer `s4` is rebased 92 times per body instead
of 128. Leaf n of a body sits at `slotOff n = 368·(n/4) + 72 + 32·(n%4)`; its heap immediate is
`2048 + slotOff n − 4096·rb n` with `rb n = slotOff n / 4096`, and leaf n is followed by `add s4,s4,s7` iff
`rb (n+1) ≠ rb n` — 16 of the 92 rebases fall between the two leaves of a pair, right after the even leaf's second
call. Setup words 4-7 place the blocks at trapdoor + 0x44000000 (ending at the unchanged key/salt block); the latch is
at words 43,677-43,679. The opener's dead words 7-10 and prefix rows 717-720 set s8/s6 accordingly, row 729 sets
`tp = 368`, and the record writer's group base is `srli t2,t1,2; mul t2,t2,tp` (+3 cycles per position).
Commit cycles 512,480,543 (−7,024,639 against A′).

**Salt map.** `CounterSaltLayout.firstLeaf j = 4096·(j/373) + 2·hpl (j mod 373) + 1` with
`hpl l = 11·(l/2) + 5·(l mod 2)` (the head pair's odd leaf, whose entry address is the generator counter);
`localCoord` sends the head's two leaves to slots 0 (odd, byte 184) and 1 (even), table copy c to slot c+2, and the
12th leaf of a 12-leaf group to slot 10 of the previous head. The generator, key and slicing are A′'s.

**Opening.** The per-position salt loop (words 739-776, 38 words instead of 23) recomputes the head pair and slot of
position i (one `remu`, group A/B, in place/copy, 12th leaf) before the generator call: at most 44 cycles per position
instead of 35: 9 cycles per position more than A′'s loop. With b368's record writer (+3 per position) the bound is
98,441 + 9·128 + 3·128 = 99,977. Header rows and cap walk are A′'s.

**Check.** The leaf run of the checker evaluates the even shape for even positions (words 44-50 plus an appended even
path, 543 words in all); quartet, cap and frontier code are A′'s.

## Bounds

| | A′ (606a7986) | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,505,182 | **512,480,543** |
| opening cycles, 128 positions (worst case) | 98,441 | **99,977** |
| proof bytes, 128 positions (worst case) | 72,192 | **72,192** |
| score | 37,511,224,751,616 | **37,004,212,899,840** |

`claim.json`: `{"commitCycles":512480543,"openingCycles":99977,"proofBytes":72192}`.
Score = (512,480,543 + 99,977) × 72,192 = 37,004,212,899,840: 1.352 % below A′, 1.174 % below df0caa4c
(37,443,874,885,632).

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 512480543 99977`, with
`submission := CommitGolf.Artifact.submission` and `submission_matches_artifact` by `rfl`.

- **Commit** (`Grouped.full_commit`, `Grouped.commit_resources`): every commit run succeeds in exactly 512,480,543
  cycles (208,184,611 steps) with 43,470,847 calls. `GroupedPacketDecode` checks the 2,048 pair packets against the
  image in 32 kernel tiles; `GroupedPacket.pairPlan` is the action list of one pair with its word addresses,
  `GroupedPacketRun.pair_walk` its register walk, `GroupedContent.pair_plan_meaning` its memory effect
  (`pairPacketMem`). `GroupedInvariant.good_step` carries the invariant `Good` over one pair: messages of later leaves
  intact, the digests of all earlier leaves at their quartet slots (`even_digest`, `odd_digest` against
  `pairFullLeafDigests`), padding and key intact, and `SaltsReady`: every copied salt whose head pair has run sits at
  its source word (`salt_head_is_head`, `src_word_below`, `generated_eq`, `salt_slice`). The memory meaning takes the
  register file (pairs 11m+10 store `a4..a7`); `PrefetchOK` (carried with `Good`) states that between head 11m and
  pair 11m+10 `a6,a7` equal table salt 8 of head 11m's reply in memory, and `a4,a5` that of head 11m+5
  (`pair_plan_regs`, `prefetch_step`, `reg_salts_of`). `GroupedPacketRun.src_address` checks the a2-relative copy
  addresses (a 16-entry sign-extension table). `GroupedScan.run_scan` counts steps/calls/cycles over the 2^23 pairs
  (`totals`: 178,823,168 / 35,082,240 / 424,398,848), `GroupedCommit` adds the setup and the unchanged quartet/upper
  phases.
- **Layout** (as in b368): `QuadCommitGeometry.quartetOffset g = 368·g`, `QuartetCommitRanges.qSource g =
  679477764 + 46·g` with the block separation lemmas `qleaf_in_block`, `qleaf_before`, `qpad_outside`,
  `qleaf_below_salts`; `GroupedPacket.cursor`, `heap_address` (a 4,096-entry sign-extension table), `cursor_next`;
  `GroupedCommitImage.no_double_rebase`, `pair_rebases_succ` count the rebases per pair.
- **Physical results** (`Grouped.physical_results`): the trapdoor holds `pairHeap` (the Quartet heap over
  `pairFullLeafDigests`, `PairPhysicalHeap`), the leaf digests and the key.
- **Opening** (`GroupedOpening.all_resources`, `fixed_open`, `selected_salt`, `certifiedHeader`): b368's record
  writer (`RunsOpeningSlack` for the 4-cycle multiply, `tp = 368` threaded as `Registers.mult`, `openCycles p =
  scheduledCycles p + 3·|p|`, trapdoor leaf digests at `68·LENGTH + 368·(i/4) + 72 + 32·(i%4)`) and the new salt loop
  (`GroupOpenLoop` models words 739-764 and proves `loop_out = loopMap`, `GroupOpenSlot` the place/offset/12th-leaf/
  counter segments); `GroupedSaltMap.loop_map_eq` (a `decide` over the 4,096 body slots) equates the loop's head and
  byte offset with `saltHead` and the slot of `coord`, so each opened salt is `salts o.permutation k i`.
- **Hiding** (`Quartet.scheme_hiding_of_pair_counter`, `PairCounterSecurity`): the counter-salt transcript is within
  `counterError` of independent salts on each side; the middle term is `Quartet.pair_iid_hiding`
  (`PairHidingCertificate`), the pair-leaf analog of `final_reference_hiding_sharp` with the same (t+1)/2^121: the
  `PairH*` modules rerun the pinned proof with the pair leaf (an unopened leaf's second call carries a fresh salt and a
  word-0 tag unique to the leaf).
- **Binding and checker** (`PairCertificate.pair_checker_facts`, `PairCheck*`): termination, query budget, binding and
  honest acceptance of the pair checker image; binding adds the even-leaf replay term `Sampling.even_leaf_small_bound`
  (`PairBinding*`, Pr ≤ q/2^124) to A′'s terms, total 15q/2^124 ≤ q/2^120. `GroupedChecks.checker_facts` transfers them
  to this submission by check-image equality (`PairCheckManifest` renders the same check image).
- **Assembly** (`GroupOpenClosing.grouped_certificate`, `PairCounterCertificate.certificate_of_facts`): A′'s assembly
  with the pair honest view (`PairCounterRefines`) and pair checker facts.

## Commands and results

From the project root, pinned Lean 4.35.0 toolchain, candidate cache purged as `verify.py` does,
`CommitGolf/Artifact.lean` regenerated from `programs.json` with `verifier/artifact.py`:

- `lake build +Solution`: build completed successfully.
- `lake env lean Audit.lean`: `certificate` depends on [propext, Classical.choice, Quot.sound];
  `submission_matches_artifact` on [propext, Quot.sound].
- `python3 verifier/check_submission.py <tree>`: ok.
- `lake env leanchecker` replays every compiled candidate module, `CommitGolf.Artifact` and `Solution`.
- The exact-cycle interpreter of the commit image (`budget_q.py`) gives 512,480,543 cycles and 43,470,847 calls.
  A full-size RV64IM emulation (Keccak-f stand-in for the oracle) of the three images, two seeds: commit 512,480,543
  cycles / 208,184,611 steps / 43,470,847 calls, with the same commitment as plain pair heads on the same message and
  key; 2 × 40 batches of 128 positions (group edges and random): every opening succeeds, at most 97,795 cycles and
  71,562 proof bytes; the check accepts every honest proof and rejects 8 tampers per batch.
- The opener is pair heads' with b368's edits (words 7-9, 35-36, 717-719, 729); the check image is unchanged.
- Commit image 807,068 bytes (< 1 MiB); opening 777 words; check 543 words.

## Provenance

- 606a7986 / A′ (kaankolcu, our account) and bc5cc89e (kaankolcu): the whole tree; files adapted as listed in
  DEPENDENCIES.md.
- 2b2405a1 (dadon): the grouped in-place generator, its hiding proof, the grouped commit and opening proofs.
- 20182e74 (dadon), b64a994e and c08b0128 (kaankolcu), c28dd9ca (dadon), 33bdbed6 (kaankolcu): the lineage
  under 2b2405a1 (Quartet tree, opening record writer, checker, chain-salt modules).
- df0caa4c (kaankolcu, our account; public commit 362137507f5f58c38d91fe5589e51f8cf585b634): the idea of reading group
  salts relative to the leaf pointer and prefetching the out-of-range ones into registers; re-derived here for pair
  heads. No file of df0caa4c is used.
- 4dbc847a / b368 (kaankolcu, our account): the 368-byte quartet blocks and their proofs (layout, record writer).
  The 368-byte block idea also appears in AdamGagol's 1a9bc5f4 (Quad lineage); no file of it is used here.
