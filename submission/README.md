# Quartet with pair heads: one keyed generator reply salts two adjacent leaves in place

This submission is our 606a7986 tree (A′: grouped in-place counter salts over 4,096-leaf windows, `remu` opener row)
with the leaves processed in **pairs** that share their salt generator call. The proof format, quartet tree, salt
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
A′'s address. Setup word 20 becomes `addi a0,s2,-200`. Calls are unchanged (43,470,847); commit cycles drop by
5,349,375 to 514,155,807.

**Salt map.** `CounterSaltLayout.firstLeaf j = 4096·(j/373) + 2·hpl (j mod 373) + 1` with
`hpl l = 11·(l/2) + 5·(l mod 2)` (the head pair's odd leaf, whose entry address is the generator counter);
`localCoord` sends the head's two leaves to slots 0 (odd, byte 184) and 1 (even), table copy c to slot c+2, and the
12th leaf of a 12-leaf group to slot 10 of the previous head. The generator, key and slicing are A′'s.

**Opening.** The per-position salt loop (words 739-776, 38 words instead of 23) recomputes the head pair and slot of
position i (one `remu`, group A/B, in place/copy, 12th leaf) before the generator call: at most 44 cycles per position
instead of 35, opening bound 98,441 + 9·128 = 99,593. Header rows, cap walk and record writer are A′'s.

**Check.** The leaf run of the checker evaluates the even shape for even positions (words 44-50 plus an appended even
path, 543 words in all); quartet, cap and frontier code are A′'s.

## Bounds

| | A′ (606a7986) | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,505,182 | **514,155,807** |
| opening cycles, 128 positions (worst case) | 98,441 | **99,593** |
| proof bytes, 128 positions (worst case) | 72,192 | **72,192** |
| score | 37,511,224,751,616 | **37,125,125,836,800** |

`claim.json`: `{"commitCycles":514155807,"openingCycles":99593,"proofBytes":72192}`.
Score = (514,155,807 + 99,593) × 72,192 = 37,125,125,836,800: 1.029 % below A′.

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 514155807 99593`, with
`submission := CommitGolf.Artifact.submission` and `submission_matches_artifact` by `rfl`.

- **Commit** (`Grouped.full_commit`, `Grouped.commit_resources`): every commit run succeeds in exactly 514,155,807
  cycles (209,859,875 steps) with 43,470,847 calls. `GroupedPacketDecode` checks the 2,048 pair packets against the
  image in 32 kernel tiles; `GroupedPacket.pairPlan` is the action list of one pair with its word addresses,
  `GroupedPacketRun.pair_walk` its register walk, `GroupedContent.pair_plan_meaning` its memory effect
  (`pairPacketMem`). `GroupedInvariant.good_step` carries the invariant `Good` over one pair: messages of later leaves
  intact, the digests of all earlier leaves at their quartet slots (`even_digest`, `odd_digest` against
  `pairFullLeafDigests`), padding and key intact, and `SaltsReady`: every copied salt whose head pair has run sits at
  its source word (`salt_head_is_head`, `src_word_below`, `generated_eq`, `salt_slice`). `GroupedScan.run_scan` counts
  steps/calls/cycles over the 2^23 pairs (`totals`: 180,498,432 / 35,082,240 / 426,074,112), `GroupedCommit` adds the
  setup and the unchanged quartet/upper phases.
- **Physical results** (`Grouped.physical_results`): the trapdoor holds `pairHeap` (the Quartet heap over
  `pairFullLeafDigests`, `PairPhysicalHeap`), the leaf digests and the key.
- **Opening** (`GroupedOpening.all_resources`, `fixed_open`, `selected_salt`, `certifiedHeader`): the new salt loop
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
- The exact-cycle interpreter of the commit image (`budget_q.py`) gives 514,155,807 cycles and 43,470,847 calls.
  A full-size RV64IM emulation (Keccak-f stand-in for the oracle) of the three images: commit 514,155,807 cycles /
  209,859,875 steps / 43,470,847 calls; 40 batches of 128 positions (group edges and random): every opening succeeds,
  at most 97,154 cycles and 71,562 proof bytes; the check accepts every honest proof and rejects 8 tampers per batch;
  24 of 24 sampled leaf digests in the trapdoor equal an independent Python model of both leaf shapes.
- Commit image 807,068 bytes (< 1 MiB); opening 777 words; check 543 words.

## Provenance

- 606a7986 / A′ (kaankolcu, our account) and bc5cc89e (kaankolcu): the whole tree; files adapted as listed in
  DEPENDENCIES.md.
- 2b2405a1 (dadon): the grouped in-place generator, its hiding proof, the grouped commit and opening proofs.
- 20182e74 (dadon), b64a994e and c08b0128 (kaankolcu), c28dd9ca (dadon), 33bdbed6 (kaankolcu): the lineage
  under 2b2405a1 (Quartet tree, opening record writer, checker, chain-salt modules).
