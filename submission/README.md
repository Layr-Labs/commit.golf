# Product: the level-22 sibling through a pointer word (-1,536 opening cycles)

Built on the promoted product best `c6d19f38-4b72-4e7a-908e-8d854bc7e2df` (our `cg-m3`, promoted commit
`12d186e2604d9e5ee32012245fdb4a6be2a30494`). The opener's prefix pass no longer copies the level-22 sibling node
into the heap; it leaves the node's address in a spare word of the quartet block, and the record writer's level-0
head loads that address instead of computing a heap slot. Only opening rows 150..152 and 748..776 change. The
commitment and checker images, embedded data, the ABI, the proof serialization and every proof byte are unchanged.

## Result

| | `c6d19f38` (base) | This entry |
| --- | ---: | ---: |
| proof bytes | 72,160 | 72,160 |
| commitment cycles | 504,586,268 | 504,586,268 |
| opening cycles (128 positions, proved bound) | 120,864 | **119,328** |
| score | 36,419,666,645,120 | **36,419,555,807,360** |

`(504,586,268 + 119,328) × 72,160 = 36,419,555,807,360`, 110,837,760 below the base (1,536 cycles × 72,160 bytes).

## Before

For every newly opened quartet `q` (block `B = groupSlots + 1024 q`) the prefix head selected the group reply and
the address of the sibling quartet's level-22 node by parity (`x30 = B+136` for even `q`, `B-856` for odd `q`;
both nodes live inside the commit's group replies of the pair), ran the inverse call into the rebuilt block
`B+512`, restored `x13, x12, x10`, and then copied the 32-byte node into the heap slot `2^22 + (q ^ 1)`:

```
760 addi x13,x0,2 ; 761 ecall (inverse into B+512) ; 762 addi x13,x0,1 ; 763 addi x12,x0,1536 ; 764 addi x10,x0,1024
765 xori x28,x28,1 ; 766 add x28,x28,x19 ; 767 slli x28,x28,5 ; 768 add x28,x28,x9     heap slot of 2^22 + (q^1)
769..776 ld x31,0/8/16/24(x30) ; sd x31,0/8/16/24(x28)                               32-byte copy
```

The record writer then rebuilt the same heap address for its level-0 sibling (rows 150..152,
`xori x7,x6,1 ; slli x7,x7,5 ; add x7,x9,x7`) and copied the 32 bytes into the proof (wide copy at 153). The head
of a new quartet cost 36 cycles (even) / 35 (odd), the level-0 head 3.

## The change

```
prefix
748 bne  x30,x0,<769>        odd quartets to the moved select (was <758>)
749 addi x10,x7,168          even: reply_E                       (unchanged)
750 addi x30,x7,136          even: sibling node address          (unchanged)
751 jal  x0,<771>            (was <760>)
769 addi x10,x7,-1056        odd: reply_O                        (was row 758)
770 addi x30,x7,-856         odd: sibling node address           (was row 759)
771 addi x13,x0,2 ; 772 ecall ; 773 addi x13,x0,1 ; 774 addi x12,x0,1536 ; 775 addi x10,x0,1024   (were 760..764)
776 sd   x30,712(x7)         the address into word 89 of the quartet block, then into the chain block at 777
758..768                     nop, not reached

record writer, level 0
150 ld   x7,712(x7)          x7 = B (from the mate copies) -> the sibling node's address
151 jal  x0,<153>            the unchanged level-0 wide copy (alignment test at 153)
152                          nop, not reached
```

Word 89 of a quartet block (`B+712`) is the word right after the rebuilt block (`B+512 .. B+712`). Nothing else in
the opener reads or writes it: the rebuilt blocks are words 64..88, the group replies words 21..45 of an even block
and 124..127 / 0..20 around an odd one, the level-22 nodes words 17..24 of the even block. The writer's level-0
source is now the commit's node itself, which the pass never writes, so the proof bytes are the same bytes as
before for every position set. A later position of the same quartet skips the head (sorted positions) and reads
the pointer written by the first one. The level-22 heap slots are no longer written by the opener at all.

Per new quartet the head is 25 cycles (even: 12 head rows including the `jal`, the call row, the 8-cycle inverse,
three restores and the store) or 24 (odd), against 36 / 35. Per record the level-0 head is 2 cycles against 3. The
writer's row 147 (the third mate copy's exit) and the copy site at 153 are pinned by the wide-copy proofs
(`site.start + 32`), so the shorter head keeps its jump at 151.

## Bound

- `headSteps` 18 / 17 and `headCycles` 25 / 24 for a new even / odd quartet (3 / 3 for a repeated quartet),
  `price headPost = 4` (rows 773..776).
- `pass_cycles_bound`: `passCycles p n j ≤ 334·n + 2` (was `345·n + 2`; 25 head + 297 chain + 12 post).
- `siblingCost` of level 0: `4 + recordCopyCost` (was 5); `lower_total_cost` 64 (was 65); one record 129 + extras
  (was 130); `recordCost` 135 / 134 (was 136 / 135); `records_total = 134·n + copySum n + 1`;
  `wide_scored_limits` 76,554 (was 76,682).
- Opening: `35 + (334·128 + 2) + (76,554 − 15) = 119,328` (base: `35 + (345·128 + 2) + (76,682 − 15) = 120,864`).

The saving is 11 cycles per newly opened quartet and 1 per record, so an opening of `n` positions in `g` distinct
quartets gains `11 g + n`; the scored bound (128 positions, 128 quartets) drops by 1,536.

## Evidence

Memory-backed RV64IM emulator (Riscv.lean cost model, deterministic stand-in oracle replies), base image against
this image on the same inputs; the base column reproduces the certified 120,864 on its worst set.

| position set | base cycles | this entry | Δ | proof bytes |
| --- | ---: | ---: | ---: | --- |
| `{131072·j + 738}`, 128 (the certified worst set) | 120,864 | 119,328 | −1,536 | identical (72,160) |
| `{131072·j + 739}`, 128 | 120,736 | 119,200 | −1,536 | identical |
| `{131072·j + 742}`, 128 (odd quartets) | 120,608 | 119,072 | −1,536 | identical |
| even/odd quartet pairs, 128 | 116,232 | 114,696 | −1,536 | identical |
| alternating parity, 128 | 120,672 | 119,136 | −1,536 | identical |
| six random 128-sets | 100,504 .. 102,012 | −1,536 each | −1,536 | identical |
| `0..127` (32 quartets) | 80,587 | 80,107 | −480 | identical |
| stride 4, 128 | 92,187 | 90,651 | −1,536 | identical |
| `{131072·j + 739}`, 127 | 119,826 | 118,302 | −1,524 | identical |
| 64 clustered | 45,375 | 44,607 | −768 | identical |
| nine scattered | 7,797 | 7,711 | −86 | identical |
| two | 2,978 | 2,954 | −24 | identical |
| one (`5`), one (`2^24−1`) | 1,791 / 2,047 | 1,779 / 2,035 | −12 | identical |

All runs halt with success and make the same oracle calls.

## Proofs

- Prefix rows (`GroupOpenWalk`): `newRows` (748 `bne` +84), `evenSel` (751 `jal` +80), `oddSel` (769, 770),
  `callRow` (771), `restoreRows` (773..775), `ptrRows` (776 `sd x30,712(x7)`), `headPost = restoreRows ++ ptrRows`,
  `inverse_fetch` (772).
- `GroupOpenStep`: `head_pre` also returns `x7 = B`; `ptr_row` (the store, its legality and its word view
  `writeWord … (pointerWord q) x30`); `head_post` (rows 773..776; no register besides `x10, x12, x13` changes);
  `pointer_address_word`, `quad_address_node` (`quadAddress i = 8·nodeWordOf (i/4 ^ 1)`). The 32-byte copy lemmas
  `sib_args` / `sib_rows` are gone.
- `GroupOpenEffect`: `HeadWrites` is the rebuilt block plus the pointer word (`rebuiltWord q + m`, `m < 26`);
  `head_outside`, `head_block`, new `head_pointer`, `fixed_pointer`; `outcome_facts` / `trace_post` also give the
  pointer word of a new quartet.
- `GroupOpenPass`: `Touched` covers `m < 26`; `Ready` carries `pointer` (every processed position's pointer word
  holds its node's address); `next_ready` proves it (the sorted-quartet lemmas moved here from `GroupOpenFixed`);
  `pass_cycles_bound` 334. `GroupOpenHeader` starts it empty. `GroupOpenLatch`: head rows, steps and cycles.
- `GroupOpenFixed`: `Seen` drops the heap-sibling field. `GroupOpenResume`: `boundary_at_end` gives the records the
  pointer fact; `kept_quad` (the node words are untouched by the pass) replaces `placed_sibling`. `K3OpenFacts`:
  `end_components` and `opened_proof` use `trapdoorQuad`.
- Writer: `GroupOpenMemory` (`quadAddress`, `pointerAddress`, `input_quad`), `GroupOpenGeometry` (`siblingAddress`
  of level 0 is `quadAddress`; `sibling_address_inside`, `sibling_address_upper`), `GroupOpenSibling` (`zeroRows`
  150..151), `GroupOpenSiblingRun` (`zeroBlock`, `execute_sibling_zero`; `execute_sibling` for levels ≥ 1),
  `GroupOpenUpperRun` (`execute_lower_zero`; `execute_lower` from level 1), `GroupOpenPrefix` (the record prefix
  leaves `x7 = B`), `GroupOpenRecordData` / `GroupOpenRecordsAPI` (`RecordStart.pointer`, `RecordBoundary.pointer`,
  costs), `GroupOpenRecordRun`, `GroupOpenRecords`, `GroupOpenRecordBytes`.
- Model (`GroupOpenModel`): `trapdoorQuad`; `physicalRecord` takes the level-0 digest separately;
  `proof_from_trapdoor_matches_virtual` asks for `trapdoorQuad t i = upperHeap … (2^22 + i/4)`, which `opened_proof`
  gets from the untouched commit node and `node_slice`.
- `GroupOpenABI` (`wideCycles`, `wide_scored_limits` 76,554), `GroupOpenFull` (119,328), `GroupOpenClosing`,
  `Solution.lean`, `claim.json`; the image in `programs.json`, `K1Manifest` (three opening chunks),
  `GroupOpenImage` and `StudyCore`.

## Build and verification

Built and verified on a separate Linux build host (r7i.4xlarge, Lean 4.35.0, contract identical to `39c57ab` /
`12d186e` outside `submission/`). The host's user systemd cannot provide the read-only sandbox, so
`scripts/run.py` refuses to start there. The verifier used is a box-local copy of `scripts/run.py` /
`verifier/verify.py` (`scripts/run_local.py`, `verifier/verify_local.py`) with only the systemd sandbox wrapper
removed: same policy check, same fresh `.work/<id>/project`, same purge of cached candidate and challenge modules,
same comparator and `verifier/comparator.json`. The same host and script verified `cg-m1`, `cg-m2` and `cg-m3`
(`c6d19f38`) at their published scores.

```text
$ git checkout --detach cg-m4-sibling-pointer        # 03953bb
$ python3 scripts/run_local.py --track product          # 16 min 6 s wall (real 16m5.769s)
✔ [9869/9871] Built CommitGolfCandidate.GroupOpenClosing (3.5s)
✔ [9870/9871] Built Solution (3.4s)
Build completed successfully (9871 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, CommitGolf.Challenge.certificate,
  CommitGolf.Challenge.submission_matches_artifact, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub,
  Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft,
  Nat.shiftRight, String.ofList, Char.ofNat, List, eagerReduce, Nat, String, String.mk, Char, optParam, autoParam,
  semiOutParam, outParam, CommitGolf.Challenge.submission] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
{"artifact_digest": "ddc0366d842979350e6145ed36b4d4dd17c38c4ecb499b349a29075b8d94e703",
 "claim": {"commitCycles": 504586268, "openingCycles": 119328, "proofBytes": 72160}, "commit": null,
 "contract_commit": "03953bb7ec7e8a922e0a5ccc6fdb7471392fbf6e", "score": 36419555807360, "status": "verified",
 "work_created": true}
RC=0

$ cat scripts/score.json
{"score": 36419555807360, "metrics": {"commitCycles": 504586268, "openingCycles": 119328, "proofBytes": 72160,
 "proverCycles": 504705596, "contractCommit": "03953bb7ec7e8a922e0a5ccc6fdb7471392fbf6e",
 "artifactDigest": "ddc0366d842979350e6145ed36b4d4dd17c38c4ecb499b349a29075b8d94e703", "verified": true}}

#print axioms CommitGolf.Challenge.certificate
  'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms CommitGolf.Challenge.submission_matches_artifact
  'CommitGolf.Challenge.submission_matches_artifact' depends on axioms: [propext, Quot.sound]
```

(`contract_commit` is the checked-out branch commit; outside `submission/` it is byte-identical to `12d186e`.)
