# Product: preserved low-12-bit chain mask (-127 opening cycles)

Based on promoted master `2a79dc7`, submission
`ea7fbe09-200e-46db-940b-1a4ca686cba9` by **Meganpark980320**.
This retains their complete five-entry chain (`60c75e80`, `d65f21f3`,
`c6d19f38`, `3b9c2633`, `ea7fbe09`), including the cap walk, writer latch,
chain constants, level-22 pointer and commitment latch improvements.
Those entries extend our next14 submission
`295a1266-202b-44e8-be6c-bbd784558a66`; our next10–next14 writer and
benbuschmann endpoint optimizations are already present, not newly added here.
Mahmoud514's earlier commitment work is also inherited.

The remaining additive idea is the paused next15 mask: replace the two shifts
at the salt-chain entry with `and x30,x6,x1`, where `x1 = 4095`.
Unlike the uncertified next15 WIP, this layout extends Meganpark980320's
existing constant-initialization detour by just one instruction: word 757
sets `x1 = x26-1`, and the return moves to 758. The chain shifts one word
earlier, with its PC-relative link offset adjusted to preserve the target.
The header costs 36 instead of 35, and each query saves one cycle. A nonempty
batch of n queries saves n-1: 127 at 128 queries, zero at one query.
Empty opening is unchanged. No direct-return 30-byte copy gain is claimed.

```json
{"commitCycles":504585244,"openingCycles":119201,"proofBytes":72160}
```

```text
(504,585,244 + 119,201) × 72,160 = 36,419,472,751,200
Improvement over ea7fbe09: 9,164,320
```

Only 17 opening words change: 757, 758 and 777..791. Image lengths,
commitment/checker images, embedded data, ABI and proof serialization remain
unchanged. Matching image literals, packed leaves, mask-preservation proofs,
chain bounds and the artifact-backed certificate accompany the image.
The earlier next15 work is preserved separately on `devin/next15-wip` and is
not a certified ancestor. Public provenance is prepared in `~/cg/sub12/`.
Nothing is pushed or submitted by this work; local certificate and emulator
checks are not a claim of official Yukon verification.

## Historical promoted-master documentation

# Product: a two-instruction commitment latch against `a5 = 2^32` (-1,024 commitment cycles)

Built on our `cg-m4` (the level-22 sibling through a pointer word, submission
`3b9c2633-0fe8-40d3-b8f5-4d46b12f587c`, commit `03953bb`), which sits on the promoted product best
`c6d19f38-4b72-4e7a-908e-8d854bc7e2df` (promoted commit `12d186e2604d9e5ee32012245fdb4a6be2a30494`). Only the
commitment image changes: setup rows 4..5, the rank-8 / rank-9 salt rows of every 11-leaf group of the body, and
the latch. The opening and checker images, the salts, every oracle input, the ABI, the proof serialization and every
proof byte are unchanged.

## Result

| | `c6d19f38` | `cg-m4` (base) | This entry |
| --- | ---: | ---: | ---: |
| proof bytes | 72,160 | 72,160 | 72,160 |
| commitment cycles | 504,586,268 | 504,586,268 | **504,585,244** |
| opening cycles (128 positions, proved bound) | 120,864 | 119,328 | 119,328 |
| score | 36,419,666,645,120 | 36,419,555,807,360 | **36,419,481,915,520** |

`(504,585,244 + 119,328) × 72,160 = 36,419,481,915,520`, 73,891,840 below `cg-m4` (1,024 cycles × 72,160 bytes).

## Before

The commitment image is the 38-word setup, the body (rows 38..181,037: four copies of the 45,250-word tile, 16,384
leaves per pass, 1,024 passes) and the latch

```
181038 srli a2,a0,32          a2 = a0 >> 32
181039 bne  a2,zero,<181041>  out after the last pass
181040 jal  zero,<38>         next pass
```

3 cycles per pass (2 on the final exit). A two-instruction latch needs a register holding a bound for `a0`, but the
body uses every register: t0, a1, a3 are the oracle selector, width and primitive, a0 and a2 the call pointers, the
others constants and quartet-block gaps, and a4..a7 carry the salts of ranks 9 and 10 of each group: rank 8 preloads
them
(`ld a4,-1848(a0); ld a5,-1840(a0); ld a6,-1832(a0); ld a7,-1824(a0)`), because from those leaves' own `a0` the
generator reply words lie more than 2 KiB below.

## The change

```
setup
4   slli a5,s3,3          a5 = 2^29 << 3 = 2^32           (was: slli s6,s3,3)
5   add  s8,s5,a5         unchanged value                 (was: add s8,s5,s6)

rank 8 of every group     ld a4,-1848(a0) ; ld a6,-1832(a0) ; ld a7,-1824(a0)     (the a5 load dropped)
rank 9 of every group     sd a4,0(a0) ; ld a2,-2008(a2) ; sd a2,8(a0)             (was: sd a4,0(a0) ; sd a5,8(a0))

latch
181038 bgeu a0,a5,<181041>
181039 jal  zero,<38>
181040 nop (not reached)
```

- `s6` held `2^32` only between rows 4 and 33 and was read only by row 5; row 33 (`addi s6,s1,112`) still sets
  its body value, so the setup costs no extra instruction and every other register ends as before.
- At rank 9's salt rows `a2 = a0 − 88` (its first call's output pointer). The second salt word, word 17 of the
  group's generator reply, is 2,008 bytes below it, so `ld a2,-2008(a2)` reaches it; the reply stays intact in
  memory for the whole group (the invariant `MsgGood.group` already holds it for every rank ≥ 1). `a2` is rewritten
  by the next `add a2,a0,s*` before the second call, as for ranks 2..8.
- Rank 8 loses a row and rank 9 gains one, so every group, tile and later row keeps its address
  (`rankPrefix 9 = 98`, was 99); 18,605 image words change, all inside the body, setup rows 4..5 and the latch.
- `a0` at the latch after pass `k` is `4,152 + 4 MiB · k`: below `2^32` for `k < 1,024`, `2^32 + 4,152` after the
  last pass. The latch is 2 cycles per pass (`bgeu` not taken, `jal`) and 1 on the final exit.

Per pass the latch saves one cycle, 1,024 in all. Nothing else changes cost.

## Bound

- `edgeCost` 2 / 1 (was 3 / 2); steps per pass `181,002` (was 181,003); `S N − S 0 = 185,346,047`,
  `C N − C 0 = 460,281,855` (`Q` unchanged at 39,276,544); `commitSteps = 38 + 185,346,047 + 6 + 14,943,221 =
  200,289,312`.
- `commitCycles = 41 + 460,281,855 + 6 + 44,303,342 = 504,585,244` (base: `41 + 460,282,879 + 6 + 44,303,342`).

## Evidence

Memory-backed RV64IM emulator (Riscv.lean cost model, stand-in oracle replies, random message), base image and this
image from the commitment entry through the first full pass (16,384 leaves) to the latch:

| | base | this entry |
| --- | ---: | ---: |
| cycles to the end of pass 1 | 449,536 | 449,535 |
| oracle calls | 38,356 | 38,356 |
| hash of all oracle inputs | `d49c20f672d0b94f` | `d49c20f672d0b94f` |
| hash of all output pointers | `1c8c0655a3f1c91f` | `1c8c0655a3f1c91f` |
| next pc / `a0` / `a5` | 38 / 4,198,456 / – | 38 / 4,198,456 / 4,294,967,296 |

The patcher checks that `a5` is named nowhere else in the image and that exactly 1,488 rank-8 / rank-9 pairs
(4 tiles × 372 groups) are rewritten.

## Proofs

- Image description: `GroupedImageBase` (`saltCode` 8 and 9, `rankPrefix 9 = 98`), `GroupedPacket` (`saltPlan`
  with `.load .x12 .x12 (-2008) (sourceWord i+1)`; `PacketRegs.limit : x15 = 2^32`). `GroupedPacketDecode` and
  `GroupedTileCopy` (the tile-0 chunk literals re-rendered from the new image) re-check the image against the packets
  unchanged in form; `GroupedCommitImage` keeps `packet_length` / `packet_next`.
- `GroupedPacketRun`: `finish` also keeps x15; `rank9_address` (`w − 4 − 251 = sourceWord + 1`); the walk
  certificates of ranks 8 and 9.
- `GroupedContent`: `followerMem` of rank 9 reads its second word from memory; `body_prefetch` / `plan_prefetch`
  give x14, x16, x17 and keep x15. `GroupedFrame`: `followerSalt` of rank 9, `follower_mem_salt`.
- `GroupedInvariant`: `MsgGood.prefetched` is x14, x16, x17; the rank-9 salt equality takes word 17 from the reply in
  memory. `GroupedSeed`: `latch_good`.
- `GroupedSetup`: `setupOps` rows 4..5, `Seed2.limit`, `SeedRegs.limit`, `post_live_frame` (x15 into `Live`).
- `GroupedScan`: `edgeCost`, `S`, `latchReg` (writes nothing now), `edge_run` (`bgeu x10,x15,+12` taken iff the
  last pass; `jal x0` back to 38), `step_live`, `packet_execute`.
- `GroupedCommit` (`commitSteps`, the scan totals), `GroupedTailEval.commitCycles`, `GroupedChecks`,
  `GroupOpenClosing.claimCommitCycles`, `Solution.lean`, `claim.json`; `programs.json` and `K1Manifest`
  (`commitCode_0_*` chunks).

## Build and verification

Built and verified on a separate Linux build host (r7i.4xlarge, Lean 4.35.0, contract identical to `12d186e`
outside `submission/`). The host's user systemd cannot provide the read-only sandbox, so `scripts/run.py` refuses to
start there. The verifier used is a box-local copy of `scripts/run.py` / `verifier/verify.py`
(`scripts/run_local.py`, `verifier/verify_local.py`) with only the systemd sandbox wrapper removed: same policy check,
same fresh `.work/<id>/project`, same purge of cached candidate and challenge modules, same comparator and
`verifier/comparator.json`. The same host and script verified `cg-m1`..`cg-m4` at their scores.

```text
$ git checkout --detach cg-m5-commit-latch           # dc9d936
$ python3 scripts/run_local.py --track product          # 16 min 7 s wall (real 16m7.229s)
✔ [9870/9871] Built Solution
Build completed successfully (9871 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, CommitGolf.Challenge.certificate,
  CommitGolf.Challenge.submission_matches_artifact, propext, Quot.sound, Classical.choice, ...] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
{"artifact_digest": "a97ac9e8dcd4c99f5514bb535a891c22382242e48d57a9196b51a872ab1082fc",
 "claim": {"commitCycles": 504585244, "openingCycles": 119328, "proofBytes": 72160}, "commit": null,
 "contract_commit": "dc9d93626ca74e03e5507c2349a20ca2c7f19e27", "score": 36419481915520, "status": "verified",
 "work_created": true}
RC=0

$ cat scripts/score.json
{"score": 36419481915520, "metrics": {"commitCycles": 504585244, "openingCycles": 119328, "proofBytes": 72160,
 "proverCycles": 504704572, "contractCommit": "dc9d93626ca74e03e5507c2349a20ca2c7f19e27",
 "artifactDigest": "a97ac9e8dcd4c99f5514bb535a891c22382242e48d57a9196b51a872ab1082fc", "verified": true}}

#print axioms CommitGolf.Challenge.certificate
  'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms CommitGolf.Challenge.submission_matches_artifact
  'CommitGolf.Challenge.submission_matches_artifact' depends on axioms: [propext, Quot.sound]
```

(`contract_commit` is the checked-out branch commit; outside `submission/` it is byte-identical to `12d186e`.)
