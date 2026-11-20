# Product: record-writer latch on the prefix pass's end pointer (-254 opening cycles)

Built on our cap-walk entry `cg-m1` ([SUBMISSION ID OF cg-m1]), itself on the promoted product best
`295a1266-202b-44e8-be6c-bbd784558a66` (AvinashNayak27, promoted commit `39c57aba0e611a1b56c2dd87b24d4990812a46ff`).
This entry changes two words of the opening image (rows 646 and 647) and the record-writer proofs that read them.
The commitment image, the checker image, embedded data, the ABI, the proof serialization and every other opening word
are unchanged.

## Result

| | `295a1266` | `cg-m1` (base of this entry) | This entry |
| --- | ---: | ---: | ---: |
| proof bytes | 72,160 | 72,160 | 72,160 |
| commitment cycles | 504,586,268 | 504,586,268 | 504,586,268 |
| opening cycles (128 positions, proved bound) | 122,135 | 121,370 | **121,116** |
| score | 36,419,758,360,480 | 36,419,703,158,080 | **36,419,684,829,440** |

`(504,586,268 + 121,116) × 72,160 = 36,419,684,829,440`, 18,328,640 below `cg-m1` (254 cycles × 72,160 bytes).

## The record latch before

Each of the opener's records (one per opened position) ends with the latch at rows 642..649:

```
642 slli x7,x6,3 ; 643 add x7,x26,x7 ; 644 sd x23,0(x7)     mark the record's cap group
645 addi x8,x8,8                                           next index
646 addi x18,x18,-1                                        remaining count
647 beq  x18,x0,<649>
648 jal  x0,<15>                                           next record
649 jal  x0,<1097>                                         cap preparation (unrolled sweep)
```

A nonfinal record spent seven cycles here (642..648) and the final one six (642..647, then 649 inside the cap
preparation).

## The record latch now

`x17` already holds the end of the index array: the prefix pass sets it at row 731 (`add x17,x8,x25`,
`indicesBase + 8·n`) for its own end-pointer loop (benbuschmann's `c4598882`), and no later instruction writes
`x17` (the record writer, its copy stubs, the cap preparation and the cap walk never name it). The writer's index
pointer `x8` starts at `indicesBase` and advances by 8 per record. So the writer can stop on `x8 = x17` and the
count in `x18` is no longer needed:

```
645 addi x8,x8,8
646 bne  x8,x17,<15>       next record
647 jal  x0,<649>          final record: to the unchanged cap-preparation entry
```

A nonfinal record now spends five cycles in the latch (642..646) and the final one still six (642..647). Over
`n` records the writer saves `2(n−1)`: 254 for the scored 128 positions. Row 648 is no longer reached. The final
record still reaches 649 (`0x1a24`), so the cap-preparation proof and every later phase are untouched.

## Bound

- `recordCost`: `(if final then 136 else 135) + recordExtra` (was 136/137).
- `records_total`: `recordsCost n 0 n = 135·n + copySum n + 1` (was `137·n + copySum n − 1`).
- `wideCycles`: `15 + (135n + copySum n + 1) + 770 + (capWalkCycles + 2) + 4`; `wide_scored_limits` 76,682 (was 76,936).
- Opening: `31 + (347·128 + 2) + (76,682 − 15) = 121,116`.

## Evidence

The memory-backed RV64IM emulator (Riscv.lean cost model, deterministic stand-in oracle replies) on the same
inputs as `cg-m1`:

| position set | `cg-m1` cycles | this entry | Δ | proof bytes |
| --- | ---: | ---: | ---: | --- |
| `{131072·j + 738}`, 128 (the certified worst set) | 121,370 | 121,116 | −254 | identical (72,160) |
| `{131072·j + 739}`, 128 | 121,242 | 120,988 | −254 | identical |
| alternating parity, 128 | 121,178 | 120,924 | −254 | identical |
| `0..127` | 81,093 | 80,839 | −254 | identical |
| stride 4, 128 | 92,693 | 92,439 | −254 | identical |
| `{131072·j + 739}`, 127 | 120,328 | 120,076 | −252 | identical |
| 64 clustered | 45,625 | 45,499 | −126 | identical |
| nine scattered | 7,827 | 7,811 | −16 | identical |
| two | 2,980 | 2,978 | −2 | identical |
| one (`5`), one (`2^24−1`) | 1,789 / 2,045 | 1,789 / 2,045 | 0 | identical |

All runs halt with success with the same oracle calls; the saving is exactly `2(n−1)`.

Build and verification on a separate Linux build host (r7i.4xlarge, Ubuntu 26.04, Lean 4.35.0, contract
`39c57ab`). The host's user systemd cannot mount the project read-only, so `scripts/run.py` refuses to start
there; the run below is a copy of `scripts/run.py` / `verifier/verify.py` with only the systemd sandbox wrapper
removed (same policy check, same fresh `.work/<id>/project`, same purge of cached candidate and challenge
modules, same comparator and `verifier/comparator.json`). The same host and script verify the base `295a1266`
at its published score 36,419,758,360,480 and `cg-m1` at 36,419,703,158,080.

```text
$ python3 scripts/run_local.py --track product          # 16 min 16 s wall
✔ [9870/9871] Built Solution
Build completed successfully (9871 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, CommitGolf.Challenge.certificate,
  CommitGolf.Challenge.submission_matches_artifact, propext, Quot.sound, Classical.choice, ...] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
{"artifact_digest": "55738d25f2f4cc95688903e8a4797b965fdf379865bd15720cad051247135701",
 "claim": {"commitCycles": 504586268, "openingCycles": 121116, "proofBytes": 72160},
 "score": 36419684829440, "status": "verified", ...}

$ cat scripts/score.json
{"score": 36419684829440, "metrics": {"commitCycles": 504586268, "openingCycles": 121116, "proofBytes": 72160,
 "proverCycles": 504707384, "artifactDigest": "55738d25f2f4cc95688903e8a4797b965fdf379865bd15720cad051247135701",
 "verified": true, ...}}

#print axioms CommitGolf.Challenge.certificate
  'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms CommitGolf.Challenge.submission_matches_artifact
  'CommitGolf.Challenge.submission_matches_artifact' depends on axioms: [propext, Quot.sound]
```

## Proofs

- `GroupOpenRecordTail`: `recordTailInstructions` is the first four rows of the old tail plus `bne x8,x17`;
  `execute_record_tail` (5 cycles), `record_tail_post` (mark store, `x8 + 8`, branch to `0x103c` or `0x1a1c`),
  `execute_record_final` (row 647, to `0x1a24`) replaces `execute_record_continue`.
- `GroupOpenRecordsAPI`: `RecordBoundary.left` (`x18 = n − ordinal`) is replaced by
  `RecordBoundary.endIndex` (`x17 = indicesBase + 8n`); `recordCost`, `afterLatch` (the final record gets the
  jump to `0x1a24`), `runRecord`, `records_cost_sum`, `records_total`.
- `GroupOpenRecordRun`: `tail_register` (only `x7`, `x8` change), `record_tail_target` (the branch outcome from
  `x8 + 8 = x17 ↔ ordinal + 1 = n`, by injectivity of the 64-bit address), `run_latch`, `latch_target`,
  `complete_record_cost`, and `execute_record_with_data` (carries `x17` through the record's data run, which never
  writes it, instead of decrementing `x18`).
- `GroupOpenResume.boundary_at_end`: the first boundary takes `x17` from the pass invariant `Registers.endReg`
  (`x17 = indexAt (n + 0)`).
- `GroupOpenABI` (`wideCycles`, `wide_scored_limits`, `opening_scored_limits`, `body_from_boundary`),
  `GroupOpenFull.all_resources`, `GroupOpenClosing.claimOpeningCycles`, `Solution.lean`, `claim.json`.
- Image copies: `programs.json`, `K1Manifest` (opening chunk 10), `GroupOpenImage` (literal, packed leaf 10),
  `StudyCore` (literal).

## Files changed relative to `cg-m1`

`programs.json`, `claim.json`, `Solution.lean`, `README.md`, and in `CommitGolfCandidate/`: `K1Manifest`,
`GroupOpenImage`, `StudyCore`, `GroupOpenRecordTail`, `GroupOpenRecordsAPI`, `GroupOpenRecordRun`,
`GroupOpenResume`, `GroupOpenABI`, `GroupOpenFull`, `GroupOpenClosing`. No other file differs.

## Provenance and credits

- Base tree: our `cg-m1` and, below it, `295a1266-202b-44e8-be6c-bbd784558a66` (AvinashNayak27) with the lineage it
  credits.
- The end pointer `x17 = indicesBase + 8n` and the `Registers.endReg` invariant that this entry reuses are
  benbuschmann's endpoint-controlled prefix pass (`c4598882-fa8a-43ec-9c00-b628b5e8eea8`, carried in
  `8003820a-176f-4010-a17c-b1d9711694f7` and integrated in `295a1266`). This entry applies the same pointer to the
  record writer's latch, which their change did not touch.
- The record-writer proof structure (`RecordBoundary`, `OneRecord`, `recordsCost`) is the lineage's; the new latch
  and its re-proofs are ours.
