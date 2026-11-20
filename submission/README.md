# Product: three-cycle sibling step and four-cycle climb in the opener's cap walk (-765 opening cycles)

Built on the promoted product best `295a1266-202b-44e8-be6c-bbd784558a66` (AvinashNayak27, promoted commit
`39c57aba0e611a1b56c2dd87b24d4990812a46ff`, claim 72,160 / 504,586,268 / 122,135). This entry changes six words
of the opening image (rows 660 and 701..705) and the proofs that read them. The commitment image, the checker
image, embedded data, the ABI, the proof serialization and every other opening word are unchanged.

## Result

| | `295a1266` (base) | This entry |
| --- | ---: | ---: |
| proof bytes | 72,160 | 72,160 |
| commitment cycles | 504,586,268 | 504,586,268 |
| opening cycles (128 positions, proved bound) | 122,135 | **121,370** |
| score | 36,419,758,360,480 | **36,419,703,158,080** |

`(504,586,268 + 121,370) × 72,160 = 36,419,703,158,080`, 55,202,400 below the base (765 cycles × 72,160 bytes).

## The cap walk before

After the record writer, the opener emits the cap frontier with a stackless depth-first walk over the 511 cap
nodes (`x6` = node, `x23 = 1`). A node is looked up at row 661 (`slli; add; ld; beq`), a marked internal node
descends at 665..667, an unmarked node is copied (668..700), and the advance block at 701..708 decides where to go
next. In the base (the `x23` root compare promoted in `85d5822f`) it was:

```
701 beq  x6,x23,<709>      root reached: return block
702 andi x7,x6,1
703 beq  x7,x0,<707>       even node: step to its right sibling
704 srli x6,x6,1           odd node: climb to the parent ...
705 jal  x0,<701>          ... and test again
707 addi x6,x6,1
708 jal  x0,<661>
```

Both moves cost five cycles: a step across `701,702,703,707,708` and a climb `701,702,703,704,705`. The root exit
was the taken `beq` at 701 (one cycle) followed by the four-cycle return block at 709.

## The cap walk now

```
660 addi x6,x6,1           (step across; falls into the lookup at 661)
701 andi x7,x6,1
702 beq  x7,x0,<660>       even node: step across                         3 cycles
703 srli x6,x6,1           odd node: climb ...
704 bne  x6,x23,<701>      ... and continue while the parent is not the root  4 cycles
705 jal  x0,<709>          the root is reached only here                  +1 cycle
```

Row 660 was the exit `jal` of the old descending mark loop (650..660). That loop has not been reachable since the
cap preparation was unrolled (row 649 jumps to the unrolled sweep at 1097, which returns to 661 directly), and no
branch, jump or linked return of the image targets 650..660; row 660 now holds the step across, so the even path
falls straight into the lookup. Rows 706..708 are no longer reached and are left as they were.

The root test moved from the entry of the block to the climb. This is sound because the walk never enters 701 with
`x6 = 1`: 701 is entered after a node is copied (row 700), from a marked cap leaf (`bgeu x6,x27` at 665, so
`x6 ≥ 256`) and from the climb itself (`bne` taken, so the parent is not 1). A copied node is never the root,
because the root is marked whenever at least one position is opened (every cap group of a position lies in
`[256, 512)`, so its top bits are 1). The empty opening leaves at row 2 and never runs the walk.

Per marked internal node the walk now spends 7 (lookup and descent) + 3 (across) + 4 (climb back) = 14 cycles
instead of 17. The root's last climb costs one more cycle (the `jal` at 705), which replaces the old one-cycle root
test, so the exit accounting is unchanged.

## Bound

- `capSubtreeCycles`: a marked internal node is charged 14 (was 17); leaves (5) and emitted nodes (37) unchanged.
- `capControlWorst 8 = 4,850` (was 5,615): the full height-8 cap has 255 internal nodes, `255 × 3 = 765`.
- `cap_walk_scored_bound`: `capWalkCycles groups 1 8 base 0 ≤ 9,074` (was 9,839) for at most 128 frontier nodes.
- `wide_scored_limits`: `wideCycles ≤ 76,936` (was 77,701). `wideCycles` keeps its form
  `15 + (137n + copySum n − 1) + 770 + (capWalkCycles + 2) + 4`; its fixed part `770 + 2 + 4` is now read as
  771 (cap preparation, including the jump at 649) + 1 (root exit `jal` at 705) + 4 (return block), where it was
  771 + 1 (root test at 701) + 4.
- Opening: `31 + (347·128 + 2) + (76,936 − 15) = 121,370`.

## Evidence

A memory-backed RV64IM emulator (the Riscv.lean cost model; oracle replies are a deterministic stand-in, which
does not affect cycles or control flow here) runs the base and the new opener on the same inputs:

| position set | base cycles | new cycles | Δ | proof bytes |
| --- | ---: | ---: | ---: | --- |
| `{131072·j + 738}`, 128 positions | 122,135 | 121,370 | −765 | identical (72,160) |
| `{131072·j + 739}`, 128 | 122,007 | 121,242 | −765 | identical |
| alternating parity, 128 | 121,943 | 121,178 | −765 | identical |
| `{131072·j + 739}`, 127 | 121,090 | 120,328 | −762 | identical |
| `0..127` | 81,117 | 81,093 | −24 | identical |
| stride 4, 128 | 92,717 | 92,693 | −24 | identical |
| 64 clustered | 45,649 | 45,625 | −24 | identical |
| nine scattered | 7,890 | 7,827 | −63 | identical |
| two (`0`, `2^24−1`) | 3,025 | 2,980 | −45 | identical |
| one (`5`), one (`2^24−1`) | 1,813 / 2,069 | 1,789 / 2,045 | −24 | identical |

All runs halt with success and make the same oracle calls. The base's first row reproduces its certified bound
122,135 exactly, and the new opener reaches the new certified bound 121,370 on the same set.

Build and verification on a separate Linux build host (r7i.4xlarge, Ubuntu 26.04, Lean 4.35.0, contract
`39c57ab`). The host's user systemd cannot mount the project read-only, so `scripts/run.py` refuses to start
there; the run below is a copy of `scripts/run.py` / `verifier/verify.py` with only the systemd sandbox wrapper
removed (same policy check, same fresh `.work/<id>/project`, same purge of cached candidate and challenge
modules, same comparator and `verifier/comparator.json`). The same host and script verify the base `295a1266`
at its published score 36,419,758,360,480.

```text
$ python3 scripts/run_local.py --track product          # 16 min 52 s wall
✔ [9870/9871] Built Solution (3.4s)
Build completed successfully (9871 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, CommitGolf.Challenge.certificate,
  CommitGolf.Challenge.submission_matches_artifact, propext, Quot.sound, Classical.choice, ...] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
{"artifact_digest": "98fd4f6085242c4f7019b7a73809d4ceb395dfa024474605d07c9faac1013615",
 "claim": {"commitCycles": 504586268, "openingCycles": 121370, "proofBytes": 72160},
 "score": 36419703158080, "status": "verified", ...}

$ cat scripts/score.json
{"score": 36419703158080, "metrics": {"commitCycles": 504586268, "openingCycles": 121370, "proofBytes": 72160,
 "proverCycles": 504707638, "artifactDigest": "98fd4f6085242c4f7019b7a73809d4ceb395dfa024474605d07c9faac1013615",
 "verified": true, ...}}

#print axioms CommitGolf.Challenge.certificate
  'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms CommitGolf.Challenge.submission_matches_artifact
  'CommitGolf.Challenge.submission_matches_artifact' depends on axioms: [propext, Quot.sound]
```

## Proofs

- `GroupOpenCapCursor.capWalkInstructions`: row 660 is `addi x6,x6,1`; rows 701..708 are the new block.
- `GroupOpenCapAdvance`: `advanceCode`; `execute_advance_parity_test`/`advance_parity_target` (701/702, to 660 or
  703); `execute_advance_right`/`advance_right_post` (660); `execute_advance_up`/`advance_up_post` (703/704, to 701 or
  705); `execute_advance_exit` (705, to 709).
- `GroupOpenCapMoves`: `advance_checks` (two cycles, no root test), `advance_left_to_right` (3 cycles),
  `advance_climb`, `advance_right_to_parent` (4 cycles, parent > 1), `advance_right_to_root` (5 cycles, ends at 709).
- `GroupOpenCapSubtree`: `cap_subtree_general` takes `1 < node`; the new `cap_root_general`/`cap_root_of_emit` walk
  the root (both children through the general theorem) and end at 709 after `capWalkCycles + 1` cycles; the `x30`
  preservation lemmas follow the new rows.
- `GroupOpenCapCost`: the 14-cycle charge and the constants above.
- `GroupOpenCapEmit.cap_root`, `GroupOpenFinish.root_exit` (the four-cycle return block from 709),
  `GroupOpenABI.cap_root_marked` (the root is marked when a position is opened) and `body_from_boundary`.
- Claim sites: `GroupOpenABI.wide_scored_limits`/`opening_scored_limits`, `GroupOpenFull.all_resources`,
  `GroupOpenClosing.claimOpeningCycles`, `Solution.lean`, `claim.json`.
- Image copies: `programs.json`, `K1Manifest` (opening chunks 10 and 11), `GroupOpenImage` (literal, packed
  leaves 10 and 11, the row-660 entry of `t238Rows`), `StudyCore` (literal).

## Files changed relative to `295a1266`

`programs.json`, `claim.json`, `Solution.lean`, `README.md`, and in `CommitGolfCandidate/`: `K1Manifest`,
`GroupOpenImage`, `StudyCore`, `GroupOpenCapCursor`, `GroupOpenCapAdvance`, `GroupOpenCapMoves`,
`GroupOpenCapSubtree`, `GroupOpenCapCost`, `GroupOpenCapEmit`, `GroupOpenFinish`, `GroupOpenABI`, `GroupOpenFull`,
`GroupOpenClosing`. No other file differs.

## Provenance and credits

- Base tree, every unchanged proof and image word: `295a1266-202b-44e8-be6c-bbd784558a66` (AvinashNayak27) and the
  lineage it credits (`ccb3572f`, `8003820a`, `c4598882`, `a8867e15`, `55e0c64c`, `85d5822f`, `657fbda1`, ...).
- The five-cycle advance block this entry replaces, and its `x23 = 1` invariant through the cap walk, come from
  `85d5822f-6ce4-4456-b66f-0f937bb782a3` (AvinashNayak27; first filed as `4929bf59` and `69bbc725`, which did not
  pass validation). The `x23` compare is reused here by the `bne` at 704.
- The cap-walk proof structure (`CapRun`, `cap_subtree_general`, `capWalkCycles` with its copy-saving potential)
  is the lineage's; this entry adds the root variant and re-proves the advance moves for the new rows.
- The rotated advance block, the use of the dead row 660 and the re-proofs are ours.
