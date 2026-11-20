# Product: chain constants 374 and 4352 held in `gp`/`sp` across the prefix pass (-252 opening cycles)

Built on our `cg-m2` ([SUBMISSION ID OF cg-m2]) and `cg-m1` ([SUBMISSION ID OF cg-m1]), on the promoted product
best `295a1266-202b-44e8-be6c-bbd784558a66` (AvinashNayak27, promoted commit
`39c57aba0e611a1b56c2dd87b24d4990812a46ff`). Only opening rows 739, 754..757 and 777..794 change. The commitment and
checker images, embedded data, the ABI and the proof serialization are unchanged.

## Result

| | `295a1266` | `cg-m2` (base) | This entry |
| --- | ---: | ---: | ---: |
| proof bytes | 72,160 | 72,160 | 72,160 |
| commitment cycles | 504,586,268 | 504,586,268 | 504,586,268 |
| opening cycles (128 positions, proved bound) | 122,135 | 121,116 | **120,864** |
| score | 36,419,758,360,480 | 36,419,684,829,440 | **36,419,666,645,120** |

`(504,586,268 + 120,864) × 72,160 = 36,419,666,645,120`, 18,184,320 below `cg-m2` (252 cycles × 72,160 bytes).

## The chain block before

The prefix pass regenerates each opened position's salt on the linked schedule: one keyed generator call for the
head of the position's chain, then `k` in-place links (`k = ((g mod 4096) / 11) mod 34`, at most 33). The counter
block that feeds the keyed call is pepedesigner's 374-based form (`ca54b35f`):

```
777 slli x30,x6,52     778 srli x30,x30,52                          n = g mod 4096
779 addi x31,x0,374    780 remu x31,x30,x31                         r = n mod 374
781 divu x30,x31,x29   782 remu x28,x31,x29                         k = r / 11, rank = r mod 11
783 sub  x7,x6,x31     784 addi x7,x7,1    785 slli x7,x7,8    786 add x7,x7,x26
787 sd   x7,0(x10)                                                  counter = ((g - r + 1) << 8) + 4096
788 slli x31,x30,2     789 ecall                                    keyed call
790 auipc x7,0         791 sub x7,x7,x31   792 addi x10,x12,0   793 jalr x0,556(x7)   into the link block
```

Rows 779 and 784 only build constants: the modulus 374 and the `+1` that, after the shift, adds 256 to the
counter. Both are paid once per position, 128 times in a scored opening.

## The change

`gp` (x3) and `sp` (x2) are never named by any opener instruction (checked on the disassembly of all 1,976
words: only the four rows 755, 756, 779 and 784 name them), and the ecall interface only reads `x5`,
`x10`..`x13`. So the header sets them once:

```
739 jal  x0,<754>          (was: addi x4,x0,-1)
754 addi x4,x0,-1          the old row 739: no previous quartet
755 addi x3,x0,374         gp = 374
756 addi x2,x26,256        sp = 4096 + 256 = 4352
757 jal  x0,<740>          first position
```

Rows 754..757 were four `nop`s behind the unconditional `jal` at 753 and were not reached before. The header
grows from 31 to 35 cycles per opening (the two `jal`s and the two constants). The chain block becomes

```
777 slli x30,x6,52 ; 778 srli x30,x30,52 ; 779 remu x31,x30,x3 ; 780 divu x30,x31,x29 ; 781 remu x28,x31,x29
782 sub x7,x6,x31  ; 783 slli x7,x7,8    ; 784 add x7,x7,x2    ; 785 sd x7,0(x10)     ; 786 slli x31,x30,2
787 ecall          ; 788 auipc x7,0      ; 789 sub x7,x7,x31   ; 790 addi x10,x12,0   ; 791 jalr x0,564(x7)
792..794 nop (not reached)
```

`((g − r) << 8) + 4352 = ((g − r + 1) << 8) + 4096`, so the generator input, every reply and every proof byte are
unchanged; the jump into the link block still lands on row `929 − k` (`564 = 4·(929 − 788)`, where the old
`556 = 4·(929 − 790)`). The link block 896..929, the `jal` back and the exit row 795 are untouched. Per position
the chain costs `33 + 8k` instead of `35 + 8k` (297 instead of 299 at `k = 33`).

## Bound

- `chainSteps = 17 + k` (was 19): 10 counter rows, the keyed call, 4 entry rows, `k` links, the `jal` back and
  the exit row. `chainCycles = chainSteps + 9 + 7·chainCalls` keeps its form (the three divide/remainder rows
  cost 4 each), so `chain_cycles_le` is 297 (was 299).
- `pass_cycles_bound`: `passCycles p n j ≤ 345·n + 2` (was `347·n + 2`; 36 head + 297 chain + 12 post).
- Header: 35 rows, 35 cycles (`HeaderFacts.run`, `header_run`).
- Opening: `35 + (345·128 + 2) + (76,682 − 15) = 120,864` (`cg-m2`: `31 + (347·128 + 2) + (76,682 − 15)`).

A one-position opening pays two cycles more than before (four header cycles against two saved); openings with
two or more positions break even or gain, and the scored 128-position bound drops by `2·128 − 4 = 252`.

## Evidence

Memory-backed RV64IM emulator (Riscv.lean cost model, deterministic stand-in oracle replies), same inputs as
`cg-m1`/`cg-m2`:

| position set | `cg-m2` cycles | this entry | Δ | proof bytes |
| --- | ---: | ---: | ---: | --- |
| `{131072·j + 738}`, 128 (the certified worst set) | 121,116 | 120,864 | −252 | identical (72,160) |
| `{131072·j + 739}`, 128 | 120,988 | 120,736 | −252 | identical |
| alternating parity, 128 | 120,924 | 120,672 | −252 | identical |
| `0..127` | 80,839 | 80,587 | −252 | identical |
| stride 4, 128 | 92,439 | 92,187 | −252 | identical |
| `{131072·j + 739}`, 127 | 120,076 | 119,826 | −250 | identical |
| 64 clustered | 45,499 | 45,375 | −124 | identical |
| nine scattered | 7,811 | 7,797 | −14 | identical |
| two | 2,978 | 2,978 | 0 | identical |
| one (`5`), one (`2^24−1`) | 1,789 / 2,045 | 1,791 / 2,047 | +2 | identical |

All runs halt with success and make the same oracle calls.

## Build and verification

On a separate Linux build host (r7i.4xlarge, Ubuntu 26.04, Lean 4.35.0, contract `39c57ab`). The host's user
systemd cannot mount the project read-only, so `scripts/run.py` refuses to start there; the run below is a copy of
`scripts/run.py` / `verifier/verify.py` with only the systemd sandbox wrapper removed (same policy check, same
fresh `.work/<id>/project`, same purge of cached candidate and challenge modules, same comparator and
`verifier/comparator.json`). The same host and script verify the base `295a1266` at its published score
36,419,758,360,480, `cg-m1` at 36,419,703,158,080 and `cg-m2` at 36,419,684,829,440.

```text
$ python3 scripts/run_local.py --track product          # 16 min 13 s wall
✔ [9870/9871] Built Solution
Build completed successfully (9871 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, CommitGolf.Challenge.certificate,
  CommitGolf.Challenge.submission_matches_artifact, propext, Quot.sound, Classical.choice, ...] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
{"artifact_digest": "b514c0df4532fcdac88966edb1dbe8a3f644d0b41851714ea1300d5fdc6168d5",
 "claim": {"commitCycles": 504586268, "openingCycles": 120864, "proofBytes": 72160},
 "score": 36419666645120, "status": "verified", ...}

$ cat scripts/score.json
{"score": 36419666645120, "metrics": {"commitCycles": 504586268, "openingCycles": 120864, "proofBytes": 72160,
 "proverCycles": 504707132, "artifactDigest": "b514c0df4532fcdac88966edb1dbe8a3f644d0b41851714ea1300d5fdc6168d5",
 "verified": true, ...}}

#print axioms CommitGolf.Challenge.certificate
  'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms CommitGolf.Challenge.submission_matches_artifact
  'CommitGolf.Challenge.submission_matches_artifact' depends on axioms: [propext, Quot.sound]
```

## Proofs

- `K3OpenChainRows`: `chainPreRows` (777..786, `remu x31,x30,x3`, `add x7,x7,x2`), `chainEnterRows` (788..791,
  `jalr x0,564(x7)`), `keyed_fetch` (787), `chainSteps = 17 + chainLinks`, `chain_lengths` (10 rows / 19 cycles,
  4 / 4, 2 / 2). `ChainEntry` gains `gp : x3 = 374` and `sp : x2 = 4352`. `chain_before` reaches the keyed call at
  787; its counter uses the new `chain_counter_sp` (`((g − r) << 8) + 4352`, from the lineage's `chain_counter'`
  and `256 + 4096 = 4352`). `after_keyed` (788), `enter_target` (`address 788 − 4k + 564 = address (929 − k)`),
  `enter_rows` (788). `K3OpenChainRun`, `K3OpenChainLink`, `K3OpenChainPost`, `K3OpenChainExit` and
  `K3OpenChainReply` build unchanged on the new rows; the chain still leaves at `address (chainStart + 19) = 796`
  and keeps every register other than `x7, x10, x28, x30, x31`, so `x3`/`x2` survive each position.
- `GroupOpenStep.Input` and `GroupOpenPass.Ready` gain `gp`/`sp`. `next_ready` carries them through each
  position with the existing `Saved` frame (`x3`, `x2` are outside the per-position write set
  `x4, x6, x7, x10, x13, x14, x17, x25, x28, x30, x31`); `input_of_ready` hands them to the position, and
  `GroupOpenLatch.exit_of` passes them from the head's register frame into `ChainEntry`.
- Header: `GroupOpenHeaderSpec.markRows` is `739 jal; 754 addi x4; 755 addi x3; 756 addi x2,x26,256; 757 jal`,
  and `HeaderFacts.run` charges 35. `GroupOpenHeaderParts.mark_frame` gives `pc = 740`, `x4 = 2^64 − 1`,
  `x3 = 374`, `x2 = 4352` (from `x26 = 4096`, set at 723 and kept by the config and key rows) and keeps every
  other register and memory (the memory goal is closed with offset-generic `jal`/`addi` lemmas; with the concrete
  `jal` offsets the kernel check recursed too deeply). `GroupOpenHeaderCore.HeaderRegisters` gains `gp`/`sp`;
  `GroupOpenHeader.header_valid` builds the extended `Ready`, `header_run` is 35 rows / 35 cycles.
- `GroupOpenPass` (`chain_cycles_le` 297, `pass_cycles_bound` `345·n + 2`), `GroupOpenFull` (header 35 in
  `leftOver`, `allowance`, `machine_run`, `all_resources`), `GroupOpenClosing.claimOpeningCycles`,
  `Solution.lean`, `claim.json`.
- Image copies: `programs.json`, `K1Manifest`, `GroupOpenImage`, `StudyCore`.

## Files changed relative to `cg-m2`

`programs.json`, `claim.json`, `Solution.lean`, `README.md`, and in `CommitGolfCandidate/`: `K1Manifest`,
`GroupOpenImage`, `StudyCore`, `K3OpenChainRows`, `GroupOpenStep`, `GroupOpenPass`, `GroupOpenLatch`,
`GroupOpenHeaderSpec`, `GroupOpenHeaderParts`, `GroupOpenHeaderCore`, `GroupOpenHeader`, `GroupOpenFull`,
`GroupOpenClosing`. No other file differs.

## Provenance and credits

- Base: our `cg-m2`/`cg-m1` and `295a1266-202b-44e8-be6c-bbd784558a66` with its lineage.
- The 374-based counter and its proofs (`K3OpenChain*`, `GroupOpenPass`) are pepedesigner's
  `ca54b35f-af11-4644-8031-a6d8b9e6fef6`; the straight-line link block is patternrecognition9-del's
  `42ccb0c2-770b-47da-89be-0c846a629cb2` as re-proved in the lineage. This entry only moves two constants out of
  that block.
- The register plan (`gp`, `sp`, the dead rows 754..757) and the re-proofs are ours.
