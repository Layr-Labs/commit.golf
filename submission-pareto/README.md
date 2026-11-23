# 5-ary Penta Permutation Tree with 4,095-Leaf Counter-Mode In-Place Salts

This Pareto-track candidate combines:

1. **5-ary (penta) permutation tree, record writer, and checker** from accepted submission
   `f5ae28bd-8f22-4693-9071-c777c40e2419` (commit `966f29e9b709833d23f67ffc27a4124b7a672628`),
   preserving levels 1..10, the root node, the 1424-byte proof record format, and the 460-word
   checker image verbatim.
2. **Counter-mode in-place salt generation with register prefetching** adapted from accepted
   submission `076b6f1a-c099-4993-8b98-fc3b92c112a3` (commit `fda8496ea3b71ba2a364c5ec8679fe18983b7580`),
   eliminating the upfront 15.26M-cycle `NonceChain` tape pass and all per-leaf salt tape loads.

## Key Design Changes

- **4,095-leaf counter-mode loop period (`1 + 4097 * 4095 = 2^24`)**:
  Each pass of the unrolled commit leaf body processes `4,095 = 91 * 45 = 372 * 11 + 3` leaves
  (`372` full 11-leaf salt groups with 4-word register prefetch into `x14..x17` for ranks `9` and `10`,
  plus one short 3-leaf group at slots `4092..4094`). Every 45 leaves (9 penta groups),
  `ADDI x20, x12, 1776` rebases the centered 12-bit destination window directly from `x12`.
- **Trailing final leaf (`i = 2^24 - 1 = 4097 * 4095`)**:
  Placed after the loop latch (words `45,190..45,200`) as a standalone 1-leaf counter-mode group,
  so `rank(i) = (i % 4095) % 11` has no index-shift special case across all `2^24` leaves and
  leaves `x12 = wordAddress (leafWord (2^24 - 1))` directly ready for `leafZeroWords` at word `45,201`.
- **On-the-fly salt materialization in the opener (48 appended words, 527 words total)**:
  On non-empty openings, word `2` jumps to word `479`, executes the displaced setup, copies the
  24-byte key from `nonceBase + 8..24` into scratch `1032..1048`, regenerates each opened leaf's
  16-byte salt via `P(4096 + 256 * (i - rank(i)) || key || 0)` into `nonceBase + 16 * i`, and
  jumps to word `11` to run the unchanged penta record loop and exit.

## Resource Comparison

| Metric | Prior lowest-cycle frontier (`f5ae28bd`) | This submission | Delta |
|---|---:|---:|---:|
| Commit cycles | 477,082,487 | **472,452,327** | **-4,630,160** |
| Opening cycles (128 positions) | 73,103 | **77,601** | +4,498 |
| Total prover cycles | 477,155,590 | **472,529,928** | **-4,625,662** |
| Opening proof bytes | 182,272 | **182,272** | 0 |

## Lean Proof Architecture (`CommitGolfCandidate/`)

- **Counter-mode security**: `CounterSaltLayout.lean` (4,095-leaf period, `groups = 1,528,182`),
  `CounterSalt{Replay,Game,Oracle,Windows}.lean`, and `PentaCounterSecurity.lean` proving
  120-bit statistical hiding (`penta_counter_hiding`).
- **Commit machine proof**: `PentaGrouped{Base,Decode,CommitImage,Packet,PacketRun,Scan,Eval,Content,Frame,Invariant,KeySetup,Commit}.lean`
  proving exact commit execution (197,513,870 steps, 39,276,922 oracle calls, 472,452,327 cycles)
  and handing off directly to the unchanged `QuadCommitPenta{Pass,Level,Layouts,Content,Root}` and
  `QuadCommit{Execution,Meaning}` modules at word `45,201`.
- **Opening machine proof**: `QuadOpeningImage.lean` (527 words), `QuadOpeningABI.lean`
  (`body_from_record_at`), and `PentaOpen{Loop,Effect,Pass,Header,Full}.lean` proving exact
  opening execution (`≤ 77,601` cycles, `128` oracle calls, `182,272` proof bytes) and virtual
  trapdoor equivalence to the honest penta transcript.
- **Certificate assembly**: `PentaCounterCertificate.lean` and `Solution.lean` proving
  `CommitGolf.Certificate submission 182272 472452327 77601` and `submission_matches_artifact`.
