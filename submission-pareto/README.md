# Five-ary cap table with three omitted root padding slots

With 16,777,216 leaves, level 10 has two real digests. Its five-slot table group
therefore ends with three zero digests. The opener reports a length that excludes
those 96 bytes, and the checker accepts the shorter length. The checker's
loader supplies zeros beyond the proof, so its table copy and record expansion
still reconstruct the same reference paths. The certificate proves the padding
identity for every honest set of positions.

At 128 positions the proof has 125,440 bytes. The certified commitment and
opening bounds are 472,452,327 and 54,828 cycles, respectively. The cap format
retains the source pointer optimization and all of the other table and record
execution from the preceding entry. The final group still copies all five slots
into memory. Its destination cursor advances only by the 64 bytes reported in
the proof.

## Inherited pointer schedule

This entry builds on `6f7af826-0a98-4c80-811a-0808e9204019`.
Each of the four cap-table levels initializes its own source pointer, so the final
group in each level skips the source increment. All groups still advance the
output pointer and copy the same 20 doublewords. The commitment and checker
images, proof bytes, and ABI are inherited.

The certified bounds are 472,452,327 commitment cycles and 54,828 opening cycles
at 125,536 proof bytes. The opener deletes four instructions from the previous
2,849-word image. The following sections describe the inherited format and its
original cycle accounting.

## Inherited entry: One table for the top four levels of 865ff261's proof: 472,507,159 cycles at 125,536 bytes

This entry is steph4n-gh's accepted Pareto entry `865ff261` with a smaller proof format. Each 1,424-byte record of the base carries a salt and four siblings at each of the eleven levels of its 5-ary tree. At the top of the tree there are few distinct nodes: levels 7 to 10 have 275 slots in all (215 + 45 + 10 + 5, ragged zero slots included), yet 128 records carry 65,536 bytes of siblings there. Here each record stops at level 6, and one table with every slot of levels 7 to 10 follows the records. The check image starts with a wrapper that rebuilds the base's records from the records and the table, then runs the base's checker unchanged. The commitment image and the salts are unchanged.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes |
| --- | ---: | ---: | ---: | ---: |
| `865ff261` by steph4n-gh (base) | 472,452,327 | 77,601 | 472,529,928 | 182,272 |
| This entry | 472,452,327 | 54,832 | 472,507,159 | 125,536 |

`claim.json` is `{"proofBytes": 125536, "commitCycles": 472452327, "openingCycles": 54832}`.

## Proof format

- Records: for each opened position in ascending order, the base record's first 912 bytes (the salt and the four siblings at each of levels 0 to 6, in the base's rotation order).
- Table, after the records: every slot of levels 7, 8, 9 and 10 in trapdoor order, as 55 groups of five 32-byte slots, ragged zero slots included. It is the same for every set of positions.
- Length `912k + 8,800` for k ≥ 1 positions and 0 for the empty opening: 125,536 bytes at k = 128, against `1,424k` for the base.

## Images

- Opening, 2,849 words: the record loop keeps the base's code up to level 6 (words 0–102) and gets a new latch (words 103–105). Word 106 jumps to an appended copy of the table (words 527–2,848), which ends with the base's exit sequence. Words 107–147, which wrote levels 7 to 10, are now no-ops; words 148–526 are unchanged.
- Check, 775 words: word 0 jumps to the wrapper at words 460–774; words 1–459 are the base's checker. The wrapper rejects any length other than `912k + 8,800` (k = 0: empty), parks the table in scratch memory, expands the records from the last one down into the base's 1,424-byte layout, clears the leftover bytes, restores the loader's registers and jumps to word 1. It makes no oracle calls. Check fuel is `2^40` steps; the wrapper needs at most `851k + 5,000`.
- Commitment: byte-identical to the base's.

## Security

- Binding: the base's binding theorem uses the oracle calls of an accepting check run (`PentaAcceptedTrace`), not the proof bytes. The wrapper makes no oracle calls and keeps the commitment, positions and values, so an accepting run on this format is an accepting run of the base checker on the expanded proof.
- Hiding: the base's hiding theorem (`penta_counter_hiding_of_transcript`) holds for any transcript builder that is local in its sense (`PentaBuildLocal`). The new builder (`capTranscriptBuilder`), which also outputs the level 7–10 table, is proved local (`cap_transcript_builder_local`): its proof part reads only nodes of levels up to 10, and the commitment remains the level-11 root.

## Lean changes

New modules: `PentaCapSpec`, `PentaCapRoundtrip`, `PentaCapFacts`, `PentaWrapCode`, `PentaWrapMemory`, `PentaWrapLoader`, `PentaWrapTable`, `PentaWrapRecord`, `PentaWrapRunA`, `PentaWrapRunB`, `PentaWrapRunC`, `PentaWrapCheckImage`, `QuadOpeningFooter`. Changed base modules: `QuadCommitImage` (check fuel), `QuadCheckImage`, `QuadCheckLoader`, `QuadCheckerMeasure`, `QuadHeaderAssembly`, `QuadCheckerObservation`, `QuadCheckerComplete`, `QuadOpeningImage`, `QuadOpeningLevel`, `QuadOpeningLevels`, `QuadOpeningRecord`, `QuadOpeningABI`, `QuadOpeningModel`, `QuadOpeningProofBytes`, `PentaOpenFull`, `PentaCounterCertificate`, and `Solution.lean`. The 28 base modules that nothing reachable from `Solution.lean` imports are not included.

## Credits

- Base: `865ff261-6a95-400c-a4cd-5dee6b1e699e` by steph4n-gh, which joins valproate-acid's 5-ary tree, record writer and checker (`f5ae28bd-8f22-4693-9071-c777c40e2419`) with mitchuski's counter-mode salts (`076b6f1a-c099-4993-8b98-fc3b92c112a3`). The record writer and checker this entry changes are valproate-acid's.
- steph4n-gh's note lists "pruned top caps on the 5-ary tree" as a next step; this entry is one such cap.
- The base's README follows unchanged. Its figures describe the base, not this entry.

---

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
