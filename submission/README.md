# Quartet with grouped in-place salts over 4,096-leaf windows

This submission is bc5cc89e-4952-4ff7-be8d-9d11905d730c (public commit f95b0dbe5b02a7d762128c74d5d7fe6a3b99e0ea:
dadon's grouped in-place salt generator of 2b2405a1-5be9-4681-b48e-a0fcefd4588d with one salt cursor per two groups)
with the salt groups re-tiled over whole 4,096-leaf bodies. The tree, leaf function, proof format and check program are
unchanged.

## What changed against bc5cc89e

**Commit.** In 2b2405a1 and bc5cc89e a group of up to eleven leaves shares one keyed permutation reply: the group's
first leaf ("head") calls the permutation on (counter, key), the reply's last 16 bytes land in its own salt slot and the
other leaves copy 16-byte slices of the reply. Groups were laid out per 64-leaf window (11, 11, 11, 11, 11, 9), six
heads per 64 leaves. Here the groups run over the whole 4,096-leaf unrolled body: 372 groups of eleven and one of four,
373 heads per body instead of 384, and 187 pair heads (shared cursor writes) instead of 192.

- A head costs 7 cycles more than an ordinary leaf (one call, three address instructions, one store, minus the four
  salt loads and stores), plus 1 cycle when it starts a cursor pair. Per body: 11 heads and 5 pair heads fewer,
  82 cycles fewer, 335,872 cycles over the vector.
- The body is shorter; the latch moves to words 45,392 (`beq s4,s9,796`) and 45,393 (`jal zero,-181488`,
  2,097,152-wrapped 1,915,664), and 197 never-executed `nop`s keep every later word at its address.
  Commit words 21-45,590 change; all other commit words, the layout, sizes and steps are unchanged.
- Counters are still the byte address of each group's first leaf, so they stay distinct.
  A commitment makes 43,470,847 oracle calls (2·2^24 leaf calls, 1,527,808 group calls, 2^22 quartet calls,
  2^22 − 1 parents).

**Opening.** One instruction: the salt-materialising prefix computes the rank inside a group as `(i mod 4096) mod 11`.
Word 740 `andi t3,t1,63` becomes `remu t3,t1,s10` (`s10` = x26 already holds 4,096, the counter base of the prefix).
The prefix row costs 3 cycles more, i.e. +3 cycles per opened position, +384 for 128 positions. Proof bytes are
unchanged.

**Check.** Byte-identical to bc5cc89e and 2b2405a1 (and to our Quartet's variant-B check image).

## Bounds

| | bc5cc89e | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,841,054 | **519,505,182** |
| opening cycles, 128 positions (worst case) | 98,057 | **98,441** |
| proof bytes, 128 positions (worst case) | 72,192 | **72,192** |
| score | 37,535,444,301,312 | **37,511,224,751,616** |

`claim.json`: `{"commitCycles":519505182,"openingCycles":98441,"proofBytes":72192}`.
Score = (519,505,182 + 98,441) × 72,192 = 37,511,224,751,616: 0.0645 % below bc5cc89e (accepted record),
0.0062 % below the 2,048-window claims 45a3e161 / 44123313 (37,513,562,617,344), 0.216 % below 2b2405a1.

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 519505182 98441`, with
`submission := CommitGolf.Artifact.submission` and `submission_matches_artifact` by `rfl`. The proof is bc5cc89e's,
with the window constant changed and the opener's prefix row re-proved:

- **Commit** (`Grouped.commit_resources`, `Grouped.full_commit`): every commit run succeeds in exactly 519,505,182
  cycles (215,209,250 steps) with 43,470,847 calls. The leaf body is the parametric `packet n` of `GroupedImageBase`
  with `heads n = 373·(n/4096) + (n%4096+10)/11`, `rank`, `pairPos` and `pairHeads n = 187·(n/4096) + (n%4096+21)/22`
  for the 4,096 period; the 64 kernel tile checks of `GroupedPacketDecode` compare every body word with it.
- **Salts and hiding** (`CounterSaltLayout`, `QuartetCounterSecurity`, `QuartetCounterCertificate`): group `j` has
  first leaf `4096·(j/373) + 11·(j%373)`, leaf `i` sits at `coord i = (373·(i/4096) + (i%4096)/11, (i%4096)%11)`;
  `coord` is injective and the counters are distinct, so the counter-mode game of 2b2405a1 applies unchanged with
  1,527,808 groups. The budget `(t+1)/2^121 + 2·groups·(2q+groups)/2^192 ≤ (t+1)/2^120` holds for the smaller
  group count.
- **Opening** (`GroupOpenWalk`, `GroupOpenStep`, `GroupOpenLatch`, `GroupOpenPass`, `GroupOpenFull`): the prefix row
  740 is `REMU x28, x6, x26`; `GroupOpenStep.masked` proves `remu i 4096 = i mod 4096` for indices below 2^24 and
  `decoded_rank` gives the group rank; the per-position charge of the seven prefix rows is 13 cycles instead of 10,
  and the opening bound becomes 98,441 (`13·p.card` in `GroupOpenFull`).
- **Check, binding, assembly**: bc5cc89e's, unchanged.

## Commands and results

From the project root, pinned Lean 4.35.0 toolchain, candidate cache purged as `verify.py` does,
`CommitGolf/Artifact.lean` regenerated from `programs.json` with `verifier/artifact.py`:

- `lake build +Solution`: build completed successfully.
- `lake env lean Audit.lean`: `certificate` depends on [propext, Classical.choice, Quot.sound];
  `submission_matches_artifact` on [propext, Quot.sound].
- `python3 verifier/check_submission.py <tree>`: ok, 602 files, score 37,511,224,751,616.
- The exact-cycle interpreter of the commit image (`budget_q.py`) reproduces 519,505,182 cycles and 43,470,847 calls
  (and 519,841,054 on bc5cc89e's image). A full-size RV64IM emulation (Keccak-f stand-in for the oracle) of the
  three images: commit 519,505,182 cycles / 215,209,250 steps; openings of group-edge and random positions 96,209 and
  96,396 cycles (≤ 98,441), 71,502 and 71,412 bytes; the check accepts the honest proof and rejects a changed value
  and a changed proof byte.
- `lake env leanchecker` replays every compiled candidate module, `CommitGolf.Artifact` and `Solution`.
- Commit image 807,068 bytes (< 1 MiB).

## Provenance

- bc5cc89e (kaankolcu, our account): the whole tree; 22 candidate files and `Solution.lean` adapted as listed in
  DEPENDENCIES.md, the other 575 modules byte-identical.
- 2b2405a1 (dadon): the grouped in-place generator, its hiding proof, the grouped commit and opening proofs.
- 20182e74 (dadon), b64a994e and c08b0128 (kaankolcu), c28dd9ca (dadon), 33bdbed6 (kaankolcu): the lineage
  under 2b2405a1 (Quartet tree, opening record writer, checker, chain-salt modules).
- newjordan's 45a3e161 and our 44123313 (in flight at freezing time) claim the bounds of the 2,048-leaf re-tiling
  (519,537,950 / 98,057 / 72,192); no file of 45a3e161 is used here. This tree extends the re-tiling to the whole
  4,096-leaf body with the `remu` opener row.
