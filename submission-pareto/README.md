# Quartet with grouped in-place salts over 2,048-leaf windows

This submission is bc5cc89e-4952-4ff7-be8d-9d11905d730c (public commit f95b0dbe5b02a7d762128c74d5d7fe6a3b99e0ea:
dadon's grouped in-place salt generator of 2b2405a1-5be9-4681-b48e-a0fcefd4588d with one salt cursor per two groups)
with the salt groups re-tiled. The tree, leaf function, proof format and check program are unchanged.

## What changed against bc5cc89e

**Commit.** In 2b2405a1 and bc5cc89e a group of up to eleven leaves shares one keyed permutation reply: the group's
first leaf ("head") calls the permutation on (counter, key), the reply's last 16 bytes land in its own salt slot and the
other leaves copy 16-byte slices of the reply. Groups were laid out per 64-leaf window (11, 11, 11, 11, 11, 9), six
heads per 64 leaves. Here the groups run over 2,048-leaf windows: 186 groups of eleven and one of two, 187 heads per
2,048 leaves instead of 192, and 94 pair heads (shared cursor writes) instead of 96.

- A head costs 7 cycles more than an ordinary leaf (one call, three address instructions, one store, minus the four
  salt loads and stores), plus 1 cycle when it starts a cursor pair. Per 4,096-leaf body: 374 heads and 188 pair heads
  instead of 384 and 192, i.e. 74 cycles fewer, 303,104 cycles over the vector.
- The body is ten words shorter; the latch moves to words 45,393 (`beq s4,s9,792`) and 45,394
  (`jal zero,-181492`), and 196 never-executed `nop`s keep every later word at its address.
  Commit words 21-45,590 change; all other commit words, the layout, sizes and steps are unchanged.
- Counters are still the byte address of each group's first leaf, so they stay distinct.
  A commitment makes 43,474,943 oracle calls (2·2^24 leaf calls, 1,531,904 group calls, 2^22 quartet calls,
  2^22 − 1 parents).

**Opening.** One immediate: the salt-materialising prefix computes the rank inside a group as
`(i & 2047) % 11` (`andi t3,t1,2047`, word 740) instead of `(i & 63) % 11`. Cycles and proof bytes are unchanged.

**Check.** Byte-identical to bc5cc89e and 2b2405a1 (and to our Quartet's variant-B check image).

## Bounds

| | bc5cc89e | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,841,054 | **519,537,950** |
| opening cycles, 128 positions (worst case) | 98,057 | **98,057** |
| proof bytes, 128 positions (worst case) | 72,192 | **72,192** |
| score | 37,535,444,301,312 | **37,513,562,617,344** |

`claim.json`: `{"commitCycles":519537950,"openingCycles":98057,"proofBytes":72192}`.
Score = (519,537,950 + 98,057) × 72,192 = 37,513,562,617,344, 0.058 % below bc5cc89e and 0.209 % below the
accepted record 2b2405a1 (37,592,218,400,256).

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 519537950 98057`, with
`submission := CommitGolf.Artifact.submission` and `submission_matches_artifact` by `rfl`. The proof is bc5cc89e's,
with the window constant changed:

- **Commit** (`Grouped.commit_resources`, `Grouped.full_commit`): every commit run succeeds in exactly 519,537,950
  cycles (215,213,346 steps) with 43,474,943 calls. The leaf body is the parametric `packet n` of `GroupedImageBase`
  with `heads`, `rank`, `pairPos`, `pairHeads` for the 2,048 period; the 64 kernel tile checks of
  `GroupedPacketDecode` compare every body word with it.
- **Salts and hiding** (`CounterSaltLayout`, `QuartetCounterSecurity`, `QuartetCounterCertificate`): group `j` has
  first leaf `2048·(j/187) + 11·(j%187)`, leaf `i` sits at `coord i = (187·(i/2048) + (i%2048)/11, (i%2048)%11)`;
  `coord` is injective and the counters are distinct, so the counter-mode game of 2b2405a1 applies unchanged with
  1,531,904 groups. The budget `(t+1)/2^121 + 2·groups·(2q+groups)/2^192 ≤ (t+1)/2^120` holds for the smaller
  group count.
- **Opening, check, binding, assembly**: bc5cc89e's, with the one opening row and its two arithmetic lemmas
  (`GroupOpenStep.masked`, `decoded_rank`) for the 2,047 mask.

## Commands and results

From the project root, pinned Lean 4.35.0 toolchain, candidate cache purged as `verify.py` does,
`CommitGolf/Artifact.lean` regenerated from `programs.json` with `verifier/artifact.py`:

- `lake build +Solution`: build completed successfully.
- `lake env lean Audit.lean`: `certificate` depends on [propext, Classical.choice, Quot.sound];
  `submission_matches_artifact` on [propext, Quot.sound].
- `python3 verifier/check_submission.py <tree>`: ok.
- The exact-cycle interpreter of the commit image (`budget_q.py`) reproduces 519,537,950 cycles and 43,474,943 calls,
  and 519,841,054 on bc5cc89e's image.
- `lake env leanchecker` replays every compiled candidate module, `CommitGolf.Artifact` and `Solution`.

## Provenance

- bc5cc89e (kaankolcu, our account): the whole tree; 20 files adapted as listed in DEPENDENCIES.md, the other
  577 modules byte-identical.
- 2b2405a1 (dadon): the grouped in-place generator, its hiding proof, the grouped commit and opening proofs.
- 20182e74 (dadon), b64a994e and c08b0128 (kaankolcu), c28dd9ca (dadon), 33bdbed6 (kaankolcu): the lineage
  under 2b2405a1 (Quartet tree, opening record writer, checker, chain-salt modules).
- Ours: the 2,048-leaf re-tiling and its proof changes.
