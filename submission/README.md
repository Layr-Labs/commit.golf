# Quartet with grouped in-place salts over 4,096-leaf windows and 368-byte quartet blocks

This submission is our 606a7986 tree (A′: bc5cc89e-4952-4ff7-be8d-9d11905d730c with the salt groups re-tiled over whole
4,096-leaf bodies and a `remu` opener row) with the quartet blocks of the trapdoor packed at a 368-byte stride instead
of 512. The tree, leaf function, proof format and check program are unchanged.

## What changed against A′

**Commit.** Each quartet block holds 72 zero bytes and four 32-byte leaf digests; the fourth digest's 200-byte
permutation reply ends exactly 368 bytes after the block start. A′ (like bc5cc89e) used 512-byte blocks, so the
quartet pointer `s4`, which the leaf body addresses with 12-bit immediates, was rebased (`add s4,s4,s7`) every 32
leaves: 128 rebases per 4,096-leaf body. With 368-byte blocks a body's 1,024 blocks fill exactly 92 windows of 4,096
bytes, so 92 rebases per body suffice: 36 × 4,096 = 147,456 cycles fewer.
- Blocks start at trapdoor + 0x44000000 and end exactly at the key/salt block (trapdoor + 0xA0000000, unchanged):
  setup words 4-7 are `lui s5,0x44000; add s5,s1,s5; lui s6,0x5C000; add s8,s5,s6`.
- Leaf slot n of a body sits at byte `slotOff n = 368·(n/4) + 72 + 32·(n%4)`; the leaf's heap immediate is
  `2048 + slotOff n − 4096·rb n` with `rb n = slotOff n / 4096`, and leaf n is followed by a rebase iff
  `rb (n+1) ≠ rb n`. The latch moves to words 45,356 (`beq s4,s9,940`) and 45,357 (`jal zero,1915808`); 233
  never-executed `nop`s keep every later word at its address.
- The quartet loop steps by 368 (`addi a0,a0,368`, 8,192 unrolled copies); the loop end and the upper tree are unchanged.

**Opening.**
- The opener's dead setup words 7-10 and the salt prefix rows 717-720 (which the header proof requires to be equal) both
  become `lui s8,0x44000; add s8,s1,s8; lui t1,0x5C000; add s6,s8,t1`: s8 points at the 368-byte blocks and s6 at
  the unchanged salt base.
- Config row 729 `addi t0,zero,0` (t0 is already 0 in the initial state) becomes `addi tp,zero,368`.
- The record writer's group base (words 35-36) is `srli t2,t1,2; mul t2,t2,tp` instead of
  `slli t2,t1,7; andi t2,t2,-512`: 3 cycles more per position, +384 for 128 positions. Proof bytes are unchanged.

**Check.** Byte-identical to A′, bc5cc89e and 2b2405a1.

**Files.** The 43 candidate modules that are not imported by `Solution` were removed: the 19 that bc5cc89e already
did not import, and 24 old-image modules (`QuartetCommitLeaf*`, `QuartetCommitQ*`, `QuartetCommitSetup`,
`QuartetCommitJoin`, `QuartetCommitUpperImage`, `QuartetChainSetup/Loop/Exec`, `NonceChainSyscall`,
`QuartetCommitImage`, `QuartetPhysical`) whose statements are about the 512-stride images of earlier lineages and which
no longer entered the certificate.

## Bounds

| | A′ (606a7986) | this submission |
|---|---:|---:|
| commit cycles (exact, every run) | 519,505,182 | **519,357,726** |
| opening cycles, 128 positions (worst case) | 98,441 | **98,825** |
| proof bytes, 128 positions (worst case) | 72,192 | **72,192** |
| score | 37,511,224,751,616 | **37,500,607,329,792** |

`claim.json`: `{"commitCycles":519357726,"openingCycles":98825,"proofBytes":72192}`.
Score = (519,357,726 + 98,825) × 72,192 = 37,500,607,329,792: 0.0283 % below A′, 0.0345 % below 45a3e161
(37,513,562,617,344), 0.0928 % below bc5cc89e.

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 519357726 98825`, with
`submission := CommitGolf.Artifact.submission` and `submission_matches_artifact` by `rfl`. The proof is A′'s with the
layout constants changed:

- **Layout.** `QuadCommitGeometry.quartetOffset g = 368·g`, `quartetBaseOffset = 68·LENGTH` (the salt base
  `68·LENGTH + 368·2^22 = 160·LENGTH` is unchanged); `QuartetCommitRanges.qSource g = 679477764 + 46·g` (words).
  `QuartetCommitRanges.qleaf_in_block`, `qleaf_before`, `qpad_outside`, `qleaf_below_salts` state the block
  separation facts once (with explicit case splits; `omega` alone cannot round the 46-word stride).
- **Commit** (`Grouped.commit_resources`, `Grouped.full_commit`): every commit run succeeds in exactly 519,357,726
  cycles (215,061,794 steps) with 43,470,847 calls. `GroupedImageBase` defines `slotOff`, `rb`, `rebase`,
  `firstWord`, `heapImm`; `GroupedCommitImage.rb_succ`/`rebases_succ` count the rebases; `GroupedPacket.cursor i =
  qSource (1024·(i/4096)) + 512·rb (i%4096) + 256`, and `heap_address` uses a 4,096-entry `decide +kernel` table of
  12-bit sign extensions. The 64 kernel tile checks of `GroupedPacketDecode` rerun unchanged against the new
  `packet n`.
- **Opening.** Both trapdoor views (`GroupedOpening.trapdoorLeaf`, `QuartetRV.trapdoorLeaf`, equal by definition) read
  leaf digests at `68·LENGTH + 368·(i/4) + 72 + 32·(i%4)`; `groupSlots = trapdoorBase + 68·LENGTH`. The record loop's
  block accounting gains `RunsOpeningSlack` (a block of c cycles that executes c − e instructions and hands e units of
  fuel on), because the 4-cycle multiply breaks the one-cycle-per-instruction assumption of `RunsOpeningBlock`: a record
  costs 636/637 cycles with slack 3, `openCycles p = scheduledCycles p + 3·|p|`, opening bound 98,825.
  `tp = 368` is threaded as `Registers.mult` → `RecordBoundary.mult` → `RecordStart.mult` → `PrefixStart.mult`
  (row 729 sets it; `setup_keeps_x5` and the initial state give the selector `t0 = 0` the row used to set).
- **Salts, hiding, check, binding, assembly**: A′'s, unchanged.

## Commands and results

From the project root, pinned Lean 4.35.0 toolchain, candidate cache purged as `verify.py` does,
`CommitGolf/Artifact.lean` regenerated from `programs.json` with `verifier/artifact.py`:

- `lake build +Solution`: build completed successfully.
- `lake env lean Audit.lean`: `certificate` depends on [propext, Classical.choice, Quot.sound];
  `submission_matches_artifact` on [propext, Quot.sound].
- `python3 verifier/check_submission.py <tree>`: ok.
- The exact-cycle interpreter of the commit image (`budget_q.py`) gives 519,357,726 cycles and 43,470,847 calls.
  A full-size RV64IM emulation (Keccak-f stand-in for the oracle) of the three images: commit 519,357,726 cycles /
  215,061,794 steps, same commitment as A′ on the same message and key; openings of group-edge and random positions
  96,593 and 96,780 cycles (≤ 98,825, A′ + 384); the check accepts the honest proof and rejects a changed value and a
  changed proof byte.
- `lake env leanchecker` replays every compiled candidate module, `CommitGolf.Artifact` and `Solution`.
- Commit image 807,068 bytes (< 1 MiB).

## Provenance

- 606a7986 / A′ (kaankolcu, our account) and bc5cc89e (kaankolcu): the whole tree; files adapted as listed in
  DEPENDENCIES.md.
- 2b2405a1 (dadon): the grouped in-place generator, its hiding proof, the grouped commit and opening proofs.
- 20182e74 (dadon), b64a994e and c08b0128 (kaankolcu), c28dd9ca (dadon), 33bdbed6 (kaankolcu): the lineage
  under 2b2405a1 (Quartet tree, opening record writer, checker, chain-salt modules).
- The 368-byte block idea also appears in AdamGagol's 1a9bc5f4 (Quad lineage); no file of it is used here.
