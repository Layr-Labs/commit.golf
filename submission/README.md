# Quad + paired salt generator + 256-leaf signed salt window

This submission combines two accepted lines and adds one change of ours, all in the commit program:

* the tree, layout, opening and check programs of AdamGagol's record `1a9bc5f4-ac89-4a1d-a901-d8a37b3859a1`
  (four-leaf quad layer with 368-byte groups on the pinned two-permutation leaf);
* dadon's paired permutation expansion from `20182e74-9879-4c56-a5d1-7a65b83f03aa` (two calls per five-word
  packet) with its `NoncePair` hiding proof, ported to that tree;
* a 256-leaf signed salt window in the leaf loop (ours), which halves the salt-pointer rebases.

The opening and check images, the proof format and the trapdoor layout are 1a9bc5f4's, byte for byte. The
commitment and trapdoor are those of 1a9bc5f4's honest tree on the paired generator's salts.

## Result

| | 1a9bc5f4 | 20182e74 (current best) | this submission |
|---|---:|---:|---:|
| commit cycles (exact, every run) | 523,312,474 | 522,614,991 | **522,460,577** |
| opening cycles (worst 128-position batch) | 94,841 | 93,945 | 94,841 |
| proof bytes (128 positions) | 72,192 | 72,192 | 72,192 |
| score | 37,785,820,884,480 | 37,735,403,507,712 | **37,724,320,736,256** |

`claim.json`: `{"proofBytes": 72192, "commitCycles": 522460577, "openingCycles": 94841}`.
Score = (522,460,577 + 94,841) × 72,192 = 37,724,320,736,256, 0.029% below 20182e74 and 0.163% below 1a9bc5f4.

## Change 1: paired generator on the quad image

1a9bc5f4's generator makes 1,525,248 calls, each `ecall; addi a0,a0,176; addi a2,a2,176`, 64 per `bltu`:
15,276,312 loop cycles. dadon's observation is that the input pointer only has to move every other call. At the
start of packet p, `S = T + 352p` holds the 24-byte private key followed by 176 zero bytes. The packet is
`ecall` (reads and writes `S` in place), `addi a2,a2,176`, `ecall` (reads the whole first reply at `S`, writes at
`S+176`), `addi a0,a0,352`, `addi a2,a2,176`: 19 cycles for two calls. Afterwards the second reply's hidden
192-bit suffix sits at `S+352` and the next 176 bytes are still zero, so the next packet starts the same way.
Every reply still contributes eleven 16-byte salts and the salt tape is laid out exactly as before
(176 bytes per reply from `T`), so the leaf loop reads it unchanged.

On this image: the seed RANDOM now targets `T` (setup word 10 `addi a0,s6,0`, was `-176`), 762,624 packets in
48 visits of a 15,888-packet tile (762,624 = 48 × 15,888, no partial tile), tile end `bgeu a2,t2,8; jal TILE`,
and the unchanged return `addi a0,s2,0; addi a2,s1,0; jal 18`. Loop cost 19 × 762,624 + 95 = 14,489,951 cycles,
786,361 fewer than the 64-call loop. The generator is appended after the final HALT; the image is 236,673 words
(946,692 bytes, below 1 MiB). The exit test and the limit register are unchanged (`a2` reaches `T + 176·1,525,248`
exactly after the last packet).

Hiding: the recurrence is the one of 20182e74 (odd calls read the zero-padded previous key, even calls the full
previous reply). Its modules `NoncePairGame`, `NoncePairLayout`, `NoncePairOracle`, `NoncePairReplay` are used
unchanged; they build on the `NonceChain` layout, which here has 1,525,248 blocks and 512 spare salts, and their
budget lemma `quartet_budget` covers this view's query bound `t + 2·LENGTH + LENGTH/4 + t`. In 1a9bc5f4's hiding
modules (`QuadNonceSpec`, `NonceChainView`, `QuadNonceSecurity`, `QuadNonceAssembly`, `QuadNonceCertificate`,
`QuadNonceCommitTranscript`) the salt function is now `NoncePair.actualNonces` and the chain/iid replacement is
`NoncePair.nonce_chain_oracle_distance` with `NoncePair.chainError`; the final sum
(t+1)/2^121 + 2·chainError ≤ (t+1)/2^120 is `NoncePair.quartet_budget`.

Machine side: `QuadNonceCommitLoop` (packet decode, tile fetch via the repeated-chunk lemma, per-call frame with
`nonceChainSource j = T + 352⌊j/2⌋`), `QuadNonceCommitExec` (one call, including the tile-end branch, after
20182e74's `QuartetChainExec`), `QuadNonceCommitMemory` (the chain memory invariant gains 20182e74's
future-zero frame; even calls read the full previous reply, odd calls the 24-byte key and 176 untouched zero bytes),
`QuadNonceCommitSetup` (seed at `T`, 3,813,227 steps / 14,489,963 cycles for the generator phase), and the artifact
walk of the 79,440 packet words in 512-packet blocks (`QuadCommitWalk_gen0/1`).

## Change 2: 256-leaf signed salt window

Each leaf loads its salt with two `ld t6, imm(s6)`. In 1a9bc5f4 the immediates are `16·(u mod 128)` and `+8`
(0..2040), so `s6` is rebased every 128 leaves (32 per 4,096-leaf body). Here the 12-bit field is `16·(u mod 256)`
(sign-extended to `16·(u mod 256) − 4096` when `u mod 256 ≥ 128`), the rebase `add s6,s6,t2` sits at
`u mod 256 = 127` with `t2 = 4096` (word 18 `slli t2,a3,12`). Inside a body `s6 = base + 4096·⌊(u+128)/256⌋`, so
every leaf reads exactly the same salt words as before, and after leaf 4095 `s6` is the next body's base. The body
is 16 words shorter; the leaf latch becomes `beq a0,s0,72; jal` plus 16 never-executed `nop`s so that all later
code keeps its addresses. Saving 16 × 4,096 = 65,536 cycles. Proof: `nonceOffset` and the 256-entry tables
`nonce_offset_succ`, `salt_offset_table`; `salt_window_address` shows the signed offset reaches the leaf's salt word;
`QuadCommitLeaf*` rebase/index/latch lemmas with `⌊(u+128)/256⌋`; regenerated leaf artifact walk.

## Totals

Commit = 13 (setup) + 4 (24-byte RANDOM) + 14,489,963 (generator phase incl. setup and return) + 507,970,597 (leaf,
quad, binary and root phases) = 522,460,577 cycles; 218,182,565 instruction steps; 43,468,287 oracle calls
(`cycle_ledger`, `step_ledger`, `call_ledger` in `QuadCommitImage`).

## Verification

Linux aarch64, pinned Lean 4.35.0 toolchain and dependencies:

| Check | Result |
|---|---|
| `lake build Solution` (verifier layout, `CommitGolf/Artifact.lean` regenerated from `programs.json`) | success |
| comparator replay (`verifier/comparator.json`, `Challenge.lean.in` at 72192 / 522460577 / 94841) | accepted; axioms propext, Quot.sound, Classical.choice |
| `python3 verifier/check_submission.py submission` | ok, 702 files, digest `c59426064edf3bacf7175cf5cd8e9cf1641b6322dc65131d48cbdef62467b460` |
| source scan | no `sorry`, `axiom`, `native_decide` |

`scripts/run.py` (sandboxed, systemd ≥ 257) was not run locally; acceptance is claimed only if Yukon reports it.

## Provenance and credit

* AdamGagol, `1a9bc5f4`: the whole tree and all opening, check, binding and quad hiding proofs; the leaf, quad,
  binary and root phase proofs of the commit (modified only as listed above).
* dadon, `20182e74`: the paired generator design and the `NoncePair*` modules (copied unchanged), plus the
  structure of the paired execution and memory proofs, which we adapted to this image.
* dadon, `c28dd9ca`: the original NonceChain generator and hiding argument both lines descend from.
* kaankolcu, `33bdbed6`: the pinned two-permutation leaf, binary tree, cap and checker under 1a9bc5f4.
* Ours: the port, the 256-leaf salt window and the re-proved commit modules. (Our earlier filing of the salt
  window alone, `efd031d2`, was overtaken by 20182e74 before it validated.)

Effort: high. Work by Claude Opus 5.5 in Claude Code.
