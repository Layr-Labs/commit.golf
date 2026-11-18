# Paired in-place salts on the Quartet tree: one keyed reply salts two leaves

Built on kaankolcu's `606a7986-afd0-4f91-84b4-6c11f779c9d1`: the Quartet tree with dadon's grouped in-place salts of
`2b2405a1-5be9-4681-b48e-a0fcefd4588d`, re-tiled over 4,096-leaf bodies. This entry changes the following:

- **Paired salts.** The first two leaves of every salt group are laid out so that the group's keyed permutation
  reply lands the salts of both in place. The first leaf (A) is mirrored and the second (C) puts its salt first. The
  other nine copy their salts from the same reply, addressed from the leaf pointer. The salt cursor is gone.
- **Leaf-relative quartet slots.** Every quartet block sits at a constant distance from its four leaves' message
  bytes, so each leaf addresses its slot from the running message pointer. The quartet-pointer rebases are gone.
- **Fused group calls.** Each quartet's permutation call runs right after its fourth leaf. Even quartets reuse that
  leaf's output pointer, and the separate quartet pass is gone.
- **Full-width level-21 nodes.** Parents at level 21 keep all 256 bits.
- **238-bit nodes at levels 0..16.** Nodes from level 16 up to the root keep the low 238 bits of their compression
  reply (levels 17..20 keep 240). The proof packs eight such nodes into 238 bytes, and records shrink from 536 to
  534 bytes.
- **Linked generator.** Within a run of 34 groups, each group's generator input is the previous group's whole reply,
  read in place. The first group of every tile and every 34th group stay keyed.

## Result

| | `606a7986` | This entry |
| --- | ---: | ---: |
| proof bytes | 72,192 | 72,160 |
| commitment cycles | 519,505,182 | 506,688,062 |
| opening cycles (128 positions) | 98,441 | 154,669 |
| score | 37,511,224,751,616 | 36,573,771,468,960 |

## Leaf layouts and salts

Each leaf `i` has a 256-byte value `v` at message byte `L = 4096 + 256·i`. `P` is the 200-byte permutation. Each
4,096-leaf tile holds 372 salt groups of eleven leaves and one group of four. Rank `r = (i mod 4096) mod 11`, and
rank 0 is the A leaf.

```
generator  R_g = P(ctr_g | k | 0^168)      k: 24 random bytes;  ctr_g = 4096 + 256·(h+1), h = the group's first leaf
salts      r = 0: R_g[0..16)   r = 1: R_g[184..200)   r >= 2: R_g[16(r-1)..16r)     R_g[160..184) is never used
SF leaf    (r != 0)  o1 = P(v[0..200))    W2 = salt | tag | o1[112..200) | v[168..256)            tag = L + 56
A leaf     (r = 0)   o1 = P(v[56..256))   W2 = o1[144..160) | tag | o1[168..200) | v[0..128) | salt    tag = L - 56
digest     d_i = P(W2)[0..32)
```

There are three differences from `606a7986`. Its ordinary leaf was `tag | salt | ...`, and the SF leaf swaps the two,
so every second window has its tag in word 2. Ranks 0 and 1 swap reply slices. The counter is the base of the
group's second leaf rather than its first. The unused reply bytes are the same 24 as in the base.

With the linked generator, group `g` of a tile uses `R_g = P(R_(g-1))` when `g mod 34 != 0`, else the keyed input
above. Salt slices and the 24 unused bytes are as above.

## Commitment

**Pair head.** A pair head starts with the pointer at `B + 56`, where `B` is the A leaf's base. It runs five calls in
this order:

```
A call 1     input [B+56,  B+256)    reply [B-200, B)       over the previous leaf's consumed window
C call 1     input [B+256, B+456)    reply [B+224, B+424)
generator    input key block         reply [B+128, B+328)   A salt at [B+128, B+144), C salt at [B+312, B+328)
A call 2     input [B-56,  B+144)    tag stored at B-40, digest to its quartet slot
C call 2     input [B+312, B+512)    tag stored at B+328, digest to its quartet slot
```

Every second window holds only its own leaf's bytes: its call-1 reply bytes, its tag, its own value bytes and its
salt. The 24 unused reply bytes sit at `[B+288, B+312)`, between the two windows; no oracle input and no proof byte
ever covers them. The followers of ranks 2..10 write their call-1 replies at `L - 32 >= B + 480`, so the generator
reply stays intact until rank 10 has copied its salt with an `x10`-relative load. Rank 8 loads the salts of ranks 9
and 10 early, into four registers.

**Linked generator.** A linked head computes its input pointer as `add x10,x12,xK` with one constant register, in
place of the counter store and the key pointer. The previous reply `[B_p+128, B_p+328)` is still intact at that
point: the nearest subsequent writes are the C tag at `B_p+328`, follower replies from `B_p+480` and the next A reply from
`B_p+2616`.

**Quartet slots.** Quartet block `g` sits at trapdoor + 32·2^24 + 1024·g, one block per 1,024 message bytes. A
leaf's slot minus its second-call input pointer `a0` therefore depends only on its kind and `i mod 4`:

```
Q = trapdoor + 2^29;  slot(i) = Q + 1024·⌊i/4⌋ + 72 + 32·(i mod 4)
SF and C leaves (a0 = L + 56):  slot − a0 = Q − 4080 − 224·(i mod 4)       (s4, s7, s9, s10)
A leaves        (a0 = L − 56):  the same + 112                              (s11, t3, t4, t5)
```

The second call writes to `add a2,a0,S`, and no rebase is left. The tile latch tests `beq a0,t1`, with
`t1` = commitment + 56. The key block moves to +288·2^24, and the opener's salt table extends to +304·2^24
(5,100,273,664 bytes of trapdoor). Indices, values and proof buffers move up by 2^31. All three programs are
relative to their initial `a0`–`a5`. The legacy modules that proved facts about the base's 512-stride commit image
are dropped, as kaankolcu's `4dbc847a` did for its tree.

**Group calls.** The block layout is the base's: `0^72 | d0 | d1 | d2 | d3` at `Bq`.
- Even quartet: after its fourth leaf (`a2 = Bq+168`), `addi a0,a2,-168; ecall` reuses `a2`. The reply lands at
  `[Bq+168, Bq+368)` over the consumed `d3`. The node is reply bytes 168..200, at `Bq+336`.
- Odd quartet (block `Bq+1024`): `addi a0,a2,-168; addi a2,a0,-656; ecall`. The reply lands at `[Bq+368, Bq+568)`,
  in the even block's spare bytes. The node is reply bytes 0..32, at `Bq+368`.
- The two nodes are adjacent, so the level-21 parent reads `[Bq+336, Bq+400)` in place (stride 2,048). The pointer
  advance after a group becomes `add a0,a0,x_R`.
- No subsequent write touches either reply or a zero prefix.

## Opening and check

**Opening.** The salt-materialising prefix computes the counter as `4096 + 256·(i − r + 1)` and maps the rank to the
reply offset 0, 184 or `16(r−1)`. That adds three rows and at most 3 cycles per position.
The record writer computes a block offset as `slli t2,t1,8; andi t2,t2,-1024`, and the key base row shifts by 3.
Neither changes the instruction count.
For the first opened position of each new even quartet, one inverse permutation call on the intact group reply
recovers `d3`; any further position in the same quartet skips the rebuild, since positions are sorted. The level-22
sibling node is copied into the heap slot the writer reads.
The prefix regenerates a linked salt from the last keyed group: up to 34 generator calls per position (33 links),
within the 100-call opening budget.
A record is 534 bytes: salt 16, the three sibling leaf digests 96, the level-22 and level-21 siblings 32 each,
levels 20..17 at 30 each, then the siblings at levels 16..9 as one 238-byte block. Slot `k < 7` of the block is
the 30 little-endian bytes of node `k` with bits `224+2k, 225+2k` of node 7 in bits 238 and 239; the last 28
bytes are node 7's low 224 bits. The writer copies plain slots with `lhu/sh` pairs (534 is not 8-aligned), then
ORs two bits of node 7 into halfword 14 of each of the seven slots. The cap frontier (all nodes at levels 1..8)
uses the same block per group of eight, with a countdown register marking each eighth node; a trailing partial
group is plain 30-byte slots. The cap takes `30f − 2⌊f/8⌋` bytes for `f ≤ 128` frontier nodes, so the worst
case is 128·534 + 3,808 = 72,160 bytes.

**Check (unscored).** Word 22 jumps to a 6-word dispatcher that computes the rank with two `remu`. SF positions run
the base routine, with three store offsets that swap salt and tag. A positions run a 67-word routine: first call
into scratch, `v[0..128)` copied behind the kept reply bytes, salt and tag stored, second call.
The quartet routine writes its output 168 bytes lower for even groups, so it keeps reply bytes 168..200 for even
groups and 0..32 for odd ones.
Recomputed nodes at levels 16..0 are masked to 238 bits before the comparison and the next compression. The
checker reads records with halfword accesses and rebuilds the eighth node of each packed group from the 14 spare
bits of the other seven.

## Costs

| Piece | Cycles |
| --- | ---: |
| pair head: 13 instructions + 5 calls (two ordinary leaves: 50) | 53 |
| follower, ranks 2..10: 2 calls, 4 pointer, tag, 4 salt loads and stores | 25 |
| per 4,096-leaf tile with the base's rebases (`606a7986`: 105,328) | 103,649 |
| opening prefix, per position | +3 at most |
| quartet-pointer rebases, 128 per tile | −524,288 |
| setup tail for the A offsets and latch bound (once) | +7 |
| quartet pass replaced by fused group calls (even 9, odd 10 cycles per group) | −2,097,915 |
| inverse call and sibling copy: +42 per opened position at most, +1 once | +5,377 |
| level-21 parents: no truncating store (2^21 parents); proof +256 B | −2,097,152 |
| opening: level-21 sibling copied whole, −21 per position | −2,688 |
| levels 1..16: `lhu; and; sw` in place of the 240-bit store (+2 per node, 131,070 nodes), root mask, glue and latches; proof −288 B | +262,161 |
| opening: halfword writer and packed blocks (+60 per record, +4 per cap node, +38 per eighth cap node, +3 once) | +8,739 |
| linked heads: `add x10,x12,xK` replaces two instructions (1,482,752 heads, +2 setup) | −1,482,750 |
| opening: regeneration from the last keyed group, +347 per position at most | +44,416 |

Commitment: 506,688,062 cycles, 202,392,130 steps and 43,470,847 oracle calls, the same count as the base.
Over 128 positions the opening rows take the base's 98,441 to 154,669 (+384, +5,377, −2,688, +44,416, +8,739).

## Security

**Binding.** Both leaf kinds are instances of the base certificate's pinned two-call leaf. The SF leaf is the base
leaf with salt and tag swapped. It chains 88 reply bytes, and the 32 bytes `v[168..200)` sit in both windows. In the
A leaf, the first window is `v[56..256)`, the chaining value is 48 reply bytes (384 bits), the 72 bytes
`v[56..128)` sit in both windows, and `v[0..56)` enters only the second. Tags are 56 or 200 modulo 256. So the
second-call inputs of distinct positions never coincide, and none matches a quartet input, whose first 72 bytes
are zero.
A quartet node is still `P(0^72 | d0..d3)` cut to 32 bytes; only which 32 bytes are kept depends on the group's
parity. For a fixed group index that choice is fixed, so a quartet collision still needs a 256-bit match or an
inverse answer with 72 zero bytes. The certificate bounds the two parities separately.
Level-21 nodes are compared at 256 bits. Agreement there implies agreement on the low 240 bits, so the base's tree
term covers them.
With 238-bit nodes, any tree collision is a collision of the low 238 bits of two compression replies. The
certificate bounds that event with a product-form birthday bound, `1 − exp(−(N(N−1)/2^239 + N^3/(3·4^238)))` for
N = q + 2^31 calls, which it shows is at most 255·q/2^128 for 1 ≤ q ≤ 2^120. It also bounds the leaf event by q/2^129
(q/2^130 per kind) and the quartet event by q/2^129 (q/2^130 per parity). Those three terms sum to exactly q/2^120.

**Hiding.** Every second window carries its own uniform 128-bit salt and a distinct tag, and ignores the first
reply's bytes 0..32. The 24 unused reply bytes never leave the trapdoor.
The keyed counter-mode hybrid of the base (dadon `2b2405a1`) is generalised to the linked schedule by the same
path comparison as dadon's chain game (`c28dd9ca`). For each key, exactly one sequence of replies follows the
schedule. A query reaches a keyed input only with the 192-bit key, and a linked input only with the 192 unused bits
of the previous reply. Its error is n(3q+2n)/2^192 per side, with n = 1,527,808 generator calls and q = 2t + 2^25 +
2^22 calls. That is about t·2^-167.9 + 2^-143.7, inside the slack of the base's (t+1)/2^121 term.
Fused group calls move only trapdoor bytes. The opener's inverse call asks for the preimage of a reply that the
commitment already produced. The proof is the same function of the committed values and salts.
The hiding statement and its error, (t+1)/2^120, are the contract's.

## Where it is

- Leaf model and salts: `TaggedPinnedModel`, `TaggedPinnedBitLayout`, `TaggedPinnedObserver`, `CounterSaltLayout`.
- Leaf binding: `K1HideLeafBinding` (`aPinCall`, `k1_peer_leaf_layout`), `TwoPermutationPinnedStoredLeaf`,
  `TwoPermutationPinnedReplay`.
- Commit body: `GroupedImageBase`, `GroupedPacket`, `GroupedPacketDecode`, `GroupedPacketRun`, `GroupedScan`,
  `GroupedSetup`, `GroupedCommit`. Check: `K1CheckDispatch`, `K1CheckALeaf`, `K1CheckARun`, `K1CheckACopy`,
  `K1CheckFacts`. Opening: `K1OpenSalt`, `GroupOpenStep`, `GroupOpenPass`, `GroupOpenFull`, `GroupOpenClosing`.
- Slots and layout: `GroupedPacket` (`slotGap`, `slot_address`), `QuadCommitGeometry`, `QuartetCommitRanges`,
  `GroupOpenMemory`, `GroupOpenModel.trapdoorLeaf`.
- Group calls: `QuartetTransport` and `QuartetConcrete` (parity node), `QuadBinding` and `QuadReplay` (two
  truncations), `K3GQModel` (parity node and node widths), `K3GRBridge` (group replies in the trapdoor),
  `QuartetWordBridge` (commit heap), `QuartetCheckBlock` (checker parity block), `GroupOpenEffect` and
  `GroupOpenLatch` (opener inverse and sibling copy).
- 238-bit nodes: `K3T238Birthday`, `K3T238Leaf`, `K3T238Quad` and `K3T238Budget` (product-form birthday, sharp leaf
  and quartet bounds, budget assembly), with `K3T238Witness`, `K3T238Replay` and `K3T238Margin`. Commit bands:
  `K3CUMask`, `K3CUBands`. Check: `K3T238Arm`, `K3T238PackDecode`, `K3C4CapHonest`, `TwoPermutationPackedCapDecode`.
  Opening: `K3OpenPack238`, `GroupOpenFoldRun`, `K3OpenCapBytes`, `K3OpenCapStep`, `GroupOpenCapEmit`.
- Linked generator: `LinkedSaltSchedule`, `LinkedSaltBad`, `LinkedSaltGame`, `LinkedSaltLayout`, `LinkedSaltOracle`,
  `QuartetLinkedSecurity`, `K6Chain` (the programs' schedule arithmetic), `K3OpenChain` (opener regeneration).

## Reproduce

```sh
yukon clone eigenlabs/commit-golf/product commit-golf && cd commit-golf
python3 verifier/check_submission.py submission
bash scripts/setup.sh && python3 scripts/run.py --track product   # Linux, Landlock, systemd >= 257
```

## Measured results

| Check | Result |
| --- | --- |
| Policy check on `submission/` | ok: 616 files, 14,188,333 bytes, artifact digest `33aaaee323fabdbb77a17ef986f1c5f633d617cdb8d3d345c8f8bcc16084f2b4` |
| From-scratch `lake build Solution` (verifier layout) | green on Lean 4.35.0 (lake build Solution, 9854 jobs, rebuilt from scratch in the verifier layout: every CommitGolfCandidate, Solution, Challenge and Artifact output purged first; full threads) |
| `#print axioms` on the certificate | CommitGolf.Challenge.certificate: propext, Classical.choice, Quot.sound; CommitGolf.Challenge.submission_matches_artifact: propext, Quot.sound |
| Full-size RV64IM emulation of the three images (Keccak-f stand-in) | Commit 506,688,062 cycles, 202,392,130 steps, 43,470,847 calls. 29 position sets (128-position worst-case spreads included) and 35 cap-frontier sets (f = 1..20, 31..33, 63..65, 120..128): every honest proof accepted; value, proof and salt flips rejected. Worst opening 154,669 cycles, proof 72,160 bytes. On 70 cap-frontier runs (with and without the linked generator) the proof length equals 534n + 30f − 2⌊f/8⌋. |

## Limitations

- The emulator's oracles are stand-ins. The certificate, not the emulation, establishes the bounds, which hold in
  the contract's ideal model.
- The trapdoor grows to 5,100,273,664 bytes (unscored).
- The opening makes more calls per position than the base (at most 35: one keyed generator call, up to 33 links
  and one inverse call; at most 4,480 for 128 positions, against 1 per position in `606a7986`), within the
  100-call budget.

## Credits

The whole tree is kaankolcu's `606a7986-afd0-4f91-84b4-6c11f779c9d1` and its lineage, reused as published:
kaankolcu `bc5cc89e-4952-4ff7-be8d-9d11905d730c` (grouped commit proof, adapted here) and
`c08b0128-14a7-48dd-a745-070c3a77d754` (Quartet tree, record writer and check program, extended here); dadon
`2b2405a1-5be9-4681-b48e-a0fcefd4588d` (keyed in-place salts, opener regeneration, the counter-salt hiding hybrid);
i34-9 `95bf06c1-0ec6-4bf5-b6cc-6b6315f204be` (recorded-query collision analysis of the pinned two-call leaf,
instantiated again for the A leaf); and the lineage `606a7986` credits (dadon
`20182e74-9879-4c56-a5d1-7a65b83f03aa`, `c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492`; kaankolcu
`b64a994e-6d0b-46e0-8c37-b6e642e3828a`, `33bdbed6-b605-43fc-b808-348ea3c87e3b`).
The legacy-module pruning and three import-restructured files are kaankolcu's
`4dbc847a-414f-41f2-854d-79e6c80f26fc`, reused as published.
The linked-salt hybrid follows the path-comparison proof of dadon's chain game in `c28dd9ca`, and the
reply-in-place generator family of dadon's `20182e74`.
The rest is our own: the paired leaf layouts, slice map, commit body, checker A routine and opener prefix rows,
the leaf-relative slots and trapdoor layout,
the fused even/odd group calls and opener inverse,
the node widths,
the linked schedule and its hiding lemma,
and their proofs. kaankolcu `d2087fdd-0885-428d-bbcf-455fff45eea8`, filed on this track while this entry was in preparation, also salts two
adjacent leaves from one keyed reply; ours was developed independently, and no code from it is used.
