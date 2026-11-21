# Combined product candidate: branch directly into the nonempty opener

The base for this archive is 0xplemonade's submitted cap writer
`15f4f81f-1001-49ac-b210-d81b03b30954`, commit `551b90ba01d6de97e1715234e1d2b4a3088886ba`.
Its cap instructions, 8,818-cycle cap-walk bound and proof of the 256-cycle
batch saving belong to that submission. The header change was developed
directly on 0andadream's `0259c643-d6d4-453b-8a2c-3e30615d3917` (`dc339c9`).
Both sources are credited. Relative to the cap-writer archive only
opening words 2 and 3 change:

* `0x300806e3` → `0x30081ee3`: replace `beq a6,zero,<709>` with `bne a6,zero,<713>`.
* `0x3190006f` → `0x3090006f`: change the fallback `jal zero` target from word 713 to 709.

A nonempty opening now enters the setup continuation in one branch instead of
a branch and a jump; the same registers, memory and PC reach word 713.
The empty path takes an additional jump and still produces zero proof bytes.
There is no change to the oracle calls, checker, commitment, proof serialization
or security games. The nonempty header costs 34 rather than 35 cycles.
The resulting claim is `(504585244 + 117823) * 72160 = 36419373314720`.

With positions `131072*j + 368` for `j=0..127`, each position takes the
longest 33-link salt chain and starts a new even quartet. The cap has one
marked leaf per sibling pair and emits 128 nodes. Sparse-memory RV64IM
replay on the exact images, zero trapdoor and identity permutation: 118,080
cycles on `0259c643`, 117,824 on `15f4f81f`, 117,823 on this archive;
all returned the same 72,160 bytes with 4,480 public calls. The empty case
took 7, 7 and 8 cycles respectively. These are machine-model replays,
not a report from the protected Linux verifier.

Manifest SHA-256: `21989510f9c5cd5d8f52e7c90d537cd3e17a63841f23d4997348568990872f73`.

## Inherited cap-writer documentation

# Cap emission saves two cycles per frontier node

Based on the product leader 0259c643. The packed opening format and all copy widths are identical to the parent. Both aligned cap copy paths share their last four-byte load and store at words 694–695. The freed words let all three alignment paths load the final halfword at 696 and select the folded path with one branch at 697. Plain slots fall through to the traversal. Folded slots advance by 28 in one instruction at 894 and jump to the traversal at 701.

For a frontier of size `f`, the saving is exactly `2*f` cycles. With 128 positions, the cap walk bound falls from 9,074 to 8,818. The opening claim is 117,824 cycles, with a 72,160-byte proof bound and 504,585,244 commitment cycles. The product is 36,419,373,386,880.

The inherited README follows.

# Product: chain exit skips the input-pointer reset (-128 opening cycles)

Built directly on the promoted product record `b2c9f0f8-d23d-474e-9d8e-673290539f88`
by AvinashNayak27 (master `2913e8d5`), which in turn credits the contributors listed in
the inherited sections below. All of the construction, the commitment, the record writer
and nearly all of the certificate are theirs; this entry changes four opening words.

## The change

After every position's salt chain, the link block's `jal` at word 929 returned to word 790,
`addi a0,zero,1024`, which re-pointed `a0` at the keyed input block before the next
position. That reset is only needed by the *skip* path (a position in the same quartet
as its predecessor), because a new quartet already sets `a0 = 1024` in its restore rows.

| Word | Before | After |
| ---: | --- | --- |
| 742 | `beq t3,tp,<777>` | `beq t3,tp,<776>` |
| 775 | `addi a0,zero,1024` | `sd t5,712(t2)` |
| 776 | `sd t5,712(t2)` | `addi a0,zero,1024` |
| 929 | `jal zero,<790>` | `jal zero,<791>` |

- New quartet: rows 773..776 still cost 4 (the store and the `a0` reset swap places), and
  the chain exit no longer executes word 790: **-1 cycle**.
- Repeated quartet: the skip branch now lands on 776 (`a0 := 1024`, +1) and the chain exit
  skips 790 (-1): unchanged.
- Word 790 is now unreachable and left in place; no words are appended, the image stays
  1,976 words. Commitment/checker images, data, ABI, every oracle call, salt and proof
  byte are unchanged.

Worst case per position drops from 331 to 330 cycles (`chainCycles <= 294`, new even
quartet head 25, post 11), so the pass bound is `330*n+2` and

```json
{"commitCycles":504585244,"openingCycles":118080,"proofBytes":72160}
```

```text
(504585244 + 118080) * 72160 = 36419391859840
Parent b2c9f0f8:  (504585244 + 118208) * 72160 = 36419401096320
Saving: 128 opening cycles; 9236480 score
```

## Proof changes

- `GroupOpenWalk`: `headRows` branch offset 136, new `loadRow` (776) and `skipRows`;
  `restoreRows` is 773..774, `ptrRows` is 775, `headPost = restoreRows ++ ptrRows ++ loadRow`.
- `GroupOpenStep`: `Registers` no longer carries `x10 = 1024` at the loop head (it is 1536
  after a chain); `load_row`, `head_skip` (via `head_skip0`) and `head_post` re-proved for
  the new rows and still deliver `x10 = 1024` at row 777 on both paths.
- `K3OpenChainRows/Link/Run/Exit/Post`: `chainExitRows` is the single `jal` to 791,
  `chainSteps = 14 + links`; `chain_post` no longer reports `x10`.
- `GroupOpenLatch`: skip head is 4 steps/cycles; `GroupOpenEffect`, `GroupOpenHeaderParts`,
  `GroupOpenHeaderCore` thread the header's `x10 = 1024` only into the key copy.
- `GroupOpenPass` (`chain_cycles_le 294`, `pass_cycles_bound 330*n+2`), `GroupOpenFull`,
  `GroupOpenClosing`, `Solution.lean`, `claim.json`; `programs.json`, `K1Manifest` and the
  `GroupOpenImage` literal/leaf lemmas regenerated from the delivered manifest.

## Evidence

A C RV64IM emulator of the `Riscv.lean` cost model (stand-in oracle) ran the full
2^24-leaf commitment (504,585,244 cycles, matching the claim) and then the parent and
this opener on the same trapdoor. Proof bytes are byte-identical on every fixture and the
checker accepts all of them:

| Fixture | Parent cycles | This entry |
| --- | ---: | ---: |
| 128 spread (distinct quartets) | 99,672 | 99,544 |
| 128 random | 99,463 | 99,335 |
| 128 consecutive (32 quartets) | 93,603 | 93,571 |
| single position | 1,914 | 1,913 |

Certification here means the local Lean build of the certificate plus the repository's
`scripts/run.py` verifier run on this host.

## Inherited documentation

# Product: hoist the quartet source bias (-256 opening cycles)

Based directly on next22 `7110ded12ffb4f8939e89779d93a01d7587e2231`.
Refreshed master `fddf62145814f5cad51fe13f472dde8ec80be4cf` delivers
exactly next19's manifest. No new public implementation is transplanted.

Each record copies three quartet mates. Previously each source head
added the same 584-byte leaf bias to its computed address. The slot
prefix now adds that bias once to `x7`; each mate head only computes
its XOR lane, shifts it and adds the biased base. Three removed steps
minus one shared step saves **two cycles per queried record**, including
partial and single-query openings. Empty openings are unchanged.

The biased base also reaches the level-zero sibling pointer load, whose
offset changes from 712 to 128. Quartet copy sites move from
`43 + 36*j` to `43 + 35*j`. Their internal branches and private-stub
returns target the relocated continuations. The level-zero head moves
from words 150/151 to 148/149, retaining its two-cycle load/jump cost.
Exactly **77 existing opening words** change; nothing is appended.
Commitment/checker images, embedded data, ABI, copy widths, oracle calls
and proof serialization are unchanged.

```json
{"commitCycles":504585244,"openingCycles":118208,"proofBytes":72160}
```

```text
(504585244 + 118208) * 72160 = 36419401096320
Next22 score: 36419419569280
Saving: 256 opening cycles; 18472960 score
```

`GroupOpenLeafFields` proves the shared bias and three-step source heads;
`GroupOpenPrefix` carries that bias through all three copies.
`GroupOpenSibling`/`SiblingRun` prove the adjusted pointer load and PC,
and `GroupOpenUpperRun` composes them. Record-prefix cost drops from
23 to 21 ordinary cycles, record-data cost from 129 to 127, and complete
record base cost from 134/135 to 132/133. `GroupOpenRecordsAPI`,
`GroupOpenRecordRun`, `GroupOpenABI`, `GroupOpenFull` and the final
certificate carry the matching aggregate bounds. The scored wide-pass
bound is 75818; alignment-dependent copy costs remain unchanged.

The exact delivered image is tested against next22 on mixed-oracle,
patterned rank-0/1/general spread, alternating, clustered, partial127
and single-query fixtures, comparing all compression inputs, roots,
trapdoors and proof bytes and requiring checker acceptance. Public
provenance is under `~/cg/sub19`. Certification here means local
artifact-backed kernel and emulator checks, not official Yukon success.

## Inherited next22: remove redundant selector initialization (-1 opening cycle)

Based directly on next21 `993e79443dc2c67a6ee5739d3ab39dc0385e19fa`.
Fetched master remains `80f406650699260a5b72975ff61a6cf39e3bfda5`, whose
manifest equals next18. No new public implementation is transplanted.

The ABI initializes `x5` to zero. No instruction before header row 729
writes it, so assigning zero again is redundant. Row 729 instead sets
the no-previous-quartet marker `x4=-1`. Row 739 jumps directly to 755,
skipping its old initialization at 754. Every nonempty opening saves
one ordinary instruction; empty openings bypass the header and retain
their existing cost. Exactly two words change, **729 and 739**; no words
are appended. Commitment/checker images, embedded data, ABI, oracle
calls, salt paths, record writers and proof serialization are unchanged.

```json
{"commitCycles":504585244,"openingCycles":118464,"proofBytes":72160}
```

```text
(504585244 + 118464) * 72160 = 36419419569280
Next21 score: 36419419641440
Saving: 1 opening cycle; 72160 score
```

`GroupOpenHeaderParts.config_frame` carries the incoming zero-selector
fact and initializes the quartet marker. `GroupOpenHeaderCore` proves
that setup preserves the selector and that the key copy preserves the
marker. `GroupOpenHeader.header_valid` discharges the selector premise
from the actual ABI state. Header cost decreases from 36 to 35; the
pass and record costs are unchanged. The image literals, packed manifest,
artifact and certificate match the delivered two-word change.

Full mixed/patterned pipeline comparisons preserve compression traces,
roots, complete trapdoors and proof bytes, with checker acceptance on
rank-0, rank-1, rank>=2, alternating, clustered, partial and single-query
fixtures. Nonempty fixtures save one cycle; empty opening/check and
invalid checking retain their prior behavior. Public provenance is under
`~/cg/sub18`. No official Yukon verifier success is claimed; certification
here means local artifact-backed kernel and emulator checks.

## Inherited next21: reply-relative salt selection (-128 opening cycles)

Based directly on next20 `cdb9137c4a01f3d02cc4ff45942e201955a10a6c`.
Fetched master `80f406650699260a5b72975ff61a6cf39e3bfda5` delivers exactly
next18's manifest. No new public implementation is transplanted; inherited
credits below remain applicable.

Rank-0 and rank-1 salts are copied directly from offsets 0 and 184 of
`x12=1536`, avoiding temporary source-address selection. Destination
calculation precedes the rank branches. Rank≥2 retains its old source
arithmetic and copy body. All three post-chain paths now cost 11 cycles
before the final-query exit adjustment, replacing 12 for ranks 0/1 and
11 for other ranks. The pass bound decreases from `332*n+2` to `331*n+2`.
The chain exit changes location but retains exactly two ordinary steps.

Exactly **18 opening words** change: **4..8, 790..799, 803, 804, 929**.
The private rank-0 copy uses unreachable old setup space; rank-1 uses
reclaimed dispatch space. No words are appended. Commitment/checker
images, embedded data, ABI, chain oracle calls, record writers and proof
serialization remain unchanged.

```json
{"commitCycles":504585244,"openingCycles":118465,"proofBytes":72160}
```

```text
(504585244 + 118465) * 72160 = 36419419641440
Next20 score: 36419428877920
Saving: 128 opening cycles; 9236480 score
```

Mixed patterned full-pipeline comparisons preserve every compression
trace, root, complete trapdoor and proof byte. Rank-0 and rank-1 spread
both reach 118465 cycles, saving 128. Rank≥2 spread is unchanged at
118465. Alternating parity, clustered, partial127 and single-query cycles
are 118401/79348/117571/2037, saving 64/24/127/1. Empty opening/check paths
remain 7/11 cycles; proofless nonempty checking rejects in 9 cycles.
The saving is rank-dependent, not one cycle for every possible query.

`GroupOpenWalk` defines the exact rank-dependent paths; `GroupOpenSelect`
proves their effective source addresses, legality, copy and frame effects.
`GroupOpenLatch` and `GroupOpenEffect` compose the unchanged memory
semantics with the new paths. The image literals, packed manifest and
certificate resource accounting match the delivered image. Local evidence
and public provenance are recorded under `~/cg/sub17`; no official Yukon
verifier success is claimed for this candidate.

## Inherited next20: constant-base salt-link dispatch

Based on next19 `0428943f868a7b8e9e733a5136ea6a1b73a0e93b`. Refetched
master `23c6dec30a12b7c19a35161f41bbd290de815d12` delivers exactly next17's
manifest. Its commitment/checker/data/ABI already match next19; no new
public implementation is transplanted. All inherited credits below apply.

The opener previously copied the query count into `x18`, used it once to
compute `8*count`, then preserved the otherwise unused count copy. The
shift now reads the original `x16`; the former copy initializes `x18=8192`
with `LUI x18,2`, without increasing header length or cost. The salt chain
replaces `AUIPC; SUB; ADDI; JALR` by `SUB x7,x18,x31; ADDI; JALR -380(x7)`.
For every link count `c<34`, the jump target is exactly
`8192-4*c-380 = address (929-c)`. Link queries and all salt bytes are unchanged.

Only opening words **715, 722, 787, 788, 789** change. The old word 790 is
unreachable from the new entry path and remains unchanged. The image is
still 1,976 words. No commitment/checker instructions, embedded data, ABI,
nonce/copy bodies, oracle calls or proof serialization change.

`GroupOpenSetup` and header rows establish the new constant; `Base`,
`Input`, head execution and `ChainEntry` carry its preservation. Chain
entry takes three rather than four ordinary steps. The exact chain bound
drops from 296 to 295 cycles and the pass bound from `333*n+2` to `332*n+2`.
The full-batch claim is:

```json
{"commitCycles":504585244,"openingCycles":118593,"proofBytes":72160}
```

```text
(504585244 + 118593) * 72160 = 36419428877920
Next19 score: 36419438114400
Saving: 128 opening cycles; 9236480 score
```

Mixed, patterned emulator comparisons use full commitments and compare
every compression call/input, full root/trapdoor, opening proof bytes and
checker acceptance. The spread/alternating/clustered/partial127/single
opening cycles are 118593/118465/79372/117698/2038, respectively; savings
are 128/128/128/127/1. Empty opening/check paths remain 7/11 cycles;
nonempty checking without proof rejects in 9 cycles.

Verification evidence and public provenance are recorded under `~/cg/sub16`.
These are local artifact-backed checks, not an official Yukon verifier run.

## Prior next19: inline aligned 28-byte and A1 copies (-64 opening cycles)

Based on next18 `ee4f0d6258119c7e53dd9ea69b6125cd801276c3`, retaining
its direct aligned nonce branch and next17's inline 30-byte writers.
Fetched master `4239e1a` still delivers next16's manifest; no new public
implementation is transplanted. All inherited contributor credits below apply.

The 28-byte final-level and 32-byte level-1 sibling copies now place both
aligned paths inline. Their shifted copies move into the old private aligned
stubs and return with fixed jumps. No words are appended.

| Copy | Alignment | Next18 cycles | Next19 cycles | Copies/batch |
| --- | --- | ---: | ---: | ---: |
| 28-byte | 0 mod 8 | 14 | 12 | 32 |
| 28-byte | 4 mod 8 | 20 | 19 | 32 |
| 28-byte | 2 mod 4 | 25 | 26 | 64 |
| A1 | 0 mod 8 | 14 | 12 | 32 |
| A1 | 4 mod 8 | 22 | 21 | 32 |
| A1 | 2 mod 4 | 27 | 28 | 64 |

Each writer saves 32 cycles per batch despite the slower shifted path.
Relative to next17 the combined nonce/28-byte/A1 layout saves 128 cycles;
the additive saving over next18 is 64 cycles.

```json
{"commitCycles":504585244,"openingCycles":118721,"proofBytes":72160}
```

```text
(504,585,244 + 118,721) × 72,160 = 36,419,438,114,400
Improvement over next18: 4,618,240
```

Only opening words within 190..219, 610..637, 1913..1938 and 1948..1975
change. Commitment/checker images, data, ABI, chain, nonce, 30-byte writers
and proof serialization are unchanged. The UpperRun proof uses a generic
one-step unfolding lemma rather than reducing a concrete thirteen-level
state, avoiding the earlier kernel memory failure. Resource composition
also rewrites only the cycle equality instead of converting whole states.

Public provenance is in `~/cg/sub15/`, with a next18 parent placeholder.
Local artifact-backed checks are not an official Yukon verifier run.

## Historical next18 documentation

# Product: direct aligned nonce branch (-64 opening cycles)

Based on our next17 commit `88c395f`, preserving next16 and the complete
promoted Meganpark980320, benbuschmann and Mahmoud514 lineage below.
Refetched master `4239e1a` delivers next16's image; no additional public
implementation is transplanted for this entry.

The aligned 16-byte nonce copy moves to unused header words 759..767,
within conditional-branch range of its entry. Its test branches directly
to four word pairs and a return, eliminating the old intermediate jump.
Costs are now 11 / 15 cycles for 4-aligned / 2-mod-4 destinations (was
12 / 15). The 64 aligned records save 64 cycles.

The nonce's shifted path, 28-byte and A1 writers and next17's eleven
30-byte sites are unchanged. No path is slower in this candidate.

```json
{"commitCycles":504585244,"openingCycles":118785,"proofBytes":72160}
```

```text
(504,585,244 + 118,785) × 72,160 = 36,419,442,732,640
Improvement over next17: 4,618,240
```

Only opening words 19 and 759..767 are edited. Image lengths, commitment/checker images,
embedded data, ABI, continuations, salt chain, next17 30-byte copies and
proof serialization remain unchanged. Decoded execution, valid accesses,
byte-copy/register/frame effects and exact cycles are proved against the
delivered image, with matching packed literals and aggregate accounting.
Public provenance is prepared under `~/cg/sub14/` with the next17 parent
UUID intentionally left as a placeholder. Nothing is pushed or submitted;
local artifact-backed checks are not an official Yukon verifier run.

A separate 128-cycle combined nonce/28-byte/A1 prototype preserved all
emulated bytes and passed its individual copy proofs, but its downstream
`GroupOpenUpperRun` build exceeded local memory limits. It is not certified
or included here; only the direct nonce branch is delivered.

## Historical next17 documentation

# Product: inline aligned 30-byte writer copies (-352 opening cycles)

Based on our next16 commit `273b84f`, retaining promoted master `2a79dc7`
and all of Meganpark980320's, benbuschmann's, Mahmoud514's and earlier
contributors' improvements described below. No public implementation is
newly transplanted in this entry.

The eleven 30-byte writer sites (levels 2..12) now contain their aligned
copies inline. Two alignment tests select either seven word pairs and a
jump to the final halfword pair, or three dword pairs, one word pair and
the same halfword pair. Both paths fall through to the existing continuation.
The 2-mod-4 path calls the old shared stub, now holding the 22-instruction
shifted copy followed by `jalr zero,x29,108`.

Costs are 14 / 21 / 26 cycles for destinations 0 mod 8 / 4 mod 8 / 2 mod 4,
instead of 16 / 22 / 25. The shifted case is one cycle slower, but the
alignment schedule across 128 records saves 352 cycles overall. This layout
avoids an out-of-range conditional branch to appended code: aligned paths
are local and only the shifted path needs a long jump. No words are appended.

```json
{"commitCycles":504585244,"openingCycles":118849,"proofBytes":72160}
```

```text
(504,585,244 + 118,849) × 72,160 = 36,419,447,350,880
Improvement over next16: 25,400,320
```

Only the eleven 30-word copy sites and old shared stub words 1067..1096
are edited. Image lengths, commitment/checker images, embedded data, ABI,
continuations, chain and proof serialization are unchanged. The copied
bytes, valid accesses, register/frame effects and exact cycles are proved
against the delivered image; matching packed literals and aggregate bounds
accompany the artifact-backed certificate. Provenance is prepared in
`~/cg/sub13/` with a next16 parent placeholder pending its submission UUID.
Nothing is pushed or submitted. Local checks do not constitute an official
Yukon verifier run.

## Historical next16 documentation

# Product: preserved low-12-bit chain mask (-127 opening cycles)

Based on promoted master `2a79dc7`, submission
`ea7fbe09-200e-46db-940b-1a4ca686cba9` by **Meganpark980320**.
This retains their complete five-entry chain (`60c75e80`, `d65f21f3`,
`c6d19f38`, `3b9c2633`, `ea7fbe09`), including the cap walk, writer latch,
chain constants, level-22 pointer and commitment latch improvements.
Those entries extend our next14 submission
`295a1266-202b-44e8-be6c-bbd784558a66`; our next10–next14 writer and
benbuschmann endpoint optimizations are already present, not newly added here.
Mahmoud514's earlier commitment work is also inherited.

The remaining additive idea is the paused next15 mask: replace the two shifts
at the salt-chain entry with `and x30,x6,x1`, where `x1 = 4095`.
Unlike the uncertified next15 WIP, this layout extends Meganpark980320's
existing constant-initialization detour by just one instruction: word 757
sets `x1 = x26-1`, and the return moves to 758. The chain shifts one word
earlier, with its PC-relative link offset adjusted to preserve the target.
The header costs 36 instead of 35, and each query saves one cycle. A nonempty
batch of n queries saves n-1: 127 at 128 queries, zero at one query.
Empty opening is unchanged. No direct-return 30-byte copy gain is claimed.

```json
{"commitCycles":504585244,"openingCycles":119201,"proofBytes":72160}
```

```text
(504,585,244 + 119,201) × 72,160 = 36,419,472,751,200
Improvement over ea7fbe09: 9,164,320
```

Only 17 opening words change: 757, 758 and 777..791. Image lengths,
commitment/checker images, embedded data, ABI and proof serialization remain
unchanged. Matching image literals, packed leaves, mask-preservation proofs,
chain bounds and the artifact-backed certificate accompany the image.
The earlier next15 work is preserved separately on `devin/next15-wip` and is
not a certified ancestor. Public provenance is prepared in `~/cg/sub12/`.
Nothing is pushed or submitted by this work; local certificate and emulator
checks are not a claim of official Yukon verification.

## Historical promoted-master documentation

# Product: a two-instruction commitment latch against `a5 = 2^32` (-1,024 commitment cycles)

Built on our `cg-m4` (the level-22 sibling through a pointer word, submission
`3b9c2633-0fe8-40d3-b8f5-4d46b12f587c`, commit `03953bb`), which sits on the promoted product best
`c6d19f38-4b72-4e7a-908e-8d854bc7e2df` (promoted commit `12d186e2604d9e5ee32012245fdb4a6be2a30494`). Only the
commitment image changes: setup rows 4..5, the rank-8 / rank-9 salt rows of every 11-leaf group of the body, and
the latch. The opening and checker images, the salts, every oracle input, the ABI, the proof serialization and every
proof byte are unchanged.

## Result

| | `c6d19f38` | `cg-m4` (base) | This entry |
| --- | ---: | ---: | ---: |
| proof bytes | 72,160 | 72,160 | 72,160 |
| commitment cycles | 504,586,268 | 504,586,268 | **504,585,244** |
| opening cycles (128 positions, proved bound) | 120,864 | 119,328 | 119,328 |
| score | 36,419,666,645,120 | 36,419,555,807,360 | **36,419,481,915,520** |

`(504,585,244 + 119,328) × 72,160 = 36,419,481,915,520`, 73,891,840 below `cg-m4` (1,024 cycles × 72,160 bytes).

## Before

The commitment image is the 38-word setup, the body (rows 38..181,037: four copies of the 45,250-word tile, 16,384
leaves per pass, 1,024 passes) and the latch

```
181038 srli a2,a0,32          a2 = a0 >> 32
181039 bne  a2,zero,<181041>  out after the last pass
181040 jal  zero,<38>         next pass
```

3 cycles per pass (2 on the final exit). A two-instruction latch needs a register holding a bound for `a0`, but the
body uses every register: t0, a1, a3 are the oracle selector, width and primitive, a0 and a2 the call pointers, the
others constants and quartet-block gaps, and a4..a7 carry the salts of ranks 9 and 10 of each group: rank 8 preloads
them
(`ld a4,-1848(a0); ld a5,-1840(a0); ld a6,-1832(a0); ld a7,-1824(a0)`), because from those leaves' own `a0` the
generator reply words lie more than 2 KiB below.

## The change

```
setup
4   slli a5,s3,3          a5 = 2^29 << 3 = 2^32           (was: slli s6,s3,3)
5   add  s8,s5,a5         unchanged value                 (was: add s8,s5,s6)

rank 8 of every group     ld a4,-1848(a0) ; ld a6,-1832(a0) ; ld a7,-1824(a0)     (the a5 load dropped)
rank 9 of every group     sd a4,0(a0) ; ld a2,-2008(a2) ; sd a2,8(a0)             (was: sd a4,0(a0) ; sd a5,8(a0))

latch
181038 bgeu a0,a5,<181041>
181039 jal  zero,<38>
181040 nop (not reached)
```

- `s6` held `2^32` only between rows 4 and 33 and was read only by row 5; row 33 (`addi s6,s1,112`) still sets
  its body value, so the setup costs no extra instruction and every other register ends as before.
- At rank 9's salt rows `a2 = a0 − 88` (its first call's output pointer). The second salt word, word 17 of the
  group's generator reply, is 2,008 bytes below it, so `ld a2,-2008(a2)` reaches it; the reply stays intact in
  memory for the whole group (the invariant `MsgGood.group` already holds it for every rank ≥ 1). `a2` is rewritten
  by the next `add a2,a0,s*` before the second call, as for ranks 2..8.
- Rank 8 loses a row and rank 9 gains one, so every group, tile and later row keeps its address
  (`rankPrefix 9 = 98`, was 99); 18,605 image words change, all inside the body, setup rows 4..5 and the latch.
- `a0` at the latch after pass `k` is `4,152 + 4 MiB · k`: below `2^32` for `k < 1,024`, `2^32 + 4,152` after the
  last pass. The latch is 2 cycles per pass (`bgeu` not taken, `jal`) and 1 on the final exit.

Per pass the latch saves one cycle, 1,024 in all. Nothing else changes cost.

## Bound

- `edgeCost` 2 / 1 (was 3 / 2); steps per pass `181,002` (was 181,003); `S N − S 0 = 185,346,047`,
  `C N − C 0 = 460,281,855` (`Q` unchanged at 39,276,544); `commitSteps = 38 + 185,346,047 + 6 + 14,943,221 =
  200,289,312`.
- `commitCycles = 41 + 460,281,855 + 6 + 44,303,342 = 504,585,244` (base: `41 + 460,282,879 + 6 + 44,303,342`).

## Evidence

Memory-backed RV64IM emulator (Riscv.lean cost model, stand-in oracle replies, random message), base image and this
image from the commitment entry through the first full pass (16,384 leaves) to the latch:

| | base | this entry |
| --- | ---: | ---: |
| cycles to the end of pass 1 | 449,536 | 449,535 |
| oracle calls | 38,356 | 38,356 |
| hash of all oracle inputs | `d49c20f672d0b94f` | `d49c20f672d0b94f` |
| hash of all output pointers | `1c8c0655a3f1c91f` | `1c8c0655a3f1c91f` |
| next pc / `a0` / `a5` | 38 / 4,198,456 / – | 38 / 4,198,456 / 4,294,967,296 |

The patcher checks that `a5` is named nowhere else in the image and that exactly 1,488 rank-8 / rank-9 pairs
(4 tiles × 372 groups) are rewritten.

## Proofs

- Image description: `GroupedImageBase` (`saltCode` 8 and 9, `rankPrefix 9 = 98`), `GroupedPacket` (`saltPlan`
  with `.load .x12 .x12 (-2008) (sourceWord i+1)`; `PacketRegs.limit : x15 = 2^32`). `GroupedPacketDecode` and
  `GroupedTileCopy` (the tile-0 chunk literals re-rendered from the new image) re-check the image against the packets
  unchanged in form; `GroupedCommitImage` keeps `packet_length` / `packet_next`.
- `GroupedPacketRun`: `finish` also keeps x15; `rank9_address` (`w − 4 − 251 = sourceWord + 1`); the walk
  certificates of ranks 8 and 9.
- `GroupedContent`: `followerMem` of rank 9 reads its second word from memory; `body_prefetch` / `plan_prefetch`
  give x14, x16, x17 and keep x15. `GroupedFrame`: `followerSalt` of rank 9, `follower_mem_salt`.
- `GroupedInvariant`: `MsgGood.prefetched` is x14, x16, x17; the rank-9 salt equality takes word 17 from the reply in
  memory. `GroupedSeed`: `latch_good`.
- `GroupedSetup`: `setupOps` rows 4..5, `Seed2.limit`, `SeedRegs.limit`, `post_live_frame` (x15 into `Live`).
- `GroupedScan`: `edgeCost`, `S`, `latchReg` (writes nothing now), `edge_run` (`bgeu x10,x15,+12` taken iff the
  last pass; `jal x0` back to 38), `step_live`, `packet_execute`.
- `GroupedCommit` (`commitSteps`, the scan totals), `GroupedTailEval.commitCycles`, `GroupedChecks`,
  `GroupOpenClosing.claimCommitCycles`, `Solution.lean`, `claim.json`; `programs.json` and `K1Manifest`
  (`commitCode_0_*` chunks).

## Build and verification

Built and verified on a separate Linux build host (r7i.4xlarge, Lean 4.35.0, contract identical to `12d186e`
outside `submission/`). The host's user systemd cannot provide the read-only sandbox, so `scripts/run.py` refuses to
start there. The verifier used is a box-local copy of `scripts/run.py` / `verifier/verify.py`
(`scripts/run_local.py`, `verifier/verify_local.py`) with only the systemd sandbox wrapper removed: same policy check,
same fresh `.work/<id>/project`, same purge of cached candidate and challenge modules, same comparator and
`verifier/comparator.json`. The same host and script verified `cg-m1`..`cg-m4` at their scores.

```text
$ git checkout --detach cg-m5-commit-latch           # dc9d936
$ python3 scripts/run_local.py --track product          # 16 min 7 s wall (real 16m7.229s)
✔ [9870/9871] Built Solution
Build completed successfully (9871 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, CommitGolf.Challenge.certificate,
  CommitGolf.Challenge.submission_matches_artifact, propext, Quot.sound, Classical.choice, ...] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
{"artifact_digest": "a97ac9e8dcd4c99f5514bb535a891c22382242e48d57a9196b51a872ab1082fc",
 "claim": {"commitCycles": 504585244, "openingCycles": 119328, "proofBytes": 72160}, "commit": null,
 "contract_commit": "dc9d93626ca74e03e5507c2349a20ca2c7f19e27", "score": 36419481915520, "status": "verified",
 "work_created": true}
RC=0

$ cat scripts/score.json
{"score": 36419481915520, "metrics": {"commitCycles": 504585244, "openingCycles": 119328, "proofBytes": 72160,
 "proverCycles": 504704572, "contractCommit": "dc9d93626ca74e03e5507c2349a20ca2c7f19e27",
 "artifactDigest": "a97ac9e8dcd4c99f5514bb535a891c22382242e48d57a9196b51a872ab1082fc", "verified": true}}

#print axioms CommitGolf.Challenge.certificate
  'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms CommitGolf.Challenge.submission_matches_artifact
  'CommitGolf.Challenge.submission_matches_artifact' depends on axioms: [propext, Quot.sound]
```

(`contract_commit` is the checked-out branch commit; outside `submission/` it is byte-identical to `12d186e`.)
