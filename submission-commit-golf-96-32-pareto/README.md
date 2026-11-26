# commit-golf-96-32-pareto: Shared-Midpoint 40-Byte Paired Late Salts, 3-Ary Bottom Layer, Selective 240/238-Bit Binary Tree, and Two-End 6-Bit Packed L15 Cap

This submission implements a statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **Shared-midpoint 40-byte paired late salts (`RANDOM(40)` over 184-byte overlapped pair rows).**
   Each 256-byte leaf `m = msg[i]` is compressed in four 96-byte calls where private randomness enters only Call 3:
   - Call 0: `u = C(m[0..96))` written in place to `m[64..96)`.
   - Call 1: `a = C(u || m[96..160))` written directly into the leaf's final-call row in the trapdoor.
   - Call 2: `b = C(m[160..256))` written directly into the leaf's final-call row in the trapdoor.
   - Call 3: even leaf `2j` hashes `a_{2j} || b_{2j} || 0^8 || s_L(j) || s_M(j)` and odd leaf `2j+1` hashes `s_M(j) || s_R(j) || 0^8 || a_{2j+1} || b_{2j+1}`.

   Consecutive even and odd 96-byte rows overlap by 8 bytes on the shared 64-bit random midpoint `s_M(j)` (`184` bytes per pair, 8-byte aligned), filled in place by one `RANDOM(40)` call at `+72` (`7` cycles/pair = `3.5` cycles/leaf before loop latch). Statistical hiding holds across all `0 <= k <= 2^24` with total variation distance strictly below `(t + 1) / 2^120` via the 5-way midpoint multiplicity bound `(2^23)^5 / (2^64)^4 = 2^-141` and 128-bit independent private halves `s_L(j), s_R(j)`.

2. **Zero-rebase 3-subpass self-advancing leaf schedule and 3-ary bottom layer (`L0 -> L1`).**
   - Phases 0, 1A, 1B, and 1C execute four constant-body streaming passes with single-instruction `bne` latches and zero base-pointer rebases (`512`-pair `RANDOM(40)`, `256`-leaf Call 0, `64`-pair Calls 1–2, `128`-pair Call 3).
   - Level 1 compresses `5,592,405` contiguous triplets `C(L0[3g] || L0[3g+1] || L0[3g+2])` directly into the zero-gapped `L1` layout (`128`-pair unrolled bulk loop with alternating `+64/+32` strides and zero gap-skip instructions, plus tail and promoted rightmost leaf `L0[16,777,215]`), giving `|L1| = 5,592,406`.

3. **Selective 240/238-bit left-aligned zero-gapped binary upper tree (`L1 -> L24`).**
   - Levels `L0`, `L1`, and the root `L24` retain full 256-bit digests.
   - Levels `L2..L5` (`4` levels) are byte-truncated to 240 bits (`sh zero, 30(a2)`).
   - Levels `L6..L23` (`18` levels, `349,533` nodes) are bit-truncated to 238 bits (`ld x6, 24(a2); and x6, x6, x27; sd x6, 24(a2)` with `x27 = 2^46 - 1`), saving 2 bits per sibling on `L6..L23`.
   - Adaptive 120-bit position binding (`≤ q / 2^120` for all `1 ≤ q ≤ 2^120`) holds via the exact survival-product birthday bound on 238-bit projected digests (`1 - ∏_{i < M} (1 - i / 2^238) ≤ q / 2^120` with `M ≤ q + 2^37`).

4. **Unified deduplicated `L15` cap with two-end 6-bit packed tail stream (`70,080` bytes at `k = 128`).**
   For any nonempty sorted position set `positions`:
   - Each opened position `i` emits its 24-byte salt, level-0 sibling(s) (`64 B` for triplet leaves, `0 B` for the promoted leaf), 32-byte level-1 sibling, four 30-byte siblings on `L2..L5`, and nine 29-byte low parts for `L6..L14` (skipping absent right siblings of promoted nodes), totaling at most `501` forward bytes per record.
   - Above `L15` (`342` cap leaves, `≤ 171` emitted cap siblings at `k = 128`), each emitted cap sibling writes its 29 low bytes forward.
   - The 6-bit top slices (`(d >>> 232) & 0x3f`) of every emitted `L6..L23` sibling (`≤ 1,323` slices at `k = 128`) are packed sequentially 6 bits at a time into `ceil(6 * n / 8)` bytes (`≤ 993 B` at `k = 128`) and appended in reverse byte order at the end of the proof (`64,128 + 4,959 + 993 = 70,080` bytes).
   - The checker reads low bytes forward from `p_lo` and pops 6-bit tails backward from `p_hi = proofEnd` in a single pass, accepting iff `p_lo == p_hi`, zero unused padding bits remain in the tail buffer, and the reconstructed `L24` root matches the claimed commitment.

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 70,080 |
| Commitment cycles | 847,977,552 |
| Opening cycles (`k = 128`) | 65,740 |
| Product score | 59,430,873,903,360 |

Commitment executes `257,978,794` instructions (`847,977,552` cycles) and `78,293,674` compression calls (`0` permutation calls). Opening uses an alignment-specialized 8-residue word-buffered stream serializer (`0` oracle calls, `≤ 65,740` cycles at `k = 128`).

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 70080 847977552 65740` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding (exact 238-bit survival-product birthday bound), and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-pareto
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
