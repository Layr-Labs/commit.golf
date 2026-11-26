# commit-golf-96-32-product: Shared-Midpoint 40-Byte Paired Late Salts, 3-Ary Bottom Layer, Domain-Separated Hash-Chained Binary Tree, and Two-End Variable-Bit L14 Cap

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

3. **Adaptive variable-width binary upper tree with domain-separated iterated hash chains (`L1 -> L24`).**
   - Levels `L0`, `L1`, and the root `L24` retain full 256-bit digests.
   - Levels `L2..L5` (`4` levels) are byte-truncated to 240 bits (`sh zero, 30(a2)`).
   - Levels `L6..L8` (`3` levels) are bit-truncated to 238 bits.
   - Levels `L9..L16` (`8` levels) use domain-separated iterated hash chains of length `c_l` (`3, 4, 8, 8, 16, 16, 16, 6`) with stage tags `256 * l + s` in `[512..576)`, compressing digests down to `235, 234, 232, 232, 230, 230, 230, 233` bits while preserving `c_l^2 * 2^{w_l} >= 2^238`.
   - Levels `L17..L23` (`7` levels) are unchained 238-bit digests.
   - Adaptive 120-bit position binding (`≤ q / 2^120` for all `1 ≤ q ≤ 2^120`) holds via a banked-credit survival-product induction in the lazy compression ROM charging weight `1` to unchained binary queries and weight `c_l` to final-stage chained queries (bounded by total cache size via stage-parent injectivity).

4. **Unified deduplicated `L14` cap with two-end variable-bit packed tail stream (`69,365` bytes at `k = 128`).**
   For any nonempty sorted position set `positions`:
   - Each opened position `i` emits its 24-byte salt, level-0 sibling(s) (`64 B` for triplet leaves, `0 B` for the promoted leaf), 32-byte level-1 sibling, and the floor-byte low parts (`levelBodyBytes l` bytes) of each present sibling on `L2..L13`.
   - Above `L14` (`683` cap leaves, `≤ 68,904` total cap frontier bits at `k = 128`), each emitted cap frontier sibling writes its `levelBodyBytes l` low bytes forward.
   - All sub-byte tail slices (`levelTailBits l = levelWidth l % 8` bits) across `L2..L23` are packed sequentially LSB-first into `ceil(totalTailBits / 8)` bytes and appended in reverse byte order at the end of the proof (`(3,797 * 128 + 68,904 + 7) / 8 = 69,365` bytes at `k = 128`).
   - The checker reads low bytes forward from `p_lo` and pops variable-width tails backward from `p_hi = proofEnd` in a single pass, accepting iff `p_lo == p_hi`, zero unused padding bits remain in the tail buffer, and the reconstructed `L24` root matches the claimed commitment.

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 69,365 |
| Commitment cycles | 850,256,070 |
| Opening cycles (`k = 128`) | 160,000 |
| Product score | 58,989,110,695,550 |

Commitment executes `850,256,070` cycles and `78,453,292` compression calls (`0` permutation calls). Opening executes `0` oracle calls, and checking executes at most `100 * k` compression calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 69365 850256070 160000` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding (banked-credit lazy-ROM survival-product bound), and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
