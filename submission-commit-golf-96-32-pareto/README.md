# commit-golf-96-32-pareto: Shared-Midpoint 40-Byte Paired Late Salts, Pure Binary 240/238-Bit Merkle Tree, and Two-End 6-Bit Packed L16 Cap

This submission implements a low-byte, statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **Shared-midpoint 40-byte paired late salts (`RANDOM(40)` over 184-byte overlapped pair rows).**
   Each 256-byte leaf `m = msg[i]` is compressed in four 96-byte calls where private randomness enters only Call 3:
   - Call 0: `u = C(m[0..96))` written in place to `m[64..96)`.
   - Call 1: `a = C(u || m[96..160))` written directly into the leaf's final-call row in the trapdoor.
   - Call 2: `b = C(m[160..256))` written directly into the leaf's final-call row in the trapdoor.
   - Call 3: even leaf `2j` hashes `a_{2j} || b_{2j} || 0^8 || s_L(j) || s_M(j)` and odd leaf `2j+1` hashes `s_M(j) || s_R(j) || 0^8 || a_{2j+1} || b_{2j+1}`, writing directly into the zero-gapped `L0` heap and truncating to 240 bits (`sh zero, 30(a2)`).

   Consecutive even and odd 96-byte rows overlap by 8 bytes on the shared 64-bit random midpoint `s_M(j)` (`184` bytes per pair, 8-byte aligned), filled in place by one `RANDOM(40)` call at `+72`. Statistical hiding holds across all `0 <= k <= 2^24` with total variation distance strictly below `(t + 1) / 2^120` via the 5-way midpoint multiplicity bound `(2^23)^5 / (2^64)^4 = 2^-141` and 128-bit independent private halves `s_L(j), s_R(j)`.

2. **Pure binary 24-level Merkle tree (`L0 -> L24`) with selective 240/238-bit truncation.**
   - Every level `l < 24` has exact power-of-two width `2^(24 - l)` stored in a zero-gapped 96-byte-pair layout (`2` 32-byte sibling slots + 32-byte zero pad), eliminating odd-node promotions and modulo arithmetic.
   - Levels `L0..L1` are byte-truncated to 240 bits (`sh zero, 30(a2)`).
   - Levels `L2..L23` (`22` levels) are bit-truncated to 238 bits (`ld x6, 24(a2); and x6, x6, x27; sd x6, 24(a2)` with `x27 = 2^46 - 1`), while the root `L24` retains all 256 bits.
   - Adaptive 120-bit position binding (`<= q / 2^120` for all `1 <= q <= 2^120`) holds via the exact survival-product birthday bound on 238-bit projected digests (`1 - prod_{i < M} (1 - i / 2^238) <= q / 2^120`).

3. **Unified deduplicated `L16` cap with two-end 6-bit packed tail stream (`67,872` bytes at `k = 128`).**
   For any nonempty sorted position set `positions`:
   - Each opened position `i` emits its 24-byte salt, two 30-byte siblings on `L0..L1`, and fourteen 29-byte low parts for `L2..L15` (`490` forward bytes per record).
   - Above `L16` (`256` cap leaves, `<= 128` emitted cap siblings at `k = 128`), each emitted cap sibling writes its 29 low bytes forward (`<= 3,712` bytes).
   - The 6-bit top slices (`(d >>> 232) & 0x3f`) of every emitted `L2..L23` sibling (`<= 1,920` slices at `k = 128`) are packed sequentially 6 bits at a time into `ceil(6 * n / 8)` bytes (`<= 1,440` bytes, zero padding remainder at `k = 128`) and appended in reverse byte order at the end of the proof (`62,720 + 3,712 + 1,440 = 67,872` bytes).
   - The single-pass checker reads low bytes forward from `p_lo` and pops 6-bit tails backward from `p_hi = proofEnd`, accepting iff `p_lo == p_hi`, zero unused padding bits remain (`cBuf == 0`), and the reconstructed `L24` root matches the claimed commitment.

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 67,872 |
| Commitment cycles | 948,322,837 |
| Opening cycles (`k = 128`) | 132,000 |
| Total prover cycles (`k = 128`) | 948,454,837 |

Commitment executes `83,886,079` compression calls (`0` permutation calls). Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 67872 948322837 132000` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding (exact 238-bit survival-product birthday bound), and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-pareto
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
