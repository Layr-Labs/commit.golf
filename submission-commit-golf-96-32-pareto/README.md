# commit-golf-96-32-pareto: Shared-Midpoint 40-Byte Paired Late Salts, Dual 3-Ary Bottom Layers (`r = 2`), Selective 256/240/238-Bit Binary Upper Tree, and Two-End 6-Bit Packed L14 Cap

This submission implements an intermediate-regime, statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **Shared-midpoint 40-byte paired late salts (`RANDOM(40)` over 184-byte overlapped pair rows).**
   Each 256-byte leaf `m = msg[i]` is compressed in four 96-byte calls where private randomness enters only Call 3 (`u = C(m[0..96))`, `a = C(u || m[96..160))`, `b = C(m[160..256))`, even `L0[2j] = C(a_{2j} || b_{2j} || 0^8 || s_L(j) || s_M(j))`, odd `L0[2j+1] = C(s_M(j) || s_R(j) || 0^8 || a_{2j+1} || b_{2j+1})`). Consecutive even and odd 96-byte rows overlap by 8 bytes on the shared 64-bit random midpoint `s_M(j)` (`184` bytes per pair, 8-byte aligned), filled in place by one `RANDOM(40)` call at `+72`. Statistical hiding holds across all `0 <= k <= 2^24` with total variation distance strictly below `(t + 1) / 2^120` via the 5-way midpoint multiplicity bound `(2^23)^5 / (2^64)^4 = 2^-141`.

2. **Dual 3-ary bottom layers (`L0 -> L1 -> L2`) with exact-divisor zero-tail unrolls.**
   - `L0 -> L1` (`5,592,405` triplets + `1` promoted `L0[16,777,215]` = `|L1| = 5,592,406`) writes dense 32-byte nodes using exact divisor `U_L1 = 1,365` (`5,592,405 = 1,365 * 4,097`).
   - `L1 -> L2` (`1,864,135` triplets + `1` promoted `L1[5,592,405]` = `|L2| = 1,864,136`) compresses dense 96-byte triplets from `L1` directly into the zero-gapped `L2` layout using exact divisor `U_L2_PAIRS = 333` (`932,067 = 333 * 2,799`).

3. **Selective 256/240/238-bit left-aligned binary upper tree (`L2 -> L23`) and `L14` deduplicated cap.**
   - `L0..L4` and root `L23` retain full 256-bit digests (`L2`, `L3`, `L4` are all even, zero promotions).
   - `L5..L8` (`4` levels) are byte-truncated to 240 bits (`sh zero, 30(a2)`).
   - `L9..L22` (`14` levels) are bit-truncated to 238 bits (`ld/and/sd` with `2^46 - 1`), proven adaptively binding (`<= q / 2^120`) via the exact 238-bit survival-product birthday bound.
   - Cutting the unified deduplicated cap at `L14` (`456 = 2 * 228` cap leaves, `<= 228` cap frontier siblings at `k = 128`) and packing 6-bit top slices of all `L9..L22` siblings in reverse at the tail of the proof yields an exact `72,927`-byte proof at `k = 128` (`<= 123,000` opening cycles, `0` oracle calls, `<= 28 * k` check calls).

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 72,927 |
| Commitment cycles | 823,597,390 |
| Opening cycles (`k = 128`) | 123,000 |
| Total prover cycles (`k = 128`) | 823,720,390 |

Commitment executes `246,647,577` instructions (`823,597,390` cycles) and `76,429,539` compression calls (`0` permutation calls). Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 72927 823597390 123000` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding, and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-pareto
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
