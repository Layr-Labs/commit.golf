# commit-golf-96-32-pareto: Shared-Midpoint 40-Byte Paired Late Salts and Pure 3-Ary FIFO Queue Tree (`814,056,832` Cycles, `91,104` Bytes)

This submission implements a minimum-cycle, statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **Shared-midpoint 40-byte paired late salts (`RANDOM(40)` over 184-byte overlapped pair rows).**
   Each 256-byte leaf `m = msg[i]` is compressed in four 96-byte calls where private randomness enters only Call 3:
   - Call 0: `u = C(m[0..96))` written in place to `m[64..96)`.
   - Call 1: `a = C(u || m[96..160))` written directly into the leaf's final-call row in the trapdoor.
   - Call 2: `b = C(m[160..256))` written directly into the leaf's final-call row in the trapdoor.
   - Call 3: even leaf `2j` hashes `a_{2j} || b_{2j} || 0^8 || s_L(j) || s_M(j)` and odd leaf `2j+1` hashes `s_M(j) || s_R(j) || 0^8 || a_{2j+1} || b_{2j+1}`, writing full 256-bit digests directly into the dense leaf array `L0[0..2^24)`.

   Consecutive even and odd 96-byte rows overlap by 8 bytes on the shared 64-bit random midpoint `s_M(j)` (`184` bytes per pair, 8-byte aligned), filled in place by one `RANDOM(40)` call at `+72`. Statistical hiding holds across all `0 <= k <= 2^24` with total variation distance strictly below `(t + 1) / 2^120` via the 5-way midpoint multiplicity bound `(2^23)^5 / (2^64)^4 = 2^-141` and 128-bit independent private halves `s_L(j), s_R(j)`.

2. **Pure 3-ary FIFO queue internal tree (`2^23 = 8,388,608` internal calls — exact information-theoretic minimum).**
   - Every internal node compresses three consecutive 32-byte nodes from the dense queue `nodes[0..25,165,824)` into `nodes[2^24 + j]` (`0 <= j < 2^23`) via a single `256`-way unrolled loop (`32,768` iterations, zero tail, zero truncation masking, zero gap padding, zero embedded data bytes).
   - Total commitment oracle calls = `4 * 2^24 + 2^23 = 75,497,472` (`814,006,332` commitment cycles).
   - Every internal and leaf digest preserves all 256 bits, yielding direct 256-bit birthday binding (`<= q / 2^120` for all `q >= 1`).

3. **Deduplicated 3-ary cap (`286` cap leaves, `143` cap calls, `91,104` bytes at `k = 128`).**
   - For any nonempty sorted position set `positions`, each opened position emits its 24-byte salt and climbs up to 10 3-ary steps (emitting two 32-byte siblings per step) until reaching the deduplicated cap frontier (`CAP_LEAF_LO = 25,165,395 .. 25,165,680`), followed by at most `191` deduplicated 32-byte cap frontier digests (`<= 91,104` bytes at `k = 128`).
   - Both `opening` (`158` words, `<= 50,500` cycles, `0` oracle calls) and `check` (`269` words, `<= 20 * k` oracle calls) use 100% 64-bit aligned `ld`/`sd` memory transfers with zero embedded data tables.

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 91,104 |
| Commitment cycles | 814,006,332 |
| Opening cycles (`k = 128`) | 50,500 |
| Total prover cycles (`k = 128`) | 814,056,832 |

Commitment executes `243,580,988` instructions (`814,006,332` cycles) and `75,497,472` compression calls (`0` permutation calls). Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images (zero static data bytes) and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 91104 814006332 50500` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding, and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-pareto
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
