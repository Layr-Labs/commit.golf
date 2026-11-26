# commit-golf-96-32-pareto: Pure Binary Uniform 238-Bit Tree, 121-Bit Early-Tagged Independent Salts, and Two-End 6-Bit Packed L16 Cap (`66,672` Bytes)

This submission implements a compact, statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **121-bit early-tagged independent salts with one-sided identical-until-bad statistical hiding.**
   A single `RANDOM(2^28)` call populates 16-byte salt slots for all `2^24` leaves, of which the low 121 bits are masked in place (`salt_i : BitVec 121`, zeroing the top 7 bits of byte 15). Each 256-byte leaf `m = msg[i]` is compressed in four 96-byte calls:
   - Call 0: `cv0 = C(salt_i || 0^7 || tag_i || m[0..72))` where `tag_i = (1 << 63) | i` uniquely domain-separates every leaf position and sets bit 63 to prevent cross-domain collisions with internal tree inputs.
   - Call 1: `cv1 = C(cv0 || m[72..136))`.
   - Call 2: `cv2 = C(cv1 || m[136..200))`.
   - Call 3: `L0[i] = mask238(C(cv2 || m[200..256) || 0^8))`.

   Statistical hiding (`TV(Real_0, Real_1) <= (t + 1) / 2^120` across every opening size `0 <= k <= 2^24` and every query budget `t`) is proved using an exact combined Stage-1/Stage-2 query budget and a one-sided identical-until-bad coupling (`t / 2^121 + negligible <= (t + 1) / 2^120`), avoiding the factor-of-2 loss of a symmetric hybrid argument and achieving the exact 121-bit per-leaf salt floor.

2. **Pure 24-level binary Merkle tree with uniform 238-bit masking (`L0..L23`) and unmasked 256-bit root (`L24`).**
   - Every digest on levels `L0..L23` (`33,554,430` nodes) is masked to 238 bits (`ld/and/sd` with `2^46 - 1`), leaving the 256-bit commitment root `L24` unmasked.
   - Adaptive 120-bit position binding (`<= q / 2^120` for all `1 <= q <= 2^120`) holds via the exact 5-block survival-product birthday bound on 238-bit projected digests (`1 - prod_{i < M} (1 - i / 2^238) <= q / 2^120`).

3. **Deduplicated `L16` cap (`256` cap leaves) with bit-packed 121-bit salts and two-end 6-bit packed tail stream (`66,672` bytes exact at `k = 128`).**
   For any nonempty sorted position set `positions` (`k = |positions|`):
   - A leading `ceil(k / 8)`-byte header packs bit 120 (the top bit) of each opened leaf's 121-bit salt (`16 B` at `k = 128`, `0` unused padding bits).
   - Each opened position emits the low 15 bytes of its salt plus sixteen 29-byte sibling bodies for levels `L0..L15` (`479 B/record`, `61,312 B` at `k = 128`).
   - Above `L16` (`256` cap leaves), at most `k` (`128` at `k = 128`) deduplicated cap siblings emit 29 low bytes forward (`<= 3,712 B`).
   - The 6-bit top slices (`(d >>> 232) & 0x3f`) of every emitted `L0..L23` sibling (`<= 17 * 128 = 2,176` slices at `k = 128`) pack sequentially into `1,632 B` (`rem = 0`) appended in reverse byte order (`16 + 61,312 + 3,712 + 1,632 = 66,672` bytes exact).
   - `opening` (`203` code words, `0` oracle calls) executes in `<= 136,000` cycles at `k = 128`; `check` (`329` code words) verifies in a single pass with `<= 28 * k` compression calls (`<= 100 * k`).

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 66,672 |
| Commitment cycles | 1,075,446,281 |
| Opening cycles (`k = 128`) | 136,000 |
| Combined prover cycles | 1,075,582,281 |

Commitment executes `83,886,079` compression calls (`0` permutation calls). Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 66672 1075446281 136000` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding (exact 238-bit survival-product birthday bound), and 120-bit one-sided statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-pareto
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
