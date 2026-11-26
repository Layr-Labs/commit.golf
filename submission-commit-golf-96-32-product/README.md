# commit-golf-96-32-product: Shared-Midpoint 40-Byte Paired Late Salts, 3-Ary Bottom Layer, 240-Bit Left-Aligned Binary Tree, and Deduplicated L15 Cap

This submission implements a statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **Shared-midpoint 40-byte paired late salts (`RANDOM(40)` with 184-byte overlapped pair rows).**
   Each 256-byte leaf `m = msg[i]` is compressed in four 96-byte calls where private randomness enters only the final call:
   - Call 0: `u = C(m[0..96))` written in place to `m[64..96)`.
   - Call 1: `a = C(u || m[96..160))` written directly to the leaf's final-call row in the trapdoor.
   - Call 2: `b = C(m[160..256))` written directly to the leaf's final-call row in the trapdoor.
   - Call 3: for even leaf `2j`, `L0[2j] = C(a_{2j} || b_{2j} || 0^8 || s_L(j) || s_M(j))`; for odd leaf `2j+1`, `L0[2j+1] = C(s_M(j) || s_R(j) || 0^8 || a_{2j+1} || b_{2j+1})`.

   Consecutive even and odd 96-byte final-call rows overlap by 8 bytes on the shared 64-bit random midpoint `s_M(j)` (`184` bytes per pair, 8-byte aligned):
   `[a_{2j} (32 B) | b_{2j} (32 B) | 0^8 | s_L(j) (16 B) | s_M(j) (8 B) | s_R(j) (16 B) | 0^8 | a_{2j+1} (32 B) | b_{2j+1} (32 B)]`.
   One 40-byte `RANDOM` syscall at offset `+72` fills `s_L(j) || s_M(j) || s_R(j)` directly in place (`7` cycles per pair = `3.5` cycles per leaf before loop latch), with zero salt copies and zero tag stores.

   Statistical hiding holds across all opening sizes `0 <= k <= 2^24`: against Stage-1 queries and unsalted Calls 0–2, every hidden Call-3 input carries 192 fresh uniform bits; for Stage-2 queries, the probability that any 5 distinct pairs share the same 64-bit midpoint `s_M` is at most `(2^23)^5 / (2^64)^4 = 2^-141`, so conditioned on avoiding 5-way midpoint collisions each query matches at most 4 hidden even and 4 hidden odd leaves, each protected by an independent uniform 128-bit private half (`s_L` or `s_R`), keeping total variation distance strictly below `(t + 1) / 2^120`.

2. **Zero-rebase 3-subpass self-advancing leaf schedule.**
   Commitment executes four streaming passes with constant repeating loop bodies and single-instruction `bne` latches (zero base-pointer rebases):
   - Phase 0 (`512`-pair unroll): `8,388,608` `RANDOM(40)` calls (`58,736,650` cycles).
   - Phase 1A (`256`-leaf unroll): Call 0 across all `2^24` leaves (`167,804,936` cycles).
   - Phase 1B (`64`-pair unroll): Calls 1 and 2 across all `2^23` pairs (`335,686,280` cycles).
   - Phase 1C (`128`-pair unroll): Call 3 across all `2^23` pairs into dense `L0` (`167,804,936` cycles).

3. **3-ary bottom layer (`L0 -> L1`) and 240-bit left-aligned binary upper tree (`L1 -> L24`).**
   - Level 1 compresses `5,592,405` contiguous triplets `C(L0[3g] || L0[3g+1] || L0[3g+2])` directly into the zero-gapped `L1` layout (`128`-pair unrolled bulk loop with alternating `+64/+32` destination strides and zero gap-skip instructions, plus tail and promoted rightmost leaf `L0[16,777,215]`), giving `|L1| = 5,592,406`.
   - Levels `L2..L23` form a left-aligned zero-gapped binary tree (`64`-pair unrolled bulk loop) with digests byte-truncated to 240 bits (`sh zero, 30(a2)`), preserving 120-bit adaptive position binding (`240`-bit projected collision resistance). Levels `L0`, `L1`, and the root `L24` remain full 256-bit digests.

4. **Unified deduplicated cap opening at `L15` (cap height `c = 9`, `342` cap leaves).**
   For any nonempty sorted position set `positions`:
   - Each opened position `i` emits its 24-byte salt (`s_L || s_M` for even, `s_M || s_R` for odd), its level-0 sibling(s) (`64 B` for triplet leaves, `0 B` for the promoted leaf), its 32-byte level-1 binary sibling, and its 30-byte truncated binary siblings on `L2..L14` (skipping absent right siblings of promoted nodes), totaling at most `510` bytes per record.
   - Above `L15` (`L15..L23`), the opener marks all ancestors of `positions` and emits each required 30-byte cap sibling once in canonical bottom-up order. By a telescoping bound on the 342-leaf cap, at most `171` cap siblings (`5,130` bytes) are emitted across `k = 128` positions, certifying a worst-case proof length of `128 * 510 + 5,130 = 70,410` bytes.

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 70,410 |
| Commitment cycles | 847,595,227 |
| Opening cycles (`k = 128`) | 107,915 |
| Product score | 59,686,778,228,220 |

Commitment executes `257,596,469` instructions (`847,595,227` cycles) and `78,293,674` compression calls (`0` permutation calls). Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 70410 847595227 107915` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding, and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
