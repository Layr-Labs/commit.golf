# commit-golf-96-32-product: 3-ary bottom, left-aligned binary Merkle tree with 128-bit tagged salts and capped deduplicated openings

This submission implements a statistically hiding, adaptively position-binding vector commitment over the track's 96→32-byte compression oracle (`C`, 8 cycles per call). The permutation oracles are unused.

## Design

1. **128-bit index-tagged salts and zero-zeroing in-place leaf hashing.**
   Commitment samples `16 * 2^24` random salt bytes in one `RANDOM` syscall and stores them in the trapdoor. Each 256-byte leaf `i` is absorbed in four contiguous 96-byte compression calls directly in the message buffer:
   - Call 0 compresses `salt[i] (16 B) || tag[i] (8 B) || msg[i][0..72) (72 B)` at `[M_i - 24, M_i + 72)` where `M_i = 4096 + 256 * i` and `tag[i] = 4072 + 256 * i` is the unique running pointer `a0`, writing `cv0` to `M_i + 40`.
   - Call 1 compresses `cv0 (32 B) || msg[i][72..136) (64 B)` at `[M_i + 40, M_i + 136)`, writing `cv1` to `M_i + 104`.
   - Call 2 compresses `cv1 (32 B) || msg[i][136..200) (64 B)` at `[M_i + 104, M_i + 200)`, writing `cv2` to `M_i + 160` (overlapping the last 8 bytes of `msg[i][136..200)` with Call 3's input so no zero-padding is required).
   - Call 3 compresses `cv2 (32 B) || msg[i][192..256) (64 B)` at `[M_i + 160, M_i + 256)`, writing the unmasked 256-bit leaf digest directly into the trapdoor level-0 array `L0[i]`.

   Because `tag[i]` is injective in `i`, any adversary query can match at most one unopened leaf's 192-bit Call-0 prefix `(salt[i], tag[i])`, giving a per-query hit probability of `2^-128` for statistical hiding across all opening sizes `0 <= k <= 2^24`. The leaf loop is unrolled 128-way (`45` cycles per lane + 4-cycle loop latch per 128 leaves).

2. **3-ary bottom layer (`L0 -> L1`) and left-aligned binary upper tree (`L1 -> L24`).**
   - Level 1 groups the `2^24 = 16,777,216` leaf digests into `5,592,405` full 3-ary triplets compressed with `C(d0 || d1 || d2)` (unmasked 256-bit outputs), plus the single rightmost promoted leaf digest `L0[16,777,215]`, giving `|L1| = 5,592,406` nodes.
   - Levels `L2..L24` form a left-aligned binary Merkle tree over `L1` (`|L_{l+1}| = ceil(|L_l| / 2)`, promoting an unpaired rightmost node unchanged). Every internal level `L1..L23` is laid out in memory with a permanent 32-byte zero gap after each child pair (`96` bytes per pair), so binary compressions read `left (32 B) || right (32 B) || 0^256 (32 B)` in place with zero memory copies or zeroing stores.
   - Outputs on levels `L2..L23` are byte-truncated to 240 bits (`sh zero, 30(a2)`), preserving `240`-bit collision resistance (`120`-bit adaptive position binding) while saving 2 bytes per binary sibling above level 1. Levels `L0`, `L1`, and the root `L24` remain full 256-bit digests.

3. **Deduplicated cap opening at `L15` (cap height `c = 9`, `342` cap leaves).**
   For a nonempty batch of sorted positions `positions`:
   - For each opened position `i`, the proof emits its 16-byte salt, its level-0 sibling(s) (`2 × 32 B` for `i / 3 < 5,592,405`, `0 B` for the promoted leaf), its 32-byte level-1 binary sibling, and its 30-byte truncated binary siblings on levels `L2..L14` (skipping missing right siblings of promoted rightmost nodes).
   - Above `L15` (levels `L15..L23`), the opener marks all ancestors of the opened positions and emits each required 30-byte sibling once in canonical bottom-up order. By a telescoping bound on the 342-leaf cap, at most `171` cap siblings are ever emitted across all `k = 128` opened leaves, bounding the worst-case proof length at `69,386` bytes.

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 69,386 |
| Commitment cycles | 906,583,074 |
| Opening cycles (`k = 128`) | 105,867 |
| Product score | 62,911,518,860,226 |

Commitment executes `324,972,924` instructions (`906,583,074` cycles) and `78,293,674` compression calls. Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images, embedded level tables, and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 69386 906583074 105867` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, adaptive 120-bit position binding, and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
