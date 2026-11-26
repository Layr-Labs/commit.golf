# commit-golf-64-32-product: Zero-Copy `C0 -> P1 -> C2 -> SM-PLS-40(C3)` Leaf, Pure Binary `256/240/238`-Bit Tree, and Two-End 6-Bit Packed `L16` Cap

This submission implements a statistically hiding, adaptively position-binding vector commitment over the track's 64→32-byte compression oracle (`C`, 8 cycles per call) and 200-byte random permutation oracle (`P`, 30 cycles per call).

## Design

1. **Zero-copy `C0 -> P1 -> C2 -> SM-PLS-40(C3)` 4-call leaf schedule (`54` oracle cycles/leaf, zero salt/tag copies).**
   Each 256-byte leaf `v = msg[i]` is hashed in four streaming passes with zero intermediate byte copies or tag stores:
   - **Phase 0 (`SM-PLS-40`, `RANDOM(40)`)**: fills 120-byte overlapped pair rows `[a_{2j}(32) | 0^8 | s_L(16) | s_M(8) | s_R(16) | 0^8 | a_{2j+1}(32)]` in place at `+40` (`3.5` cycles/leaf before latch).
   - **Phase 1A (`C0`)**: `c0 = C(v[192..256)) -> v[192..224)` (in-place 64-byte compression, 8 oracle cycles).
   - **Phase 1B (`P1`, inverse-query hardened)**: `y = P(v[24..192) || c0) -> v[24..224)` (in-place 200-byte permutation placing the compression output `c0` in the trailing 32-byte field `[168..200)`, preventing inverse-permutation leaf forging; 30 oracle cycles).
   - **Phase 1C (`C2`)**: `a_i = C(v[0..24) || y[0..40))` written directly into the leaf's 120-byte pair row at offset `+0` (even) or `+88` (odd), leaving the `0^8` gaps and `SM-PLS-40` salts untouched (8 oracle cycles).
   - **Phase 1D (`C3`)**: hashes `[0..64)` (even: `a_{2j} || 0^8 || s_L || s_M`) and `[56..120)` (odd: `s_M || s_R || 0^8 || a_{2j+1}`) directly into the `L0` heap (8 oracle cycles).

   Because `C3` and all internal tree calls `L1..L24` never invoke `P`, conditioning on any fixed permutation realization `p` yields full 120-bit statistical hiding (`TV < (t + 1) / 2^120`) via the `SM-PLS-40` 5-way midpoint multiplicity bound.

2. **Pure binary 24-level Merkle tree (`256b: L0..L1`, `240b: L2..L5`, `238b: L6..L23`, `256b: L24`).**
   - `L0..L1` and root `L24` retain full 256-bit digests (`10` cycles/node at `L1`).
   - `L2..L5` (`4` levels) are byte-truncated to 240 bits (`sh zero, 30(a2)`).
   - `L6..L23` (`18` levels) are bit-truncated to 238 bits (`ld/and/sd` with `2^46 - 1`).
   - Adaptive 120-bit position binding (`<= q / 2^120` for all `1 <= q <= 2^120`) combines the exact 238-bit 5-block survival-product birthday bound (`<= (8191 / 8192) * q / 2^120`) with the cross-oracle `P1` permutation-witness bound (`<= q / 2^133 = (1 / 8192) * q / 2^120`).

3. **Unified deduplicated `L16` cap with two-end 6-bit packed tail stream (`68,512` bytes exact at `k = 128`).**
   - Each opened position emits its 24-byte salt, two 32-byte siblings (`L0..L1`), four 30-byte siblings (`L2..L5`), and ten 29-byte low parts (`L6..L15`) = `498` forward bytes/record (`63,744` B at `k = 128`).
   - Above `L16` (`256` cap leaves), at most `128` deduplicated cap siblings emit 29 low bytes forward (`<= 3,712` B).
   - The 6-bit top slices (`(d >>> 232) & 0x3f`) of every emitted `L6..L23` sibling (`<= 1,408` slices at `k = 128`) pack into `1,056` bytes (`rem = 0`) appended in reverse byte order (`63,744 + 3,712 + 1,056 = 68,512` bytes exact).
   - `opening` (`235` words, `0` data bytes) executes in `<= 110,258` cycles (`0` oracle calls); `check` (`277` words, `0` data bytes) verifies in a single pass (`<= 28 * k` calls).

## Certified Claim

| Claim | Bound |
| --- | ---: |
| Proof bytes (`k = 128`) | 68,512 |
| Commitment cycles | 1,276,210,876 |
| Opening cycles (`k = 128`) | 110,258 |
| Product score | 87,443,313,532,608 |

Commitment executes `83,886,079` total oracle calls (`67,108,863` compressions + `16,777,216` forward permutations). Opening executes `0` oracle calls.

## Artifacts and Verification

- `programs.json` contains the three RV64IM machine images (zero static data bytes) and memory layout.
- `claim.json` declares the certified resource bounds.
- `Solution.lean` assembles `CommitGolf.Certificate submission 68512 1276210876 110258` and proves `submission = CommitGolf.Artifact.submission` by reflexivity.
- `CommitGolfCandidate/` contains the complete formal proofs of instruction decoding, exact machine execution, termination, completeness, query budgets, worst-case proof size, prover cycles, cross-oracle adaptive 120-bit position binding, and 120-bit statistical hiding.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-64-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
