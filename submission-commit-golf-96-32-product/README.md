# commit-golf-96-32-product: capped Merkle tree with 192-bit salts (stage D1)

This is a salted binary Merkle commitment over the track's 96→32-byte compression
oracle. Compression costs eight cycles. The programs use compression only.

**Leaves.** Each 2048-bit leaf is absorbed in four 64-byte blocks by an in-place chain.
The chain starts from the 32-byte state `salt ‖ 0^64`, where the salt is a private
192-bit (24-byte) value from the machine's `RANDOM` call (`saltState` in the Lean
model). Each call compresses the contiguous 96 bytes `chaining value ‖ next block` and
writes over the last 32 bytes it consumed. The fourth call writes the leaf's heap slot.
Two leaves are hashed per loop iteration, in 43 instructions and 99 cycles.

**Tree.** Parents are single direct calls on `left ‖ right ‖ 0^256` in a "gap heap"
(pair `j` at offset `96·j`). They are computed two per iteration, in descending slot order (bottom-up),
and only up to tree level 7 (the *cap*, 128 nodes). The commitment is a 64-step
96-byte chain over the cap pairs, starting from zero: `h_{k+1} = C(h_k ‖ cap[2k] ‖ cap[2k+1])`.
The chain state lives in otherwise unused gap slots.

**Proof.** The proof is the 128 cap digests (4,096 bytes), then one 568-byte record per
opened position in increasing order. A record is the 24-byte salt followed by the 17
siblings from the leaf up to its cap node. The checker enforces the exact length
`4096 + 568·card` and recomputes the cap chain (64 calls). For each record it
recomputes the salted leaf (4 calls) and the 17-level climb (17 calls), then compares the
result with the transmitted cap node.

| Claim (full commitment, opening of 128 leaves) | Bound |
| --- | ---: |
| Proof bytes | 76,800 |
| Commitment cycles | 1,073,741,261 |
| Opening cycles | 40,874 |

The commitment costs `64·2^24 − 563` cycles and makes `5·2^24 − 64` public queries.
The opening costs `1322 + 309·card` cycles and makes no queries. The checker makes
`64 + 21·card ≤ 85·card` queries. The product score is
`(commitCycles + openingCycles) · proofBytes = 82,466,467,968,000`.

**Security.**
- Binding is proved by collision extraction: 85 compression inputs per replayed record,
  and a birthday bound of `(q+340)^2/2^256 ≤ q/2^120`.
- Hiding is proved by a hybrid over the unopened leaves, and the whole loss is at most
  `2^24·4·(K+T+b+8)/2^192 ≤ (b+1)/2^120`. The first chain step of each hidden leaf is
  charged at 2^-192 per query because of the 192-bit salt. The honest transcript is
  charged once, as a single memoized heap computation:
  `T = 9·2^24 − 1 + 64` queries.

`programs.json` delivers the three machine images and their ABI. `Solution.lean`
assembles the complete certificate and proves equality with the generated artifact.
The supporting `CommitGolfCandidate/` modules prove execution, resource bounds,
completeness, binding and hiding for those images.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
