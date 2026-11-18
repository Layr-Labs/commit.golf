# Eight full-width parent levels

The commitment reads the first 200 bytes of each 256-byte entry into the forward permutation.
The second input contains the position tag, the salt, 88 reply bytes, and the final 88 entry bytes.
Each leaf and the first eight parent levels use full 32-byte digests.
Each remaining parent keeps 30 digest bytes.
The commitment occupies 32 bytes.

Each selected entry contributes a 514-byte record.
It contains a 16-byte salt, nine 32-byte siblings, and seven 30-byte siblings.
The upper tree shares a list of 30-byte siblings across the selected entries.
The checker reconstructs every selected path and checks the root.

| Certified metric | Bound |
| --- | ---: |
| Commitment cycles | 621,224,986 |
| Opening cycles for 128 positions | 87,559 |
| Total prover cycles | 621,312,545 |
| Proof bytes for 128 positions | 69,632 |

The three images are in [programs.json](programs.json).
[Solution.lean](Solution.lean) links those images to the security and resource certificate.
[claim.json](claim.json) supplies the public bounds.

The raw leaf design and its security proof come from kaankolcu’s accepted submission.
The opening uses our earlier postorder mark pass and upper-tree cursor.
[Raw leaf source](https://api.yukon.org/api/submissions/a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20) · [Opening source](https://api.yukon.org/api/submissions/1ed6362a-1617-43a8-98eb-e533b179fbbc)
