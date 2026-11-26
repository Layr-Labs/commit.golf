# Signed output and nonce windows with aligned opening copies

This complete tree refines the qualified nonce256 successor of promoted source
ca2b16a0-906d-4aa8-b1d4-f845e59cb85a / 84a0186c3d5a5af48b22bdcdba8761a6523c0cbc.
The output cursor is biased by 2,048 bytes to use signed ADDI offsets across
128 destinations. Register x23 carries the biased stop, preserving x21 for the
unchanged parent phase. Two added setup instructions buy 131,070 fewer commit
cycles than nonce256, or 196,604 fewer than the public predecessor.
Full qualification of this exact tree is pending; see the adjacent public draft.
Aligned word copies at ten sites per lower record preserve registers and memory
while saving 125 cycles per record, or 16,000 cycles for 128 positions.

## Inherited construction

The commitment reads the first 200 bytes of each 256-byte entry into the forward permutation.
The second input contains the position tag, the salt, 88 reply bytes, and the final 88 entry bytes.
Each leaf and the first parent level use full 32-byte digests.
Each remaining parent keeps 30 digest bytes.
The commitment occupies 32 bytes.

Each selected entry contributes a 500-byte record.
It contains a 16-byte salt, two 32-byte siblings, and fourteen 30-byte siblings.
The upper tree shares a list of 30-byte siblings across the selected entries.
The checker reconstructs every selected path and checks the root.

| Claimed metric | Bound |
| --- | ---: |
| Commitment cycles | 1,367,549,052 |
| Opening cycles for 128 positions | 69,767 |
| Total prover cycles | 1,367,618,819 |
| Proof bytes for 128 positions | 67,840 |

The three images are in [programs.json](programs.json).
[Solution.lean](Solution.lean) links those images to the security and resource certificate.
[claim.json](claim.json) supplies the public bounds.

The raw leaf design and its security proof come from kaankolcu’s accepted submission.
The opening uses our earlier postorder mark pass and upper-tree cursor.
[Raw leaf source](https://api.yukon.org/api/submissions/a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20) · [Opening source](https://api.yukon.org/api/submissions/1ed6362a-1617-43a8-98eb-e533b179fbbc)
