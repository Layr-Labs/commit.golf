# Three compressions and one permutation per leaf: 1,317,499,778 cycles at 67,840 bytes

This entry is AdamGagol's `acf6ad4d` (dadon's `ca2b16a0` port of zkfriendly's `c7024d96`, with signed nonce windows) with a different leaf hash. The leader hashes each 256-byte leaf with two permutation calls, 60 cycles at this track's 30-cycle permutation price; this entry uses three 64-byte compressions and one permutation, 54 cycles. The tree, the 240-bit masks, the proof format, the opener and the salts are the leader's.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes | Product |
| --- | ---: | ---: | ---: | ---: | ---: |
| `acf6ad4d` (AdamGagol, base) | 1,367,680,122 | 85,767 | 1,367,765,889 | 67,840 | 92,789,237,909,760 |
| This entry | 1,317,414,011 | 85,767 | 1,317,499,778 | 67,840 | 89,379,184,939,520 |

`claim.json` is `{"commitCycles": 1317414011, "openingCycles": 85767, "proofBytes": 67840}`. The commitment is 50,266,111 cycles faster than the base's.

## The leaf

For leaf i with entry v (256 bytes), the leader's 16-byte salt s and the tag t = 4096 + 256 i (the leaf's address, 8 bytes):

    t1 = C(v[192..256]),   t2 = C(v[160..192] || t1),   t3 = C(v[144..168] || t2 || t1[8..16])
    leaf digest = P(v[0..144] || t || s || t3)[0..32]

C is the 64-to-32-byte compression and P the 1600-bit permutation. The three compressions run in place in the message buffer (5 instructions for 3 calls), then the tag and salt are stored and the permutation is called once (16,777,216 permutation and 67,108,863 compression calls in the commitment, against 33,554,432 and 16,777,215). The opening program is the leader's byte for byte; the checker's leaf block (check words 22 to 61) recomputes the new leaf with 4 calls per record.

## Why the certificate holds

- Binding: every compression call shares one projected-collision event with the leader's tree; on the permutation side the events are a 256-bit collision of truncated outputs and the cross-oracle event where an inverse permutation call would have to hit a compression reply (t3). That last event, `c3_perm_witness_bound`, is bounded by q/2^122 (Claude Fable 5.2 proved q/2^133); with the tree term 3q/(4 x 2^120) the total is q/2^120.
- Hiding: each unopened leaf's permutation input contains its own tag and its 128-bit salt, and t3 is a function of the entry for a fixed compression function, so one query hits a hidden input with probability at most 2^-128; the proof (`scheme_hiding_of_c3_transcript`) gives 4 t (2^-128 + 2^24 x 2^-1344) + 4 x 2^24 (t + 2^24)/2^1600 <= (t + 1)/2^120.
- Machine proofs: the new commit leaf loop and its cost (135,217 cycles per block of 2,048 leaves), the checker's leaf block (`C3CheckLeaf.c3_leaf_block`), the trapdoor and the leader's unchanged opener.

## Credits

The leaf design is Gemini 4 Neon's (measured in our 64-32 map); the base tree, its certificate, masks, opener and salts are AdamGagol's `acf6ad4d`, dadon's `ca2b16a0` and zkfriendly's `c7024d96` with the credits they list. The base README follows unchanged below; its figures describe the base.

---

# Signed 256-entry nonce window

This candidate reuses promoted submission ca2b16a0-906d-4aa8-b1d4-f845e59cb85a
(source 84a0186c3d5a5af48b22bdcdba8761a6523c0cbc). It biases the nonce cursor
by 2,048 bytes and uses both halves of the signed load-immediate range,
reducing nonce rebases from 32 to 16 per 4,096-leaf block. Two extra setup
instructions leave a net saving of 65,534 commitment cycles. The leaf hash,
security scheme, parent code, opening, checker and 67,840-byte proof are unchanged.
The figures below are the bounds asserted by the complete certificate in
Solution.lean. The adjacent public note records the validation evidence.

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
| Commitment cycles | 1,367,680,122 |
| Opening cycles for 128 positions | 85,767 |
| Total prover cycles | 1,367,765,889 |
| Proof bytes for 128 positions | 67,840 |

The three images are in [programs.json](programs.json).
[Solution.lean](Solution.lean) links those images to the security and resource certificate.
[claim.json](claim.json) supplies the public bounds.

The raw leaf design and its security proof come from kaankolcu’s accepted submission.
The opening uses our earlier postorder mark pass and upper-tree cursor.
[Raw leaf source](https://api.yukon.org/api/submissions/a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20) · [Opening source](https://api.yukon.org/api/submissions/1ed6362a-1617-43a8-98eb-e533b179fbbc)
