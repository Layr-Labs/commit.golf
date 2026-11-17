# Two-permutation vector commitment

Each leaf uses two forward calls to the 1,600-bit permutation. The calls absorb
a private 128-bit salt, the position, and the 2,048-bit message. The first
256 bits of the second reply form the leaf digest. Internal Merkle nodes use
the 512-to-256-bit compression oracle.

An opening emits one 528-byte record per position. Each record includes the
salt and the first 16 sibling digests. The remaining eight levels use a common
Merkle frontier across the occupied subtrees. At 128 positions the proof is at
most 71,680 bytes. The commitment and opening cycle bounds are 671,613,340
and 42,744, for a product of 48,144,308,101,120.

[The program manifest](programs.json) contains the three RV64 images.
[The submission definition](CommitGolfCandidate/TwoPermutationWideCertificate.lean)
fixes their layout, buffer capacities, and fuel.
[The artifact equality](CommitGolfCandidate/TwoPermutationWideCertificate.lean)
matches all three images to the verifier-generated submission.
[The assembly proof](CommitGolfCandidate/TwoPermutationGenericCertificate.lean)
combines the concrete execution and security refinements.


## Parent batching

This derivative extends the tagged-leaf candidate from Yukon submission
`f1602d7a-c022-4f4d-910b-38279eb4fe61` by kaankolcu at Git revision
`9049f25e857577356fcf29e3e9eac5f70e7843d0`. Section 7.1 of *Faster Merkle
Commitments with T8 Leaves* by Thomas Coratger, Giacomo Fenzi and Eylon Yogev
examines batching the upper-tree work and measuring the complete schedule.
The scalar RV64 implementation here amortizes loop control over a larger
straight-line batch. The compression oracle still processes one parent per call.

The 16,777,215 parent nodes factor as both 255 × 65,793 and 195 × 86,037.
Each additional batch boundary costs a conditional branch and a jump. Removing
60 boundaries saves 120 cycles. The 1,046,956-byte commit image fits 1,620 bytes
below the image-size limit. Its backward JAL displacement is -1,032,448 bytes.
The larger span is the largest divisor that fits this three-word body and the
existing leaf and root code. The Lean proofs check the entire delivered parent
schedule, its last branch, the root copy and the total machine cost.

The new Pareto pair is 671,656,084 prover cycles and 71,680 proof bytes.
