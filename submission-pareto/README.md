# Two-permutation vector commitment

Each leaf uses two forward calls to the 1,600-bit permutation. The calls absorb
a private 128-bit salt, the position, and the 2,048-bit message. The first
256 bits of the second reply form the leaf digest. Internal Merkle nodes use
the 512-to-256-bit compression oracle.

An opening emits one 528-byte record per position. Each record includes the
salt and the first 16 sibling digests. The remaining eight levels use a common
Merkle frontier across the occupied subtrees. At 128 positions the proof is at
most 71,680 bytes. The commitment and opening cycle bounds are 671,613,460
and 41,216, for a product of 48,144,207,175,680.

Each nonempty opening computes all 255 internal occupancy marks in descending order.
A midpoint address gives each parent a four-instruction block.
The fixed sweep takes 1,023 cycles, including entry and return.

[The program manifest](programs.json) contains the three RV64 images.
[The submission definition](CommitGolfCandidate/TwoPermutationWideCertificate.lean)
fixes their layout, buffer capacities, and fuel.
[The artifact equality](CommitGolfCandidate/TwoPermutationWideCertificate.lean)
matches all three images to the verifier-generated submission.
[The assembly proof](CommitGolfCandidate/TwoPermutationGenericCertificate.lean)
combines the concrete execution and security refinements.
