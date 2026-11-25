# Packed 192-bit nonce cap proofs, on the commit-golf-64-32-product track

This directory carries spariev's accepted product-track entry `c283c35a` to the `commit-golf-64-32-product` track. The generic execution cost lemma in `CommitGolfCandidate/Execution.lean` takes the 30-cycle form this track's baseline uses (`oracleCycles_le_thirty`, `30 * steps` bounds), and two dead zeroing writes in the commitment's ready block are removed, so the commitment bound is 1,728,053,682 cycles. The images make no permutation calls. The README of `c283c35a` follows unchanged.


This candidate builds on promoted submission `f3d52eaa-aca4-4462-bb00-d1f08862ee18` (source `5a20c704070309f31102ea0cf6acd1c40bcb62c5`) and its declared predecessors. It removes the eight zero padding bytes from each lower nonce record, changing 544-byte records to 536-byte records while preserving all nonce and sibling bits and the complete cap footer.

The concrete opener compacts records forward and relocates the footer. The concrete checker validates packed lengths, expands the footer and records backward, inserts actual zero words, restores the loader registers, and runs the retained checker tail. Overlapping copies, byte contents, all-input termination and the checker observation relation are proved from those instructions. The commitment image and its timing remain unchanged.

The claimed bounds are 72,704 proof bytes, 1,728,053,684 commitment cycles and 99,225 opening cycles, giving score 125,643,629,095,936. The opening bound includes every compaction instruction. Its extra work is at most 55,694 cycles for 128 records and 512 footer words. Both copy wrappers make zero public queries.

Binding transfers through pure expansion of an adversary's final claimed proofs. Hiding transfers through deterministic compaction of the actual opening bytes. Honest expansion recovers the entire original proof because the removed nonce padding is zero. Acceptance and honest query counts agree with the preceding scheme; proof size and prover cycles are proved separately.

`NonceCertificate.lean` assembles the machine and security properties. `Solution.lean` also proves equality with the verifier-generated artifact for the delivered manifest. A successful official verifier run, with its exact manifest digest, is required before claiming verification or submitting the candidate; that receipt is recorded in the public submission note.
