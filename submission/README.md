# Long-range parent batches with packed 192-bit nonces

This candidate extends nonce submission22ab66cc-8149-4363-a0c3-119bfc3d6170.
It retains its192-bit independent private nonces, full256-bit hashes, complete
Merkle construction, proof serialization, checker and adaptive security proofs.

After the first15 internal parents, the commitment processes3075 batches of5456
parents. Each batch contains16368 query/advance instructions. A BNE with a short
forward displacement selects one of two long-range JAL instructions: repeat the
batch, or return directly to the root copy. Exactly two latch instructions run
per batch, including the last. LongParentSchedule proves this execution for
arbitrary oracle replies and composes it with the fetched prefix, leaves and root.

The actual16537-word commitment image occupies66148 bytes, below the1MiB limit.
Its loop branch is at PC70232; root and loop jumps follow at70236 and70240. Their
encoded displacements are checked against fetched bytes. Group341-named concrete
modules retain their historical filenames but now specialize the schedule to5456.
Group341Encoding also proves that the independently assembled code equals the
literal delivered image.

Commitment costs1728059435 cycles and620763186 instructions. It saves43051 cycles
relative to the nonce predecessor, whose49200 short-branch batches plus one final
jump are replaced by6150 executed latch instructions. Public queries remain9*N-1.
The opening remains13+379*k cycles, including48525 for128 selected leaves, and
its proof remains102400 bytes. The claimed product is176958255104000.

Each private nonce occupies24 bytes and is zero-extended to256 bits before leaf
hashing. The opening emits that padded salt and24 sibling digests. NoncePrivacy,
HidingCoordinate and the shared9*N-1-query continuation retain the120-bit hiding
bound, while the unchanged full-width checker supplies the binding argument.

Solution.lean proves the full machine-derived certificate and equality with the
artifact regenerated from programs.json. Only a successful official verifier run
counts as verification; the public submission note records its result, source
identity and direct dependency citations.
