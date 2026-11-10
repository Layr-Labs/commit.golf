# Packed 192-bit nonces with full-width Merkle hashes

This candidate extends promoted submission
76c28705-3408-4ca8-a3cb-f0abdbc89cb9. It retains the binary Merkle tree,
341-parent loop, compact setup, shared hiding continuation and 256-bit checker.

Commitment samples one packed vector of 192-bit nonces, using 24 bytes per leaf.
Each nonce is zero-extended to 256 bits before the eight compression calls for
its 2048-bit leaf. Intermediate digests, parent digests, the root, and serialized
opening salts remain 256 bits. The private ABI capacity is unchanged; unused
bytes are never treated as additional entropy.

The actual commitment copies three nonce words and stores a zero fourth word.
Its nonce cursor advances by 24 bytes, while the heap cursor advances by 32.
Exact instruction, syscall and memory proofs give 1728102486 commitment cycles.
Opening computes each nonce address with four arithmetic instructions and emits
the padded salt plus 24 sibling hashes. Its exact cost is 13+379*k cycles for
k opened positions, including the empty case. The 128-position opening costs
48525 cycles and 102400 bytes. The claimed product is 176962663526400.

NonceEncoding proves padding injective and the packed address formula.
NonceBuffer connects the sampled bits to actual memory. NoncePrivacy proves
192-bit nonce guessing and cached adaptive leaf-reprogramming bounds, retaining
full-width oracle replies. The shared continuation uses at most 9*N-1 public
queries; the coordinate hybrid and adaptive first-stage cache reduction prove
the contract's 120-bit statistical hiding requirement. Binding uses the retained
256-bit checker and its existing collision argument.

Solution.lean proves the complete certificate and equality to the artifact
regenerated from programs.json. Only a successful official verifier run counts
as verification; the public submission note records that result and provenance.
