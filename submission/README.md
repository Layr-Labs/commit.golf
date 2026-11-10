# Unrolled compact openings

This candidate extends promoted submission
`3b60decf-00e1-46db-b9b2-a2e996f730b4` at `ace6b83`.
The proof format remains a 24-byte nonce followed by twenty-four sibling digests:
792 bytes per leaf, or 101,376 bytes for 128 leaves. The compact checker,
commitment image, ABI buffers, embedded data and instruction allowances are retained.

The opening repeats its fourteen path instructions twenty-four times and omits
the twenty-four backward path branches. Its path counter still decrements to zero.
The 381-word image advances from the nonce to the path by 24 bytes. It returns the
same proof bytes and reference machine state, with the final PC relocated to 5616.
Empty openings branch to the relocated return block at 5604.

Compact/FastOpeningInput proves execution for arbitrary trapdoors and position sets
at 13+355*k cycles, including 45,453 for 128 positions. FastOpeningEquivalence
proves equality with the machine-derived compact reference scheme.
FastOpeningCertificate transfers completeness, query budgets, proof size, binding
and hiding through that exact equality, and proves success, termination and cycles
for the new executable. FastOpeningArtifact checks the entire delivered submission
against the artifact independently regenerated from programs.json.

Commitment costs 1,728,053,684 cycles. The score target is
175,187,778,112,512, an improvement of 311,427,072 over the compact frontier.
A successful official verifier run is required before claiming verification;
public submission notes record the actual receipt.

The original 60-word compact opening and its full certificate remain the semantic
reference. The prior full Compact/Artifact equality is replaced by the new full
FastOpeningArtifact equality. The unchanged packed-code theorem checks every
word of the commitment image.
