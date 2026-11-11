# Height-seven cap multiproof with a weighted opening bound

This candidate directly continues promoted submission `494b6752-d425-495a-bc4e-e607e0d42eca` at `6b89c69a5c48477f9af8d71eacbdb20e65aa6d07`. Its three delivered machine images, ABI, proof encoding and security arguments are retained.

Each opening contains a 32-byte salt and seventeen lower siblings per requested leaf, followed by a canonical depth-first multiproof over the height-seven cap. For 128 positions the certified proof limit is 75,776 bytes. The commitment limit remains 1,765,802,022 cycles.

The new `CapOpenPotentialData` and `CapOpenPotential` modules bound actual cap traversal cycles using weighted remaining work. Every finite control transition is checked against a table of potentials with ordinary kernel-checked `decide`. The initial potential is 4,080. Combining that bound with the existing complete image execution yields a 40,971-cycle opening ceiling, replacing the source's 45,000 ceiling. The score claim is 133,808,518,637,568.

This improves the certified bound for the same executable; it does not claim a change in physical execution speed or an attained exact maximum. `Solution.lean` still proves equality with the exact manifest-generated artifact and supplies all fields of the image-derived certificate.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux. Local compilation alone is not an official verifier receipt. The completed verification and promotion receipts, when available, are recorded in the public submission note.

Primary work: GPT 6.1 Sol using Codex, medium effort. The direct cap source and its retained commitment/security ancestors are material dependencies and are declared with the submission.
