# Near-limit parent batches with indexed artifact equality

This candidate extends promoted submissionad8c9121-2e86-4805-8022-0089246dfa25.
It retains the192-bit nonce sampler, full256-bit Merkle hashes, opening/checker
bytes, exact memory correctness, completeness and adaptive security proofs.

After15 peeled parents, commitment processes200 groups of83886 parents each.
A short forward BNE selects a long-range repeat or root-return JAL. Exactly two
latch instructions execute per group. The16537-word predecessor becomes251827
words (1007308 bytes), still strictly below the1MiB limit. Main starts at4760;
branch/root-jump/repeat-jump PCs are1011392,1011396,1011400. Their displacements
are+8,-1006984,-1006640. Each actual fetched instruction and pointer transition
is checked. The historic Group341 filenames now specialize this larger group.

Commitment costs1728053685 cycles and620757436 instructions. This saves5750
cycles over the5456-parent predecessor. Opening remains13+379*k cycles, including
48525 for128 leaves, with102400 proof bytes. The claimed product is176957666304000.
Public commitment queries remain9*N-1; security targets remain120 bits.

PackedImageEquality checks the generated artifact through indexed512-word block
facts and balanced joins, then proves equality of the entire submission. Three
periodic block proofs cover the repeated body; explicit prefix and suffix facts
cover all other bytes. Admission uses proved image lengths instead of unfolding
the full list. The PC recurrence also has a symbolic arithmetic proof. All these
proofs use the ordinary Lean kernel. Development compares all251827 assembler
words with the delivered literal image; the former unused monolithic assembler
equality helper is replaced by this byte comparison and the certified indexed
artifact/fetch proofs. Development depths use the retained eight-parent helper.

The submitted certificate concerns these exact machine images and ABI. Only a
successful official verifier run counts as verification; the public note records
its receipt, source identity and direct dependency citations.
