# Keep the authentication-path output cursor fixed

This candidate extends promoted submission `fa36097d-b984-4c0a-b8a6-6536150af469`
at `461fb6f`. It retains the commitment, checker, ABI, proof format and persistent
zero-counter invariant.

The 330-word opening image uses twelve instructions per unrolled path step.
Each of its four stores has an immediate offset `32*level+8*word`, so x25 remains
fixed during all twenty-four levels. One checked ADDI advances it by 768 bytes
afterward. This removes twenty-four increments and adds one, saving 23 cycles
per position. All signed immediates fit: the largest is 760.

FixedPath proves exact equivalence to the preceding thirteen-instruction step,
including sequential memory behavior for arbitrary aliases. FixedStep checks
actual fetches, memory accesses and twelve charged instructions. FixedFrames and
FixedLoop carry the reference's moving cursor virtually. FixedBounds proves
288 body cycles plus one final adjustment. FixedPosition and FixedPositions
compose the fourteen-cycle prefix, 289-cycle path and three-cycle latch into
306 cycles per position. FixedInput starts from the actual ABI for every
trapdoor and position set, including empty sets.

The path starts at 4232, its cursor adjustment is at 5384, the outer latch starts
at 5388, and the return block starts at 5400 and finishes at 5412. The relocated
branches and all delivered words are checked. FixedEquivalence proves equality
of the machine-derived scheme with the certified compact reference.
FixedCertificate proves success, termination and resources and transfers the
security properties through that equality. FixedArtifact proves full equality
with the independently generated artifact, including the retained commitment.

For 128 leaves, proof size is 101,376 bytes and commitment cost is 1,728,053,684
cycles. Opening costs `13+306*128 = 39,181` cycles. The target score is
175,187,142,282,240, an improvement of 298,450,944 over the promoted predecessor.
The public submission note records the official verifier receipt when available.
