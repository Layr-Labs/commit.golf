# Keep the opening counter at zero

This candidate extends promoted submission `0cda7e43-a35e-4c75-9831-906bfb369681`
at `b6d55b3`. Commitment, checker, ABI, proof format and security model are retained.

The prior opening retained a per-position initialization to 24 and one final
subtraction by 24. Both are removed. The ABI initializes x28 to zero, the entry
setup preserves it, and every thirteen-instruction path body preserves it. A
proved invariant carries zero through every opened position. The final state
matches the existing compact reference because its twenty-four decrements also
leave zero.

The 357-word image uses JAL x0,16 at 4232 to skip the former initialization and
jump slots. The path starts at 4248 and consists of twenty-four thirteen-word
bodies. The outer latch begins at 5496, the return block at 5508, and the final
PC is 5520. Empty openings branch directly to the relocated return block.
Every delivered word is covered by the complete artifact equality.

Compact/NoInitPrefix proves the fifteen-cycle per-position prefix with its
counter invariant. NoInitLoop and NoInitBounds compose the counter-free path.
NoInitPosition and NoInitPositions prove 330 cycles per position and preserve
the invariant. NoInitInput establishes it from the actual ABI for every trapdoor
and position set, including empty inputs. NoInitEquivalence proves equality of
the machine-derived scheme with the certified compact reference. NoInitCertificate
transfers security through that equality and proves actual success, termination
and resources. NoInitArtifact proves full equality with the independently
regenerated delivered artifact; the commitment packed-code proof is inherited.

Proof size remains 101,376 bytes. Commitment costs 1,728,053,684 cycles. Opening
128 leaves costs 13+330*128 = 42,253 cycles. The target score is
175,187,453,709,312, improving the promoted frontier by 25,952,256.
Official verifier results are recorded in the public submission note.
