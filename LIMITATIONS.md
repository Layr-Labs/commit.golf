# Challenge scope and limitations

This document explains the fixed v1 contract. The authoritative games, parameters,
prices and certificate are linked from [RULES.md](RULES.md).

**Security.** The 120-bit targets are query-dependent advantage bounds: binding is
at most `q / 2^120` for `q ≥ 1`, and hiding is at most
`min(1, (t + 1) / 2^120)`. They are not uniform `2^-120` failure probabilities.
Classical adversaries have unrestricted local computation. Compression and the
two-sided permutation are independent ideal primitives. Concrete implementations,
quantum adversaries and constructions sharing a primitive need separate arguments.
Position binding supplies no extractor, extraction-time bound or SNARG
knowledge-soundness premise.

**Hiding.** Opening cardinality is fixed before choosing the adversary; messages
and agreeing positions may depend on its oracle answers before commitment. The
adversary sees the root and one opening proof. An oracle-dependent cardinality,
post-commitment position selection, repeated openings and an efficient simulator
are outside the certificate. A generic extension to adversary-selected cardinality
can lose a factor of `2^24 + 1`; that is a proof loss, not a demonstrated attack.
Timing, access traces and allocation are hidden by the game, so side-channel
resistance is not certified. See [Hiding](CommitGolf/Hiding.lean) for the precise
comparison with CY24.

**Resources.** The product track's objective covers worst-case abstract cycles for
one full commitment and one 128-position opening, multiplied by its proof-byte bound,
without amortization. The Pareto track ranks the same two measures, total cycles and
proof bytes, separately under the same certificate and limits, including the
`2^53 - 1` cap on their product. Checker cycles, trapdoor storage, commitment/value/index
bytes, code size, loading the 4-GiB input and interface output decoding are unranked.
Admission, query budgets and termination still constrain them. Declared capacities
do not measure actual allocation, touched bytes or peak working memory.

Public primitive calls cost eight abstract cycles, including fixed input/output
handling with no per-byte increment. Input is captured before output writes;
overlapping buffers and overwriting consumed input are permitted. A caller that
retains its physical input may need copies or restoration outside this objective.
Code unrolling can trade unscored image size for fewer charged instructions. A
lower score therefore need not imply lower application memory use or physical
end-to-end time. Oracle queries, operation profiles and machine cycles are distinct
measures; moving between them requires a proved bridge. Host-side preparation and
extractor re-entry counts do not by themselves measure runtime.

**Artifacts and trust.** Each image's combined code/data is strictly below 1 MiB.
Kernel-checked equality connects the delivered bytes and ABI to the certified
submission. The generated-Artifact alias supports admission at the image limit;
arbitrary independent large-image encodings have no general equality-checking
practicality guarantee. Native export and checksums supply no proof authority.
Python parsing/rendering and score arithmetic remain trusted verifier code.

Pinned Lake/dependency configurations and OS package setup execute before candidate
compilation. Package repositories remain mutable and can fail before verification;
that yields no candidate verdict. Candidate elaboration can execute native commands.
The supported Linux verifier contains compilation/export with systemd/Landlock and
a private writable cache, then replays selected declarations through the kernel.
This boundary depends on the host OS and is not a universal sandbox-escape proof.
The four-hour/24-GiB verification limits constrain proof processing separately from
machine scoring. Yukon service promotion and repository administration are additional
operational trust boundaries. Each track's directory (`submission/` or
`submission-pareto/`) should change only through that track's verified promotions;
Yukon enforces this, not the repository.

Changes to security games, prices, workloads or dependency assumptions require an
explicitly versioned challenge. Necessary verifier repairs require independent review
and compatibility replay before carrying acceptance forward.
