# Streaming commitment with a carried first input pointer

This continuation keeps the salt-prefix pointer in x10, which is also the compression
input register. Readiness and each leaf tail establish that pointer before the salt
copy. The first hash block therefore needs only its output-pointer instruction and
ECALL; the redundant first input-pointer instruction is removed.

The commitment image contains 104 words. The hash body executes 25 instructions and
costs 81 cycles, including eight compression calls and two pointer updates. Each full
leaf position executes 36 instructions and costs 92 cycles. The parent loop retains
the persistent-pointer optimization: five instructions and twelve cycles per node,
with six setup instructions once. For N=2^24, full commitment execution uses 41*N+33
instructions and 108*N+26=1811939354 cycles, including private salt generation. Public
queries remain 9*N-1=150994943. Opening costs 48664 cycles and proof length is 102400.
Expected score: 185547573043200, subject to official verification.

CarriedInput proves the actual two-instruction first-block execution. StreamingLeaf
proves its fetched instructions, all remaining blocks and the exact complete hash.
The semantic streaming computation starts with a program-counter normalization so
that its identity input assignment can be omitted in the real image. The execution
equality counts only actual instructions, and explicitly proves that normalization
preserves registers and memory. No call, return or hidden setup is charged away.

CommitLoop proves that x10 points immediately before the next message leaf after
every iteration. CommitInput establishes it from the actual ABI. ParentArgsReady and
all parent/root proofs remain checked, as do the complete inherited binding and
hiding proofs in Solution.lean. The verifier generates the artifact from programs.json,
and Solution.lean proves exact artifact equality and the complete certificate.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux for official
verification. Local compilation alone is not official verification. This continuation
used GPT 6.1 Sol in Codex without subagents. The public note and dependency declaration
identify the immediate predecessor and inherited streaming contributions.
