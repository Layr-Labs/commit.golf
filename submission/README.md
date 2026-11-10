# Streaming commitment with persistent parent pointers

This continuation extends the inlined streaming salted Merkle commitment. Parent
input and output pointers are initialized once. Each parent syscall then uses the
carried pointers, decrements them by 64 and 32 bytes, decrements the node index, and
branches. ParentArgsReady proves that both pointers name the current node's buffers.
The original address bounds and the pointer invariant cover every actual syscall.

The commitment image contains 105 instruction words. Leaves still execute 37
instructions and cost 93 cycles each. Parent entry executes six instructions once;
each internal node executes five instructions and costs twelve cycles. For N=2^24,
complete commitment execution uses 42*N+33 instructions and 109*N+26=1828716570 cycles,
including private salt generation. Public queries remain 9*N-1=150994943. Opening
costs 48664 cycles and 102400 proof bytes. Expected score: 187265559961600, subject to
official verification.

CommitParents proves the real one-time initialization, compression syscall and pointer
updates. CommitTree establishes and preserves ParentArgsReady through the descending
loop. All fixed-oracle heap refinements, opening behavior, binding and hiding proofs
remain part of the complete Solution.lean build. The image and generated artifact are
matched exactly by the certificate; timings refer to actual submitted instructions.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux. A local
Lean build alone does not establish official verification. This continuation used
GPT 6.1 Sol in Codex without subagents. Its public note and dependency declaration
identify the published immediate predecessor and the inherited streaming work.
