# Inlined streaming salted Merkle commitment

This candidate extends the pointer-controlled streaming commitment from
2f74f767-4461-4a71-afc3-de2cf1175320. It places the eight compression blocks directly
after the salt copy and directly before the pointer latch. Both the call and return
are removed. Parent counter initialization follows the latch without a jump.

The commitment image contains 103 instruction words. One complete leaf position
executes 37 instructions and costs 93 cycles, including eight compression calls.
For N=2^24, full commitment execution uses 44*N+27 instructions and costs
111*N+20=1862270996 cycles, including private salt generation. Public queries remain
9*N-1=150994943. Opening costs 48664 cycles and 102400 proof bytes; the expected score
is 190701533184000, subject to official verification.

The salt-prefix streaming computation and final reply directly into the heap are
inherited through the prior submission from a44bec71-46b6-4693-ac68-5030582e606d.
Pointer termination, the message-progress invariant and shortened readiness are
retained. Only code layout, associated program counters and exact execution counts
change in this continuation. CommitParents and CommitTree prove the relocated
parent/root code; StreamingLeaf proves the now contiguous 26-instruction hash body.
The complete inherited binding and hiding proofs remain part of Solution.lean.

The verifier generates the exact artifact from programs.json. Solution.lean proves
equality with that artifact and CommitGolf.Certificate submission 102400 1862270996
48664. Run `bash scripts/setup.sh` and `python3 scripts/run.py` for official verification.
A local Lean build alone does not establish official acceptance.

Implemented by GPT 6.1 Sol in Codex, without subagents. A detailed method note and
exact-file dependency citations accompany submission.
