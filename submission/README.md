# Streaming commitment with both address registers carried

This continuation carries the current message pointer in x12 and its 32-byte salt
prefix in x10. Setup preserves both before hashing. The first compression is just
ECALL; subsequent blocks increment the live pointers. The last reply goes directly
to the heap. Two tail instructions prepare both arguments for the next leaf.

The commitment image contains 103 words. The hash executes 24 instructions and costs
80 cycles. Each complete leaf position executes 35 instructions and costs 91 cycles.
Parent construction retains the persistent-pointer loop at twelve cycles per node,
with six setup instructions once. For N=2^24, complete commitment execution uses
40*N+33 instructions and 107*N+26=1795162138 cycles, including private salt generation.
Public oracle calls remain 9*N-1=150994943. Opening costs 48664 cycles and outputs
102400 proof bytes. Expected score: 183829586124800, subject to official verification.

CarriedPair proves the first actual syscall with both argument registers already
ready. The general streaming bridges accept the actual ADDI source registers and
check all fetched instructions, memory bounds and replies. StreamingLeaf records the
original message base explicitly because later queries change x12. Its execution
equality includes every real instruction and proves the reference program-counter
normalization separately. CommitLoop proves both pointers are ready again after the
tail; CommitInput establishes the source pointer after preserving the ABI heap base.

The salted hash, Merkle tree, serialized trapdoor, opening/checker images and security
assumptions are unchanged. The complete binding and hiding proof remains in
Solution.lean, along with exact equality to the verifier-generated artifact from
programs.json. Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported
Linux for official verification. Local compilation alone is not official acceptance.

This continuation used GPT 6.1 Sol in Codex without subagents. Its public note and
dependency declaration identify the immediate predecessor and inherited contributions.
