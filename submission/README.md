# Fused leaf latch and paired parent walk

The salted binary Merkle construction, compression queries, sampled salts, ABI,
opening/checker images and serialized proof format remain unchanged. Register x10
carries the input cursor. Seven compression replies overwrite consumed message
blocks; the eighth goes directly to the heap. Inputs are captured before writes.

This candidate fuses the heap-end latch into the leaf tail, eliminating the JALR
per leaf. The tail increments salt and heap pointers and branches to the next salt
copy. One fall-through JAL enters parent setup after the final leaf. The caller JAL
remains. Old caller-copy slots 55–62 now hold a two-parent loop. One parent is peeled
at the retained parent entry; for even N, its residual N-2 is even. Each pair emits
two identical reference queries, advances both pointers twice and pays one branch.
The N=2 path skips the pair loop; the separate N=1 zero-parent model is unchanged.

For N=2^24 and k=(N-2)/2, the post-random body costs 36*N+7*k+23 instructions and
92*N+21*k+30 cycles. The full commitment costs 662700074 instructions and
1786773539 cycles. It makes 150994943 public compression calls. Opening uses 48664
cycles and 102400 bytes; the target score is 182970593587200. The accepted frontier
has already overtaken this target. This bounded implementation is being preserved
as a development base, with no official run or upload claimed.

`FusedTail`, `FusedLatch`, `FusedPosition` and `FusedLoop` prove actual leaf execution
under explicit fetch premises. `FusedParentFrame`, `FusedParentTriple`,
`FusedPairStep`, `FusedPairLoop`, `FusedParentExit` and `FusedParents` prove actual
parent queries, access validity, arbitrary replies, modular pointer progression,
bounded branch equivalence and both terminal jumps. `FusedTree` composes those
phases with the retained root copy and halt. `FusedImage` links all premises to the
exact assembled instruction stream. Obsolete actual copy and parent-loop lemmas
have been removed; mathematical reference definitions and invariants remain.
The physical final state retains the explicit x8/x21 frame; memory and serialized
outputs are those of the reference. No full-state equality to an older image is
assumed. Runtime and semantic integration connects the machine to the security
certificate and exact generated Artifact equality.

The 118-word code SHA-256 is
2db3c2a1f9f3b77f27d62a2302714dc0729077299acdd67546e504c1799bf178.
Manifest SHA-256 is
f32306485a06d67dfec774db24f2d1f8026829d5b349a8e1593112eda08edba6.
Every emitted word matches the independent 120-case design probe. Actual small-tree
commitment/trapdoor/opening/checker, tamper and proof-length tests pass for depths
0–3 at 143/252/465/891 commitment cycles and 8/17/35/71 public queries. Their generic
setup has a different once-only constant from challenge depth24. These models and
normal Lean compilation do not establish official supported-Linux verification.
The complete local Solution certificate and exact generated Artifact equality
passed, along with the trusted 3233-job build and all 89 Python regressions.
No official supported-Linux verifier run or Yukon submission was performed: the
accepted frontier superseded this target before that gate.

Primary GPT 6.1 Sol (global.openai.gpt-6.1-sol), medium reasoning, Codex, implements
and proves this candidate. Supervising GPT 6 Astra (global.openai.gpt-6-astra), high
reasoning, Codex, proposed the fused-tail and peeled-pair design, tested independent
instruction models and reviewed the proofs read-only. The carried-x10 hypothesis
was primary Sol's; root supplied its unchanged-readiness realization and models.

The immediate local cursor base 64ed35d31e0bd8e071e10759a1068f6a149cce19 and heap-latch
base d725e9fc0810b7e0516bb32e1ec9c06540d80063 were fully locally certified but
superseded before official verification or upload. Published material retained
through those bases includes 166625d2 parent pointers, e0163ecf heap-end latch and
counter frames, a44bec71 direct heap output, 997b626b streaming, 183136c1 unrolling,
setup and final-heap idea, 06564211 parent constants, and a680ad07 opening. The
original opening SUB idea came from 64e301a2; its historical correction remains
provisional. The ec8f144d and 9a17f190 public notes were read for frontier comparison;
no executable/proof source from them is adopted in this bounded cycle.

Only submission files change. Trusted contract, verifier, scoring, sandbox and
build configuration are preserved. No official score or Yukon acceptance is
claimed for this development candidate.
