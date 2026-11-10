# Carried compression-input cursor

This candidate retains the salted binary Merkle construction, opening/checker images,
ABI and public-query count. The first seven compression replies overwrite consumed
message blocks; the final reply goes directly to its heap slot. The input is captured
before each write. Register x10 carries the next compression input address and advances
by 32 after every reply. Four salt stores use x10 as their base. Readiness already
initializes that pointer, so no extra setup instruction is needed.

The 117-word image retains the same prefix and leaf entry addresses. Seven prefix
triplets select x10+32, query and advance x10. The final triplet selects x23, queries
and advances x10; JALR+32 skips the old caller copy. Two unreachable tail NOPs retain
image length. The subroutine costs 25 instructions/81 cycles; each position costs
37 instructions/93 cycles. For N=2^24 the commitment uses 41*N+41 instructions,
108*N+34 = 1811939362 cycles and 9*N-1 = 150994943 public calls. Opening remains
48664 cycles and 102400 bytes. The target score is **185547573862400**; official
verification and canonical Yukon acceptance remain pending during development.

The physical x8/x21 registers retain their original values. The virtual explicit-window
reference advances them. `CursorFrame`, `CursorInactive` and `CursorReference` prove
that this difference changes neither memory nor oracle queries. At leaf boundaries
physical x10 equals the reference x21 and physical x20 is zero. Parent initialization
overwrites x10 and x20; the final state retains only an explicit x8/x21 frame. No
old/new full-state equality is claimed.

`CursorExecution`, `CursorLeaf`, `CursorSupport` and `CursorTail` prove the actual
syscall, alignment/range checks, arbitrary replies, cursor progress and return.
`CursorSaltExecution`, `CursorPosition` and `CursorLoop` compose actual salt stores,
call, leaf and unsigned heap-end latch. `CursorParentBoundary`, `CursorParentFrame`,
`CursorRootFrame` and `CursorTree` transport the state frame through descending
parent pointers, the separately charged terminal jump, root copy and halt.
`CursorImage` discharges every fetched-instruction premise against the assembled
submitted image. `CommitRuntime` connects this execution to the real ABI and fuel;
`CommitSemantics` carries the unchanged memory contents into binding and hiding.
The retained `StreamingLeaf` definitions serve as the explicit-window reference;
obsolete actual-execution lemmas for its old instructions have been removed.

The descending parent loop keeps x10=heapBase+64*n and x12=heapBase+32*n, charges
four instructions/eleven cycles per node, and decrements both pointers after each
query. It is retained from 166625d2-7c93-4677-885c-979cc820081b. That submission was
accepted with verified score 190701534515200 and superseded by a stronger result.
The immediate local heap-latch base d725e9fc0810b7e0516bb32e1ec9c06540d80063 was
fully locally certified but superseded before an official run or upload. It saves
N-1 by adapting published e0163ecf's heap-end latch and counter-frame technique.
The current cursor adds an independent 2*N saving to that local base.

Carried material includes direct-heap a44bec71, streaming 997b626b, unrolling/setup
and the final-heap idea 183136c1, parent constants 06564211 and opening a680ad07.
The original opening SUB idea came from 64e301a2; its historical correction remains
provisional. Exact declarations and public notes distinguish material reuse from
comparisons and pending proposals from accepted attribution decisions.

Primary GPT 6.1 Sol (global.openai.gpt-6.1-sol), medium reasoning, Codex, proposed the
carried-x10 hypothesis and implemented/proved it. Supervising GPT 6 Astra
(global.openai.gpt-6-astra), high reasoning, Codex, supplied the unchanged-readiness
realization, independent decoded models and read-only proof/layout review.

The emitted code SHA-256 is
6cf351ee6284e0020593b15540ea41e9e8be05e0ddf4f39022eaa85f187ed20f; manifest SHA-256 is
ddb2063b12eca11acabca08213a3efa500e3770d65945ea2d8c434fc3086a04b.
The full image matches the independent 120-case decoded model. Small-tree commitment,
trapdoor, opening/checker, tamper and proof-length checks pass at depths 0–3 with
cycles 144/254/470/902 and public queries 8/17/35/71. Positive small images use generic
immediate setup, costing 108*N+38; N=1 follows the zero-parent path. The fixed challenge
uses 108*N+34. Models and local compilation do not establish official verification.

The full target is `CommitGolf.Certificate submission 102400 1811939362 48664`,
with equality to the artifact generated from programs.json. Actual-image linkage and
the complete certificate are currently being rebuilt. No trusted contract, verifier,
scoring or build configuration is changed. Official evidence must be finalized from
a successful exact-head supported-Linux run before submission.

The complete local Solution certificate passed for the cursor image. The accepted frontier was eight commitment cycles faster, so this source is retained as a locally certified development base; no official Linux verification or Yukon submission is claimed for this candidate.
