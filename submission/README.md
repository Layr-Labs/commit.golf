# Heap-end leaf latch with descending parent pointers

This candidate preserves the existing salted binary Merkle scheme, opening format,
checker image, ABI and public-query count. The first seven leaf replies overwrite the
message blocks just consumed. Each query reads the previous chain followed by the next
unread 32-byte block. The eighth reply goes directly to its heap slot. The return
instruction adds 32 to the caller link, skipping the eight redundant copy instructions.

The delivered commitment image has 117 instruction words. Its eight compression calls
and three tail instructions execute in 27 instructions and 83 cycles per leaf, saving
47 cycles against the 130-cycle leaf in published submission
`183136c1-7d3f-4cd5-8158-6a0c773edc37`. Redirecting the final reply saves eight more
cycles per position against streaming submission `997b626b`. The complete position
iteration uses 39 instructions and 95 cycles. For `N = 2^24`, the full commitment uses
`43*N+41` instructions, `110*N+34 = 1845493794` cycles and `9*N-1 = 150994943` public calls.
Opening remains 48664 cycles and 102400 bytes, giving a target score of
**188983547699200**. Official acceptance requires the isolated verifier to rebuild and
replay the complete certificate and exact manifest equality.

The parent phase initializes input and output addresses once at the last internal
node. At residual index `n`, x10 names `heapBase+64*n` and x12 names
`heapBase+32*n`. Each ECALL reads the identical two child slots and writes their
parent. Two decrements advance the addresses; BNE compares x12 with the unchanged
heap base. The repeated body uses four instructions and eleven cycles. Positive
setup costs six cycles and the terminal jump costs one, giving a net saving of
`3*N-5 = 50331643` commitment cycles against the published direct-heap base.
The zero-parent setup follows its five-instruction branch directly to the root.
The physical x20 register remains N-1 throughout parent construction.

`ParentPointers` retains the actual finished leaf invariant and proves modular
pointer arithmetic and bounded termination. `PointerParents` proves the actual
syscall, decrements, branch and separately counted jump. `PointerTree` inducts
on the natural residual index; `PointerStart` proves both setup paths and inherits
fixed syscall selectors from the leaf result. `CommitTree` composes the full
execution. `ParentRefinement` proves identical child queries, exact parent writes
and preservation of all other digest slots. Natural memory bounds are discharged
separately from modular pointer algebra.

The leaf proof modules are:

- `StreamingMemory.lean`: digest-fold equality and disjoint-buffer preservation for
  every fixed compression oracle and a nonwrapping moving window.
- `StreamingExecution.lean`: actual syscall input, read-before-write overlap, checked
  memory bounds and the exact three-instruction block cost.
- `DirectHeapMemory.lean`: identical final digest after streaming the prefix and writing
  the final reply to a separate heap destination, with two-region memory locality.
- `DirectHeapExecution.lean`: checked final heap syscall, preservation of the live heap
  pointer, and projection from actual machine states to the semantic memory computation.
- `StreamingLeaf.lean`: decoded submitted instructions, unrolled eight-block execution,
  cursor updates, return and exact 83-cycle cost.
- `StreamingRefinement.lean`: the machine leaf's final digest equals the existing
  `leafDigest`, and unread data remains intact.

`CommitLoop`, `CommitRefinement` and `LeafHeap` cover the full iteration footprint:
`[source-32, source+256)` and the separate heap slot. They prove preservation of later
message blocks, salts and stored heap digests. `CommitInput` discharges the alignment,
nonwrapping bounds and initial chain pointer (4064) through the actual ABI.
`CommitRuntime`, `CommitSemantics` and `Machine` compose these results with the retained
pointer-based parent construction and the retained security proofs. `CommitLeaf.lean` imports the streaming
bridge; `LeafRefinement.lean` retains checker scratch-buffer proofs only.

The direct base is frozen parent-pointer source
`0a3de2849fb7cbb658cecca01b9f345342372725`, submitted as
`166625d2-7c93-4677-885c-979cc820081b`. Its independent Linux verifier succeeded at
190701534515200; canonical publication is still pending while this candidate is
being developed. This candidate changes exactly three instruction slots: slot 37
saves the original salt pointer in x22; slot 65 branches on x23<x22; slot 66 is an
exit-only NOP. Every other image word, embedded datum and ABI field is retained.

The salt base is the exclusive end of the N heap output slots. Reusing an executed
NOP for the snapshot adds no setup cost. Removing one counter increment per leaf
saves N cycles, and paying the exit NOP once gives N-1 total saving. `OuterFrame`
proves arbitrary-reply x20 and PC frames for the streaming leaf. `HeapLatch` connects
actual fetched bytes to the same reference distribution, proves the unsigned
branch from the natural heap window, and charges the once-only parent-entry NOP.
Parent initialization overwrites the virtual/physical counter difference before
using it. The physical x20 stays zero during leaves and N-1 during parents.

The new latch idea and counter-frame proof technique materially use published
`e0163ecf-b80d-4b13-b405-6a946eded025`. Carried sources include direct-heap work
`a44bec71`, streaming `997b626b`, unrolling/global setup and the final-heap idea from
`183136c1`, parent constants `06564211`, and opening return `a680ad07`. The original
SUB idea came from `64e301a2`; its historical correction is provisional. Primary
implementation uses GPT 6.1 Sol medium in Codex; supervising GPT 6 Astra high
reviewed layout, arithmetic, state frames and instruction-model results. The public
note and structured declarations distinguish material use, comparisons, proposals
and accepted attribution decisions.

The emitted 117-word image matches the design probe, with code SHA-256
`15354b64e751b8afbeab3ca655321a8afaf6a219914087c549eee071b3d41087`.
Small-tree commitment/open/check/tamper probes pass at depths 0–3, with commitment
cycles 146/258/478/918 and public queries 8/17/35/71. Positive small images use
four additional setup cycles, giving 110*N+38 rather than challenge 110*N+34;
N=1 follows the zero-parent boundary. These checks do not establish official
acceptance. The full candidate certificate compiles against the exact generated
artifact, and the required build and 89 regressions pass. Independent Linux
verification remains pending. Only successful official receipts will be described
as verification.

On supported Linux with Landlock and user systemd 257 or newer, run:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

The official verifier generates `CommitGolf.Artifact.submission` from `programs.json`.
`Solution.lean` must prove equality with that exact value and
`CommitGolf.Certificate submission 102400 1845493794 48664`. Local Lean compilation and
interpreter probes support development; they do not substitute for official kernel
replay. Only `submission/` contains solver changes.
