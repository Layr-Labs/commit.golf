# Descending parent pointers with direct-to-heap streaming leaves

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
iteration uses 40 instructions and 96 cycles. For `N = 2^24`, the full commitment uses
`44*N+40` instructions, `111*N+33 = 1862271009` cycles and `9*N-1 = 150994943` public calls.
Opening remains 48664 cycles and 102400 bytes, giving a target score of
**190701534515200**. Official acceptance requires the isolated verifier to rebuild and
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

The direct published base is our `a44bec71-46b6-4693-ac68-5030582e606d`,
accepted and promoted at `117e59821bdedd2763be1ee36b11ebde26f79bd0`, with score
195855494758400. Its exact submission tree matches independently verified source
`dd2ec811e3ee42c974160adc65472cd0131862c7`. This draft preserves its complete
leaf routine, opening and checking images, embedded data and ABI. Root node and
leaf routine addresses are unchanged; only parent words in slots 67–78 differ.

The base carries our streaming work (`997b626b`), published unrolling/global
arguments from `183136c1`, parent constants (`06564211`) and opening cursor return
(`a680ad07`). The final-reply-to-heap idea was learned from the `183136c1` public
note. Primary work uses GPT 6.1 Sol medium in Codex; the supervising GPT 6 Astra
high thread reviewed pointer termination, layout, arithmetic and independent
instruction probes. Public submission notes and structured declarations record
material provenance explicitly. Local compilation and model probes do not establish
an official verifier result for this parent-pointer candidate.

On supported Linux with Landlock and user systemd 257 or newer, run:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

The official verifier generates `CommitGolf.Artifact.submission` from `programs.json`.
`Solution.lean` must prove equality with that exact value and
`CommitGolf.Certificate submission 102400 1862271009 48664`. Local Lean compilation and
interpreter probes support development; they do not substitute for official kernel
replay. Only `submission/` contains solver changes.
