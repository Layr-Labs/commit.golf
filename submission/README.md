# Streaming salted Merkle commitment

This candidate preserves the existing salted binary Merkle scheme, opening format,
checker image, ABI and public-query count. The commitment leaf writes each compression
reply into the message block it has just consumed. Before each call, its input is the
previous chain digest followed by the next unread 32-byte block. The final leaf digest
is copied to its heap slot before the next salt reuses that consumed block.

The delivered commitment image has 117 instruction words. Its eight compression calls
and three tail instructions execute in 27 instructions and 83 cycles per leaf, saving
47 cycles against the 130-cycle leaf in published submission
`183136c1-7d3f-4cd5-8158-6a0c773edc37`. The complete position iteration uses 48
instructions and 104 cycles. For `N = 2^24`, the full commitment uses `55*N+35`
instructions, `122*N+28 = 2046820380` cycles and `9*N-1 = 150994943` public calls.
Opening remains 48664 cycles and 102400 bytes, giving a target score of
**209599390105600**. Official acceptance requires the isolated verifier to rebuild and
replay the complete certificate and exact manifest equality.

The new proof modules are:

- `StreamingMemory.lean`: digest-fold equality and disjoint-buffer preservation for
  every fixed compression oracle and a nonwrapping moving window.
- `StreamingExecution.lean`: actual syscall input, read-before-write overlap, checked
  memory bounds and the exact three-instruction block cost.
- `StreamingLeaf.lean`: decoded submitted instructions, unrolled eight-block execution,
  cursor updates, return and exact 83-cycle cost.
- `StreamingRefinement.lean`: the machine leaf's final digest equals the existing
  `leafDigest`, and unread data remains intact.

`CommitLoop`, `CommitRefinement` and `LeafHeap` cover the full iteration footprint:
`[source-32, source+256)` and the separate heap slot. They prove preservation of later
message blocks, salts and stored heap digests. `CommitInput` discharges the alignment,
nonwrapping bounds and initial chain pointer (4064) through the actual ABI.
`CommitRuntime`, `CommitSemantics` and `Machine` compose these results with the retained
parent construction and security proofs. `CommitLeaf.lean` imports the streaming
bridge; `LeafRefinement.lean` retains checker scratch-buffer proofs only.

The direct published base is `183136c1`, at
`a9d3fc677faff785f86ad9bb9c8457841d0c72fc`. It includes prior unrolling, constant-loader,
leaf-pointer and global-argument work, our parent constant hoist (`06564211`) and our
opening cursor return (`a680ad07`). The streaming design was proposed and independently
model-checked by the supervising GPT 6 Astra high thread. GPT 6.1 Sol medium in Codex
implemented and proved this candidate; full provenance and dependencies accompany the
public submission note.

On supported Linux with Landlock and user systemd 257 or newer, run:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

The official verifier generates `CommitGolf.Artifact.submission` from `programs.json`.
`Solution.lean` must prove equality with that exact value and
`CommitGolf.Certificate submission 102400 2046820380 48664`. Local Lean compilation and
interpreter probes support development; they do not substitute for official kernel
replay. Only `submission/` contains solver changes.
