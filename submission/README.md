# Quartet: one permutation call per group of four leaves

This submission keeps cursor43's leaf. It replaces the three binary compression parents at the bottom of every
group of four leaves with a single forward permutation call.

## What changed against cursor43

**Commit.** Leaves are unchanged. Each leaf makes two forward permutation calls on the raw entry window, with the
position tag and a private 128-bit salt from one RANDOM call. For each group `g` of four leaves, the program
writes a 200-byte block: 72 zero bytes, then the four 32-byte leaf digests `4g, …, 4g+3`. It then makes one
forward permutation call on that block. The first 32 bytes of the reply are the quartet node `2^22 + g`, a full
256-bit digest. Above the quartet nodes is cursor43's binary compression tree, with internal digests that keep
240 bits and zero the top 16, and the same eight-level cap. The trapdoor stores the quartet input blocks at a
512-byte stride, the upper heap and the salts. A commitment makes 2^25 + 2^22 + (2^22 − 1) = 41,943,039 oracle
calls. That is 8,388,608 fewer than cursor43's 50,331,647.

**Opening.** Each opened position contributes a 534-byte record:

- the 16-byte salt;
- the three other leaf digests of its quartet, 3 × 32 bytes, in slot order `(i mod 4) xor 1, 2, 3`;
- the 32-byte sibling of its quartet node;
- thirteen 30-byte projected siblings.

The last eight levels use the shared frontier of cursor43, 30 bytes per boundary node and at most 128 nodes for
128 positions. The opening program makes no oracle calls.

**Check** (not scored). The image is cursor43's proved 367-word checker at unchanged instruction addresses, with
five words changed and a 127-word block appended:

- words 0 and 8: record stride 534 and heap base 2^22;
- word 59: a jump to the appended block;
- words 62 and 63: fourteen lower levels instead of sixteen.

The appended block copies the computed leaf digest into slot `i mod 4` at `13312 + 72` and the three proof
siblings into the other slots. It permutes the 200-byte block, sets the heap index to `2^22 + ⌊i/4⌋`, and jumps
back. The 72-byte prefix at 13312 lies below every input buffer and is never written, so it is zero. The cap
phase (words 273–366) is byte-identical to cursor43's, so its proofs carry over unchanged.

## Bounds

| | cursor43 | Quartet |
|---|---|---|
| commit cycles (exact) | 637,936,351 | **541,679,900** |
| opening cycles, 128 positions (worst case, attained) | 88,311 | **93,945** |
| proof bytes, 128 positions (worst case, attained) | 67,584 | **72,192** |
| score | 43,120,258,756,608 | **39,111,737,418,240** |

`claim.json`: `{"commitCycles": 541679900, "openingCycles": 93945, "proofBytes": 72192}`.

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 541679900 93945`. Here
`submission` is the generated `CommitGolf.Artifact.submission`, and `submission_matches_artifact` holds by
`rfl`. The proof composes the following pieces:

- **Assembly** (`QuartetAssembly.quartet_certificate`, `QuartetCertificate.certificate_of_facts`): admission,
  machine success, termination of commit and opening, honest budgets, proof size and cycle bounds. They come from
  - `QuartetCommit.exact_cost`: every commit run succeeds in exactly 541,679,900 cycles with 41,943,039 calls;
  - `QuartetRV.opening_physical` and `QuartetOpening.scored_limits`: the opening's run for every position set,
    and its 93,945-cycle and 72,192-byte bounds at 128 positions.
- **Hiding** (`QuartetCommit.actual_hiding`): `min 1 ((t+1)/2^120)`. It follows from
  `Sampling.Quartet.concrete_hiding_of_refinement` and the exact commit and opening transcript refinement
  `QuartetCommit.commit_really_refines`.
- **Check program** (`Packed.Checker.executable_checker_facts`):
  - termination on every input;
  - at most `26·k` check calls (17 per record, at most 8 per cap group);
  - honest acceptance;
  - for every accepted input and every opened index, a recorded quartet opening: both leaf rows, the quartet
    permutation row with the leaf in slot `i mod 4`, and a 22-level projected path to the commitment.

  The new pieces are `QuartetCheckBlock.lean` (exact execution of the quartet block: 132 steps, 139 cycles, one
  call), `QuartetCheckHonest.lean`, and the 14-level lower recursion starting at heap node `lowerNode i 2`.
- **Binding** (`Quartet.quartet_scheme_binding`): `q/2^120`. It uses cursor43's pinned peer-leaf layout. The
  bound `Sampling.quad_replay_bound_of_layout` splits as 3q/(4·2^120) for compression collisions, q/2^124 for
  leaf events, and q/2^124 for quartet-node collisions or inverse hits on the 2^1024-element quartet domain.
  The total is at most q/2^120.

## Commands and results

From the project root, with the pinned Lean 4.35.0 toolchain. The candidate cache was purged as `verify.py`
does, and `CommitGolf/Artifact.lean` was regenerated from `programs.json` with `verifier/artifact.py`.

- `lake build +Solution`: "Build completed successfully (9736 jobs)", from a purged candidate cache.
- `lake env lean Audit.lean`: `certificate` depends on [propext, Classical.choice, Quot.sound];
  `submission_matches_artifact` on [propext, Quot.sound].
- `python3 verifier/check_submission.py .`: `ok`, artifact digest
  `cdc20922c28ec17527534f9959a7bb93d2310165d06f2bfdaf7bce7d9c323055`, score 39,111,737,418,240.
- The exact-cycle interpreter of the commit image reproduces 541,679,900 cycles and 41,943,039 calls.
- The generator's tests pass at depths 8, 9 and 11 and at full size: honest proofs accept, tampered proofs
  reject, oracle traces are exact, and at 128 positions the opening is 72,192 bytes and 93,945 cycles with
  2,431 check calls.

## Provenance

The Quartet commit, opening and hiding proofs, and the quartet binding bound, were written by our account in
an earlier session on top of our cursor43 submission. The checker proof is a port of cursor43's checker proof
to this image, and the assembly is new in this submission. As in cursor43, the position-binding proof adapts
the recorded-query collision analysis from
[i34-9's public submission](https://github.com/Layr-Labs/commit.golf/pull/109) at commit
`604a4c90c6560e7c2da10b2a097d116c7a679ce9`.
