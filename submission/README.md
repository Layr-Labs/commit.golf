# Unrolled leaf blocks for the nonce-packed cap multiproof

This candidate builds on promoted submission `c283c35a-98fc-4898-a64d-f586abfcee44`, which restores
submission `243b0d14` and its declared predecessors (the nonce-packed cap multiproof with 536-byte
records). Everything visible in the opening and checking images, the trapdoor layout, the proof
format and every security argument is unchanged. The only behavioural change is in the commitment
image: the leaf loop now runs as unrolled blocks of 256 leaves, which removes almost all per-leaf
pointer and loop overhead.

## Claim

| Field | Previous | This candidate |
| --- | --- | --- |
| `proofBytes` | 72,704 | 72,704 |
| `commitCycles` | 1,728,053,684 | 1,678,377,395 |
| `openingCycles` | 99,225 | 99,225 |
| Score | 125,643,629,095,936 | 122,031,964,180,480 |

The commitment bound is the exact cost of the proved execution:
`3*2^24 + 22282*2^16 + 838862*200 + 195 = 1,678,377,395`. The terms are the private-randomness
syscall, 65,536 unrolled blocks, 200 long parent groups, and the fixed setup, parent setup, root copy
and halt. The score drops by 3,611,664,915,456 (2.87%).

## What changed in the commitment image

The previous leaf loop executed 34 instructions and 90 cycles per leaf: a seven-instruction salt
copy, eight compression blocks of three instructions each, and a three-instruction latch
(`addi s2,s2,24`, `addi s7,s7,32`, `bltu s7,s6`). The salt pointer `s2` and the heap pointer `s7`
moved once per leaf only so that the next iteration could use the same immediates.

The new image keeps every previous word except word 54 and appends 7,947 words after the parent
group tail (words 251,827 to 259,773, PC 1,011,404 onward). The image has 259,774 words
(1,039,096 bytes), below the 1 MiB limit.

- Word 54 (`jal ra, ...`) keeps its return link `ra = 4316` and now targets the new block instead
  of the old loop. The old leaf loop words remain in place but are no longer executed.
- A leaf with slot `j` (0 to 63 in its segment) is 31 instructions:
  `ld t1,24j(s2)`, `sd t1,0(a0)`, `ld t1,24j+8(s2)`, `sd t1,8(a0)`, `ld t1,24j+16(s2)`,
  `sd t1,16(a0)`, `sd zero,24(a0)`, seven retained blocks `addi a2,a0,32; ecall; addi a0,a0,32`,
  and the final block `addi a2,s7,32j; ecall; addi a0,a0,32`. All immediates fit in 12 bits
  (the largest are 1,528 and 2,016).
- A segment is 64 leaves followed by `addi s2,s2,1536` and `addi s7,a2,32`. The second instruction
  rebases the heap pointer from the last reply address, so no 2,048-byte immediate is needed.
- A block is four segments followed by `bltu s7,s6,+8`, `jal zero,4364` (exit to the unchanged
  parent setup) and `jal zero,block` (loop). 2^24 leaves are exactly 65,536 blocks.

Per block the machine executes 7,946 instructions and charges 22,282 cycles and 2,048 public queries,
including the final jump. That is 87.04 cycles per leaf instead of 90. The hash computation, the
query order, every input and output address, the leaf digests, the stored salts and the final
register file are identical to the previous image. The parent schedule, root copy, setup and
randomness syscall are untouched.

## What changed in the certificate

The reference semantics did not change. `commitBody`, `commitLeaves` and `commitPositionRun` are
the same definitions, so all refinement, binding, hiding, completeness, budget and nonce-packing
proofs are reused as they are. The new proof shows that the unrolled block executes exactly
`commitLeaves` for the same reference states.

New modules, in dependency order:

- `UnrolledShift`: the lagging frame `unrolledShift slot state`, which lowers x18 by `24*slot` and
  x23 by `32*slot`. It commutes with every register write other than x18/x23, with memory writes,
  `writeBits`, `readBuffer` and `oracleInput`.
- `UnrolledSalt`: on the shifted frame, the seven salt instructions with immediates
  `24*slot+c` take exactly the steps of the retained salt copy (same addresses, same validity checks).
- `UnrolledBlocks`: eight compression blocks on the shifted frame. The last block's
  `addi a2,s7,32*slot` produces the reference heap slot, so each block refines `cursorNextState`
  and the eight blocks refine `cursorHeapBlocks`.
- `UnrolledPosition`: one unrolled leaf is 31 instructions, 87 cycles and 8 queries, and refines one
  `commitPositionRun`. The reference pointer advance becomes one more slot of lag (`unrolled_next_frame`).
- `UnrolledSegment`: 64 leaves, then the two rebase instructions, which restore the reference frame.
  This uses the reference fact that after every position `x12 + 32 = x23`
  (`unrolled_position_output`). Invariant, link and heap-window progress follow from the existing
  per-position lemmas.
- `UnrolledBlock`: four segments, the heap-end branch (decided by the existing heap window) and the
  two jumps. `unrolled_loop` composes all blocks into
  `commitLeaves state (256*(blocks+1))`, ending at the parent setup.
- `UnrolledTree`: `unrolled_schedule_linked_body` joins the block loop with the retained parent
  setup, the long parent schedule and root serialization, in the same shape as the previous
  `long_parent_schedule_linked_body`.
- `UnrolledImage`: links every block instruction to the delivered words
  (`unrolled_image_fetched`), with the exit and loop jump targets checked by `decide`.

Changed modules:

- `Group341Words`: word 54 retargeted, and the arithmetic word description
  `unrolledLeafWord`/`unrolledSegmentWord`/`unrolledBlockWord` appended to the literal image list
  `group341ImageWords`. The depth-24 image is this literal list, as before. The `Asm` generator
  `commitCode` in `Programs` is unchanged and still assembles the previous image; it is not used
  for the delivered depth.
- `Group341Encoding`: image length 259,774, the tail-word lemma `group341_end_word` (now with an
  explicit `slot < 3` bound), and `unrolled_block_word_at` for indexed fetch checking.
- `Group341Image`: passes the new bound arguments to `group341_end_word`.
- `Commit`: the ready sequence now ends with `jal ra` to PC 1,011,404 (`commit_ready_linked`).
  The legacy `commit_leaf_call` takes its word-54 fetch as a premise. `FusedPosition`,
  `FusedLoop`, `FusedTree`, `CursorPosition` and `CursorLoop` thread that premise through
  `fused_position`, `fused_leaves`, `fused_body`, `cursor_position` and `cursor_leaves`; none of
  these theorems is used by the certificate. `QuadImage` drops the unused word-54 fetch lemma
  `contiguous_image_entry`.
- `CommitRuntime`: `ready_body`, `commit_after_random`, `commitExecution` and `commit_execute` use
  the unrolled tree. The full instruction allowance (unchanged at `512*2^24+1024`) still
  reaches the exact result, with 8,018,854,470 steps to spare.
- `CommitSemantics`, `Machine`, `NonceMachine`, `NonceCertificate`, `Solution` and `claim.json`
  carry the new commitment cycle constant. `CapMachine` and `CapCertificate`, which are outside the
  certificate's import closure, carry it as well.
- `Properties`: admission uses the new image length.
- `CapPackedImageEquality`: regenerated for the 508 packed declarations of the delivered manifest.
  The 490 periodic body windows are unchanged. The head window, the mixed tail window and the 16
  block windows are checked word by word against `longImageSpec`, which now includes
  `unrolledBlockWord`.

`Solution.lean` proves `submission_matches_artifact` against the verifier-generated artifact and
`certificate : Certificate submission 72704 1678377395 99225` through `nonce_certificate`, as before.
