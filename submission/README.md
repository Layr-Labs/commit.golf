# Unrolled leaf loop (64 bodies per branch)

This builds on the promoted product tree c283c35a (pre-reset 243b0d14 lineage: packed 192-bit nonce cap proofs).

## Change

The commitment leaf loop executed one 33-instruction leaf body (salt copy, eight
carried-cursor compressions, salt/heap pointer increments) followed by a per-leaf
`bltu` back-edge. This tree appends 64 byte-identical copies of that body at the end of the
commit image (word 251827, PC 1011404), followed by one `bltu x23,x22,+8` and two long
jumps (re-enter the group / exit to the unchanged parent setup at 4592). The setup's
`jal x1` (word 54) now enters the unrolled group. Since 2^24 = 64 × 262144, each group costs
2114 instructions and 5698 cycles instead of 64 × 90 = 5760. No existing instruction moved;
the old loop remains as unreached code.

Commit cycles: 1,728,053,684 → 1,711,800,756 (−16,252,928). Opening, checking, proof format,
nonce, cap multiproof and all security arguments are unchanged.

Claim: proofBytes 72,704, commitCycles 1,711,800,756, openingCycles 99,225 →
score 124,461,976,218,624 (−0.94%).

## Proof

- `UnrollLeaf.lean`: the salt copy, prefix triples, heap query and pointer increments with
  fetch premises relative to a symbolic base PC.
- `UnrollLoop.lean`: one relocated position (33 instructions, 89 cycles, 8 queries) refines
  `commitPositionRun`; k bodies compose by induction; the group end branch/jumps; the whole
  loop over 262144 groups refines `commitLeaves` with exact cycles 5698·g and queries 512·g.
- `UnrollImage.lean`: all 64 bodies and the group end are fetched from the delivered image
  (`unroll_body_word`, `unroll_end_word` over the indexed image description).
- `UnrollRuntime.lean`: the long parent schedule composed with the unrolled loop; `CommitRuntime`
  uses it with the new exact constants. Packed artifact equality is regenerated for the
  253,942-word image.

Built with `lake build Solution CommitGolf.Challenge` on Linux (Lean v4.35.0).
