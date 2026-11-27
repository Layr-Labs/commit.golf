# Binary-bottom chained tree with shared-midpoint salts

This certificate is for the `ptr` image. Every parent is binary, and levels L9 to L16 are
variable-width chains. Each leaf pair takes one 40-byte private draw, `s_L ‖ s_M ‖ s_R`, so each
leaf has a 24-byte salt window: its 16 private bytes plus the 8-byte shared midpoint. Unchained
parents keep a running source pointer and a running destination pointer.

`claim.json` is `{"proofBytes": 67840, "commitCycles": 911200264, "openingCycles": 186934}`.

## The tree

The leaf hashes a 256-byte entry with four 96-byte compressions; the salt enters only the last
call. Even leaves take `s_M ‖ s_L` and odd leaves take `s_R ‖ s_M`, read from the pair row at
offset 72 or 88. Parents hash `left ‖ right ‖ 0^32`. Chained levels L9 to L16 use 2, 4, 6, 8, 12,
16, 16 and 16 calls and keep 236, 234, 233, 232, 231, 230, 230 and 230 bits. Each chained level
meets `calls² · 2^width ≥ 2^238` (strict density ρ ≥ 1). Chain stages carry a nonzero level and
stage tag, and plain parents a zero third block. L2 to L8 and L17 to L23 keep 240 bits; L1 and the
root keep 256. No ternary node sits anywhere in the tree.

A 128-position opening is 128 records of 3,780 bits and 256 cap slots of 230 bits, 542,720 bits
in all. A record holds the leaf's own 24-byte salt window and its siblings at L0 to L14. The
checker reads every transmitted bit; there is no tail search. Any other cardinality sends a
792-byte record per position: the salt window and 24 full siblings.

## What the certificate proves

`CommitGolf.Challenge.certificate` is
`CommitGolfCandidate.Chained.BinaryMachine.Check.certified`, which composes the following.

- Commit (`full_commit_run`, `committed_root`, `committed_trapdoor`): exactly 911,200,264 cycles
  and 84,087,039 calls for every message and oracle. The machine returns the abstract tree's
  root and keeps every node and salt window in the trapdoor.
- Opener (`open_law`): it terminates on every trapdoor and position set and makes no calls. On
  committed trapdoors it returns the abstract opening. Every 128-position opening takes at most
  186,934 cycles.
- Checker (`batch_of_cap cap_judgment`, `checker_result`): it terminates on every input. It
  accepts exactly the wire-valid inputs, and makes at most 100 calls per position; at 128
  positions the exact cap-pair count is at most 2,048 (`pair_total_bound`).
- Completeness (`canonical_valid`): every honest opening is wire-valid.
- Binding (`Pw.check_binding`): two accepted openings that disagree at a position replay to two
  recorded 24-level binary paths with the same shape and root. Through the chained binding
  reduction with a 2^32 replay reserve, they yield `q/2^120`.
- Hiding (`machine_hiding`): the machine transcript equals the abstract scheme's under every
  fixed oracle. `PtrHiding.scheme_hiding` bounds that scheme with the shared-midpoint argument
  and the binary tree's 16,978,175 parent calls. Only the opened leaves' own salt windows are
  transmitted.

## Credits

- The batch opener's record and cap passes, the whole checker proof, the binding replay and the
  certificate assembly are ported from our S5 entry `5acafa20`. Its abstract checker model is
  rewritten here for the binary bottom.
- The shared-midpoint 40-byte draw and its hiding argument come from our R4 line (`673cbe9f`,
  `19cb7f2a`), which builds on dadon's `b4f31491`.
- The chained-level binding core comes from our `14c08500`, which builds on ekrembal's
  `1a30c52f`.
- The late-salt leaf and its hiding modules come from our `aeca157a`, and the 240-bit upper
  nodes from our `cfff5595`.
- The base machine model comes from dadon's `c9b8af82`.
- The 2048-biased message cursor follows AdamGagol's `a7c38c21`.
- Further inherited sources: our `9f54292d`, `97b601a0` and `98b5b7e9`.
