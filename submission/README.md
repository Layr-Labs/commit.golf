# Quartet with permutation-chain salts

This submission adds a 341-triplet quartet loop to the chain leader
`f8612ed51db54d0c572f45af7620e6c7dac94243`. Its construction is Quartet (submission c08b0128-14a7-48dd-a745-070c3a77d754, public commit
3d226fc9746c8308fe56deb4f161a814cc127ab0) with the 2^28-byte salt draw replaced by a permutation chain.
The opening and check programs are byte-identical to Quartet's.

## What changed against Quartet

**Commit.** Quartet drew all 2^24 salts with one RANDOM call of 2^28 bytes (33,554,433 cycles). Here the
program draws 24 private bytes into the low bytes of a 200-byte state `x0` whose other 176 bytes are zero.
It then iterates `x(j+1) = P(xj)` with forward permutation calls. Each reply is written 176 bytes after the
previous one, so the next reply overwrites its last 24 bytes: every state keeps a 192-bit suffix that is
never stored in the tape. The salts are the eleven 16-byte slices of each reply's first 176 bytes.

- Words 13, 14 and 21 of the commitment program change: the seed goes to `T - 176` (`T` = trapdoor +
  0xA0000000, the salt tape), 24 bytes instead of 2^28, and word 21 jumps to the generator.
- The generator is appended after the final HALT (words 178,360-261,560): three setup instructions, a
  jump into an unrolled block of 27,731 copies of `ecall; addi a0,a0,176; addi a2,a2,176` entered at
  copy 3, and `bgeu a2,t2,8; jal BLOCK` at the block end. The 1,525,202 calls end exactly at the 55th block
  end. It then returns to the leaf loop at word 22 with `a0` set to the message.
- The last reply's suffix lies in the indices buffer, which the commitment never loads. The seed itself
  sits in an unused tail of the last quartet source block and is overwritten later by the leaf loop.
- The image is 261,561 words (1,046,244 bytes, below the 1 MiB limit). A commitment makes
  41,943,039 + 1,525,202 = 43,468,241 oracle calls.

**Opening and check.** Unchanged.

## Bounds

| | Quartet | Quartet + chain salts |
|---|---|---|
| commit cycles (exact) | 541,679,900 | **523,373,526** |
| opening cycles, 128 positions (worst case, attained) | 93,945 | **93,945** |
| proof bytes, 128 positions (worst case, attained) | 72,192 | **72,192** |
| score | 39,111,737,418,240 | **37,790,163,666,432** |

`claim.json`: `{"commitCycles": 523373526, "openingCycles": 93945, "proofBytes": 72192}`.

## What is proved

`Solution.lean` proves `CommitGolf.Challenge.certificate : Certificate submission 72192 523373526 93945`.
Here `submission` is the generated `CommitGolf.Artifact.submission`, and `submission_matches_artifact` holds
by `rfl`. The proof composes the following pieces:

- **Commit** (`QuartetCommit.exact_cost`): every commit run succeeds in exactly 523,373,526 cycles with
  43,468,241 calls. `QuartetChainSetup`, `QuartetChainLoop` and `QuartetChainExec` execute the seed draw and
  the generator for every possible reply and hand the leaf loop a state with Quartet's `StartLeafRegs`.
  The Quartet leaf and upper phases are reused, and the quartet loop is regrouped with the same memory effects through a memory frame
  (`QuartetCommitInput.BodyContent`: message words, salt words, zero quartet headers) that
  `QuartetChainMemory.final_content` establishes for the chain's output.
- **Commit distribution** (`QuartetCommit.tape_distribution`): under every fixed oracle, the commitment and
  trapdoor are those of Quartet's honest tree on the salts `actualNonces π k` of a uniform 192-bit key `k`.
- **Hiding** (`QuartetCommit.actual_hiding`): `min 1 ((t+1)/2^120)`, through
  `Sampling.Quartet.scheme_hiding_of_chain` and the refinement `QuartetCommit.commit_really_refines`.
  On each side the chain world is within `chainError (t + 2·2^24 + 2^22 + t)` of the independent-salt
  world (`NonceChainOracle.nonce_chain_oracle_distance`; the honest public computation now includes the
  2^22 quartet calls, `QuartetChainView`). Quartet's independent-salt bound holds at `(t+1)/2^121`
  (`QuartetFinalSharp`). `QuartetChainSecurity.quartet_chain_budget` checks the sum against `(t+1)/2^120`.
- **Opening, check, binding, assembly**: Quartet's, unchanged. `QuartetChainCertificate` and
  `QuartetChainAssembly` are Quartet's `QuartetCertificate`/`QuartetAssembly` with the chain refinement and
  the commit call bound stated against `COMMIT_BUDGET`.

## Local validation

The quartet loop now executes four initial triplets followed by 12,300 blocks of 341 triplets.
Its backward BNE spans -4092 bytes and replaces the former BEQ/JAL latch. Entry and exit jumps
preserve the surrounding program interfaces; the upper phase still starts at word 46,765.
The exact phase proof accounts for 4,194,304 oracle calls and 41,955,343 cycles, saving 4,080
commit cycles. Opening and check bytes, and the complete chain generator, are unchanged.

`lake build CommitGolfCandidate.QuartetChainAssembly` passed, including the exact artifact
identity and the existing security proofs. `lake env lean submission/Solution.lean` passed
after the checker dependencies built successfully (9,653 jobs). The submission policy check
returned `ok: true`, no errors, and score 37,790,163,666,432; artifact digest
`9b690dab74a43b6c045e66297412feefae1ef2a5e1ef18911321ddff47744a2c`. A separate dry run of the encoded quartet instructions
confirmed 12,303 control instructions and the same phase cost and exit PC.

Official verification has not completed: the current runner's Landlock ABI requires thread
synchronization through signals blocked by the verifier's syscall policy. Submission awaits an
unmodified verifier run on a compatible runner.

## Provenance

The permutation-chain salt generator and its hiding proof are taken from submission
c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492 (public commit 0a3c94c3045e):

- unchanged: `NonceChainGame`, `NonceChainReplay`, `NonceChainPath`, `NonceChainHidden`, `PublicQueryList`;
- one constant changed: `NonceChainLayout` (1,525,202 replies and 6 spare salts instead of 1,525,248 and
  512), `NonceChainOracle` (6 spare salts);
- import line changed: `NonceChainSyscall`;
- adapted to the Quartet layout and the unrolled loop: `QuartetChainLoop`, `QuartetChainExec`,
  `QuartetChainSetup`, `QuartetChainMemory` (from `NonceChainLoop`, `NonceChainExec`, `NonceChainSetup`,
  `NonceChainMemory`), `QuartetChainView` (from `NonceChainView`, adds the quartet calls),
  `QuartetChainSecurity` (from `NonceChainSecurity`), `QuartetChainRepresentation`
  (from `NonceChainRepresentation`), and `QuartetFinalSharp` (as that submission's
  `pinned_final_reference_hiding_sharp`).

That submission credits a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20, the 128-bit layout of
d15d9bde-2caf-4450-84eb-81f1e3babc9e and the finite permutation strategy model of
24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e. Quartet's own provenance applies to everything else; as there, the
position-binding proof adapts the recorded-query collision analysis from
[i34-9's public submission](https://github.com/Layr-Labs/commit.golf/pull/109) at commit
`604a4c90c6560e7c2da10b2a097d116c7a679ce9`.
