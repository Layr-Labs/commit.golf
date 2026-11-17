import CommitGolfCandidate.CapPrograms

namespace CommitGolfCandidate
open CommitGolf

def nonceCopyLoop (name : String) (backward : Bool) : List Asm :=
  [.label name, ld 6 23 0, sd 6 25 0,
   addi 23 23 (if backward then -8 else 8),
   addi 25 25 (if backward then -8 else 8),
   addi 28 28 (-1), .branch 1 28 0 name, insn 0x00008067]

def nonceCompactOpeningCode : List Asm :=
  let original := capOpeningCode LOG_LENGTH
  original.take (original.length-1) ++ [.jump 0 "compact-entry",
    .label "compact-entry", mv 22 25, mv 23 15, mv 25 15, mv 24 16,
    .branch 0 24 0 "compact-footer", .label "compact-record",
    addi 28 0 3, .jump 1 "compact-copy", addi 23 23 8,
    addi 28 0 64, .jump 1 "compact-copy", addi 24 24 (-1),
    .branch 1 24 0 "compact-record", .label "compact-footer",
    regop 28 22 23 0 32, shift 28 28 3 true,
    .branch 0 28 0 "compact-finish", .jump 1 "compact-copy",
    .label "compact-finish", regop 11 25 15 0 32] ++
    halt true ++ nonceCopyLoop "compact-copy" false

def nonceExpandedCheckCode : List Asm :=
  [.jump 0 "expand-entry", .label "expand-initializer-tail"] ++
  (capCheckCode LOG_LENGTH).drop 1 ++
  [.label "expand-entry", mv 26 11, mv 24 16,
   insn (7*2^20 + 17*2^15 + 7*2^12 + 6*2^7 + 0x13),
   .branch 1 6 0 "reject"] ++ li 29 536 ++
  [regop 6 16 29 0 1, .branch 6 17 6 "reject", shift 7 16 3,
   regop 18 17 7] ++ li 19 (sizes LOG_LENGTH).proof ++
  [.branch 6 19 18 "reject", regop 23 15 17, addi 23 23 (-8),
   regop 25 15 18, addi 25 25 (-8), regop 28 17 6 0 32,
   shift 28 28 3 true, .branch 0 28 0 "expand-record-guard",
   .jump 1 "expand-copy", .label "expand-record-guard",
   .branch 0 24 0 "expand-finish", .label "expand-record",
   addi 28 0 64, .jump 1 "expand-copy", sd 0 25 0,
   addi 25 25 (-8), addi 28 0 3, .jump 1 "expand-copy",
   addi 24 24 (-1), .branch 1 24 0 "expand-record",
   .label "expand-finish", mv 17 18] ++
   ([1,6,7,18,19,23,24,25,28,29].map fun reg => addi reg 0 0) ++
   [.jump 0 "expand-initializer-tail"] ++ nonceCopyLoop "expand-copy" true

def nonceCompressedProgram : Submission :=
  { capExperimental LOG_LENGTH with
    image := fun phase =>
      match phase with
      | .commit => (capExperimental LOG_LENGTH).image .commit
      | .opening => ⟨assemble (nonceCompactOpeningCode), []⟩
      | .check => ⟨assemble (nonceExpandedCheckCode), []⟩
    steps := fun phase =>
      match phase with
      | .commit => (capExperimental LOG_LENGTH).steps .commit
      | .opening => 2*(capExperimental LOG_LENGTH).steps .opening
      | .check => 2*(capExperimental LOG_LENGTH).steps .check }

end CommitGolfCandidate
