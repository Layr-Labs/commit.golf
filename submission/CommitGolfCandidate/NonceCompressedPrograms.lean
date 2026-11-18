import CommitGolfCandidate.CapPrograms
import CommitGolfCandidate.NonceExpandCode

/-! The delivered opening and check images: the cap-level opener with the proof compaction
appended, and the cap-level checker with the proof expansion in front. -/
namespace CommitGolfCandidate
open CommitGolf

/-- x23/x25 carry aligned source/destination pointers, x28 a positive word
count. x6 is scratch; x1 returns to the caller. -/
def nonceCopyLoop (name : String) (backward : Bool) : List Asm :=
  [.label name, ld 6 23 0, sd 6 25 0,
   addi 23 23 (if backward then -8 else 8),
   addi 25 25 (if backward then -8 else 8),
   addi 28 28 (-1), .branch 1 28 0 name, insn 0x00008067]

/-- `lhu rd, offset(base)`. -/
def s6Lhu (rd base offset : Nat) : Asm :=
  insn (offset * 2^20 + base * 2^15 + 5 * 2^12 + rd * 2^7 + 3)

/-- `sh rs, offset(base)`. -/
def s6Sh (rs base offset : Nat) : Asm :=
  insn ((offset / 32) * 2^25 + rs * 2^20 + base * 2^15 + 1 * 2^12 + (offset % 32) * 2^7 + 0x23)

/-- Replace the instruction at word `index`; labels are not words. -/
def asmReplaceWord : List Asm → Nat → Asm → List Asm
  | [], _, _ => []
  | .label name :: rest, index, new => .label name :: asmReplaceWord rest index new
  | _ :: rest, 0, new => new :: rest
  | item :: rest, index + 1, new => item :: asmReplaceWord rest index new

/-- In-place compaction of the internal proof at x15 (x16 records, end x25) into the delivered
format: per record 16 nonce bytes, then 128 bytes (three group digests and the first sibling),
then the 13 other siblings with their first 30 bytes; then the first 30 bytes of every footer node.
x23 reads, x25 writes, x22 is the internal end. Copies go by halfwords. -/
def s6CompactCode : List Asm :=
  [.label "compact-entry", mv 22 25, mv 23 15, mv 25 15, mv 24 16,
   .branch 0 24 0 "compact-footer",
   .label "compact-record", addi 28 0 8, .jump 1 "compact-halves", addi 23 23 16,
   addi 28 0 64, .jump 1 "compact-halves", addi 29 0 13,
   .label "compact-sibling", .jump 1 "compact-field", addi 23 23 2, addi 29 29 (-1),
   .branch 1 29 0 "compact-sibling", addi 24 24 (-1), .branch 1 24 0 "compact-record",
   .label "compact-footer", .branch 0 23 22 "compact-finish", .jump 1 "compact-field",
   addi 23 23 2, .jump 0 "compact-footer",
   .label "compact-finish", regop 11 25 15 0 32] ++ halt true ++
  [.label "compact-halves", s6Lhu 6 23 0, s6Sh 6 25 0, addi 23 23 2, addi 25 25 2,
   addi 28 28 (-1), .branch 1 28 0 "compact-halves", insn 0x00008067,
   .label "compact-field"] ++
  ((List.range 15).flatMap fun j => [s6Lhu 6 23 (2 * j), s6Sh 6 25 (2 * j)]) ++
  [addi 23 23 30, addi 25 25 30, insn 0x00008067]

/-- The cap opener with its HALT (word 110) replaced by a jump into the compaction. -/
def nonceCompactOpeningCode : List Asm :=
  asmReplaceWord (capOpeningCode LOG_LENGTH) 110 (.jump 0 "compact-entry") ++ s6CompactCode

/-- The delivered check code (`NonceExpandCode`): the retained checker entered through the
in-place proof expansion. -/
def nonceExpandedCheckCode : List Asm := nonceCheckCode

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
