import CommitGolfCandidate.CapPrograms

/-! The delivered checker image: the retained checker with its first word replaced by a jump
into the proof expansion appended after the truncation code.

The expansion works in place, from the end of the proof down. It rejects odd lengths, lengths
below `534 * count`, footers that are not whole 30-byte fields and expanded lengths above the
proof capacity. Then every 30-byte footer field becomes a 32-byte node with two zero top
bytes; every 534-byte record becomes a 576-byte record: 13 such nodes, 128 bytes copied as
they are, eight zero bytes, the 8-byte tag `4072 + 256 * position` of the record's position
(read from the position buffer) and the 16-byte nonce. All copies go by halfwords. Finally x17
holds the expanded length, the scratch registers are cleared and the retained initializer
resumes at its second word. -/
namespace CommitGolfCandidate
open CommitGolf

/-- `lhu rd, offset(base)`. -/
def nonceExpandLoadHalf (rd base offset : Nat) : Asm :=
  insn (offset * 2^20 + base * 2^15 + 5 * 2^12 + rd * 2^7 + 3)

/-- `sh source, offset(base)`. -/
def nonceExpandStoreHalf (source base offset : Nat) : Asm :=
  insn ((offset / 32) * 2^25 + source * 2^20 + base * 2^15 + 1 * 2^12 + (offset % 32) * 2^7 + 0x23)

/-- Words 200..256 of the delivered checker. The checker never reaches them: word 199 is a
jump to the reject sequence and no branch or jump targets them. -/
def nonceCheckUnusedWords : List Nat :=
  [0x58d13, 0x80c13, 0x78f313, 0xf8031ee3, 0xe93, 0xbe9e93, 0x218e8e93, 0x3d80333, 0xf868e4e3,
   0x381393, 0x788933, 0x993, 0xb99993, 0x198993, 0xb99993, 0x48098993, 0xb99993, 0x98993,
   0xb99993, 0x98993, 0xf529ece3, 0x1178bb3, 0xff8b8b93, 0x1278cb3, 0xff8c8c93, 0x40688e33,
   0x3e5e13, 0xe0463, 0x58000ef, 0x20c0263, 0x4000e13, 0x4c000ef, 0xcb023, 0xff8c8c93,
   0x300e13, 0x3c000ef, 0xfffc0c13, 0xfe0c12e3, 0x90893, 0x93, 0x313, 0x393, 0x913, 0x993,
   0xb93, 0xc13, 0xc93, 0xe13, 0xe93, 0xc21ff06f, 0xbb303, 0x6cb023, 0xff8b8b93, 0xff8c8c93,
   0xfffe0e13, 0xfe0e16e3, 0x8067]

/-- The expansion (words 445..545). x23 reads and x25 writes, both moving down. -/
def nonceExpandCode : List Asm :=
  [.label "expand-entry", mv 26 11,
   insn (1 * 2^20 + 17 * 2^15 + 7 * 2^12 + 6 * 2^7 + 0x13), .branch 1 6 0 "reject",
   addi 29 0 534, regop 6 16 29 0 1, .branch 6 17 6 "reject",
   regop 28 17 6 0 32, addi 7 0 30, regop 30 28 7 7 1, .branch 1 30 0 "reject",
   regop 28 28 7 5 1,
   addi 29 0 576, regop 18 16 29 0 1, shift 7 28 5, regop 18 18 7,
   addi 19 0 25, shift 19 19 29, .branch 6 19 18 "reject",
   regop 23 15 17, regop 25 15 18, mv 24 16, mv 29 28,
   .label "expand-footer", .branch 0 29 0 "expand-records", .jump 1 "expand-node",
   addi 29 29 (-1), .jump 0 "expand-footer",
   .label "expand-records", .branch 0 24 0 "expand-done",
   .label "expand-record", addi 29 0 13,
   .label "expand-sibling", .jump 1 "expand-node", addi 29 29 (-1),
   .branch 1 29 0 "expand-sibling",
   addi 28 0 64, .jump 1 "expand-halves",
   addi 25 25 (-8), sd 0 25 0, addi 25 25 (-8),
   shift 6 24 3, regop 6 6 13, ld 6 6 4088, shift 6 6 8, addi 6 6 2047, addi 6 6 2025,
   sd 6 25 0, addi 28 0 8, .jump 1 "expand-halves",
   addi 24 24 (-1), .branch 1 24 0 "expand-record",
   .label "expand-done", mv 17 18] ++
  ([1, 6, 7, 18, 19, 23, 24, 25, 28, 29, 30].map fun reg => addi reg 0 0) ++
  [.jump 0 "expand-initializer-tail",
   .label "expand-halves", addi 23 23 (-2), addi 25 25 (-2), nonceExpandLoadHalf 6 23 0,
   nonceExpandStoreHalf 6 25 0, addi 28 28 (-1), .branch 1 28 0 "expand-halves", insn 0x00008067,
   .label "expand-node", addi 25 25 (-32), addi 23 23 (-30), nonceExpandStoreHalf 0 25 30] ++
  ((List.range 15).reverse.flatMap fun half =>
    [nonceExpandLoadHalf 6 23 (2 * half), nonceExpandStoreHalf 6 25 (2 * half)]) ++
  [insn 0x00008067]

/-- The delivered check code: 546 words. -/
def nonceCheckCode : List Asm :=
  [.jump 0 "expand-entry", .label "expand-initializer-tail"] ++
  (capCheckCore LOG_LENGTH).drop 1 ++ s3CheckFiller 19 ++ nonceCheckUnusedWords.map insn ++
  s3LeafSubroutine ++ capCheckTruncation ++ nonceExpandCode

end CommitGolfCandidate
