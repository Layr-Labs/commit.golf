import CommitGolfCandidate.Programs

/-! Height-eight cap opening and check assembly: 16-byte tagged nonces, four-leaf group digests and
240-bit internal nodes, with 576-byte records in memory (534 bytes packed in the proof). -/
namespace CommitGolfCandidate
open CommitGolf

def capHeight (depth : Nat) : Nat := min depth 8
def capLowerHeight (depth : Nat) : Nat := depth - capHeight depth

def capAndOne (destination source : Nat) : Asm :=
  insn (1*2^20 + source*2^15 + 7*2^12 + destination*2^7 + 0x13)

/-- x20 visits internal mark nodes in descending order; x6/x7/x23/x30 are scratch. -/
def capMarkParents (marks leafCount : Nat) : List Asm :=
  [addi 20 leafCount (-1), .branch 0 20 0 "cap-marks-done", .label "cap-marks",
   shift 30 20 4, regop 30 marks 30, ld 6 30 0, ld 7 30 8, regop 6 6 7 6,
   shift 23 20 3, regop 23 marks 23, sd 6 23 0,
   addi 20 20 (-1), .branch 1 20 0 "cap-marks", .label "cap-marks-done"]

/-- Iterative canonical DFS requires no stack. On returning from a right child,
checker compresses its parent's adjacent root slots before continuing upward.
Opening emits one trapdoor heap root for each unknown subtree. -/
def capWalk (checking : Bool) (marks leafCount roots proofEnd : Nat) : List Asm :=
  [addi 20 0 1, addi 31 0 1, .label "cap-visit",
   shift 7 20 3, regop 23 marks 7, ld 6 23 0,
   .branch 0 6 0 "cap-unknown", .branch 7 20 leafCount "cap-advance",
   shift 20 20 1, .jump 0 "cap-visit", addi 0 0 0, .label "cap-unknown"] ++
  (if checking then
    [addi 6 25 32, .branch 6 proofEnd 6 "reject",
     shift 7 20 5, regop 23 roots 7] ++ copyDigest 25 23
   else [shift 7 20 5, regop 23 roots 7] ++ copyDigest 23 25) ++
  [addi 25 25 32, .label "cap-advance", .branch 0 20 31 "cap-done",
   capAndOne 7 20, .branch 0 7 0 "cap-right", shift 20 20 1 true] ++
  (if checking then
    [shift 10 20 6, regop 10 roots 10, shift 12 20 5, regop 12 roots 12, insn 0x73,
     .jump 0 "cap-truncate"]
   else [.jump 0 "cap-advance"]) ++
  [.label "cap-right", addi 20 20 1, .jump 0 "cap-visit", .label "cap-done"]

/-- Group stub of the opening (words 138..191). With x20 = position and x25 at the
record's digest field, it copies the three other leaf digests of the position's
group cell (cell base `x9 + 2^28 + 328 + 368 * (position / 4)`, digest `u` at
offset `32 u`) in increasing place order, sets x20 to the group's heap node
`position / 4 + x19` and returns through x1. x6, x7, x23 and x30 are scratch. -/
def capOpenGroupStub : List Asm :=
  [.label "open-group-stub", shift 7 20 2 true, addi 6 0 368, regop 23 7 6 0 1,
   insn (2^28 + 6*2^7 + 0x37), regop 23 23 6, regop 23 23 9, addi 23 23 328,
   insn (3*2^20 + 20*2^15 + 7*2^12 + 30*2^7 + 0x13)] ++
  ((List.range 4).flatMap fun (place : Nat) =>
    [addi 6 0 (place : Int), .branch 0 6 30 s!"open-group-skip-{place}"] ++
      copyDigest 23 25 (32*place) ++ [addi 25 25 32, .label s!"open-group-skip-{place}"]) ++
  [regop 20 7 19, insn 0x00008067]

/-- Words 111..137 of the opening image. The cap opener halts at word 110 and
never reaches them. -/
def capOpenUnusedWords : List Nat :=
  [0xc8b13, 0x78b93, 0x78c93, 0x80c13, 0x20c0063, 0x300e13, 0x38000ef, 0x8b8b93,
   0x4000e13, 0x2c000ef, 0xfffc0c13, 0xfe0c14e3, 0x417b0e33, 0x3e5e13, 0xe0463,
   0x14000ef, 0x40fc85b3, 0x100293, 0x513, 0x73, 0xbb303, 0x6cb023, 0x8b8b93,
   0x8c8c93, 0xfffe0e13, 0xfe0e16e3, 0x8067]

/-- Cap opening at group depth `depth - 2`. Each record holds the 16-byte nonce,
the tag `4072 + 256 * position` and an untouched zero word, the three other leaf
digests of the position's group, and the lower siblings of the group node. -/
def capOpeningCode (depth : Nat) : List Asm :=
  let groups := 2^(depth-2)
  let lower := capLowerHeight (depth-2)
  let capLeaves := 2^(capHeight (depth-2))
  [mv 9 12, mv 24 13, mv 25 15, mv 27 16] ++
  li 19 groups ++ li 6 (432*groups+256) ++ [regop 18 9 6] ++
  li 22 28672 ++ [addi 29 0 capLeaves, addi 17 0 16, addi 0 0 0] ++ [addi 31 0 1, .branch 0 27 0 "open-done",
   .label "open-position", ld 20 24 0, regop 6 20 17 0 1, regop 23 18 6] ++
  (copyDigest 23 25).take 4 ++ [shift 6 20 8, addi 6 6 2047, addi 6 6 2025, sd 6 25 16] ++
  [addi 25 25 32, .jump 1 "open-group-stub"] ++ li 28 lower ++
  [.branch 0 28 0 "open-group", .label "open-path",
   insn (1*2^20 + 20*2^15 + 4*2^12 + 7*2^7 + 0x13),
   shift 7 7 5, regop 23 9 7] ++ copyDigest 23 25 ++
  [addi 25 25 32, shift 20 20 1 true, addi 28 28 (-1), .branch 1 28 0 "open-path",
   .label "open-group", shift 7 20 3, regop 23 22 7, sd 31 23 0,
   addi 24 24 8, addi 27 27 (-1), .branch 1 27 0 "open-position"] ++
  capMarkParents 22 29 ++ capWalk false 22 29 9 0 ++
  [.label "open-done", regop 11 25 15 0 32] ++ halt true ++
  capOpenUnusedWords.map insn ++ capOpenGroupStub

/-- Checker core. The leaf routine returns the digest of the record's group of four
leaves, so a record holds its salt, the three other group digests and `lower` path
siblings, `lower` being the binary levels between the groups and the cap. -/
def capCheckCore (depth : Nat) : List Asm :=
  let lower := capLowerHeight depth - 2
  let capLeaves := 2^(capHeight depth)
  [mv 26 11, mv 24 13, mv 8 14, mv 25 15, mv 27 16, regop 22 15 17] ++
  li 6 (32*(lower+4)) ++
  [regop 7 16 6 0 1, .branch 6 17 7 "reject", .branch 0 27 0 "cap-empty"] ++
  li 21 256 ++ li 9 28672 ++ li 18 12288 ++ li 19 capLeaves ++
  [addi 31 0 1, .label "check-position", ld 20 24 0] ++
  copyDigest 25 21 ++ [addi 25 25 32, .jump 1 "leaf"] ++ li 29 lower ++
  [.branch 0 29 0 "check-group", .label "check-path", capAndOne 7 20,
   .branch 0 7 0 "check-left"] ++ copyDigest 21 21 0 32 ++ copyDigest 25 21 ++
  [.jump 0 "check-compress", .label "check-left"] ++ copyDigest 25 21 0 32 ++
  [.label "check-compress"] ++ compressScratch ++
  [.jump 1 "path-truncate", shift 20 20 1 true, addi 29 29 (-1), .branch 1 29 0 "check-path",
   .label "check-group", regop 20 20 19, shift 7 20 3, regop 30 9 7,
   shift 7 20 5, regop 23 18 7, ld 6 30 0, .branch 0 6 0 "check-store"] ++
  ((List.range 4).flatMap fun word =>
    [ld 6 21 (8*word), ld 7 23 (8*word), .branch 1 6 7 "reject"]) ++
  [.jump 0 "check-next", .label "check-store"] ++ copyDigest 21 23 ++
  [sd 31 30 0, .label "check-next", addi 24 24 8, addi 27 27 (-1),
   .branch 1 27 0 "check-position"] ++
  capMarkParents 9 19 ++ capWalk true 9 19 18 22 ++
  [.branch 1 25 22 "reject"] ++
  ((List.range 4).flatMap fun word =>
    [ld 6 18 (32+8*word), ld 7 26 (8*word), .branch 1 6 7 "reject"]) ++
  [.jump 0 "accept", .label "cap-empty", .branch 1 17 0 "reject",
   .label "accept"] ++ halt true ++ [.label "reject"] ++ halt false

/-- Leaf recompute and group node. On entry scratch words 256..272 hold the
nonce and the tag, x8 points to the 256-byte value, x20 holds the position and
x25 the record's three other leaf digests of the group. Three permutation calls:
the first on `nonce || tag || value[0..176)` built at address 0, the second on
`reply[136..200) || value[120..256)` built at 56, the third on 72 zero bytes and
the four leaf digests of the group at 56, where the leaf's own digest takes
place `x20 mod 4` and the record's digests the other places in order. The group
digest is copied to 256..280, x20 becomes the group index, x8 advances by 256,
x25 by 96, and x1 returns. Only memory below 288 is written; x5..x8, x10..x13,
x20 and x25 are clobbered. -/
def s3LeafSubroutine : List Asm :=
  [.label "leaf"] ++
  ((List.range 3).flatMap fun word => [ld 6 0 (256+8*word), sd 6 0 (8*word)]) ++
  ((List.range 22).flatMap fun word => [ld 6 8 (8*word), sd 6 0 (24+8*word)]) ++
  [addi 5 0 0, addi 10 0 0, addi 11 0 200, addi 12 0 0, addi 13 0 1, insn 0x73] ++
  ((List.range 8).flatMap fun word => [ld 6 0 (136+8*word), sd 6 0 (56+8*word)]) ++
  ((List.range 17).flatMap fun word => [ld 6 8 (120+8*word), sd 6 0 (120+8*word)]) ++
  [addi 10 0 56, insn 0x73, insn (3*2^20 + 20*2^15 + 7*2^12 + 7*2^7 + 0x13), shift 7 7 5] ++
  copyDigest 0 7 0 128 ++
  ((List.range 4).flatMap fun (place : Nat) =>
    [addi 6 0 ((32*place : Nat) : Int), insn (2^25 + 7*2^20 + 6*2^15 + 4*2^8 + 0x63)] ++
    copyDigest 25 0 0 (128+32*place) ++ [addi 25 25 32]) ++
  ((List.range 9).map fun word => sd 0 0 (56+8*word)) ++
  [insn 0x73] ++ copyDigest 0 0 0 256 ++
  [shift 20 20 2 true, addi 8 8 256, insn 0x00008067]

/-- Never executed: every filler word jumps to the rejecting halt. -/
def s3CheckFiller (count : Nat) : List Asm := List.replicate count (.jump 0 "reject")

/-- `SH x0, offset(base)`: clears two bytes. -/
def capClearHalf (base offset : Nat) : Asm :=
  insn ((offset / 32) * 2^25 + base * 2^15 + 1 * 2^12 + (offset % 32) * 2^7 + 0x23)

/-- Every internal node keeps 240 bits. After a lower-path compression the reply's
bytes 30 and 31 in the scratch buffer are cleared before the proof cursor
advances (x1 returns into the path loop); after a cap compression the parent
root's bytes 30 and 31 are cleared before the walk advances. -/
def capCheckTruncation : List Asm :=
  [.label "path-truncate", capClearHalf 21 30, addi 25 25 32, insn 0x00008067,
   .label "cap-truncate", capClearHalf 12 30, .jump 0 "cap-advance"]

/-- Words 0..180 are the retained checker, 181..256 filler, 257..439 the leaf
routine, 440..444 the truncation code; the delivered image appends its
expansion wrapper after them. -/
def capCheckCode (depth : Nat) : List Asm :=
  capCheckCore depth ++ s3CheckFiller 76 ++ s3LeafSubroutine ++ capCheckTruncation

/-- Cap images; the complete certificate is assembled separately. -/
def capExperimental (depth : Nat) : Submission :=
  { candidate depth with image := fun program =>
      match program with
      | .commit => (candidate depth).image .commit
      | .opening => ⟨assemble (capOpeningCode depth), []⟩
      | .check => ⟨assemble (capCheckCode depth), []⟩ }
end CommitGolfCandidate
