import CommitGolfCandidate.CompressionInput
import CommitGolf.Programs

/-! A salted binary Merkle baseline, implemented as RV64IM images.

Each leaf uses four direct 96-byte compression calls, starting from a private 256-bit
salt and absorbing four 512-bit blocks. Internal nodes compress two child digests. The private
trapdoor stores a heap-indexed tree followed by the salts. Each opening contains the
salt and the copath, in increasing position order. This module constructs programs;
it does not assert their security or supply a challenge certificate. -/

namespace CommitGolfCandidate
open CommitGolf

inductive Asm where
  | word (value : BitVec 32)
  | label (name : String)
  | branch (condition left right : Nat) (target : String)
  | jump (link : Nat) (target : String)

def insn (value : Nat) : Asm := .word (BitVec.ofNat 32 value)
def imm (value : Int) (bits : Nat) : Nat := (value % (2 ^ bits : Nat)).toNat

def addi (rd rs : Nat) (value : Int) : Asm :=
  insn (imm value 12 * 2^20 + rs * 2^15 + rd * 2^7 + 0x13)
def shift (rd rs amount : Nat) (right : Bool := false) : Asm :=
  insn (amount * 2^20 + rs * 2^15 + (if right then 5 else 1) * 2^12 + rd * 2^7 + 0x13)
def regop (rd left right : Nat) (f3 : Nat := 0) (f7 : Nat := 0) : Asm :=
  insn (f7 * 2^25 + right * 2^20 + left * 2^15 + f3 * 2^12 + rd * 2^7 + 0x33)
def ld (rd base offset : Nat) : Asm :=
  insn (offset * 2^20 + base * 2^15 + 3 * 2^12 + rd * 2^7 + 3)
def sd (rs base offset : Nat) : Asm :=
  insn ((offset / 32) * 2^25 + rs * 2^20 + base * 2^15 + 3 * 2^12 +
    (offset % 32) * 2^7 + 0x23)
def mv (rd rs : Nat) : Asm := addi rd rs 0

def li (rd value : Nat) : List Asm :=
  [addi rd 0 0] ++ ((Nat.digits 2048 value).reverse.flatMap fun digit =>
    [shift rd rd 11, addi rd rd digit])

/-- Copy one digest, using x6 as scratch. Source/destination may coincide. -/
def copyDigest (source destination : Nat) (sourceOffset : Nat := 0)
    (destinationOffset : Nat := 0) : List Asm :=
  (List.range 4).flatMap fun j =>
    [ld 6 source (sourceOffset + 8*j), sd 6 destination (destinationOffset + 8*j)]

def halt (success : Bool) : List Asm :=
  [addi 5 0 1, addi 10 0 (if success then 0 else 1), insn 0x73]

def labelPositions (code : List Asm) : List (String × Nat) :=
  (code.foldl (fun (state : Nat × List (String × Nat)) instruction =>
    match instruction with
    | .label name => (state.1, (name, state.1) :: state.2)
    | _ => (state.1 + 1, state.2)) (0, [])).2

def branchWord (condition left right : Nat) (offset : Int) : BitVec 32 :=
  let n := imm offset 13
  BitVec.ofNat 32 ((n / 4096 % 2) * 2^31 + (n / 32 % 64) * 2^25 +
    right * 2^20 + left * 2^15 + condition * 2^12 + (n / 2 % 16) * 2^8 +
    (n / 2048 % 2) * 2^7 + 0x63)

def jumpWord (link : Nat) (offset : Int) : BitVec 32 :=
  let n := imm offset 21
  BitVec.ofNat 32 ((n / 2^20 % 2) * 2^31 + (n / 2 % 1024) * 2^21 +
    (n / 2048 % 2) * 2^20 + (n / 4096 % 256) * 2^12 + link * 2^7 + 0x6f)

def assemble (code : List Asm) : List (BitVec 32) :=
  let labels := labelPositions code
  let words := code.filter fun instruction => match instruction with
    | .label _ => false | _ => true
  words.zipIdx |>.map fun (instruction, pc) =>
    let target := fun name => labels.find? (fun pair => pair.1 == name)
    match instruction with
    | .word value => value
    | .branch condition left right name =>
      match target name with
      | some (_, address) => branchWord condition left right (4 * ((address : Int) - pc))
      | none => 0x00100073
    | .jump link name =>
      match target name with
      | some (_, address) => jumpWord link (4 * ((address : Int) - pc))
      | none => 0x00100073
    | .label _ => 0x00100073

/-- x21 points to two digest words. The adapter appends a zero third word
for the actual 96-byte compression call and restores the temporary padding. -/
def compressScratch : List Asm :=
  [addi 5 0 0, mv 10 21, addi 11 0 64, mv 12 21, addi 13 0 0,
   .jump 31 "compress96"]

/-- One query to the 96-byte oracle. The third digest-sized word is saved,
zeroed for the call, then restored. x14..x17 hold the saved words and x31
holds the return address. The caller's digest output is disjoint from this
temporary padding. This keeps the binary Merkle encoding unchanged. -/
def compression96Routine : List Asm :=
  [.label "compress96",
   ld 14 10 64, ld 15 10 72, ld 16 10 80, ld 17 10 88,
   sd 0 10 64, sd 0 10 72, sd 0 10 80, sd 0 10 88,
   addi 11 0 96, insn 0x73,
   sd 14 10 64, sd 15 10 72, sd 16 10 80, sd 17 10 88,
   addi 11 0 64, insn 0x000f8067]

/-- The caller initializes the first scratch word to the salt. Each of four blocks copies
64 message bytes from x8 behind the chaining value and makes one direct 96-byte
compression call C(state | b_2j | b_2j+1). Consumes 256 bytes from x8, returns through x1. -/
def leafSubroutine : List Asm :=
  [.label "leaf", addi 28 0 4, .label "leaf-block"] ++
  ((List.range 8).flatMap fun j => [ld 6 8 (8*j), sd 6 21 (32 + 8*j)]) ++
  [addi 5 0 0, mv 10 21, addi 11 0 96, mv 12 21, addi 13 0 0, insn 0x73,
   addi 8 8 64, addi 28 28 (-1), .branch 1 28 0 "leaf-block", insn 0x00008067]

/-- Heap slots 1..2*n-1 contain tree nodes; slot 0 is unused. -/
def trapdoorBytes (depth : Nat) : Nat := 96 * 2^depth
def openingBytes (depth : Nat) : Nat := 32 * (depth + 1)

/-- In-place leaf chain. x8 points at the 32-byte salt slot just below leaf i's message
(free memory for i = 0, otherwise the already-consumed last block of leaf i-1). Each call
compresses the contiguous 96 bytes [chaining value | next 64-byte block] and writes the new
chaining value over the last 32 bytes it consumed; the fourth call writes the heap slot. -/
def commitCode (depth : Nat) : List Asm :=
  let n := 2^depth
  [addi 8 10 (-32), mv 26 11, mv 9 12] ++ li 19 n ++ li 6 (64*n) ++
  [regop 18 9 6] ++ li 6 (32*n) ++ [regop 23 9 6] ++
  -- Sample all salts once; each is an independent uniform 256-bit block.
  [addi 5 0 2, mv 10 18] ++ li 11 (32*n) ++ [insn 0x73] ++
  li 21 256 ++ [addi 20 0 0, addi 5 0 0, addi 11 0 96, addi 13 0 0, .label "commit-leaf"] ++
  copyDigest 18 8 ++
  [mv 10 8, addi 12 8 64, insn 0x73,
   addi 10 8 64, addi 12 8 128, insn 0x73,
   addi 10 8 128, addi 12 8 192, insn 0x73,
   addi 10 8 192, mv 12 23, insn 0x73,
   addi 8 8 256, addi 18 18 32, addi 23 23 32, addi 20 20 1, .branch 6 20 19 "commit-leaf",
   addi 20 19 (-1), .branch 0 20 0 "commit-root", .label "commit-parent",
   shift 6 20 6, regop 10 9 6, shift 7 20 5, regop 12 9 7,
   addi 5 0 0, addi 11 0 64, addi 13 0 0, .jump 31 "compress96",
   addi 20 20 (-1), .branch 1 20 0 "commit-parent", .label "commit-root"] ++
  copyDigest 9 26 32 ++ halt true ++ compression96Routine

def openingCode (depth : Nat) : List Asm :=
  let n := 2^depth
  [mv 9 12, mv 24 13, mv 25 15, mv 27 16] ++ li 19 n ++ li 6 (64*n) ++
  [regop 18 9 6, .branch 0 27 0 "open-done", .label "open-position", ld 20 24 0,
   shift 6 20 5, regop 23 18 6] ++ copyDigest 23 25 ++
  [addi 25 25 32, regop 20 20 19] ++ li 28 depth ++
  [.branch 0 28 0 "open-next", .label "open-path",
   -- XORI x7,x20,1 selects the sibling heap slot.
   insn (1 * 2^20 + 20 * 2^15 + 4 * 2^12 + 7 * 2^7 + 0x13),
   shift 7 7 5, regop 23 9 7] ++ copyDigest 23 25 ++
  [addi 25 25 32, shift 20 20 1 true, addi 28 28 (-1), .branch 1 28 0 "open-path",
   .label "open-next", addi 24 24 8, addi 27 27 (-1), .branch 1 27 0 "open-position",
   .label "open-done"] ++ li 6 (openingBytes depth) ++
  [regop 11 16 6 0 1] ++ halt true

/-- Reject malformed lengths and every mismatching root. Values/indices are supplied
by the trusted ABI; their validity and sorting do not depend on proof bytes. -/
def checkCode (depth : Nat) : List Asm :=
  [mv 26 11, mv 24 13, mv 8 14, mv 25 15, mv 27 16] ++
  li 6 (openingBytes depth) ++ [regop 7 16 6 0 1, .branch 1 7 17 "reject"] ++
  li 21 256 ++ [.branch 0 27 0 "accept", .label "check-position", ld 20 24 0] ++
  copyDigest 25 21 ++ [addi 25 25 32, .jump 1 "leaf"] ++ li 29 depth ++
  [.branch 0 29 0 "check-root", .label "check-path",
   -- ANDI x7,x20,1 selects left/right ordering.
   insn (1 * 2^20 + 20 * 2^15 + 7 * 2^12 + 7 * 2^7 + 0x13),
   .branch 0 7 0 "check-left"] ++ copyDigest 21 21 0 32 ++ copyDigest 25 21 ++
  [.jump 0 "check-compress", .label "check-left"] ++ copyDigest 25 21 0 32 ++
  [.label "check-compress"] ++ compressScratch ++
  [addi 25 25 32, shift 20 20 1 true, addi 29 29 (-1), .branch 1 29 0 "check-path",
   .label "check-root"] ++
  ((List.range 4).flatMap fun j =>
    [ld 6 21 (8*j), ld 7 26 (8*j), .branch 1 6 7 "reject"]) ++
  [addi 24 24 8, addi 27 27 (-1), .branch 1 27 0 "check-position",
   .label "accept"] ++ halt true ++ [.label "reject"] ++ halt false ++
  leafSubroutine ++ compression96Routine

def sizes (depth : Nat) : Sizes :=
  ⟨trapdoorBytes depth, openingBytes depth * LENGTH⟩

/-- Reserve the contract's full message and values buffers even for small test trees.
Scratch memory [256,352) is below all input/output buffers. -/
def layout (depth : Nat) : Layout :=
  let message := 4096
  let commitment := message + LENGTH * (LEAF_SIZE / 8)
  let trapdoor := commitment + DIGEST_BYTES
  let indices := trapdoor + trapdoorBytes depth
  let values := indices + LENGTH * 8
  let proof := values + LENGTH * (LEAF_SIZE / 8)
  ⟨message, commitment, trapdoor, indices, values, proof⟩

def candidate (depth : Nat) : Submission where
  sizes := sizes depth
  layout := layout depth
  image
    | .commit => ⟨assemble (commitCode depth), []⟩
    | .opening => ⟨assemble (openingCode depth), []⟩
    | .check => ⟨assemble (checkCode depth), []⟩
  steps
    | .commit => 512 * 2^depth + 1024
    | .opening => 32 * (depth + 1) * LENGTH + 1024
    | .check => 512 * (depth + 1) * LENGTH + 1024

/-- The actual candidate uses the challenge's complete 2^24-leaf vector. -/
def submission : Submission := candidate LOG_LENGTH

end CommitGolfCandidate
