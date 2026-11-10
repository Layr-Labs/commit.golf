import CommitGolf.Programs
import CommitGolfCandidate.Group341Words

/-! A salted binary Merkle baseline, implemented as RV64IM images.

Each leaf uses eight compression calls, starting from a private 256-bit salt and
absorbing eight 256-bit blocks. Internal nodes compress two child digests. The private
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

/-- x21 points to a 64-byte scratch input; compression overwrites its first half. -/
def compressScratch : List Asm :=
  [addi 5 0 0, mv 10 21, addi 11 0 64, mv 12 21, addi 13 0 0, insn 0x73]

/-- The caller initializes the first scratch half to the salt. Consumes 256 bytes
from x8, preserves x8's final pointer, and returns through x1. -/
def leafSubroutine : List Asm :=
  [.label "leaf", addi 28 0 8, .label "leaf-block"] ++
  copyDigest 8 21 0 32 ++ compressScratch ++
  [addi 8 8 32, addi 28 28 (-1), .branch 1 28 0 "leaf-block", insn 0x00008067]

/-- Commitment streams seven replies through consumed message blocks. The final
reply goes directly to the heap; the tail advances both output pointers and
branches directly to the contiguous salt copy at the leaf entry.
The carried x10 input advances after each captured query. Fixed selectors remain
live. The final fall-through jump enters parent setup. -/
def commitLeafSubroutine : List Asm :=
  [.label "leaf"] ++ (copyDigest 18 10).take 6 ++ [sd 0 10 24] ++
  ((List.range 8).flatMap fun block =>
    [if block=7 then addi 12 23 0 else addi 12 10 32,insn 0x73,addi 10 10 32]) ++
  [addi 18 18 24,addi 23 23 32,.branch 6 23 22 "leaf",.jump 0 "commit-parent-start"]

/-- Heap slots 1..2*n-1 contain tree nodes; slot 0 is unused. -/
def trapdoorBytes (depth : Nat) : Nat := 96 * 2^depth
def openingBytes (depth : Nat) : Nat := 32 * (depth + 1)

/-- A direct upper-immediate load and jump keep seven slots while executing two. -/
def commitLi (rd value : Nat) : List Asm :=
  if value % 4096 = 0 ∧ value < 2^31 then
    [insn (value + rd * 2^7 + 0x37), insn 0x0180006f] ++
      List.replicate 5 (addi 0 0 0)
  else li rd value

def quadCommitCode (depth : Nat) : List Asm :=
  let n := 2^depth
  [mv 8 10, mv 26 11, mv 9 12] ++ commitLi 19 n ++ commitLi 6 (64*n) ++
  [regop 18 9 6] ++ commitLi 6 (32*n) ++ [regop 23 9 6] ++
  -- Sample all salts once; each is an independent uniform 192-bit nonce.
  [addi 5 0 2, mv 10 18] ++ commitLi 11 (24*n) ++ [insn 0x73] ++
  -- Keep three physical setup slots so the main-loop addresses remain stable.
  [addi 21 8 (-32), mv 22 18, addi 0 0 0, addi 20 0 0] ++ compressScratch.take 5 ++
  [addi 28 0 0, .label "commit-leaf"] ++
  [.jump 0 "commit-initial-call"] ++ (copyDigest 18 10).drop 1 ++
  [.label "commit-initial-call", .jump 1 "leaf", .label "commit-parent-pair", insn 0x73,
    addi 10 10 (-64), addi 12 12 (-32), insn 0x73,
    addi 10 10 (-64), addi 12 12 (-32), .branch 1 12 9 "commit-parent-quad",
    .jump 0 "commit-root"] ++
  [addi 18 18 24, addi 23 23 32, .branch 6 23 22 "commit-leaf", addi 0 0 0,
   -- Fixed syscall selectors survive the leaf loop. Initialize descending
   -- parent addresses once, then advance them by subtraction after each query.
    .label "commit-parent-start", addi 20 19 (-1), shift 6 20 6, regop 10 9 6, shift 7 20 5,
   .branch 0 20 0 "commit-root", regop 12 9 7, .label "commit-parent", insn 0x73,
   addi 10 10 (-64), addi 12 12 (-32), .branch 1 12 9 "commit-parent-pair",
   .jump 0 "commit-root", addi 0 0 0, .label "commit-root"] ++
  copyDigest 9 26 32 ++ halt true ++ commitLeafSubroutine ++ [addi 0 0 0] ++
  -- Peel three parents before entering this body. Four queries share one
  -- end-pointer branch; the retained pair handles the N=4 fall-through.
  [.label "commit-parent-quad"] ++
  ((List.range 4).flatMap fun _ =>
    [insn 0x73, addi 10 10 (-64), addi 12 12 (-32)]) ++
  [.branch 1 12 9 "commit-parent-quad", .jump 0 "commit-root"]


/-- Execute the first four-parent body once, then enter the eight-parent loop.
The branch remains conditional so N=8 uses the retained fall-through root jump. -/
def patchOctEntry : List Asm → Bool → List Asm
  | [], _ => []
  | .label name :: rest, _ => .label name :: patchOctEntry rest (name == "commit-parent-quad")
  | .branch condition left right _ :: rest, true =>
      .branch condition left right "commit-parent-oct" :: patchOctEntry rest false
  | instruction :: rest, active => instruction :: patchOctEntry rest active

def octParentCode : List Asm :=
  [.label "commit-parent-oct"] ++
  ((List.range 8).flatMap fun _ => [insn 0x73,addi 10 10 (-64),addi 12 12 (-32)]) ++
  [.branch 1 12 9 "commit-parent-oct",.jump 0 "commit-root"]

/-- Seven peeled parents leave N-8, a multiple of eight at the challenge depth. -/
def octCommitCode (depth : Nat) : List Asm :=
  patchOctEntry (quadCommitCode depth) false ++ octParentCode

/-- Execute the eight-parent prefix once, then enter the long-jump parent group. -/
def patchGroup341Entry : List Asm → Bool → List Asm
  | [], _ => []
  | .label name :: rest, _ => .label name :: patchGroup341Entry rest (name == "commit-parent-oct")
  | .branch condition left right _ :: rest, true =>
      .branch condition left right "commit-parent-group341" :: patchGroup341Entry rest false
  | instruction :: rest, active => instruction :: patchGroup341Entry rest active

def group341ParentCode : List Asm :=
  [.label "commit-parent-group341"] ++
  ((List.range 83886).flatMap fun _ => [insn 0x73,addi 10 10 (-64),addi 12 12 (-32)]) ++
  [.branch 1 12 9 "commit-parent-group-continue",.jump 0 "commit-root",
    .label "commit-parent-group-continue",.jump 0 "commit-parent-group341"]

/-- Compact ABI setup for the fixed challenge depth. -/
def compactSetupCode : List Asm :=
  [mv 8 10,mv 26 11,mv 9 12,insn (16777216+19*2^7+0x37),
   insn (1073741824+6*2^7+0x37),regop 18 9 6,
   insn (536870912+6*2^7+0x37),regop 23 9 6,addi 5 0 2,mv 10 18,
   insn (402653184+11*2^7+0x37),insn 0x0600006f] ++
   List.replicate 23 (addi 0 0 0)

def commitCode (depth : Nat) : List Asm :=
  if depth=24 then compactSetupCode ++
    (patchGroup341Entry (octCommitCode depth) false ++ group341ParentCode).drop 35
  else octCommitCode depth

def rawOpeningCode (depth : Nat) : List Asm :=
  let n := 2^depth
  [mv 9 12, mv 24 13, mv 25 15, mv 27 16] ++ li 19 n ++ li 6 (64*n) ++
  [regop 18 9 6, .branch 0 27 0 "open-done", .label "open-position", ld 20 24 0,
   shift 6 20 1,regop 6 6 20,shift 6 6 3,regop 23 18 6] ++ (copyDigest 23 25).take 6 ++ [sd 0 25 24] ++
  [addi 25 25 32, regop 20 20 19] ++ li 28 depth ++
  [.branch 0 28 0 "open-next", .label "open-path",
   -- XORI x7,x20,1 selects the sibling heap slot.
   insn (1 * 2^20 + 20 * 2^15 + 4 * 2^12 + 7 * 2^7 + 0x13),
   shift 7 7 5, regop 23 9 7] ++ copyDigest 23 25 ++
  [addi 25 25 32, shift 20 20 1 true, addi 28 28 (-1), .branch 1 28 0 "open-path",
   .label "open-next", addi 24 24 8, addi 27 27 (-1), .branch 1 27 0 "open-position",
   .label "open-done",
   -- The output cursor advanced by exactly the serialized proof length.
   regop 11 25 15 0 32] ++ halt true


/-- Keep all opening PCs while avoiding redundant constant-load instructions. -/
def compactOpeningSetup : List Asm :=
  [mv 9 12,mv 24 13,mv 25 15,mv 27 16,
   insn (16777216+19*2^7+0x37),insn (1073741824+6*2^7+0x37),regop 18 9 6,
   insn 0x0300006f] ++ List.replicate 11 (addi 0 0 0)

def compactOpeningCounter : List Asm :=
  [addi 25 25 32,regop 20 20 19,addi 28 0 24,insn 0x00c0006f,
   addi 0 0 0,addi 0 0 0]

def patchOpeningConstants : List Asm → Nat → List Asm
  | [], _ => []
  | .label name :: rest, index => .label name :: patchOpeningConstants rest index
  | instruction :: rest, index =>
      (if index<19 then (compactOpeningSetup[index]?).getD (addi 0 0 0)
       else if 32 ≤ index ∧ index<38 then (compactOpeningCounter[index-32]?).getD (addi 0 0 0)
       else instruction) :: patchOpeningConstants rest (index+1)

def openingCode (depth : Nat) : List Asm :=
  if depth=24 then patchOpeningConstants (rawOpeningCode depth) 0 else rawOpeningCode depth

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
   .label "accept"] ++ halt true ++ [.label "reject"] ++ halt false ++ leafSubroutine

def sizes (depth : Nat) : Sizes :=
  ⟨trapdoorBytes depth, openingBytes depth * LENGTH⟩

/-- Reserve the contract's full message and values buffers even for small test trees.
Scratch memory [256,320) is below all input/output buffers. -/
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
    | .commit => ⟨if depth=24 then group341ImageWords else assemble (commitCode depth), []⟩
    | .opening => ⟨assemble (openingCode depth), []⟩
    | .check => ⟨assemble (checkCode depth), []⟩
  steps
    | .commit => 512 * 2^depth + 1024
    | .opening => 32 * (depth + 1) * LENGTH + 1024
    | .check => 512 * (depth + 1) * LENGTH + 1024

/-- The actual candidate uses the challenge's complete 2^24-leaf vector. -/
def submission : Submission := candidate LOG_LENGTH

end CommitGolfCandidate
