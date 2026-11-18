import CommitGolf.Programs

/-! Quad commit machine image, independent of the opening and checker images.
The leaf body is 8d2a211's pinned two-permutation leaf. Only its destination
immediate and rebase sites differ. Regenerate with `python3 submission/quad_lean_gen.py`.
The raw image is `submission/quad-commit.hex`. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

/-- Offset encoded in the signed 12-bit destination immediate. -/
def slotImmediate (u : Nat) : BitVec 12 :=
  BitVec.ofInt 12 (-1768 + 368 * Int.ofNat ((u % 44) / 4) + 32 * Int.ofNat (u % 4))

def leafWords (u : Nat) : List (BitVec 32) :=
  [0xfe050613, 0x00000073, 0x03850513, 0x00a53023,
   BitVec.ofNat 32 (0x000b3f83 + 1048576 * (16 * (u % 128))), 0x01f53423,
   BitVec.ofNat 32 (0x008b3f83 + 1048576 * (16 * (u % 128))), 0x01f53823,
   BitVec.ofNat 32 (0x000a0613 + 1048576 * (slotImmediate u).toNat),
   0x00000073, 0x0c850513] ++
  (if u % 44 = 43 ∨ u = 4095 then [0x7f860a13] else []) ++
  (if u % 128 = 127 then [0x007b0b33] else [])

def setupWords : List (BitVec 32) :=
  [0x00058413, 0x00060493, 0x00050913, 0x10001a37, 0x6e8a0a13, 0x01448a33, 0x6c001b37, 0x000b0b13, 0x01648b33, 0x00200293, 0xf50b0513, 0x01800593, 0x00058593, 0x00000073, 0x00000293, 0x0c800593, 0x00100693, 0x05d9906f, 0x00b69393]

def leafLatchWords : List (BitVec 32) :=
  [0x00850463, 0xe05d306f]

def quadSetupWords : List (BitVec 32) :=
  [0x10001537, 0xfb850513, 0x00a48533, 0x08000637, 0x00060613, 0x00c48633, 0x10000ab7, 0x000a8a93, 0x01548ab3]

def quadLatchWords : List (BitVec 32) :=
  [0x01560463, 0xffdcf06f]

def parentSetupWords : List (BitVec 32) :=
  [0x04000593, 0x00000693, 0x10000537, 0xfc050513, 0x00a48533, 0x08000637, 0xfe060613, 0x00c48633, 0x00048a93]

def parentLatchWords : List (BitVec 32) :=
  [0x01560463, 0xa2dc206f]

/-- NonceChain generator (31727a8 words 233170..233368, retargeted) + x12 restore; entered from word 17, returns to word 18. -/
def genWords : List (BitVec 32) :=
  [0x000b0613, 0x100023b7, 0x00038393, 0x016383b3, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073,
   0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613,
   0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0x00000073, 0x0b050513,
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0xd07660e3, 0x00090513, 0x00048613, 0xc8c6606f]

def rootWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073] ++ genWords

def quadWords : List (BitVec 32) := [0x00000073, 0x17050513, 0x02060613]
def parentWords : List (BitVec 32) := [0x00000073, 0x00061f23, 0xfc050513, 0xfe060613]
def leafCode : List (BitVec 32) := (List.range 4096).flatMap leafWords
def quadCode : List (BitVec 32) := (List.replicate 16384 quadWords).flatten
def parentCode : List (BitVec 32) := (List.replicate 15709 parentWords).flatten

def image : Image := ⟨setupWords ++ leafCode ++ leafLatchWords ++ quadSetupWords ++
  quadCode ++ quadLatchWords ++ parentSetupWords ++ parentCode ++ parentLatchWords ++ rootWords, []⟩

/-- Only the commit image and the common layout are fixed here. -/
def submission (opening checker : Image) : Submission where
  sizes := ⟨2080378880, 8959041024⟩
  layout := ⟨4096,4294971392,4294971424,6375350304,6509568096,10804535392⟩
  image := fun | .commit => image | .opening => opening | .check => checker
  steps := fun | .commit => 1073807360 | .opening => 17179934720 | .check => 34359803904

/-- Number of ordinary machine steps of the intended successful trace (seed draw, generator, tree). -/
def executionSteps : Nat := 219034462
/-- Sum of the phase ledger; reachability is proved in `QuadNonceCommitTranscript`. -/
def executionCycles : Nat := 523312474
def executionCalls : Nat := 43468287

theorem submission_commit_image (opening checker : Image) :
    (submission opening checker).image .commit = image := rfl

theorem enough_commit_fuel (opening checker : Image) :
    executionSteps ≤ (submission opening checker).steps .commit := by
  change executionSteps ≤ 1073807360
  decide

theorem call_ledger : executionCalls = 1525248 + (2 * 2^24 + 2^22 + (2^22 - 1)) := by decide

theorem cycle_ledger : executionCycles =
    (13 + 4 + 8 + (10 * 1525248 + 1525248 / 64) + 4) + (9 + 9 + 11) +
    ((11 * 4096 + 94 + 32 + 14 * 4096) * 4096 + (2 * 4096 - 1)) +
    (10 * 2^22 + (2 * 256 - 1)) +
    (11 * (2^22 - 1) + (2 * 267 - 1)) := by decide

theorem step_ledger : executionCycles = executionSteps + 7 * executionCalls + 3 := by decide

theorem parent_partition : 15709 * 267 = 2^22 - 1 := by decide

theorem quad_partition : 16384 * 256 = 2^22 := by decide

end TwoPermutationPrototype.Quad.Commit
