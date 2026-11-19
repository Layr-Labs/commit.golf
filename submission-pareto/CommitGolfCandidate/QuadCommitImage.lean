import CommitGolf.Programs

/-! Quad2 commit machine image, independent of the opening and checker images.
The leaf body is 8d2a211's pinned two-permutation leaf. Only its destination
immediate and rebase sites differ. Passes: setup, NonceChain generator (after the root),
leaves into leaf groups, level-1 quad nodes into level-1 groups, level-2 nodes into level-2
groups, level-3 nodes into heap nodes 2^18 .. 2^19-1, binary parents 2^18-1 .. 1, root. -/
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
  [0x00058413, 0x00060493, 0x00050913, 0x10001a37, 0x6e8a0a13, 0x01448a33, 0x6c001b37, 0x000b0b13, 0x01648b33, 0x00200293, 0xf50b0513, 0x01800593, 0x00058593, 0x00000073, 0x00000293, 0x0c800593, 0x00100693, 0x134f206f, 0x00b69393]

def leafLatchWords : List (BitVec 32) :=
  [0x00850463, 0xe05d306f]

/-- x10 := leaf group 0, x12 := quad-group slot 0 (`QUAD2_GROUP_BASE+72`), x21 := x12 + 368·2^20. -/
def quadSetupWords : List (BitVec 32) :=
  [0x10001537, 0xfb850513, 0x00a48533, 0x7c004637, 0x00060613, 0x00c48633, 0x17000ab7, 0x000a8a93, 0x01560ab3]

/-- x10 := level-1 group 0 (`QUAD2_GROUP_BASE`), x12 := level-2 slot 0 (`QUAD3_GROUP_BASE+72`),
x21 := x12 + 368·2^18. -/
def quad2SetupWords : List (BitVec 32) :=
  [0x7c004537, 0xfb850513, 0x00a48533, 0x02001637, 0x00060613, 0x00c48633, 0x05c00ab7, 0x000a8a93, 0x01560ab3]

/-- x10 := level-2 group 0 (`QUAD3_GROUP_BASE`), x12 := heap node 2^18, x21 := heap node 2^19. -/
def quad3SetupWords : List (BitVec 32) :=
  [0x02001537, 0xfb850513, 0x00a48533, 0x00800637, 0x00060613, 0x00c48633, 0x01000ab7, 0x000a8a93, 0x01548ab3]

def quadLatchWords : List (BitVec 32) :=
  [0x01560463, 0xffdcf06f]

def parentSetupWords : List (BitVec 32) :=
  [0x04000593, 0x00000693, 0x01000537, 0xfc050513, 0x00a48533, 0x00800637, 0xfe060613, 0x00c48633, 0x00048a93]

def parentLatchWords : List (BitVec 32) :=
  [0x01560463, 0x9acca06f]

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
   0x0b060613, 0x00000073, 0x0b050513, 0x0b060613, 0xd07660e3, 0x00090513, 0x00048613, 0xbb50d06f]

def rootWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073] ++ genWords

def quadWords : List (BitVec 32) := [0x00000073, 0x17050513, 0x02060613]
/-- Four level-1 (or level-2) nodes: the destination advances 32, 32, 32, then 272 bytes to the next group. -/
def quadGroupWords : List (BitVec 32) :=
  quadWords ++ quadWords ++ quadWords ++ [0x00000073, 0x17050513, 0x11060613]
def parentWords : List (BitVec 32) := [0x00000073, 0x00061f23, 0xfc050513, 0xfe060613]
def leafCode : List (BitVec 32) := (List.range 4096).flatMap leafWords
def quadCode : List (BitVec 32) := (List.replicate 4096 quadGroupWords).flatten
def quad2Code : List (BitVec 32) := (List.replicate 4096 quadGroupWords).flatten
def quad3Code : List (BitVec 32) := (List.replicate 16384 quadWords).flatten
def parentCode : List (BitVec 32) := (List.replicate 13797 parentWords).flatten

def image : Image := ⟨setupWords ++ leafCode ++ leafLatchWords ++ quadSetupWords ++
  quadCode ++ quadLatchWords ++ quad2SetupWords ++ quad2Code ++ quadLatchWords ++
  quad3SetupWords ++ quad3Code ++ quadLatchWords ++
  parentSetupWords ++ parentCode ++ parentLatchWords ++ rootWords, []⟩

/-- Only the commit image and the common layout are fixed here. -/
def submission (opening checker : Image) : Submission where
  sizes := ⟨2466267136, 10167000576⟩
  layout := ⟨4096,4294971392,4294971424,6761238560,6895456352,11190423648⟩
  image := fun | .commit => image | .opening => opening | .check => checker
  steps := fun | .commit => 1073807360 | .opening => 17179934720 | .check => 34359803904

/-- Number of ordinary machine steps of the intended successful trace (seed draw, generator, tree). -/
def executionSteps : Nat := 207237662
/-- Sum of the phase ledger; reachability is proved in `QuadNonceCommitTranscript`. -/
def executionCycles : Nat := 493165594
def executionCalls : Nat := 40846847

theorem submission_commit_image (opening checker : Image) :
    (submission opening checker).image .commit = image := rfl

theorem enough_commit_fuel (opening checker : Image) :
    executionSteps ≤ (submission opening checker).steps .commit := by
  change executionSteps ≤ 1073807360
  decide

theorem call_ledger : executionCalls = 1525248 + (2 * 2^24 + 2^22 + 2^20 + 2^18 + (2^18 - 1)) := by decide

theorem cycle_ledger : executionCycles =
    (13 + 4 + 8 + (10 * 1525248 + 1525248 / 64) + 4) + (9 + 9 + 9 + 9 + 11) +
    ((11 * 4096 + 94 + 32 + 14 * 4096) * 4096 + (2 * 4096 - 1)) +
    (10 * 2^22 + (2 * 256 - 1)) + (10 * 2^20 + (2 * 64 - 1)) + (10 * 2^18 + (2 * 16 - 1)) +
    (11 * (2^18 - 1) + (2 * 19 - 1)) := by decide

theorem step_ledger : executionCycles = executionSteps + 7 * executionCalls + 3 := by decide

theorem parent_partition : 13797 * 19 = 2^18 - 1 := by decide

theorem quad_partition : 4 * 4096 * 256 = 2^22 := by decide

theorem quad2_partition : 4 * 4096 * 64 = 2^20 := by decide

theorem quad3_partition : 16384 * 16 = 2^18 := by decide

end TwoPermutationPrototype.Quad.Commit
