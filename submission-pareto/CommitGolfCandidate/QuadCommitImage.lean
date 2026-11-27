import CommitGolf.Programs
import CommitGolf.Artifact

/-! Penta commit machine image, independent of the opening and checker images.
Words 0 .. 45,200 are taken directly from `Artifact.commitCode` (our 4,095-leaf counter-mode
in-place salt prefix with prefetch, proved in `PentaGrouped*`); the words after 45,201 are the
hybrid tree: 5-ary levels 1-2 (written into 5-ary groups), then levels 3-20 written into binary
groups (slots 3 and 4), the root node and the unchanged root copy (212905 words). -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

/-- Offset encoded in the signed 12-bit destination immediate (45-leaf centered window). -/
def slotImmediate (u : Nat) : BitVec 12 :=
  BitVec.ofInt 12 (-1536 + 368 * Int.ofNat ((u % 45) / 5) + 32 * Int.ofNat (u % 5))

def setupWords : List (BitVec 32) :=
  List.ofFn fun i : Fin 19 => Artifact.commitCode.get 32 ⟨i.val, by omega⟩

def leafLatchWords : List (BitVec 32) :=
  List.ofFn fun i : Fin 18 => Artifact.commitCode.get 32 ⟨45183 + i.val, by omega⟩

/-- Clear slots 1 .. 4 of the last level-0 group (relative to the last leaf's slot in x12). -/
def leafZeroWords : List (BitVec 32) :=
  [0x02063023, 0x02063423, 0x02063823, 0x02063c23, 0x04063023, 0x04063423, 0x04063823, 0x04063c23,
   0x06063023, 0x06063423, 0x06063823, 0x06063c23, 0x08063023, 0x08063423, 0x08063823, 0x08063c23]

/-- Radix of the groups that hold level-`m` nodes (`radix m` of the tree spec). -/
def levelRadix (m : Nat) : Nat := if m < 3 ∨ 13 ≤ m then 5 else 2

/-- One node: permutation call, next input group, next output slot (+32 inside a group; after the
last slot +240 for a 5-ary group, +336 for a binary one). -/
def nodeWordsR (rho t : Nat) : List (BitVec 32) :=
  [0x00000073, 0x17050513, if t + 1 = rho then (if rho = 5 then 0x0f060613 else 0x15060613) else 0x02060613]

def nodeCodeR (rho n : Nat) : List (BitVec 32) := (List.range n).flatMap (fun p => nodeWordsR rho (p % rho))

/-- Loop body nodes, loop iterations, tail nodes and cleared words of level `m`. -/
def levelS : Nat → Nat
  | 1 => 29430
  | 2 => 14585
  | 3 => 1000
  | 4 => 1000
  | 5 => 1000
  | 6 => 1000
  | 7 => 1000
  | 8 => 1000
  | 9 => 1000
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | _ => 0

def levelQ : Nat → Nat
  | 1 => 114
  | 2 => 46
  | 3 => 134
  | 4 => 67
  | 5 => 33
  | 6 => 16
  | 7 => 8
  | 8 => 4
  | 9 => 2
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | _ => 0


def levelR : Nat → Nat
  | 1 => 424
  | 2 => 179
  | 3 => 218
  | 4 => 109
  | 5 => 555
  | 6 => 778
  | 7 => 389
  | 8 => 195
  | 9 => 98
  | 10 => 1049
  | 11 => 525
  | 12 => 263
  | 13 => 132
  | 14 => 27
  | 15 => 6
  | 16 => 2
  | _ => 0


def levelZ : Nat → Nat
  | 1 => 4
  | 2 => 4
  | 3 => 0
  | 4 => 4
  | 5 => 4
  | 6 => 0
  | 7 => 4
  | 8 => 4
  | 9 => 0
  | 10 => 4
  | 11 => 4
  | 12 => 4
  | 13 => 12
  | 14 => 12
  | 15 => 16
  | 16 => 12
  | _ => 0

/-- x10 := level m-1 group 0, x12 := level m slot 0, x21 := slot after the loop part. -/
def levelSetupWords : Nat → List (BitVec 32)
  | 1 => [0x00001537, 0xfd850513, 0x00a48533, 0x4999c637, 0x00060613, 0x00c48633, 0x5851aab7, 0x840a8a93,
   0x01548ab3]
  | 2 => [0x4999c537, 0xfd850513, 0x00a48533, 0x58523637, 0x00060613, 0x00c48633, 0x5b43aab7, 0x6a0a8a93,
   0x01548ab3]
  | 3 => [0x58523537, 0xfd850513, 0x00a48533, 0x5b43f637, 0x06060613, 0x00c48633, 0x5cbc3ab7, 0x8e0a8a93,
   0x01548ab3]
  | 4 => [0x5b43f537, 0xfd850513, 0x00a48533, 0x5cbcd637, 0x06060613, 0x00c48633, 0x5d78fab7, 0xca0a8a93,
   0x01548ab3]
  | 5 => [0x5cbcd537, 0xfd850513, 0x00a48533, 0x5d794637, 0x06060613, 0x00c48633, 0x5dd5eab7, 0x720a8a93,
   0x01548ab3]
  | 6 => [0x5d794537, 0xfd850513, 0x00a48533, 0x5dd78637, 0x06060613, 0x00c48633, 0x5e047ab7, 0xc60a8a93,
   0x01548ab3]
  | 7 => [0x5dd78537, 0xfd850513, 0x00a48533, 0x5e06a637, 0x06060613, 0x00c48633, 0x5e1d1ab7, 0x660a8a93,
   0x01548ab3]
  | 8 => [0x5e06a537, 0xfd850513, 0x00a48533, 0x5e1e3637, 0x06060613, 0x00c48633, 0x5e297ab7, 0xb60a8a93,
   0x01548ab3]
  | 9 => [0x5e1e3537, 0xfd850513, 0x00a48533, 0x5e2a0637, 0x06060613, 0x00c48633, 0x5e2faab7, 0xde0a8a93,
   0x01548ab3]
  | 10 => [0x5e2a0537, 0xfd850513, 0x00a48533, 0x5e2ff637, 0x06060613, 0x00c48633, 0x5e2ffab7, 0x060a8a93,
   0x01548ab3]
  | 11 => [0x5e2ff537, 0xfd850513, 0x00a48533, 0x5e32f637, 0x06060613, 0x00c48633, 0x5e32fab7, 0x060a8a93,
   0x01548ab3]
  | 12 => [0x5e32f537, 0xfd850513, 0x00a48533, 0x5e347637, 0x06060613, 0x00c48633, 0x5e347ab7, 0x060a8a93,
   0x01548ab3]
  | 13 => [0x5e347537, 0xfd850513, 0x00a48533, 0x5e353637, 0x00060613, 0x00c48633, 0x5e353ab7, 0x000a8a93,
   0x01548ab3]
  | 14 => [0x5e353537, 0xfd850513, 0x00a48533, 0x5e356637, 0x00060613, 0x00c48633, 0x5e356ab7, 0x000a8a93,
   0x01548ab3]
  | 15 => [0x5e356537, 0xfd850513, 0x00a48533, 0x5e357637, 0x00060613, 0x00c48633, 0x5e357ab7, 0x000a8a93,
   0x01548ab3]
  | 16 => [0x5e357537, 0xfd850513, 0x00a48533, 0x5e358637, 0x00060613, 0x00c48633, 0x5e358ab7, 0x000a8a93,
   0x01548ab3]
  | _ => []

def levelLatchWords : Nat → List (BitVec 32)
  | 1 => [0x01560463, 0xc75a906f]
  | 2 => [0x01560463, 0xc50d506f]
  | 3 => [0x01560463, 0x91cfd06f]
  | 4 => [0x01560463, 0x91cfd06f]
  | 5 => [0x01560463, 0x91cfd06f]
  | 6 => [0x01560463, 0x91cfd06f]
  | 7 => [0x01560463, 0x91cfd06f]
  | 8 => [0x01560463, 0x91cfd06f]
  | 9 => [0x01560463, 0x91cfd06f]
  | _ => []

/-- `sd x0, 8t(x12)`: clear the ragged slots after the last node. -/
def levelZeroWords : Nat → List (BitVec 32)
  | 1 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 2 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 3 => []
  | 4 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 5 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 6 => []
  | 7 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 8 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 9 => []
  | 10 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 11 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 12 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 13 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23, 0x04063023, 0x04063423, 0x04063823, 0x04063c23]
  | 14 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23, 0x04063023, 0x04063423, 0x04063823, 0x04063c23]
  | 15 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23, 0x04063023, 0x04063423, 0x04063823, 0x04063c23, 0x06063023, 0x06063423, 0x06063823, 0x06063c23]
  | 16 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23, 0x04063023, 0x04063423, 0x04063823, 0x04063c23]
  | _ => []

def levelCode (m : Nat) : List (BitVec 32) :=
  levelSetupWords m ++ (if levelQ m = 0 then [] else nodeCodeR (levelRadix m) (levelS m) ++ levelLatchWords m) ++
    nodeCodeR (levelRadix m) (levelR m) ++ levelZeroWords m

def levelsCode : List (BitVec 32) :=
  levelCode 1 ++ levelCode 2 ++ levelCode 3 ++ levelCode 4 ++ levelCode 5 ++ levelCode 6 ++ levelCode 7 ++ levelCode 8 ++ levelCode 9 ++ levelCode 10 ++ levelCode 11 ++ levelCode 12 ++ levelCode 13 ++ levelCode 14 ++ levelCode 15 ++ levelCode 16

/-- x10 := level-16 group 0, x12 := trapdoor + 32 (old heap node 1), one node. -/
def rootSetupWords : List (BitVec 32) :=
  [0x5e358537, 0xfd850513, 0x00a48533, 0x02048613, 0x00000073]

def genWords : List (BitVec 32) :=
  [0x000b0613, 0x100023b7, 0x00038393, 0x016383b3] ++
  (List.replicate 288 [0x00000073, 0x0b050513, 0x0b060613]).flatten ++
  [0xa8766063, 0x00090513, 0x00048613, 0xa981806f]

def rootWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073] ++ genWords

def leafCode : List (BitVec 32) :=
  List.ofFn fun i : Fin 45164 => Artifact.commitCode.get 32 ⟨19 + i.val, by omega⟩

theorem setup_words_length : setupWords.length = 19 := List.length_ofFn
theorem leaf_code_length : leafCode.length = 45164 := List.length_ofFn
theorem leaf_latch_words_length : leafLatchWords.length = 18 := List.length_ofFn

def image : Image := ⟨setupWords ++ leafCode ++ leafLatchWords ++ leafZeroWords ++ levelsCode ++
  rootSetupWords ++ rootWords, []⟩

/-- Only the commit image and the common layout are fixed here. -/
def submission (opening checker : Image) : Submission where
  sizes := ⟨2080378880, 41204842496⟩
  layout := ⟨4096,4294971392,4294971424,6375350304,6509568096,10804535392⟩
  image := fun | .commit => image | .opening => opening | .check => checker
  steps := fun | .commit => 1073807360 | .opening => 17179934720 | .check => 1099511627776

/-- Number of ordinary machine steps of the intended successful trace. -/
def executionSteps : Nat := 197816153
/-- Exact certified commit cycles. -/
def executionCycles : Nat := 473458614
def executionCalls : Nat := 39377494

theorem submission_commit_image (opening checker : Image) :
    (submission opening checker).image .commit = image := rfl

theorem enough_commit_fuel (opening checker : Image) :
    executionSteps ≤ (submission opening checker).steps .commit := by
  change executionSteps ≤ 1073807360
  decide

end TwoPermutationPrototype.Quad.Commit
