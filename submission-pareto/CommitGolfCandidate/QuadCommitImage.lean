import CommitGolf.Programs
import CommitGolf.Artifact

/-! Penta commit machine image, independent of the opening and checker images.
Words 0 .. 45,200 are taken directly from `Artifact.commitCode` (our 4,095-leaf counter-mode
in-place salt prefix with prefetch, proved in `PentaGrouped*`); the words after 45,201 are the
hybrid tree: 5-ary levels 1-2 (written into 5-ary groups), then levels 3-20 written into binary
groups (slots 3 and 4), the root node and the unchanged root copy (187478 words). -/
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
def levelRadix (m : Nat) : Nat := if m < 2 then 5 else 2

/-- One node: permutation call, next input group, next output slot (+32 inside a group; after the
last slot +240 for a 5-ary group, +336 for a binary one). -/
def nodeWordsR (rho t : Nat) : List (BitVec 32) :=
  [0x00000073, 0x17050513, if t + 1 = rho then (if rho = 5 then 0x0f060613 else 0x15060613) else 0x02060613]

def nodeCodeR (rho n : Nat) : List (BitVec 32) := (List.range n).flatMap (fun p => nodeWordsR rho (p % rho))

/-- Loop body nodes, loop iterations, tail nodes and cleared words of level `m`. -/
def levelS : Nat → Nat
  | 1 => 29430
  | 2 => 1000
  | 3 => 1000
  | 4 => 1000
  | 5 => 1000
  | 6 => 1000
  | 7 => 1000
  | 8 => 1000
  | 9 => 1000
  | 10 => 1000
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | _ => 0

def levelQ : Nat → Nat
  | 1 => 114
  | 2 => 671
  | 3 => 335
  | 4 => 167
  | 5 => 83
  | 6 => 41
  | 7 => 20
  | 8 => 10
  | 9 => 5
  | 10 => 2
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | _ => 0


def levelR : Nat → Nat
  | 1 => 424
  | 2 => 89
  | 3 => 545
  | 4 => 773
  | 5 => 887
  | 6 => 944
  | 7 => 972
  | 8 => 486
  | 9 => 243
  | 10 => 622
  | 11 => 1311
  | 12 => 656
  | 13 => 328
  | 14 => 164
  | 15 => 82
  | 16 => 41
  | 17 => 21
  | 18 => 11
  | 19 => 6
  | 20 => 3
  | 21 => 2
  | _ => 0


def levelZ : Nat → Nat
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 4
  | 10 => 0
  | 11 => 4
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 4
  | 17 => 4
  | 18 => 4
  | 19 => 0
  | 20 => 4
  | 21 => 0
  | _ => 0

/-- x10 := level m-1 group 0, x12 := level m slot 0, x21 := slot after the loop part. -/
def levelSetupWords : Nat → List (BitVec 32)
  | 1 => [0x00001537, 0xfd850513, 0x00a48533, 0x4999c637, 0x00060613, 0x00c48633, 0x5851aab7, 0x840a8a93,
   0x01548ab3]
  | 2 => [0x4999c537, 0xfd850513, 0x00a48533, 0x58523637, 0x06060613, 0x00c48633, 0x5fae2ab7, 0x9a0a8a93,
   0x01548ab3]
  | 3 => [0x58523537, 0xfd850513, 0x00a48533, 0x5fae6637, 0x06060613, 0x00c48633, 0x635afab7, 0xda0a8a93,
   0x01548ab3]
  | 4 => [0x5fae6537, 0xfd850513, 0x00a48533, 0x635c8637, 0x06060613, 0x00c48633, 0x65316ab7, 0xfa0a8a93,
   0x01548ab3]
  | 5 => [0x635c8537, 0xfd850513, 0x00a48533, 0x65339637, 0x06060613, 0x00c48633, 0x661caab7, 0x8a0a8a93,
   0x01548ab3]
  | 6 => [0x65339537, 0xfd850513, 0x00a48533, 0x661f2637, 0x06060613, 0x00c48633, 0x66924ab7, 0xd20a8a93,
   0x01548ab3]
  | 7 => [0x661f2537, 0xfd850513, 0x00a48533, 0x6694f637, 0x06060613, 0x00c48633, 0x66cd1ab7, 0x760a8a93,
   0x01548ab3]
  | 8 => [0x6694f537, 0xfd850513, 0x00a48533, 0x66cfe637, 0x06060613, 0x00c48633, 0x66ebfab7, 0x3e0a8a93,
   0x01548ab3]
  | 9 => [0x66cfe537, 0xfd850513, 0x00a48533, 0x66ed6637, 0x06060613, 0x00c48633, 0x66fb7ab7, 0xa20a8a93,
   0x01548ab3]
  | 10 => [0x66ed6537, 0xfd850513, 0x00a48533, 0x66fc2637, 0x06060613, 0x00c48633, 0x6701cab7, 0xde0a8a93,
   0x01548ab3]
  | 11 => [0x66fc2537, 0xfd850513, 0x00a48533, 0x67038637, 0x06060613, 0x00c48633, 0x67038ab7, 0x060a8a93,
   0x01548ab3]
  | 12 => [0x67038537, 0xfd850513, 0x00a48533, 0x67073637, 0x06060613, 0x00c48633, 0x67073ab7, 0x060a8a93,
   0x01548ab3]
  | 13 => [0x67073537, 0xfd850513, 0x00a48533, 0x67091637, 0x06060613, 0x00c48633, 0x67091ab7, 0x060a8a93,
   0x01548ab3]
  | 14 => [0x67091537, 0xfd850513, 0x00a48533, 0x670a0637, 0x06060613, 0x00c48633, 0x670a0ab7, 0x060a8a93,
   0x01548ab3]
  | 15 => [0x670a0537, 0xfd850513, 0x00a48533, 0x670a8637, 0x06060613, 0x00c48633, 0x670a8ab7, 0x060a8a93,
   0x01548ab3]
  | 16 => [0x670a8537, 0xfd850513, 0x00a48533, 0x670ac637, 0x06060613, 0x00c48633, 0x670acab7, 0x060a8a93,
   0x01548ab3]
  | 17 => [0x670ac537, 0xfd850513, 0x00a48533, 0x670ae637, 0x06060613, 0x00c48633, 0x670aeab7, 0x060a8a93,
   0x01548ab3]
  | 18 => [0x670ae537, 0xfd850513, 0x00a48533, 0x670af637, 0x06060613, 0x00c48633, 0x670afab7, 0x060a8a93,
   0x01548ab3]
  | 19 => [0x670af537, 0xfd850513, 0x00a48533, 0x670b0637, 0x06060613, 0x00c48633, 0x670b0ab7, 0x060a8a93,
   0x01548ab3]
  | 20 => [0x670b0537, 0xfd850513, 0x00a48533, 0x670b1637, 0x06060613, 0x00c48633, 0x670b1ab7, 0x060a8a93,
   0x01548ab3]
  | 21 => [0x670b1537, 0xfd850513, 0x00a48533, 0x670b2637, 0x06060613, 0x00c48633, 0x670b2ab7, 0x060a8a93,
   0x01548ab3]
  | _ => []

def levelLatchWords : Nat → List (BitVec 32)
  | 1 => [0x01560463, 0xc75a906f]
  | 2 => [0x01560463, 0x91cfd06f]
  | 3 => [0x01560463, 0x91cfd06f]
  | 4 => [0x01560463, 0x91cfd06f]
  | 5 => [0x01560463, 0x91cfd06f]
  | 6 => [0x01560463, 0x91cfd06f]
  | 7 => [0x01560463, 0x91cfd06f]
  | 8 => [0x01560463, 0x91cfd06f]
  | 9 => [0x01560463, 0x91cfd06f]
  | 10 => [0x01560463, 0x91cfd06f]
  | _ => []

/-- `sd x0, 8t(x12)`: clear the ragged slots after the last node. -/
def levelZeroWords : Nat → List (BitVec 32)
  | 1 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 2 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 3 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 4 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 5 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 10 => []
  | 11 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 17 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 18 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 19 => []
  | 20 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 21 => []
  | _ => []

def levelCode (m : Nat) : List (BitVec 32) :=
  levelSetupWords m ++ (if levelQ m = 0 then [] else nodeCodeR (levelRadix m) (levelS m) ++ levelLatchWords m) ++
    nodeCodeR (levelRadix m) (levelR m) ++ levelZeroWords m

def levelsCode : List (BitVec 32) :=
  levelCode 1 ++ levelCode 2 ++ levelCode 3 ++ levelCode 4 ++ levelCode 5 ++ levelCode 6 ++ levelCode 7 ++ levelCode 8 ++ levelCode 9 ++ levelCode 10 ++ levelCode 11 ++ levelCode 12 ++ levelCode 13 ++ levelCode 14 ++ levelCode 15 ++ levelCode 16 ++ levelCode 17 ++ levelCode 18 ++ levelCode 19 ++ levelCode 20 ++ levelCode 21

/-- x10 := level-20 group 0, x12 := trapdoor + 32 (old heap node 1), one node. -/
def rootSetupWords : List (BitVec 32) :=
  [0x670b2537, 0xfd850513, 0x00a48533, 0x02048613, 0x00000073]

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
  sizes := ⟨2080378880, 47647293440⟩
  layout := ⟨4096,4294971392,4294971424,6375350304,6509568096,10804535392⟩
  image := fun | .commit => image | .opening => opening | .check => checker
  steps := fun | .commit => 1073807360 | .opening => 17179934720 | .check => 1099511627776

/-- Number of ordinary machine steps of the intended successful trace. -/
def executionSteps : Nat := 199026454
/-- Exact certified commit cycles. -/
def executionCycles : Nat := 477488172
def executionCalls : Nat := 39780245

theorem submission_commit_image (opening checker : Image) :
    (submission opening checker).image .commit = image := rfl

theorem enough_commit_fuel (opening checker : Image) :
    executionSteps ≤ (submission opening checker).steps .commit := by
  change executionSteps ≤ 1073807360
  decide

end TwoPermutationPrototype.Quad.Commit
