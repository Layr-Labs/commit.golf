import CommitGolfCandidate.PairChildren
import CommitGolfCandidate.CheckInputSound
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def batchSalt (input : CheckInput) (r : Nat) :=
  readBuffer (CommitGolfCandidate.submission.initialState .check input) (10871640096+528*r) 16

def lowerSibling (input : CheckInput) (r level : Nat) :=
  readBuffer (CommitGolfCandidate.submission.initialState .check input) (10871640096+528*r+16+32*level) 32

def supplied (input : CheckInput) (p : Nat) :=
  readBuffer (CommitGolfCandidate.submission.initialState .check input) (10871707680+32*p) 32

def lowerHash (H : Compression) (input : CheckInput) (r : Nat) :=
  recordAncestor H 16 (recordValue input r) (batchSalt input r) (recordIndex input r) (lowerSibling input r)

def firstAt (input : CheckInput) (u : Nat) :=
  (List.range 128).find? (fun r => openingIndex input.positions r / 65536 == u)

def childrenAt (H : Compression) (input : CheckInput) (p : Nat) : Children :=
  ⟨(firstAt input (2*p)).map (lowerHash H input), (firstAt input (2*p+1)).map (lowerHash H input)⟩

def parentAt (H : Compression) (input : CheckInput) (p : Nat) :=
  (childrenAt H input p).parent H (supplied input p)

def capTable (H : Compression) (input : CheckInput) (p : Nat) :=
  if p < 128 then parentAt H input p else 0

structure BatchValid (H : Compression) (input : CheckInput) : Prop where
  length : input.proof.length = 71680
  records : ∀ r < 128, let i := openingIndex input.positions r
    (childrenAt H input (i/131072)).child (i.testBit 16) = some (lowerHash H input r)
  root : referenceHeap H 128 (capTable H input) 1 = input.commitment

def fullSibling (H : Compression) (input : CheckInput) (r level : Nat) :=
  let i := openingIndex input.positions r
  if level < 16 then lowerSibling input r level
  else if level = 16 then (childrenAt H input (i/131072)).sibling (i.testBit 16) (supplied input (i/131072))
  else referenceHeap H 128 (capTable H input) (((128+i/131072) / 2^(level-17)) ^^^ 1)

theorem fromPair (H : Compression) (input : CheckInput) (good : BatchValid H input) (r : Nat) (hr : r<128) :
    recordAncestor H 17 (recordValue input r) (batchSalt input r) (recordIndex input r) (fullSibling H input r) =
    parentAt H input (openingIndex input.positions r/131072) := by
  let i := recordIndex input r
  have path16 : recordPathPrefix 16 i (fullSibling H input r) = recordPathPrefix 16 i (lowerSibling input r) := by
    unfold recordPathPrefix
    apply List.map_congr_left
    intro n hn; have lt := List.mem_range.mp hn
    simp [fullSibling,lt]
  have extend : recordPathPrefix 17 i (fullSibling H input r) =
      recordPathPrefix 16 i (lowerSibling input r) ++ [(i.val.testBit 16,fullSibling H input r 16)] := by
    rw [← path16]
    simp only [recordPathPrefix,show List.range 17=List.range 16++[16] by decide,
      List.map_append,List.map_cons,List.map_nil]
  change climb H _ (recordPathPrefix 17 i _) = _
  rw [extend,climb,List.foldl_append]
  exact parent_on_path (good.records r hr) H (supplied input (i.val/131072))

end CommitGolfCandidate.PairCap
