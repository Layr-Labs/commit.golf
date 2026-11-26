import CommitGolfCandidate.LateReplay
import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.PairChildren
import CommitGolfCandidate.HidingTree

namespace CommitGolfCandidate.Late.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def recordIndex (p : Positions) (r : Nat) : Index :=
  (p.sort (· ≤ ·))[r]?.getD ⟨0, by decide⟩

def recordValue (input : CheckInput) (r : Nat) : Entry :=
  ((input.positions.attach.sort (fun x y => x.val ≤ y.val))[r]?.map input.values).getD 0

def depth (input : CheckInput) : Nat := if input.positions.card = BATCH then 16 else 24

def proofAt (input : CheckInput) (off n : Nat) := readBuffer
  (Late.submission.initialState .check input) (Late.submission.layout.proof+off) n

/-- Record stride: 510 bytes at 128 positions (24 + 3 x 32 + 13 x 30), 792 otherwise. -/
def stride (input : CheckInput) : Nat := if input.positions.card = BATCH then 510 else 792

def start (input : CheckInput) (r : Nat) := r*stride input

def salt (input : CheckInput) (r : Nat) : Salt := proofAt input (start input r) 24
/-- Batch siblings of levels 3..15 are 30-byte fields, zero-extended. -/
def sibling (input : CheckInput) (r l : Nat) : Digest :=
  if input.positions.card = BATCH ∧ 3 ≤ l then widen (proofAt input (start input r+120+30*(l-3)) 30)
  else proofAt input (start input r+24+32*l) 32
def supplied (input : CheckInput) (p : Nat) : Digest := widen (proofAt input (65280+30*p) 30)

def path (i : Index) (d : Nat) (nodes : Nat → Digest) : List (Bool × Digest) :=
  (List.range d).map fun l => (i.val.testBit l, nodes l)

def lower (h : Compression) (input : CheckInput) (r d : Nat) : Digest :=
  let i := recordIndex input.positions r
  climbAt h 0 (leaf h (i.val.testBit 0) (salt input r) (recordValue input r))
    (path i d (sibling input r))

def first (input : CheckInput) (bucket : Nat) :=
  (List.range 128).find? fun r => (recordIndex input.positions r).val/65536 == bucket

def children (h : Compression) (input : CheckInput) (pair : Nat) : PairCap.Children :=
  ⟨(first input (2*pair)).map fun r => lower h input r 16,
   (first input (2*pair+1)).map fun r => lower h input r 16⟩

/-- The height-17 node of a pair, stored in cut form. -/
def parent (h : Compression) (input : CheckInput) (pair : Nat) :=
  cut 17 ((children h input pair).parent h (supplied input pair))

def capTable (h : Compression) (input : CheckInput) (p : Nat) := if p < 128 then parent h input p else 0

def upper (h : Compression) (input : CheckInput) := referenceHeap h 128 (capTable h input)

structure BatchValid (h : Compression) (input : CheckInput) : Prop where
  length : input.proof.length = 69120
  agree : ∀ r < 128, let i := (recordIndex input.positions r).val
    (children h input (i/131072)).child (i.testBit 16) = some (lower h input r 16)
  root : upper h input 1 = input.commitment

def Valid (h : Compression) (input : CheckInput) : Prop :=
  if input.positions.card = BATCH then BatchValid h input else
    input.proof.length = input.positions.card*792 ∧
      ∀ r < input.positions.card, lower h input r 24 = input.commitment

def evaluation (o : Oracle) (input : CheckInput) :=
  o.eval (Late.submission.scheme.check input.commitment input.positions input.values input.proof)

def MachineLaw : Prop := ∀ o input,
  (evaluation o input).2 ≤ (if input.positions.card = BATCH then 2815 else 28*input.positions.card) ∧
  ((evaluation o input).1 = true ↔ Valid o.compression input)

def AcceptsValid : Prop := ∀ o input, (evaluation o input).1 = true → Valid o.compression input

theorem sound_of_machine (law : MachineLaw) : AcceptsValid :=
  fun o input accepted => (law o input).2.mp accepted

def capPath (h : Compression) (input : CheckInput) (r : Nat) : List (Bool × Digest) :=
  let i := recordIndex input.positions r
  let p := i.val/131072
  path i 16 (sibling input r) ++ [(i.val.testBit 16,
    (children h input p).sibling (i.val.testBit 16) (supplied input p))] ++
    heapPath (upper h input) (128+p) 7

theorem batch_path_root (o : Oracle) (input : CheckInput) (h : BatchValid o.compression input)
    (r : Nat) (hr : r < 128) :
    let i := recordIndex input.positions r
    climbAt o.compression 0 (leaf o.compression (i.val.testBit 0) (salt input r) (recordValue input r))
      (capPath o.compression input r) = input.commitment := by
  let i := recordIndex input.positions r
  let p := i.val/131072
  let H := o.compression
  have inside : p < 128 := by have e := i.isLt; change i.val < 16777216 at e; dsimp [p]; omega
  have hit := PairCap.parent_on_path (h.agree r hr) H (supplied input p)
  have root := reconstruct_heap_root H (upper H input) 7 p inside (fun n hp hn =>
    reference_heap_parent H 128 (capTable H input) n hp hn)
  have eq := reference_heap_leaf H 128 (capTable H input) p inside
  simp only [capTable, if_pos inside] at eq
  have len : (path i 16 (sibling input r) ++ [(i.val.testBit 16,
      (children H input p).sibling (i.val.testBit 16) (supplied input p))]).length = 17 := by
    simp [path]
  show climbAt H 0 _ (path i 16 (sibling input r) ++ [(i.val.testBit 16,
      (children H input p).sibling (i.val.testBit 16) (supplied input p))] ++
      heapPath (upper H input) (128+p) 7) = _
  rw [climbAt_append, len, climbAt_append, climbAt_eq_climb H _ (by omega)]
  simp only [path, List.length_map, List.length_range, Nat.zero_add, climbAt_cons, climbAt_nil]
  change climb H (cut 17 (if i.val.testBit 16 then combine H _ (lower H input r 16)
    else combine H (lower H input r 16) _)) (heapPath (upper H input) (128+p) 7) = _
  rw [hit]
  exact (congrArg (fun x => climb H x (heapPath (upper H input) (128+p) 7)) eq.symm).trans
    (root.trans h.root)

end CommitGolfCandidate.Late.Check
