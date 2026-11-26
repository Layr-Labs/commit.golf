import CommitGolfCandidate.TruncHeap
import CommitGolfCandidate.TruncCodec
import CommitGolfCandidate.PairChildren
import CommitGolfCandidate.CheckInputSound
import CommitGolfCandidate.TruncWireImage
import CommitGolfCandidate.LateProjectedLeaf
import CommitGolfCandidate.LateReplay
import CommitGolfCandidate.LateArtifact

namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

abbrev Salt := Late.Salt
def leafDigest (h : Compression) (i : Index) := Late.leaf h (i.val.testBit 0)
def leafChainInputs (h : Compression) (i : Index) := Late.inputs h (i.val.testBit 0)
abbrev openingInputs := Late.openingInputs
abbrev openingWitness := Late.openingWitness
def replayLeaf (i : Index) := Late.replay (i.val.testBit 0)
theorem replay_leaf_run (o : Oracle) (i : Index) (s : Salt) (v : Entry) :
    o.run (replayLeaf i s v)=pure ((leafDigest o.compression i s v,leafChainInputs o.compression i s v),4) :=
  Late.replay_run o _ s v
abbrev Children := PairCap.Children

def wideInput (i : CheckInput) : CheckInput :=
  if i.positions.card=BATCH then {i with proof:=unpack i.proof} else i

def recordAncestor (H : Compression) (levels : Nat) (v : Entry) (s : Salt) (i : Index) (sibling : Nat→Digest) :=
  climb H (LENGTH+i.val) (leafDigest H i s v) (recordPathPrefix levels i sibling)

def recordRoot (H : Compression) (v : Entry) (s : Salt) (i : Index) (sibling : Nat→Digest) :=
  climb H (LENGTH+i.val) (leafDigest H i s v) (recordPath i sibling)

def batchSalt (i : CheckInput) (r : Nat) := readBuffer (submission.initialState .check i) (12079599648+536*r) 24
def lowerSibling (i : CheckInput) (r l : Nat) := readBuffer (submission.initialState .check i) (12079599648+536*r+24+32*l) 32
def supplied (i : CheckInput) (p : Nat) := readBuffer (submission.initialState .check i) (12079668256+32*p) 32
def firstAt (i : CheckInput) (u : Nat) := (List.range 128).find? fun r=>openingIndex i.positions r/65536==u

def lowerHash (H : Compression) (i : CheckInput) (r : Nat) :=
  recordAncestor H 16 (recordValue i r) (batchSalt i r) (recordIndex i r) (lowerSibling i r)

def childrenAt (H : Compression) (i : CheckInput) (p : Nat) : Children :=
  ⟨(firstAt i (2*p)).map (lowerHash H i),(firstAt i (2*p+1)).map (lowerHash H i)⟩

def parentFrom (H : Compression) (n : Nat) (c : Children) (slot : Digest) :=
  if c.left.isNone && c.right.isNone then slot else storeNode n (c.parent H slot)

theorem parent_on_path {c : Children} {dir : Bool} {d : Digest} (child : c.child dir=some d)
    (H : Compression) (n : Nat) (slot : Digest) :
    storeNode n (H (pathInput d (dir,c.sibling dir slot)))=parentFrom H n c slot := by
  rcases c with ⟨l,r⟩
  cases dir <;> cases l <;> cases r <;>
    simp_all [PairCap.Children.child,PairCap.Children.parent,PairCap.Children.sibling,parentFrom,pathInput,combine]

def parentAt (H : Compression) (i : CheckInput) (p : Nat) := parentFrom H (128+p) (childrenAt H i p) (supplied i p)
def capTable (H : Compression) (i : CheckInput) (p : Nat) := if p<128 then parentAt H i p else 0

structure BatchValid (H : Compression) (i : CheckInput) : Prop where
  length : i.proof.length=72704
  records : ∀ r<128, let x:=openingIndex i.positions r
    (childrenAt H i (x/131072)).child (x.testBit 16)=some (lowerHash H i r)
  root : referenceHeap H 128 (capTable H i) 1=i.commitment

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
  unfold recordAncestor
  rw [extend,climb_append,record_path_prefix_length]
  have idx : (LENGTH+i.val)/2^16/2=128+i.val/131072 := by change (16777216+i.val)/65536/2=_;omega
  change storeNode ((LENGTH+i.val)/2^16/2) (H (pathInput (lowerHash H input r) (i.val.testBit 16,fullSibling H input r 16)))=parentAt H input (i.val/131072)
  rw [idx]
  simp only [fullSibling,Nat.lt_irrefl,ite_false,ite_true,parentAt]
  exact parent_on_path (good.records r hr) H (128+i.val/131072) (supplied input (i.val/131072))

end CommitGolfCandidate.Trunc
