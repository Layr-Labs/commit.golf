import CommitGolfCandidate.Stage3cParent
import CommitGolfCandidate.LateModel
set_option Elab.async false
namespace CommitGolfCandidate.Chained.Binary
open CommitGolf

def height (n : Nat) : Height := ⟨n%24,by omega⟩

def continueM {M : Type→Type} [Monad M] (hash : Input→M Output) (h : Height) (n : Nat) (seed : Seed) : M Output :=
  match n with
  | 0 => hash (pack (.inl (workClass h,seed)))
  | j+1 => do let v←continueM hash h j seed
              hash (encodeNext (workClass h) (j+1) v)

def parentM {M : Type→Type} [Monad M] (hash : Input→M Output) (h : Height) (l r : Output) : M Output := do
  let v←continueM hash h (calls h-1) (r ++ l)
  pure (storeReply h v)

theorem continue_pure (H : Compression) (h : Height) (l r : Output) (n : Nat) :
    continueM (M:=Id) H h n (r ++ l)=H ((parentQueries H h l r n).getLastD 0) := by
  induction n with
  | zero => rfl
  | succ j ih =>
    change H (encodeNext _ _ (continueM (M:=Id) H h j (r ++ l)))=_
    rw [ih,parentQueries,List.getLastD_concat]

theorem parent_pure (H : Compression) (h : Height) (l r : Output) :
    parentM (M:=Id) H h l r=parentDigest H h l r := by
  change storeReply h (continueM (M:=Id) H h (calls h-1) (r ++ l))=_
  rw [continue_pure];rfl

def parentsM {M : Type→Type} [Monad M] (hash : Input→M Output) (h : Height) :
    List Output→M (List Output)
  | l::r::xs => do let p←parentM hash h l r;return p::(←parentsM hash h xs)
  | _=>pure []

def levelsM {M : Type→Type} [Monad M] (hash : Input→M Output) : Nat→List Output→M Late.Levels
  | 0, xs=>pure [xs]
  | d+1, xs=>do let ps←parentsM hash (height (23-d)) xs;return xs::(←levelsM hash d ps)

def treeM {M : Type→Type} [Monad M] (hash : Input→M Output) (m : Message) (s : Late.SaltTape) : M Late.Levels := do
  let leaves←(List.finRange LENGTH).mapM fun i=>Late.leafM hash (i.val.testBit 0) (s i) (m i)
  levelsM hash 24 leaves

structure Field where
  bits : Nat
  value : Nat

def recordFields (t : Late.Levels) (s : Late.SaltTape) (i : Index) : List Field :=
  ⟨192,(s i).toNat⟩::(List.range 15).map fun level=>
    ⟨if level=0 then 256 else wireWidth (height (level-1)),
     (Late.node t level ((i.val/2^level) ^^^ 1)).toNat⟩

def slot (t : Late.Levels) (indices : List Index) (p : Nat) : Field :=
  let left:=indices.any fun i=>i.val/32768==2*p
  let right:=indices.any fun i=>i.val/32768==2*p+1
  let v:=if left || right then Late.node t 15 (2*p+if left && !right then 1 else 0) else Late.node t 16 p
  ⟨230,v.toNat⟩

def encode : List Field→Nat
  | []=>0
  | f::fs=>f.value%2^f.bits+2^f.bits*encode fs

/-- Salt plus one sibling at each of the fifteen levels below the batch cap. -/
def recordBits : Nat :=
  192 + ((List.range 15).map (fun j => if j = 0 then 256 else wireWidth (height (j - 1)))).sum

/-- `k = 128` records, then 256 batch slots of the 230-bit cap. -/
def proofBits : Nat := 128 * recordBits + 256 * 230

def proofBytes : Nat := proofBits / 8

def packed (t : Late.Levels) (s : Late.SaltTape) (indices : List Index) : Proof :=
  let v:=encode (indices.flatMap (recordFields t s)++(List.range 256).map (slot t indices))
  (List.range proofBytes).map fun n=>BitVec.ofNat 8 (v/2^(8*n))

def opening (t : Late.Levels) (s : Late.SaltTape) (p : Positions) : Proof :=
  let indices:=p.sort (·≤·)
  if p.card=BATCH then packed t s indices else indices.flatMap (Late.record t s LOG_LENGTH)

theorem packed_length (t s ix) : (packed t s ix).length=proofBytes := by simp [packed]
/-- ptr narrows level 2 from 256 bits to 240, so a record is 3780 bits and a proof is 67840 bytes.
The same statement is re-decided for a wider level 2 or for 238-bit levels 6–8. -/
theorem field_geometry : recordBits = 3780 ∧ proofBytes = 67840 := by decide +kernel
def scheme (check : Late.Checker) : Scheme where
  Trapdoor := Late.Levels × Late.SaltTape
  commit m := do
    let s←Late.sampleSalts
    let t←treeM Late.hash m s
    return (Late.node t LOG_LENGTH 0,t,s)
  opening td p := pure (opening td.1 td.2 p)
  check := check
def HidingGoal := ∀ c : Late.Checker, (scheme c).Hiding HIDING_ERROR
end CommitGolfCandidate.Chained.Binary
