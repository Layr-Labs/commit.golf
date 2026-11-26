import CommitGolfCandidate.S4Model
import CommitGolfCandidate.LateBinding
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Digest Block Salt)

inductive Lane | bl | br | t0 | t1 | t2 deriving DecidableEq,Repr
def lane (h i : Nat) : Lane :=
  if h=0 then if i%3=0 then .t0 else if i%3=1 then .t1 else .t2
  else if i%2=0 then .bl else .br

abbrev Peers := Digest × Digest
def payload (d : Lane) (v : Digest) (p : Peers) : Block :=
  match d with
  | .bl => Late.parentBlock v p.1
  | .br => Late.parentBlock p.1 v
  | .t0 => p.2 ++ p.1 ++ v
  | .t1 => p.1 ++ v ++ p.2
  | .t2 => v ++ p.2 ++ p.1

private theorem appendParts {m n : Nat} {a c : BitVec m} {b d : BitVec n} (e : a++b=c++d) : a=c ∧ b=d := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (fun x : BitVec (m+n)=>x.extractLsb' n m) e
  · simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (fun x : BitVec (m+n)=>x.extractLsb' 0 n) e
theorem slotInjective (d : Lane) (v w : Digest) (a b : Peers) (e : payload d v a=payload d w b) : v=w := by
  cases d
  · exact (appendParts e).2
  · exact (appendParts (appendParts e).1).2
  · exact (appendParts e).2
  · exact (appendParts (appendParts e).1).2
  · exact (appendParts (appendParts e).1).1

def projectionWidth : Profile → Nat | .byte=>240 | .packed=>238
def project (p : Profile) (v : Digest) := v.extractLsb' 0 (projectionWidth p)

private theorem lowPad {k m w : Nat} (v : Digest) (small : w≤k) :
    (((0 : BitVec m) ++ v.extractLsb' 0 k).extractLsb' 0 w) = v.extractLsb' 0 w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ik : i<k:=by omega
  simp only [BitVec.getLsbD_extractLsb',Nat.zero_add,hi,decide_true,Bool.true_and]
  rw [BitVec.getLsbD_append (x:=(0 : BitVec m)) (y:=v.extractLsb' 0 k),if_pos ik]
  simp [BitVec.getLsbD_extractLsb',ik]

theorem retainedProjection (p : Profile) (h : Nat) (v : Digest) : project p (retained p h v)=project p v := by
  unfold project retained
  split
  · rename_i e
    apply lowPad;cases p
    · unfold bits at e;split at e <;> simp_all
    · decide
  · split
    · apply lowPad;cases p <;> decide
    · rfl

def climb (p : Profile) (H : Compression) (h i : Nat) (v : Digest) : List Peers → Digest
  | [] => v
  | a::as => climb p H (h+1) (i/radix h) (retained p (h+1) (H (payload (lane h i) v a))) as

def pathInputs (p : Profile) (H : Compression) (h i : Nat) (v : Digest) : List Peers → List Block
  | []=>[]
  | a::as=>let x:=payload (lane h i) v a
           x::pathInputs p H (h+1) (i/radix h) (retained p (h+1) (H x)) as

def Witness (p : Profile) (H : Compression) (xs ys : List Block) : Prop :=
  ∃ x∈xs,∃ y∈ys,x≠y ∧ project p (H x)=project p (H y)

theorem pathWitness (p : Profile) (H : Compression) (h i : Nat) (v w : Digest) (xs ys : List Peers)
    (len : xs.length=ys.length) (ne : v≠w) (eqn : climb p H h i v xs=climb p H h i w ys) :
    Witness p H (pathInputs p H h i v xs) (pathInputs p H h i w ys) := by
  induction xs generalizing h i v w ys with
  | nil=>cases ys with
         | nil=>exact False.elim (ne eqn)
         | cons =>simp at len
  | cons x xs ih=>
    cases ys with
    | nil=>simp at len
    | cons y ys=>
      let a:=payload (lane h i) v x
      let b:=payload (lane h i) w y
      let left:=retained p (h+1) (H a)
      let right:=retained p (h+1) (H b)
      by_cases same : left=right
      · have coll:=congrArg (project p) same
        change project p (retained _ _ _)=project p (retained _ _ _) at coll
        have bitsEq:=(retainedProjection p (h+1) (H a)).symm.trans (coll.trans (retainedProjection p (h+1) (H b)))
        exact ⟨a,List.mem_cons_self ..,b,List.mem_cons_self ..,fun e=>ne (slotInjective _ _ _ _ _ e),bitsEq⟩
      · obtain ⟨u,hu,z,hz,diff,coll⟩:=ih (h+1) (i/radix h) left right ys (by simpa using len) same eqn
        exact ⟨u,List.mem_cons_of_mem _ hu,z,List.mem_cons_of_mem _ hz,diff,coll⟩

theorem openingWitness (p : Profile) (H : Compression) (i : Index) (a b : Salt) (v w : Entry) (xs ys : List Peers)
    (len : xs.length=ys.length) (ne : v≠w)
    (root : climb p H 0 i.val (Late.leaf H (i.val.testBit 0) a v) xs =
      climb p H 0 i.val (Late.leaf H (i.val.testBit 0) b w) ys) :
    Witness p H (Late.inputs H (i.val.testBit 0) a v ++ pathInputs p H 0 i.val (Late.leaf H (i.val.testBit 0) a v) xs)
      (Late.inputs H (i.val.testBit 0) b w ++ pathInputs p H 0 i.val (Late.leaf H (i.val.testBit 0) b w) ys) := by
  by_cases e : Late.leaf H (i.val.testBit 0) a v=Late.leaf H (i.val.testBit 0) b w
  · obtain ⟨x,hx,y,hy,n,c⟩:=Late.leaf_collision H _ a b v w ne e
    exact ⟨x,List.mem_append_left _ hx,y,List.mem_append_left _ hy,n,congrArg (project p) c⟩
  · obtain ⟨x,hx,y,hy,n,c⟩:=pathWitness p H 0 i.val _ _ xs ys len e root
    exact ⟨x,List.mem_append_right _ hx,y,List.mem_append_right _ hy,n,c⟩
end CommitGolfCandidate.S4
