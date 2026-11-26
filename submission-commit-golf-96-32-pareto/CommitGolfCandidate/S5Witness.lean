import CommitGolfCandidate.S5Model
import CommitGolfCandidate.Stage3cRowWitness
namespace CommitGolfCandidate.S5
open CommitGolf Chained Chained.Replay
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


private theorem full_collision {t : Trace} {rows : List PublicRow} {H : Compression} {a b : Input}
    (recorded : ∀ r∈rows,Stored t r) (ha : .compression a (H a)∈rows) (hb : .compression b (H b)∈rows)
    (diff : a≠b) (matchOut : H a=H b) : ¬Good canonicalEncoding t := by
  intro good
  obtain ⟨i,ia,oi⟩:=recorded _ ha
  obtain ⟨j,ib,oj⟩:=recorded _ hb
  have eq:=good.outputs (oi.trans (matchOut.trans oj.symm))
  exact diff (ia.symm.trans ((congrArg t.input eq).trans ib))

theorem mixed_witness (H : Compression) (rows : List PublicRow) (i : Index) (a b : Salt) (v w : Entry) (ne : v≠w)
    (p q : Peers) (xs ys : List LayerStep)
    (shape : xs.map (fun s=>(s.height,s.right))=ys.map (fun s=>(s.height,s.right)))
    (lv : rowReads rows H (Late.inputs H (i.val.testBit 0) a v))
    (rv : rowReads rows H (Late.inputs H (i.val.testBit 0) b w)) :
    let leafA:=Late.leaf H (i.val.testBit 0) a v
    let leafB:=Late.leaf H (i.val.testBit 0) b w
    let x:=payload (lane 0 i.val) leafA p
    let y:=payload (lane 0 i.val) leafB q
    .compression x (H x)∈rows → .compression y (H y)∈rows →
    rowPath rows H (H x) xs → rowPath rows H (H y) ys →
    walk H (H x) xs=walk H (H y) ys → Witness rows := by
  dsimp only
  intro hx hy px py root t stored
  by_cases leaves : Late.leaf H (i.val.testBit 0) a v=Late.leaf H (i.val.testBit 0) b w
  · obtain ⟨x,hx',y,hy',distinct,eq⟩:=Late.leaf_collision H _ a b v w ne leaves
    exact Or.inr (full_collision stored (lv _ hx') (rv _ hy') distinct eq)
  · by_cases bottom : H (payload (lane 0 i.val) (Late.leaf H (i.val.testBit 0) a v) p)=
                      H (payload (lane 0 i.val) (Late.leaf H (i.val.testBit 0) b w) q)
    · exact Or.inr (full_collision stored hx hy (fun eq=>leaves (slotInjective _ _ _ _ _ eq)) bottom)
    · exact Or.inl (walk_collision t H _ _ xs ys shape (path_stored t rows H _ _ stored px)
        (path_stored t rows H _ _ stored py) bottom root)
end CommitGolfCandidate.S5
