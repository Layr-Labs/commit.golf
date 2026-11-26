import CommitGolfCandidate.Stage3cCompletedParent
import CommitGolfCandidate.LateBinding
namespace CommitGolfCandidate.Chained
open CommitGolf

structure LayerStep where
  height : Height
  right : Bool
  sibling : Output

def children (r : Bool) (x sibling : Output) : Output × Output :=
  if r then (sibling,x) else (x,sibling)

def nextNode (H : Compression) (x : Output) (step : LayerStep) : Output :=
  let pair:=children step.right x step.sibling
  parentDigest H step.height pair.1 pair.2

def walk (H : Compression) (x : Output) : List LayerStep → Output
  | [] => x
  | s::tail => walk H (nextNode H x s) tail

def pathRecorded (t : Trace) (H : Compression) (x : Output) : List LayerStep → Prop
  | [] => True
  | s::tail => let pair:=children s.right x s.sibling
               Recorded t H s.height pair.1 pair.2 ∧ pathRecorded t H (nextNode H x s) tail

theorem walk_collision (t : Trace) (H : Compression) (x y : Output) (left right : List LayerStep)
    (shape : left.map (fun s=>(s.height,s.right))=right.map (fun s=>(s.height,s.right)))
    (a : pathRecorded t H x left) (b : pathRecorded t H y right)
    (diff : x≠y) (root : walk H x left=walk H y right) : FinalCollision canonicalEncoding calls width t := by
  induction left generalizing x y right with
  | nil =>
    cases right with
    | nil => exact False.elim (diff root)
    | cons => simp at shape
  | cons step rest ih =>
    cases right with
    | nil => simp at shape
    | cons other tail =>
      obtain ⟨h,dir,u⟩:=step;obtain ⟨h',dir',v⟩:=other
      simp only [List.map_cons,List.cons.injEq,Prod.mk.injEq] at shape
      obtain ⟨⟨rfl,rfl⟩,shape⟩:=shape
      by_cases join : nextNode H x ⟨h,dir,u⟩=nextNode H y ⟨h,dir,v⟩
      · have pairs : children dir x u≠children dir y v := by
          cases dir <;> simp_all [children]
        exact collision_from_parent t H h _ _ _ _ a.1 b.1 pairs join
      · exact ih _ _ _ shape a.2 b.2 join root

def reads (t : Trace) (H : Compression) (xs : List Input) :=
  ∀ x∈xs, ∃ i, t.input i=x ∧ t.output i=H x

theorem opening_witness (t : Trace) (H : Compression) (odd : Bool) (s u : Late.Salt) (v w : CommitGolf.Entry)
    (left right : List LayerStep) (different : v≠w)
    (shape : left.map (fun z=>(z.height,z.right))=right.map (fun z=>(z.height,z.right)))
    (lv : reads t H (Late.inputs H odd s v)) (rv : reads t H (Late.inputs H odd u w))
    (lp : pathRecorded t H (Late.leaf H odd s v) left) (rp : pathRecorded t H (Late.leaf H odd u w) right)
    (root : walk H (Late.leaf H odd s v) left=walk H (Late.leaf H odd u w) right) :
    FinalCollision canonicalEncoding calls width t ∨ ¬Good canonicalEncoding t := by
  by_cases same : Late.leaf H odd s v=Late.leaf H odd u w
  · right;intro good
    obtain ⟨x,hx,y,hy,ne,hit⟩:=Late.leaf_collision H odd s u v w different same
    obtain ⟨i,ax,ay⟩:=lv x hx
    obtain ⟨j,bx,by'⟩:=rv y hy
    have rows:=good.outputs (ay.trans (hit.trans by'.symm))
    exact ne (ax.symm.trans ((congrArg t.input rows).trans bx))
  · exact Or.inl (walk_collision t H _ _ left right shape lp rp same root)
end CommitGolfCandidate.Chained
