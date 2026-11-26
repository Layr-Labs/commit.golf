import CommitGolfCandidate.S4Auth
import CommitGolfCandidate.S4Queries
namespace CommitGolfCandidate.S4
open CommitGolf OracleComp OracleSpec
open Late (Digest Block)
open Queries (join done query retime)
abbrev Trace := Digest × List Block

private theorem boundLeaf (odd : Bool) (s : Late.Salt) (v : Entry) : IsTotalQueryBound (Late.replay odd s v) 4 := by
  unfold Late.replay Late.hash
  repeat first | apply (isTotalQueryBound_query_bind_iff).mpr; constructor; decide | intro _
  trivial

def leafTrace (v : View) (r : Nat) : Queries 4 Trace :=
  let odd:=(v.idx r).val.testBit 0
  ⟨Late.replay odd (v.salt r) (v.entry r),
   fun o=>(Late.leaf o.compression odd (v.salt r) (v.entry r),Late.inputs o.compression odd (v.salt r) (v.entry r)),
   fun o=>Late.replay_run o odd (v.salt r) (v.entry r),boundLeaf _ _ _⟩

def replayRecord (p : Profile) (v : View) (r : Nat) (data : Nat→Peers) : (n : Nat) → Queries (4+n) Trace
  | 0=>leafTrace v r
  | n+1=>join (n:=4+n) (m:=1) (replayRecord p v r data n) fun prev=>
      let x:=payload (lane n (nodeIndex (v.idx r).val n)) prev.1 (data n)
      Queries.map (fun y=>(retained p (n+1) y,x::prev.2)) (Queries.query x)

def inputAt (p : Profile) (H : Compression) (v : View) (r : Nat) (data : Nat→Peers) (n : Nat) :=
  payload (lane n (nodeIndex (v.idx r).val n)) (recordAt p H v r n data) (data n)

def recordInputs (p : Profile) (H : Compression) (v : View) (r : Nat) (data : Nat→Peers) : Nat → List Block
  | 0=>Late.inputs H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r)
  | n+1=>inputAt p H v r data n::recordInputs p H v r data n

theorem replayValue (p : Profile) (o : Oracle) (v : View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    (replayRecord p v r data n).eval o=(recordAt p o.compression v r n data,recordInputs p o.compression v r data n) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [replayRecord,Queries.join,Queries.map,Queries.query,ih,recordAt,walk,recordInputs,inputAt]

theorem inputsLength (p : Profile) (H : Compression) (v : View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    (recordInputs p H v r data n).length=4+n := by induction n with | zero=>rfl | succ n ih=>simp [recordInputs,ih,Nat.add_assoc]

theorem recordsCollide (p : Profile) (H : Compression) (v w : View) (l r : Nat) (a b : Nat→Peers) (n : Nat)
    (idx : v.idx l=w.idx r) (diff : v.entry l≠w.entry r)
    (root : recordAt p H v l n a=recordAt p H w r n b) :
    Witness p H (recordInputs p H v l a n) (recordInputs p H w r b n) := by
  induction n with
  | zero=>
    change Late.leaf H ((v.idx l).val.testBit 0) _ _=Late.leaf H ((w.idx r).val.testBit 0) _ _ at root
    rw [←idx] at root
    obtain ⟨x,hx,y,hy,ne,eq⟩:=Late.leaf_collision H _ _ _ _ _ diff root
    exact ⟨x,hx,y,by simpa only [recordInputs,←idx] using hy,ne,congrArg (project p) eq⟩
  | succ n ih=>
    let x:=inputAt p H v l a n;let y:=inputAt p H w r b n
    change retained p (n+1) (H x)=retained p (n+1) (H y) at root
    by_cases ne : x=y
    · have inp :=ne;unfold x y inputAt at inp;rw [←idx] at inp
      obtain ⟨u,hu,z,hz,neq,eq⟩:=ih (slotInjective _ _ _ _ _ inp)
      exact ⟨u,List.mem_cons_of_mem _ hu,z,List.mem_cons_of_mem _ hz,neq,eq⟩
    · exact ⟨x,List.mem_cons_self ..,y,List.mem_cons_self ..,ne,
        (retainedProjection p (n+1) (H x)).symm.trans ((congrArg (project p) root).trans (retainedProjection p (n+1) (H y)))⟩
end CommitGolfCandidate.S4
