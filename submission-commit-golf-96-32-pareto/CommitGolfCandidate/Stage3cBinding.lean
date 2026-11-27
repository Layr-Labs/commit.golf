import CommitGolfCandidate.Stage3cWire
import CommitGolfCandidate.Stage3cRowWitness
import CommitGolf.Artifact
/-! Binding for the ptr image: two accepted openings that disagree at a position give two
recorded 24-level binary paths with the same shape and root, hence `witness_of_paths`. -/
namespace CommitGolfCandidate.Pw
open CommitGolf Chained Chained.Replay OracleComp

def upperShape (i : Index) : List (Height × Bool) :=
  (List.range 24).map fun h=>(height h,(Geo.nodeIndex i.val h).testBit 0)

structure RecordedPath (H : Compression) (x : CheckInput) (i : Index) (present : i∈x.positions)
    (rows : List PublicRow) : Type where
  salt : Late.Salt
  path : List LayerStep
  shape : path.map (fun s=>(s.height,s.right))=upperShape i
  leafRows : rowReads rows H (Late.inputs H (i.val.testBit 0) salt (x.values ⟨i,present⟩))
  pathRows : rowPath rows H (Late.leaf H (i.val.testBit 0) salt (x.values ⟨i,present⟩)) path
  root : Chained.walk H (Late.leaf H (i.val.testBit 0) salt (x.values ⟨i,present⟩)) path=x.commitment

theorem path_weaken {H x i present a b} (p : RecordedPath H x i present a) (inc : ∀ z∈a,z∈b) :
    Nonempty (RecordedPath H x i present b) := by
  have lift (v : Output) (steps : List LayerStep) : rowPath a H v steps → rowPath b H v steps := by
    induction steps generalizing v with
    | nil=>intro _;trivial
    | cons step rest ih=>
      intro h;exact ⟨fun j hj=>inc _ (h.1 j hj),ih _ h.2⟩
  exact ⟨⟨p.salt,p.path,p.shape,fun z hz=>inc _ (p.leafRows z hz),lift _ _ p.pathRows,p.root⟩⟩

def leftClaim (c : Scheme.Claim) : CheckInput := ⟨c.root,c.positions₀,c.values₀,c.proof₀⟩
def rightClaim (c : Scheme.Claim) : CheckInput := ⟨c.root,c.positions₁,c.values₁,c.proof₁⟩

structure CheckReplay (scheme : Scheme) where
  run : CheckInput → OracleComp World Unit
  /-- At most half of the two-opening replay reserve for either claim. -/
  cost : ∀ x,PublicQueryBound (run x) (2^31)
  sound : ∀ (o : Oracle) (x : CheckInput),
    (o.eval (scheme.check x.commitment x.positions x.values x.proof)).1=true →
    ∀ r∈support (fixedOracleRun o (recordRows (run x))),∀ i (p : i∈x.positions),
      Nonempty (RecordedPath o.compression x i p r.2)

theorem check_binding {scheme : Scheme} (spec : CheckReplay scheme) : scheme.Binding := by
  apply binding_of_replay
  let pair (c : Scheme.Claim) := spec.run (leftClaim c) >>= fun _=>spec.run (rightClaim c)
  refine ⟨pair,?_,?_⟩
  · intro c
    have bounds:=public_query_bound_bind (spec.cost (leftClaim c)) (fun _=>spec.cost (rightClaim c))
    exact bounds.mono (by decide : 2^31+2^31≤2^32)
  · intro o c breaks result reach
    obtain ⟨⟨i,li,ri,diff⟩,leftOK,rightOK⟩:=breaks
    change result∈support (fixedOracleRun o (recordRows (spec.run (leftClaim c) >>= fun _=>spec.run (rightClaim c)))) at reach
    rw [record_rows_bind,fixed_oracle_run_bind,mem_support_bind_iff] at reach
    obtain ⟨a,ha,rest⟩:=reach
    rw [fixed_oracle_run_bind,mem_support_bind_iff] at rest
    obtain ⟨b,hb,ret⟩:=rest
    rw [fixed_oracle_run_pure,support_pure,Set.mem_singleton_iff] at ret;subst result
    obtain ⟨l⟩:=spec.sound o (leftClaim c) leftOK a ha i li
    obtain ⟨r⟩:=spec.sound o (rightClaim c) rightOK b hb i ri
    obtain ⟨l'⟩:=path_weaken l (fun z hz=>List.mem_append_left b.2 hz)
    obtain ⟨r'⟩:=path_weaken r (fun z hz=>List.mem_append_right a.2 hz)
    exact witness_of_paths (a.2++b.2) o.compression (i.val.testBit 0) l'.salt r'.salt _ _ l'.path r'.path diff
      (l'.shape.trans r'.shape.symm) l'.leafRows r'.leafRows l'.pathRows r'.pathRows (l'.root.trans r'.root.symm)
end CommitGolfCandidate.Pw
