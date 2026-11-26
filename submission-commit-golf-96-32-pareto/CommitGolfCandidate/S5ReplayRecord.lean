import CommitGolfCandidate.S5ReplayWalk
import CommitGolfCandidate.S5Wire
namespace CommitGolfCandidate.S5.Replay
open CommitGolf OracleComp
open Chained (Input Output)
open Chained.Replay (PublicRow rowReads rowPath)
def pathWeight (h n : Nat):=((List.range' h n).map fun d=>Chained.calls (height d)).sum
theorem path_weight (i : Index) (data : Nat→Peers) (h n : Nat) : weight (pathOf i data h n)=pathWeight h n:=by
  simp only [weight,pathOf,List.map_map,Function.comp_def,stepOf,pathWeight]
def recordCost (n : Nat) :=5+pathWeight 1 n

def recordCode (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) : Code (recordCost n) Output :=
  let i:=v.idx r
  let leaf:=leafCode (i.val.testBit 0) (v.salt r) (v.entry r)
  widen (join leaf (fun d=>join (ask (payload (lane 0 i.val) d (data 0))) (fun y=>walkCode y (pathOf i data 1 n))))
    (by rw [path_weight];unfold recordCost;omega)
def bottomInput (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) : Input :=
  let i:=v.idx r
  payload (lane 0 i.val) (Late.leaf H (i.val.testBit 0) (v.salt r) (v.entry r)) (data 0)
private theorem bottom_value (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) :
    H (bottomInput H v r data)=Auth.recordAt H v r 1 data := by
  unfold Auth.recordAt;rw [Auth.walk];simp only [Auth.walk,Auth.compressRow,ite_true,S4.nodeIndex,S4.span,
    ite_true,Nat.div_one,pow_zero,Nat.mul_one];rfl
theorem bottom_walk (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    Chained.walk H (H (bottomInput H v r data)) (pathOf (v.idx r) data 1 n)=Auth.recordAt H v r (n+1) data := by
  apply (congrArg (fun y : Output=>Chained.walk H y (pathOf (v.idx r) data 1 n)) (bottom_value H v r data)).trans
  unfold Auth.recordAt
  simpa only [Nat.add_comm 1 n] using model_walk H (v.idx r) (Late.leaf H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r)) data 1 n (by decide)
theorem record_value (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    (recordCode v r data n).value H=Auth.recordAt H v r (n+1) data :=
  (walk_value H (H (bottomInput H v r data)) (pathOf (v.idx r) data 1 n)).trans (bottom_walk H v r data n)

theorem record_inputs (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    (recordCode v r data n).inputs H=List.append (α:=Input) (Late.inputs H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r))
      ([bottomInput H v r data]++(walkCode (H (bottomInput H v r data)) (pathOf (v.idx r) data 1 n)).inputs H) := by
  rfl

theorem records_path (H : Compression) (x : CheckInput) (v : Auth.View) (r : Nat) (i : Index) (mem : i∈x.positions)
    (index : v.idx r=i) (entry : v.entry r=x.values ⟨i,mem⟩) (data : Nat→Peers) (root : Auth.recordAt H v r 24 data=x.commitment)
    (table : List PublicRow) (reads : ∀ q∈(recordCode v r data 23).inputs H,PublicRow.compression q (H q)∈table) :
    Nonempty (RecordedPath H x i mem table) := by
  subst i
  let i:=v.idx r
  let bottom:=bottomInput H v r data
  let path:=pathOf i data 1 23
  rw [record_inputs] at reads
  have leaf : rowReads table H (Late.inputs H (i.val.testBit 0) (v.salt r) (v.entry r)) :=
    fun q h=>reads _ (List.mem_append_left _ h)
  have first : PublicRow.compression bottom (H bottom)∈table:=reads bottom (List.mem_append_right _ (by simp [bottom]))
  have rest : rowPath table H (H bottom) path:=walk_rows H _ _ table (fun q h=>reads _ (List.mem_append_right _ (List.mem_append_right _ h)))
  have out : Chained.walk H (H bottom) path=x.commitment:=(bottom_walk H v r data 23).trans root
  refine ⟨⟨v.salt r,data 0,path,?_,?_,?_,?_,?_⟩⟩
  · simp only [path,pathOf,upperShape,List.map_map,Function.comp_def,stepOf,i]
  · rw [←entry];exact leaf
  · rw [←entry];exact first
  · rw [←entry];exact rest
  · rw [←entry];exact out

theorem proof_queries : recordCost 23=100 ∧ recordCost 14=76:=by decide +kernel
end CommitGolfCandidate.S5.Replay
