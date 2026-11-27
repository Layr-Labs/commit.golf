import CommitGolfCandidate.Stage3cReplayWalk
import CommitGolfCandidate.Stage3cWire
set_option Elab.async false
namespace CommitGolfCandidate.Pw.Replay
open CommitGolf OracleComp
open Chained (Input Output)
open Chained.Replay (PublicRow rowReads rowPath)
def pathWeight (h n : Nat):=((List.range' h n).map fun d=>Chained.calls (height d)).sum
theorem path_weight (i : Index) (data : Nat→Peers) (h n : Nat) : weight (pathOf i data h n)=pathWeight h n:=by
  simp only [weight,pathOf,List.map_map,Function.comp_def,stepOf,pathWeight]
/-- Four leaf calls, then the parent calls of the first `n` binary levels. -/
def recordCost (n : Nat) :=4+pathWeight 0 n

def recordCode (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) : Code (recordCost n) Output :=
  let i:=v.idx r
  let leaf:=leafCode (i.val.testBit 0) (v.salt r) (v.entry r)
  widen (join leaf (fun d=>walkCode d (pathOf i data 0 n))) (by rw [path_weight];unfold recordCost;omega)

theorem leaf_walk (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    Chained.walk H (Late.leaf H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r)) (pathOf (v.idx r) data 0 n)=
      Auth.recordAt H v r n data := by
  unfold Auth.recordAt
  have w:=model_walk H (v.idx r) (Late.leaf H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r)) data 0 n
  rw [Nat.zero_add] at w;exact w
theorem record_value (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    (recordCode v r data n).value H=Auth.recordAt H v r n data :=
  (walk_value H _ (pathOf (v.idx r) data 0 n)).trans (leaf_walk H v r data n)

theorem record_inputs (H : Compression) (v : Auth.View) (r : Nat) (data : Nat→Peers) (n : Nat) :
    (recordCode v r data n).inputs H=List.append (α:=Input) (Late.inputs H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r))
      ((walkCode (Late.leaf H ((v.idx r).val.testBit 0) (v.salt r) (v.entry r)) (pathOf (v.idx r) data 0 n)).inputs H) := by
  rfl

theorem records_path (H : Compression) (x : CheckInput) (v : Auth.View) (r : Nat) (i : Index) (mem : i∈x.positions)
    (index : v.idx r=i) (entry : v.entry r=x.values ⟨i,mem⟩) (data : Nat→Peers) (root : Auth.recordAt H v r 24 data=x.commitment)
    (table : List PublicRow) (reads : ∀ q∈(recordCode v r data 24).inputs H,PublicRow.compression q (H q)∈table) :
    Nonempty (RecordedPath H x i mem table) := by
  subst i
  let i:=v.idx r
  let path:=pathOf i data 0 24
  rw [record_inputs] at reads
  have leaf : rowReads table H (Late.inputs H (i.val.testBit 0) (v.salt r) (v.entry r)) :=
    fun q h=>reads _ (List.mem_append_left _ h)
  have rest : rowPath table H (Late.leaf H (i.val.testBit 0) (v.salt r) (v.entry r)) path:=
    walk_rows H _ _ table (fun q h=>reads _ (List.mem_append_right _ h))
  have out : Chained.walk H (Late.leaf H (i.val.testBit 0) (v.salt r) (v.entry r)) path=x.commitment:=
    (leaf_walk H v r data 24).trans root
  refine ⟨⟨v.salt r,path,?_,?_,?_,?_⟩⟩
  · simp only [path,pathOf,upperShape,List.map_map,Function.comp_def,stepOf,i,List.range_eq_range']
  · rw [←entry];exact leaf
  · rw [←entry];exact rest
  · rw [←entry];exact out

theorem proof_queries : recordCost 24=100 ∧ recordCost 15=76:=by decide +kernel
end CommitGolfCandidate.Pw.Replay
