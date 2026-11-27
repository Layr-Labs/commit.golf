import CommitGolfCandidate.Stage3cReplayCap
set_option Elab.async false
namespace CommitGolfCandidate.Pw.Replay
open CommitGolf OracleComp
open Chained (Input)
open Chained.Replay (PublicRow recordRows)
def allRecords (v : Auth.View) (data : Nat→Nat→Peers) (n : Nat) : Code (n*100) Unit :=
  widen (foreach (fun r=>map (fun _=>()) (recordCode v r (data r) 24)) (List.range n)) (by rw [List.length_range,proof_queries.1])
def batchBudget:=128*recordCost 15+(256*16+8*(256*16))+128*100
def batchReplay (x : CheckInput) : Code batchBudget Unit :=
  let v:=batchView x
  join (recover v) (fun data=>allRecords v data 128)
def replay (x : CheckInput) : Code (2^31) Unit :=
  if x.positions.card=BATCH then widen (batchReplay x) (by decide +kernel)
  else widen (allRecords (plainView x) (plainView x).peers x.positions.card) (by
    have upper : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
    change x.positions.card≤16777216 at upper;omega)
theorem per_record {H : Compression} {v : Auth.View} {data : Nat→Nat→Peers} {n r : Nat} (inside : r<n) {q : Input}
    (ev : q∈(recordCode v r (data r) 24).inputs H) : q∈(allRecords v data n).inputs H := by
  apply foreach_mem (fun r=>map (fun _=>()) (recordCode v r (data r) 24)) (List.range n) H (List.mem_range.mpr inside)
  rw [map_inputs];exact ev

attribute [local irreducible] recover allRecords recordCode
set_option maxRecDepth 12000 in
theorem replay_valid (o : Oracle) (x : CheckInput) (valid : wireValid o.compression x) (i : Index) (present : i∈x.positions) :
    Nonempty (RecordedPath o.compression x i present (rows o.compression ((replay x).inputs o.compression))) := by
  let H:=o.compression
  obtain ⟨r,inside,index,entry⟩:=selected x i present
  have add {z : Input} (has : z∈(replay x).inputs H) : PublicRow.compression z (H z)∈rows H ((replay x).inputs H) :=
    List.mem_map.mpr ⟨z,has,rfl⟩
  by_cases yes : x.positions.card=BATCH
  · rw [wireValid,if_pos yes] at valid
    obtain ⟨_,accept⟩:=valid
    let v:=batchView x
    let data:=(recover v).value H
    have row : r<128:=by rw [yes] at inside;exact inside
    have root : Auth.recordAt H v r 24 (data r)=x.commitment:=by
      apply Eq.trans _ (Auth.batchImpliesRoot H v _ accept r row)
      exact Auth.walk_congr H (v.idx r).val _ _ _ 24 (fun h bound=>recover_value H v r h bound)
    apply records_path H x v r i present index entry (data r) root
    intro z hz
    apply add
    unfold replay;rw [if_pos yes]
    change z∈(recover v).inputs H++(allRecords v data 128).inputs H
    exact List.mem_append_right _ (per_record row hz)
  · rw [wireValid,if_neg yes] at valid
    let v:=plainView x
    apply records_path H x v r i present index entry (v.peers r) (valid.2 r inside)
    intro z hz;apply add;unfold replay;rw [if_neg yes]
    exact per_record inside hz

def replay_of_wire (sound : ∀ (o : Oracle) (x : CheckInput),
    (o.eval (Artifact.submission.scheme.check x.commitment x.positions x.values x.proof)).1=true → wireValid o.compression x) :
    CheckReplay Artifact.submission.scheme where
  run x:=(replay x).program
  cost x:=(replay x).cost
  sound o x ok result reach i present:=by
    rw [(replay x).correct o,support_pure,Set.mem_singleton_iff] at reach
    subst result;exact replay_valid o x (sound o x ok) i present

theorem replay_size : batchBudget=59392 := by decide +kernel
end CommitGolfCandidate.Pw.Replay
