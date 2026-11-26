import CommitGolfCandidate.S4RecordWire
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)
attribute [local irreducible] List.range List.finRange

theorem sane (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) :
    (canonicalInput m ps t s).proof.length≤17179869184 := by
  change (opening .byte t s ps).length≤_
  rw [openingSize];have bound : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at bound
  split <;> simp <;> omega

theorem recordSegment (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (r : Nat) (br : r<ps.card) :
    let b:=decide (ps.card=BATCH)
    ContainsAt (canonicalInput m ps t s).proof (r*recordBytes b) (mainRecord b t s (recordIndex ps r)) := by
  let xs:=ps.sort (·≤·)
  let b:=decide (ps.card=BATCH)
  have rb : r<xs.length:=by simpa only [xs,Finset.length_sort] using br
  have index : recordIndex ps r=xs[r]:=by unfold recordIndex;rw [List.getElem?_eq_getElem rb];rfl
  have seg:=flat_field xs (mainRecord b t s) (recordBytes b) (mainRecordSize b t s) r rb
  rw [Nat.mul_comm (recordBytes b) r,←index] at seg
  obtain ⟨l,h,ll,eq⟩:=seg
  change ContainsAt (opening .byte t s ps) _ _
  by_cases yes : ps.card=BATCH
  · have bb : b=true:=decide_eq_true yes
    rw [bb] at eq ll
    unfold opening;dsimp only;rw [if_pos yes];unfold serialize
    simp only [List.flatMap_append,List.flatMap_assoc]
    change ContainsAt (xs.flatMap (mainRecord true t s) ++ _ ++ _) _ _
    rw [eq];refine ⟨l,_,?_,by simp only [List.append_assoc,decide_eq_true yes];rfl⟩
    simpa only [b,yes,decide_true] using ll
  · have bb : b=false:=decide_eq_false yes
    rw [bb] at eq ll
    unfold opening;dsimp only;rw [if_neg yes];unfold serialize
    simp only [List.flatMap_assoc]
    change ContainsAt (xs.flatMap (mainRecord false t s) ++ _) _ _
    rw [eq];refine ⟨l,_,?_,by simp only [List.append_assoc,decide_eq_false yes];rfl⟩
    simpa only [b,decide_eq_false yes] using ll


end CommitGolfCandidate.S4
