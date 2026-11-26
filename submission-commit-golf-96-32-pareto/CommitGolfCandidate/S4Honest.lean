import CommitGolfCandidate.S4Decode
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)

private theorem recordTotal (ps : Positions) (t : Levels) (s : SaltTape) (b : Bool) :
    ((ps.sort (·≤·)).flatMap (mainRecord b t s)).length=ps.card*recordBytes b := by
  simp only [List.length_flatMap];rw [show ((ps.sort (·≤·)).map fun i=>(mainRecord b t s i).length)=
    List.replicate ps.card (recordBytes b) by simp only [mainRecordSize,List.map_const',Finset.length_sort]]
  simp [Nat.mul_comm]

private theorem appendTail {whole : Proof} {off : Nat} {part : Proof} (e : ContainsAt whole off part) (tail : Proof) :
    ContainsAt (whole++tail) off part:=by
  obtain ⟨a,b,ha,h⟩:=e
  exact ⟨a,b++tail,ha,by rw [h];simp [List.append_assoc]⟩

private theorem addPrefix {whole : Proof} {off : Nat} {part : Proof} (e : ContainsAt whole off part) (head : Proof) :
    ContainsAt (head++whole) (head.length+off) part:=by
  obtain ⟨a,b,ha,h⟩:=e
  exact ⟨head++a,b,by simp [ha],by rw [h];simp [List.append_assoc]⟩

theorem slotSegment (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (batch : ps.card=BATCH) (j : Nat) (bj : j<171) :
    ContainsAt (opening .byte t s ps) (65280+30*j) (bytes (n:=30) ((pairSlot t (ps.sort (·≤·)) j).setWidth 240)) := by
  let xs:=ps.sort (·≤·)
  let slot (i : Nat) :=pairSlot t xs i
  let f (i : Nat) :=mainBytes (bits .byte 16,slot i)
  have len (i : Nat) : (f i).length=30:=by simp only [f,mainBytes,List.length_map,List.length_range];decide
  have seg:=flat_field (List.range 171) f 30 len j (by rw [List.length_range];exact bj)
  rw [List.getElem_range] at seg
  have pre:=recordTotal ps t s true
  rw [batch] at pre;change (xs.flatMap (mainRecord true t s)).length=65280 at pre
  let x:=canonicalInput m ps t s
  suffices field : ContainsAt x.proof (65280+30*j) (bytes (n:=30) ((slot j).setWidth 240)) from field
  change ContainsAt (opening .byte t s ps) _ _
  unfold opening;dsimp only;rw [if_pos batch];unfold serialize
  simp only [List.flatMap_append,List.flatMap_assoc,List.flatMap_map]
  change ContainsAt (xs.flatMap (mainRecord true t s) ++ (List.range 171).flatMap f ++ _) _ _
  have bytesEq : f j=bytes (n:=30) ((slot j).setWidth 240):=baseField 30 _
  rw [bytesEq] at seg
  have upto:=addPrefix seg (xs.flatMap (mainRecord true t s))
  rw [pre] at upto
  exact appendTail upto _

private theorem slotParsed (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (tree : HonestTree .packed H m s t) (batch : ps.card=BATCH) (j : Nat) (bj : j<171) :
    (readView (canonicalInput m ps t s)).slot j=pairSlot t (ps.sort (·≤·)) j := by
  let xs:=ps.sort (·≤·)
  let slot (i : Nat) :=pairSlot t xs i
  let f (i : Nat) :=mainBytes (bits .byte 16,slot i)
  have len (i : Nat) : (f i).length=30:=by simp only [f,mainBytes,List.length_map,List.length_range];decide
  have seg:=flat_field (List.range 171) f 30 len j (by rw [List.length_range];exact bj)
  rw [List.getElem_range] at seg
  have pre:=recordTotal ps t s true
  rw [batch] at pre;change (xs.flatMap (mainRecord true t s)).length=65280 at pre
  let x:=canonicalInput m ps t s
  have field : ContainsAt x.proof (65280+30*j) (bytes (n:=30) ((slot j).setWidth 240)):=by
    change ContainsAt (opening .byte t s ps) _ _
    unfold opening;dsimp only;rw [if_pos batch];unfold serialize
    simp only [List.flatMap_append,List.flatMap_assoc,List.flatMap_map]
    change ContainsAt (xs.flatMap (mainRecord true t s) ++ (List.range 171).flatMap f ++ _) _ _
    have bytesEq : f j=bytes (n:=30) ((slot j).setWidth 240):=baseField 30 _
    rw [bytesEq] at seg
    have upto:=addPrefix seg (xs.flatMap (mainRecord true t s))
    rw [pre] at upto
    exact appendTail upto _
  have size : x.proof.length≤17179869184:=by change (opening .byte t s ps).length≤_;rw [openingSize,if_pos batch];decide
  have parsedSlot:=parsed field size
  change (proofAt x _ 30).setWidth 256=slot j
  rw [parsedSlot]
  unfold slot pairSlot
  cases e : xs.find? (fun i=>nodeIndex i.val 16==j) with
  | none=>exact nodeRoundtrip H m s t tree 16 j (by decide) (by decide)
  | some i=>exact nodeRoundtrip H m s t tree 15 _ (by decide) (by decide)

theorem honestValid (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (tree : HonestTree .packed H m s t) : wireValid H (canonicalInput m ps t s) := by
  let v:=readView (canonicalInput m ps t s)
  change (if ps.card=BATCH then (opening .byte t s ps).length=70410 ∧ BatchValid .packed H v (node t 24 0)
    else (opening .byte t s ps).length=ps.card*824 ∧
      ∀ r<ps.card,recordAt .packed H v r 24 (v.peers r)=node t 24 0)
  by_cases hb : ps.card=BATCH
  · rw [if_pos hb]
    refine ⟨by rw [openingSize,if_pos hb];rfl,?_⟩
    apply honestBatch .packed H m s t tree v
    · intro r br
      simpa only [hb,ite_true] using decodedRecord H m ps t s tree r (by simpa only [hb,BATCH] using br)
    · exact canonicalSlots t ps hb v rfl (slotParsed H m ps t s tree hb)
  · rw [if_neg hb]
    refine ⟨by rw [openingSize,if_neg hb,Nat.mul_comm],?_⟩
    intro r br
    obtain ⟨salt,value,peers⟩:=decodedRecord H m ps t s tree r br
    rw [if_neg hb] at peers
    have e:=honestRecord .packed H m s t tree v r 24 (by decide) salt value peers
    have ix : nodeIndex (v.idx r).val 24<1:=indexInside _ _
    simpa only [show nodeIndex (v.idx r).val 24=0 by omega] using e
end CommitGolfCandidate.S4
