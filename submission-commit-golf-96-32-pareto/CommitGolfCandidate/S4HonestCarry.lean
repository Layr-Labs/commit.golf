import CommitGolfCandidate.S4Honest
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)
attribute [local irreducible] List.range List.finRange
private theorem readLast (xs : Proof) (a : Nat) (w : Digest)
    (seg : ContainsAt xs a (bytes (n:=30) (w.setWidth 240))) :
    Carry.read xs (a+29)=w.extractLsb' 232 8 := by
  obtain ⟨l,r,ll,rfl⟩:=seg
  have mem : 29<(bytes (n:=30) (w.setWidth 240)).length:=by simp [bytes]
  unfold Carry.read
  rw [List.append_assoc,List.getElem?_append_right (by omega),ll,Nat.add_sub_cancel_left,
    List.getElem?_append_left mem,List.getElem?_eq_getElem mem,Option.getD_some]
  change (w.setWidth 240).extractLsb' 232 8=w.extractLsb' 232 8
  exact BitVec.extractLsb'_setWidth_of_le (by decide)

theorem actualCanonical (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (tree : HonestTree .packed H m s t) (batch : ps.card=BATCH) :
    Carry.Canonical (Carry.read (opening .byte t s ps)) := by
  let f:=Carry.read (opening .byte t s ps)
  have size : ps.card=128:=batch
  have slot (j : Nat) (hj : j<171) :
      Carry.lower (f (65280+30*j+29))=f (65280+30*j+29) := by
    dsimp only [f];rw [readLast _ _ _ (slotSegment H m ps t s batch j hj)]
    unfold pairSlot
    split
    · exact nodeHighByte H m s t tree 16 _ (by decide) (by decide)
    · exact nodeHighByte H m s t tree 15 _ (by decide) (by decide)
  constructor
  · intro c hc
    change Carry.lower (f (Carry.carrier c))=f (Carry.carrier c)
    by_cases standard : c<1152
    · let r:=c/9
      let h:=6+c%9
      have br : r<ps.card:=by dsimp [r];omega
      have lo : 6≤h:=by dsimp [h];omega
      have bh : h<15:=by dsimp [h];omega
      have recSeg:=recordSegment m ps t s r br
      simp only [decide_eq_true batch] at recSeg
      have field:=mainSibling true t s (recordIndex ps r) h 0 bh (by unfold radix;rw [if_neg (by omega : h≠0)];decide)
      have sz : fieldBytes true h=30:=by simp only [fieldBytes,Bool.true_and,decide_eq_true (by omega : 1<h)];rfl
      rw [sz] at field
      have piece:=recSeg.trans field
      change ContainsAt (opening .byte t s ps) _ (bytes (n:=30) ((sibling t (recordIndex ps r).val h 0).setWidth 240)) at piece
      have atByte : Carry.carrier c=r*recordBytes true+(fieldOffset true h+32*0)+29:=by
        unfold Carry.carrier recordBytes fieldOffset
        simp only [if_pos standard,ite_true,if_neg (by omega : h≠0),Bool.true_and,decide_eq_true (by omega : 1<h)]
        dsimp only [r,h];omega
      dsimp only [f];rw [atByte,readLast _ _ _ piece]
      exact nodeHighByte H m s t tree h _ lo (by omega)
    · have off : Carry.carrier c=65280+30*(c-1152)+29:=by rw [Carry.carrier,if_neg standard];omega
      rw [off];exact slot (c-1152) (by omega)
  · intro k hk last
    change Carry.lower (f _) = f _
    have off : 70080+k=65280+30*(160+k/30)+29:=by omega
    rw [off];exact slot _ (by omega)

def actualInput (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) : CheckInput :=
  ⟨node t LOG_LENGTH 0,ps,m.restrict ps,actualOpening t s ps⟩

theorem widenHonest (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (tree : HonestTree .packed H m s t) :
    wideInput (actualInput m ps t s)=canonicalInput m ps t s := by
  unfold wideInput actualInput canonicalInput
  simp only [actualOpening]
  by_cases b : ps.card=BATCH
  · simp only [if_pos b,Carry.packed_length,ite_true]
    rw [Carry.inverse _ (by rw [openingSize,if_pos b];rfl) (actualCanonical H m ps t s tree b)]
  · simp only [if_neg b]

end CommitGolfCandidate.S4
