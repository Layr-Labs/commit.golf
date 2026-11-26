import CommitGolfCandidate.S4SaltDecode
import CommitGolfCandidate.S4Roundtrip
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)
attribute [local irreducible] List.range List.finRange

attribute [local irreducible] opening proofAt node sibling Late.leaf
theorem recPeer (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (tree : HonestTree .byte H m s t) (r h n : Nat) (br : r<ps.card)
    (bh : h<(if ps.card=BATCH then 15 else 24)) (bn : n<radix h-1) :
    let b:=decide (ps.card=BATCH)
    let start:=r*recordBytes b+fieldOffset b h+32*n
    (proofAt (canonicalInput m ps t s) start (fieldBytes b h)).setWidth 256=sibling t (recordIndex ps r).val h n := by
  let b:=decide (ps.card=BATCH)
  let x:=canonicalInput m ps t s
  let digest:=sibling t (recordIndex ps r).val h n
  have level : h<(if b then 15 else 24):=by simpa only [b,decide_eq_true_eq] using bh
  have mem:=(recordSegment m ps t s r br).trans (mainSibling b t s (recordIndex ps r) h n level bn)
  have read:=parsed mem (sane ..)
  simp only [Nat.add_assoc] at read ⊢
  rw [read]
  by_cases short : b && decide (1<h)
  · have step : 2≤h:=by have hp:=Bool.and_eq_true_iff.mp short;exact of_decide_eq_true hp.2
    have top : h<24:=by split at bh <;> omega
    rw [show fieldBytes b h=30 from if_pos short]
    unfold sibling;exact nodeRoundtrip H m s t tree h _ step top
  · rw [fieldBytes,if_neg short];rfl


end CommitGolfCandidate.S4
