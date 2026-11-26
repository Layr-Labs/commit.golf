import CommitGolfCandidate.S4RecordSegment
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)
attribute [local irreducible] List.range List.finRange

attribute [local irreducible] opening proofAt node sibling Late.leaf
theorem recSalt (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (r : Nat) (br : r<ps.card) :
    (readView (canonicalInput m ps t s)).salt r=s (recordIndex ps r) := by
  let b:=decide (ps.card=BATCH)
  change proofAt (canonicalInput m ps t s) (r*recordBytes b) 24=s (recordIndex ps r)
  have field := (recordSegment m ps t s r br).trans (mainSalt b t s (recordIndex ps r))
  rw [Nat.add_zero] at field
  exact parsed field (sane m ps t s)


end CommitGolfCandidate.S4
