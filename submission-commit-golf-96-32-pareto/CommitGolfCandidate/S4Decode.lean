import CommitGolfCandidate.S4PeerDecode
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)
attribute [local irreducible] List.range List.finRange

attribute [local irreducible] opening proofAt node sibling Late.leaf
private theorem fullRead (x : CheckInput) (b : Bool) (off : Nat) :
    (proofAt x off (fieldBytes b 0)).setWidth 256=proofAt x off 32 := by
  cases b <;> exact BitVec.setWidth_eq _

theorem decodedRecord (H : Compression) (m : Message) (ps : Positions) (t : Levels) (s : SaltTape)
    (tree : HonestTree .byte H m s t) (r : Nat) (br : r<ps.card) :
    let v:=readView (canonicalInput m ps t s)
    v.salt r=s (v.idx r) ∧ v.entry r=m (v.idx r) ∧
      ∀ h<(if ps.card=BATCH then 15 else 24),v.peers r h=truePeers t (v.idx r) h := by
  refine ⟨recSalt _ _ _ _ _ br,honestValue _ _ _ _ _ br,?_⟩
  intro h bh
  have p0:=recPeer H m ps t s tree r h 0 br bh (by unfold radix;split <;> decide)
  apply Prod.ext
  · exact p0
  · by_cases z : h=0
    · subst h
      let x:=canonicalInput m ps t s
      let b:=decide (ps.card=BATCH)
      let off:=r*recordBytes b+fieldOffset b 0+32
      have p1:=recPeer H m ps t s tree r 0 1 br bh (by decide)
      exact (fullRead x b off).symm.trans p1
    · simp only [readView,canonicalInput,truePeers,if_neg z]

end CommitGolfCandidate.S4
