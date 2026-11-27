import CommitGolfCandidate.Stage3cAuth
namespace CommitGolfCandidate.Pw.Auth
open CommitGolf
open Late (Digest SaltTape Levels node)

/-- The 96-byte input row of a binary parent: zero third block, right child, left child.
The third argument is kept for the S5 row shape and is ignored. -/
def row (_d : Nat) (a b _c : Digest) : Late.Block := (0 : Digest) ++ b ++ a

theorem row_block (d : Nat) (a b c : Digest) : row d a b c=Late.parentBlock a b := rfl

theorem row_parent (H : Compression) (d : Nat) (a b c : Digest) :
    compressRow H (d+1) (row d a b c)=Chained.parentDigest H (height d) a b := by
  have lo : (row d a b c).extractLsb' 0 256=a := BitVec.extractLsb'_append_eq_right
  have mid : (row d a b c).extractLsb' 256 256=b := by
    have middle (z a b : BitVec 256) : (z++b++a).extractLsb' 256 256=b :=
      (BitVec.extractLsb'_append_eq_of_le (xhi:=z++b) (xlo:=a) (start:=256) (len:=256) le_rfl).trans
        BitVec.extractLsb'_append_eq_right
    exact middle _ a b
  simp [compressRow,lo,mid]
end CommitGolfCandidate.Pw.Auth
