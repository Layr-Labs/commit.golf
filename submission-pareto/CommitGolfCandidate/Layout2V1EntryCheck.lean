import CommitGolfCandidate.GroupOpenTable
import CommitGolfCandidate.Layout2Tables

namespace CommitGolfCandidate.Layout2
open CommitGolf
open TwoPermutationPrototype.GroupedOpening (pget pget_get)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000

/-- Read both bytes directly from the delivered packed tree. The u16 range and table
value are checked together, so the physical data establishes the required safety bound. -/
def entryCheck (r i : Nat) : Bool :=
  let off:=tableOffset r+2*i
  let v:=decTables r i
  decide (v<4272*r) && (pget K1Artifact.checkData off+256*pget K1Artifact.checkData (off+1)==v)

def entriesCheck (r first : Nat) : Nat→Bool
  | 0 => true
  | n+1 => entryCheck r (first+n) && entriesCheck r first n

theorem entries_sound (r startIndex n : Nat) (ok : entriesCheck r startIndex n = true)
    (i : Nat) (lo : startIndex ≤ i) (hi : i < startIndex + n) : entryCheck r i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [entriesCheck, Bool.and_eq_true] at ok
    by_cases last : i = startIndex + n
    · simpa only [last] using ok.1
    · exact ih ok.2 (by omega)

end CommitGolfCandidate.Layout2
