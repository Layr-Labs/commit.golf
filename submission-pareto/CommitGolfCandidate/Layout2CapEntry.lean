import CommitGolfCandidate.Layout2CapTables
import CommitGolfCandidate.Layout2Helpers
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf Layout2Helpers
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
def u16 (j : Nat) := pget K1Artifact.checkData j+256*pget K1Artifact.checkData (j+1)
def u32 (j : Nat) := u16 j+65536*u16 (j+2)
def checkEntry (m i : Nat) : Bool :=
  let d:=dec m i
  let e:=enc m i
  (d<8*size m) && (e<8*size m) && (enc m d==i) && (dec m e==i) && (u16 (offset m+2*i)==d)
def scan (m start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkEntry m (start+n) && scan m start n

theorem in_scan (m start n : Nat) (ok : scan m start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : checkEntry m i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [scan,Bool.and_eq_true] at ok
    by_cases last : i=start+n
    · simpa [last] using ok.1
    · exact ih ok.2 (by omega)
end CommitGolfCandidate.Layout2.Cap
