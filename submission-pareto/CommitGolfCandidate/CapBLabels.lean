import CommitGolfCandidate.CapBSymbol
namespace CommitGolfCandidate.CapB.Symbol
set_option maxRecDepth 16000
def oldTags (m i : Nat) :=
  let g:=i/1904;let j:=i%1904/240;let b:=i%1904%240
  if b<238 then [256*(8*g+j)+b] else if g<m/8 then [256*(8*g+7)+(224+2*j+(b-238))] else []

def compareAt (m i : Nat) := tags m i == oldTags m (Layout2.Cap.enc m i)
def scan (m start : Nat) : Nat→Bool
  | 0=>true
  | n+1=>compareAt m (start+n) && scan m start n
theorem in_scan (m start n : Nat) (ok : scan m start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : compareAt m i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [scan,Bool.and_eq_true] at ok
    by_cases last : i=start+n
    · simpa [last] using ok.1
    · exact ih ok.2 (by omega)
end CommitGolfCandidate.CapB.Symbol
