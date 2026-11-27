import CommitGolfCandidate.Stage3cGeometry
import CommitGolfCandidate.Stage3cScheme
import CommitGolfCandidate.Stage3cFieldWidths
/-! Lanes and peers of the binary checker model. A record carries one sibling per level;
the second peer component is unused (zero) and kept so that rows have the S5 shape. -/
namespace CommitGolfCandidate.Pw
open CommitGolf Chained
open Late (Digest Block Salt)

abbrev height (d : Nat) : Height := Binary.height d
def bits : Nat→Nat | 0=>256 | n+1=>Chained.wireWidth (height n)
theorem bits_eq (d : Nat) : bits d=BinaryMachine.levelBits d := by cases d <;> rfl

inductive Lane | bl | br deriving DecidableEq,Repr
def lane (_h i : Nat) : Lane := if i%2=0 then .bl else .br

abbrev Peers := Digest × Digest
def payload (d : Lane) (v : Digest) (p : Peers) : Block :=
  match d with
  | .bl => Late.parentBlock v p.1
  | .br => Late.parentBlock p.1 v

private theorem appendParts {m n : Nat} {a c : BitVec m} {b d : BitVec n} (e : a++b=c++d) : a=c ∧ b=d := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (fun x : BitVec (m+n)=>x.extractLsb' n m) e
  · simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (fun x : BitVec (m+n)=>x.extractLsb' 0 n) e
theorem slotInjective (d : Lane) (v w : Digest) (a b : Peers) (e : payload d v a=payload d w b) : v=w := by
  cases d
  · exact (appendParts e).2
  · exact (appendParts (appendParts e).1).2
end CommitGolfCandidate.Pw
