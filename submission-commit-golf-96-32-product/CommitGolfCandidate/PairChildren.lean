import CommitGolfCandidate.Model

namespace CommitGolfCandidate.PairCap
open CommitGolf

/-- A missing child has no record at that level-8 node. A populated child
stores the unique digest agreed upon by every record at that node. -/
structure Children where
  left : Option Digest
  right : Option Digest
deriving DecidableEq

def Children.child (p : Children) (right : Bool) : Option Digest :=
  if right then p.right else p.left

def Children.write (p : Children) (right : Bool) (d : Digest) : Option Children :=
  match p.child right with
  | none => some (if right then { p with right := some d } else { p with left := some d })
  | some old => if old = d then some p else none

theorem write_agrees {p p' : Children} {r : Bool} {d : Digest}
    (wrote : p.write r d = some p') : p'.child r = some d := by
  rcases p with ⟨l,h⟩
  cases r <;> cases l <;> cases h <;> simp_all [Children.write, Children.child]
  all_goals grind

theorem write_preserves {p p' : Children} {r s : Bool} {d e : Digest}
    (already : p.child s = some e) (wrote : p.write r d = some p') :
    p'.child s = some e := by
  unfold Children.write at wrote
  split at wrote
  · simp only [Option.some.injEq] at wrote
    subst p'
    cases r <;> cases s <;> simp_all [Children.child]
  · split at wrote
    · cases wrote; exact already
    · contradiction

def Children.parent (p : Children) (H : Compression) (slot : Digest) : Digest :=
  match p.left, p.right with
  | none, none => slot
  | some l, none => combine H l slot
  | none, some r => combine H slot r
  | some l, some r => combine H l r

/-- The one missing step in an ordinary record is its partner, taken from a
verified record when present and from the supplied pair slot otherwise. -/
def Children.sibling (p : Children) (right : Bool) (slot : Digest) : Digest :=
  (p.child (!right)).getD slot

theorem parent_on_path {p : Children} {right : Bool} {d : Digest}
    (atChild : p.child right = some d) (H : Compression) (slot : Digest) :
    (if right then combine H (p.sibling right slot) d else combine H d (p.sibling right slot)) =
      p.parent H slot := by
  rcases p with ⟨l,r⟩
  cases right <;> cases l <;> cases r <;>
    simp_all [Children.parent, Children.sibling, Children.child]

end CommitGolfCandidate.PairCap
