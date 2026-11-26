import CommitGolfCandidate.TwoPermutationHybridPaths
namespace TwoPermutationPrototype.Packed
open CommitGolf CommitGolfCandidate Sampling TwoPermutationPrototype.Checker
open CommitGolfCandidate.ShortTree
inductive CapPath238 (rows : List PublicRow) : Nat → Nat → BitVec 256 → BitVec 256 → Prop where
  | done (node : Nat) (digest : BitVec 256) : CapPath238 rows node 0 digest digest
  | step {node height : Nat} {child parent sibling root : BitVec 256}
      (call : PublicRow.compression (pathPair node child sibling) parent ∈ rows)
      (next : CapPath238 rows (node / 2) height (Hybrid.pad238 parent) root) :
      CapPath238 rows node (height + 1) child root

theorem CapPath238.mono {first last : List PublicRow} {node height : Nat}
    {start finish : BitVec 256} (path : CapPath238 first node height start finish)
    (contained : ∀ row ∈ first, row ∈ last) : CapPath238 last node height start finish := by
  induction path with
  | done node digest => exact .done node digest
  | step call _ ih => exact .step (contained _ call) ih

theorem CapPath238.append {rows : List PublicRow} {node m n : Nat} {start middle finish : BitVec 256}
    (first : CapPath238 rows node m start middle)
    (last : CapPath238 rows (node / 2 ^ m) n middle finish) :
    CapPath238 rows node (m + n) start finish := by
  induction first with
  | done node digest =>
    simpa using last
  | @step node height child parent sibling root call next ih =>
    have address : node / 2 ^ (height + 1) = (node / 2) / 2 ^ height := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    rw [address] at last
    rw [show height + 1 + n = (height + n) + 1 by omega]
    exact .step call (ih last)

end TwoPermutationPrototype.Packed
