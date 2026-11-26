import CommitGolfCandidate.ReconstructedCheckParent
import CommitGolfCandidate.ReconstructedBindingPaths

namespace CommitGolfCandidate.Reconstruction.CheckPath
open CommitGolf Binding TwoPermutationPrototype.Sampling

/-- An upward checker step records the child selected by the position, its
revealed sibling, the computed parent, and the public calls used by the parent. -/
structure Edge (o : Oracle) (log : List PublicRow) (depth : Nat) (side : Bool) (child par : Binding.Digest) where
  left : Binding.Digest
  right : Binding.Digest
  leftCanonical : Canonical (depth+1) left
  rightCanonical : Canonical (depth+1) right
  choose : (if side then right else left)=child
  value : parent (oracleCompression o) depth left right=par
  observed : CheckParentExecution.rows o (pairKey (depth+1) left right) 0 (work depth) ⊆ log

theorem Edge.extend {o : Oracle} {log : List PublicRow} {depth : Nat} {side : Bool} {child par : Binding.Digest}
    (edge : Edge o log depth side child par) {directions : List Bool} {root : Binding.Digest}
    (prior : Binding.Path (history log) (oracleCompression o) depth directions root par) :
    Binding.Path (history log) (oracleCompression o) (depth+1) (side::directions) root child := by
  rw [←edge.choose];apply Binding.Path.step prior edge.left edge.right side edge.leftCanonical edge.rightCanonical _ edge.value
  intro j hj
  exact history_mono edge.observed (CheckParentExecution.recorded o _ depth j hj)

def dirs (idx : Index) (d : Nat) := (List.range' (24-d) d).map (fun bit=>idx.val.testBit bit)

theorem recorded_path (o : Oracle) (log : List PublicRow) (idx : Index) (nodes : Nat→Binding.Digest)
    (edges : ∀ d<24, Edge o log d (idx.val.testBit (23-d)) (nodes (d+1)) (nodes d)) :
    Binding.Path (history log) (oracleCompression o) 24 (route idx) (nodes 0) (nodes 24) := by
  have scan (d : Nat) (ok : d≤24) :
      Binding.Path (history log) (oracleCompression o) d (dirs idx d) (nodes 0) (nodes d) := by
    induction d with
    | zero=>exact .root _
    | succ d ih=>
      have step:=(edges d (by omega)).extend (ih (by omega))
      change Binding.Path _ _ _ ((List.range' (24-(d+1)) (d+1)).map _) _ _
      rw [List.range'_succ,List.map_cons]
      simpa only [dirs,show 24-(d+1)=23-d by omega,show 23-d+1=24-d by omega] using step
  have eq : List.range' (24-24) 24=List.range 24 := by decide
  simpa only [dirs,route,eq] using scan 24 (by decide)

def lowerCalls := 2 + ((List.range' 9 15).map work).sum

def upperCalls (count : Nat→Nat) := ((List.range 9).map (fun d=>count d*work d)).sum

theorem record_calls : lowerCalls=84 := by decide

theorem cap_calls (count : Nat→Nat) (fits : ∀ d<9, count d≤2^d) : upperCalls count≤2303 := by
  have cap : upperCalls (fun d=>2^d)=2303 := by decide
  rw [←cap];unfold upperCalls
  have go (xs : List Nat) (bounded : ∀ d∈xs,d<9) :
      (xs.map (fun d=>count d*work d)).sum ≤ (xs.map (fun d=>2^d*work d)).sum := by
    induction xs with
    | nil=>rfl
    | cons d xs ih=>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (fits _ (bounded _ (by simp))))
        (ih (fun x h=>bounded _ (List.mem_cons_of_mem _ h)))
  exact go _ (fun _ h=>List.mem_range.1 h)

theorem public_bound (k cap : Nat) (size : k≤2^24) (small : cap≤2303) : k*lowerCalls+cap≤2^31 := by
  rw [record_calls];omega

end CommitGolfCandidate.Reconstruction.CheckPath
