import CommitGolfCandidate.TwoPermutationTranscript
import CommitGolfCandidate.ProjectedCompression
import CommitGolfCandidate.TwoPermutationCheckerPaths

/-! The bottom two internal levels retain all 256 reply bits. Higher nodes
retain the low 240 bits. Leaves and the public compression oracle are unchanged.
The node index, rather than the input value, selects the stored representation. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.ShortTree
set_option maxRecDepth 8192

def projectMixed (node : Nat) (digest : Digest) : Digest :=
  if node < 2 ^ 21 then padLow digest else digest

theorem projectMixed_projected (node : Nat) (digest : Digest) (small : node < 2 ^ 21) :
    projectMixed node digest = padLow digest := by
  simp only [projectMixed, if_pos small]

theorem projectMixed_full (node : Nat) (digest : Digest) (large : 2 ^ 21 ≤ node) :
    projectMixed node digest = digest := by
  simp only [projectMixed, if_neg (Nat.not_lt.mpr large)]

/-- Both representations preserve exactly the low240 witness used by binding. -/
theorem low240_projectMixed (node : Nat) (digest : Digest) :
    low240 (projectMixed node digest) = low240 digest := by
  unfold projectMixed
  split
  · exact low240_padLow digest
  · rfl

def mixedTranscriptHeap (compress : Compression) (leaves : DigestTape) (node : Nat) : Digest :=
  if branch : 0 < node ∧ node < LENGTH then
    projectMixed node (compress
      (mixedTranscriptHeap compress leaves (2 * node + 1) ++
       mixedTranscriptHeap compress leaves (2 * node)))
  else if leaf : LENGTH ≤ node ∧ node < 2 * LENGTH then
    leaves ⟨node - LENGTH, by omega⟩
  else 0
termination_by 2 * LENGTH - node
decreasing_by all_goals omega

theorem mixed_heap_leaf (compress : Compression) (leaves : DigestTape) (index : Index) :
    mixedTranscriptHeap compress leaves (LENGTH + index.val) = leaves index := by
  rw [mixedTranscriptHeap, dif_neg (by omega), dif_pos (by have := index.isLt; omega)]
  apply congrArg leaves
  apply Fin.ext
  simp only [Nat.add_sub_cancel_left]

theorem mixed_heap_parent (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (branch : node < LENGTH) :
    mixedTranscriptHeap compress leaves node =
      projectMixed node (compress
        (mixedTranscriptHeap compress leaves (2 * node + 1) ++
         mixedTranscriptHeap compress leaves (2 * node))) := by
  rw [mixedTranscriptHeap, dif_pos ⟨positive, branch⟩]

/-- Parent and leaf contents uniquely determine the used part of this heap. -/
theorem mixed_heap_unique (compress : Compression) (leaves : DigestTape) (heap : Nat → Digest)
    (parents : ∀ node, 0 < node → node < LENGTH →
      heap node = projectMixed node (compress (heap (2 * node + 1) ++ heap (2 * node))))
    (leafValues : ∀ index : Index, heap (LENGTH + index.val) = leaves index)
    (node : Nat) (positive : 0 < node) (inside : node < 2 * LENGTH) :
    heap node = mixedTranscriptHeap compress leaves node := by
  by_cases branch : node < LENGTH
  · rw [parents node positive branch, mixed_heap_parent _ _ _ positive branch]
    rw [mixed_heap_unique compress leaves heap parents leafValues (2 * node + 1) (by omega) (by omega),
      mixed_heap_unique compress leaves heap parents leafValues (2 * node) (by omega) (by omega)]
  · let index : Index := ⟨node - LENGTH, by omega⟩
    have address : LENGTH + index.val = node := by dsimp [index]; omega
    rw [← address, leafValues index, mixed_heap_leaf]
termination_by 2 * LENGTH - node
decreasing_by all_goals omega

theorem mixed_heap_projected (compress : Compression) (leaves : DigestTape) (node : Nat)
    (positive : 0 < node) (small : node < 2 ^ 21) :
    padLow (mixedTranscriptHeap compress leaves node) = mixedTranscriptHeap compress leaves node := by
  have branch : node < LENGTH := by change node < 16777216; norm_num at small; omega
  let answer : Digest := compress
    (mixedTranscriptHeap compress leaves (2 * node + 1) ++ mixedTranscriptHeap compress leaves (2 * node))
  have parent : mixedTranscriptHeap compress leaves node = projectMixed node answer :=
    mixed_heap_parent compress leaves node positive branch
  have projected := projectMixed_projected node answer small
  calc
    padLow (mixedTranscriptHeap compress leaves node) = padLow (projectMixed node answer) :=
      congrArg padLow parent
    _ = padLow (padLow answer) := congrArg padLow projected
    _ = padLow answer := congrArg (fun x => (0 : BitVec 16) ++ x) (low240_padLow answer)
    _ = projectMixed node answer := projected.symm
    _ = mixedTranscriptHeap compress leaves node := parent.symm

theorem mixed_honest_heap_climb (compress : Compression) (leaves : DigestTape) (node : Nat)
    (positive : 2 ≤ node) (bounded : node < 2 * LENGTH) :
    let heap := mixedTranscriptHeap compress leaves
    projectMixed (node / 2) (compress (pathPair node (heap node) (heap (node ^^^ 1)))) =
      heap (node / 2) := by
  let heap := mixedTranscriptHeap compress leaves
  change projectMixed (node / 2) (compress (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node / 2)
  have parent := mixed_heap_parent compress leaves (node / 2) (by omega) (by omega)
  change heap (node / 2) = projectMixed (node / 2)
    (compress (heap (2 * (node / 2) + 1) ++ heap (2 * (node / 2)))) at parent
  rw [parent]
  by_cases even : node % 2 = 0
  · rw [pathPair, ite_eq_left even, Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show 2 * (node / 2) + 1 = node + 1 by omega, show 2 * (node / 2) = node by omega]
  · have odd : Odd node := Nat.odd_iff.mpr (by omega)
    rw [pathPair, ite_eq_right even, Nat.xor_one_of_odd odd]
    rw [show 2 * (node / 2) + 1 = node by omega, show 2 * (node / 2) = node - 1 by omega]

end TwoPermutationPrototype.Sampling
