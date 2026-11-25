import CommitGolfCandidate.TwoPermutationPinnedReplay
import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.ProjectedCompression
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.K3T238Witness

/-! Authenticated paths of the checker. Each compression row retains the actual full reply while its child
authentication step receives the node the checker keeps at the parent's heap index (`nodeKeep`: 256 bits at level
21, 238 bits at levels 8..16, 240 bits elsewhere). Two paths for one leaf with different leaf digests expose two
compression rows whose replies agree on their low 238 bits. -/
namespace TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker OracleComp

private theorem equal_path_pair {node : Nat} {child₀ sibling₀ child₁ sibling₁ : BitVec 256}
    (same : pathPair node child₀ sibling₀ = pathPair node child₁ sibling₁) : child₀ = child₁ := by
  by_cases parity : node % 2 = 0
  · simp only [pathPair, ite_eq_left parity] at same
    have hit := congrArg (fun packed : BitVec 512 => packed.extractLsb' 0 256) same
    exact BitVec.extractLsb'_append_eq_right.symm.trans (hit.trans BitVec.extractLsb'_append_eq_right)
  · simp only [pathPair, ite_eq_right parity] at same
    have hit := congrArg (fun packed : BitVec 512 => packed.extractLsb' 256 256) same
    exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)

/-- A proof path only cites compression rows actually recorded during the check. -/
inductive ProjectedPath (rows : List PublicRow) : Nat → Nat → BitVec 256 → BitVec 256 → Prop where
  | done (node : Nat) (digest : BitVec 256) : ProjectedPath rows node 0 digest digest
  | step {node height : Nat} {child parent sibling root : BitVec 256}
      (call : PublicRow.compression (pathPair node child sibling) parent ∈ rows)
      (next : ProjectedPath rows (node / 2) height (nodeKeep (node / 2) parent) root) :
      ProjectedPath rows node (height + 1) child root

theorem ProjectedPath.mono {first last : List PublicRow} {node height : Nat}
    {start finish : BitVec 256} (path : ProjectedPath first node height start finish)
    (contained : ∀ row ∈ first, row ∈ last) : ProjectedPath last node height start finish := by
  induction path with
  | done node digest => exact .done node digest
  | step call _ ih => exact .step (contained _ call) ih

theorem ProjectedPath.append {rows : List PublicRow} {node m n : Nat} {start middle finish : BitVec 256}
    (first : ProjectedPath rows node m start middle)
    (last : ProjectedPath rows (node / 2 ^ m) n middle finish) :
    ProjectedPath rows node (m + n) start finish := by
  induction first with
  | done node digest =>
    simpa using last
  | @step node height child parent sibling root call next ih =>
    have address : node / 2 ^ (height + 1) = (node / 2) / 2 ^ height := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    rw [address] at last
    rw [show height + 1 + n = (height + n) + 1 by omega]
    exact .step call (ih last)

/-- Two accepted paths for the same leaf either have equal leaf digests or
expose a 238-bit collision in the recorded compression rows. -/
theorem ProjectedPath.compare {rows : List PublicRow} {node height : Nat}
    {start₀ start₁ root : BitVec 256}
    (left : ProjectedPath rows node height start₀ root)
    (right : ProjectedPath rows node height start₁ root) :
    CompressionWitness238 rows ∨ start₀ = start₁ := by
  induction height generalizing node start₀ start₁ root with
  | zero =>
    cases left
    cases right
    exact Or.inr rfl
  | succ height ih =>
    cases left with
    | @step _ _ _ parent₀ sibling₀ _ call₀ tail₀ =>
      cases right with
      | @step _ _ _ parent₁ sibling₁ _ call₁ tail₁ =>
        rcases ih tail₀ tail₁ with collision | sameParent
        · exact Or.inl collision
        by_cases sameInput : pathPair node start₀ sibling₀ = pathPair node start₁ sibling₁
        · exact Or.inr (equal_path_pair sameInput)
        · exact Or.inl ⟨_, _, _, _, call₀, call₁, sameInput, node_keep_low238 _ sameParent⟩

end TwoPermutationPrototype.Packed
