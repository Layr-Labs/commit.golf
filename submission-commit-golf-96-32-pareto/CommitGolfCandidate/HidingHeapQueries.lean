import CommitGolfCandidate.HidingLeaf

/-! A bounded oracle computation for the reference heap. This is a security-proof
continuation, not a replacement for the submitted machine or its cycle accounting.
Recomputing subtrees lets the leaf hiding lemma charge every honest compression. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- One parent compression as an oracle program, matching `combine`. -/
def hashParent (left right : Digest) : OracleComp World Digest := do
  let answer ← (liftM (World.query (.inr (.inl ((padInput (right ++ left)))))) : OracleComp World Digest)
  pure answer

theorem hash_parent_bound (left right : Digest) : PublicQueryBound (hashParent left right) 1 := by
  change 1 ≤ 1 ∧ ∀ answer, PublicQueryBound (pure answer : OracleComp World Digest) (1-1)
  exact ⟨le_refl _, fun _ => trivial⟩

theorem fixed_hash_parent (oracle : Oracle) (left right : Digest)
    {α : Type} (next : Digest → OracleComp World α) :
    fixedOracleRun oracle (hashParent left right >>= next) =
      fixedOracleRun oracle (next (combine oracle.compression left right)) := by
  simp only [hashParent, bind_assoc, pure_bind]
  erw [fixed_oracle_run_public]
  rfl

/-- Compute a heap node from oracle-computed leaves. Fuel bounds the tree depth;
the refinement theorem below proves it is sufficient on all nodes of interest. -/
def queryHeap (leafCount : Nat) (leaf : Nat → OracleComp World Digest) :
    Nat → Nat → OracleComp World Digest
  | 0, node =>
      if leafCount ≤ node ∧ node < 2*leafCount then leaf (node-leafCount) else pure 0
  | fuel+1, node =>
      if 0 < node ∧ node < leafCount then do
        let left ← queryHeap leafCount leaf fuel (2*node)
        let right ← queryHeap leafCount leaf fuel (2*node+1)
        hashParent left right
      else if leafCount ≤ node ∧ node < 2*leafCount then leaf (node-leafCount)
      else pure 0

/-- Two child computations and one parent compression per internal node. -/
def heapQueryBudget (leafBudget : Nat) : Nat → Nat
  | 0 => leafBudget
  | depth+1 => heapQueryBudget leafBudget depth + heapQueryBudget leafBudget depth + 1

theorem heap_query_budget_ge_leaf (leafBudget depth : Nat) :
    leafBudget ≤ heapQueryBudget leafBudget depth := by
  induction depth with
  | zero => exact Nat.le_refl _
  | succ depth ih => simp only [heapQueryBudget]; omega

theorem heap_query_budget_formula (leafBudget depth : Nat) :
    heapQueryBudget leafBudget depth + 1 = (leafBudget+1)*2^depth := by
  induction depth with
  | zero => simp [heapQueryBudget]
  | succ depth ih =>
    simp only [heapQueryBudget, Nat.pow_succ]
    nlinarith

theorem query_heap_bound (leafCount : Nat) (leaf : Nat → OracleComp World Digest)
    (leafBudget : Nat) (bounded : ∀ index, PublicQueryBound (leaf index) leafBudget)
    (fuel node : Nat) :
    PublicQueryBound (queryHeap leafCount leaf fuel node) (heapQueryBudget leafBudget fuel) := by
  induction fuel generalizing node with
  | zero =>
    simp only [queryHeap, heapQueryBudget]
    split
    · exact bounded _
    · trivial
  | succ fuel ih =>
    simp only [queryHeap]
    split
    · have parent := public_query_bound_bind (ih (2*node)) (fun left =>
        public_query_bound_bind (ih (2*node+1)) (fun right => hash_parent_bound left right))
      simpa only [heapQueryBudget, Nat.add_assoc] using parent
    · split
      · exact (bounded _).mono (heap_query_budget_ge_leaf leafBudget (fuel+1))
      · trivial

/-- The depth bound ensures no valid subtree is cut short. Every returned digest
is exactly the reference heap digest, with the same fixed compression table. -/
theorem query_heap_reference (oracle : Oracle) (leafCount : Nat)
    (leaf : Nat → OracleComp World Digest) (values : Nat → Digest)
    (leafExact : ∀ index, fixedOracleRun oracle (leaf index) = pure (values index))
    (fuel node : Nat) (positive : 0 < node) (inside : node < 2*leafCount)
    (enough : leafCount ≤ 2^fuel*node) :
    fixedOracleRun oracle (queryHeap leafCount leaf fuel node) =
      pure (referenceHeap oracle.compression leafCount values node) := by
  induction fuel generalizing node with
  | zero =>
    have lower : leafCount ≤ node := by simpa only [Nat.pow_zero, Nat.one_mul] using enough
    have address : leafCount+(node-leafCount) = node := by omega
    rw [queryHeap, if_pos ⟨lower, inside⟩, leafExact]
    rw [← address, reference_heap_leaf _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  | succ fuel ih =>
    rw [queryHeap]
    split
    · rename_i branch
      have leftEnough : leafCount ≤ 2^fuel*(2*node) := by
        calc leafCount ≤ 2^(fuel+1)*node := enough
             _ = 2^fuel*(2*node) := by rw [Nat.pow_succ]; ring
      have rightEnough : leafCount ≤ 2^fuel*(2*node+1) :=
        leftEnough.trans (Nat.mul_le_mul_left _ (by omega))
      rw [fixed_oracle_run_bind, ih (2*node) (by omega) (by omega) leftEnough, pure_bind]
      rw [fixed_oracle_run_bind, ih (2*node+1) (by omega) (by omega) rightEnough, pure_bind]
      have final := fixed_hash_parent oracle
        (referenceHeap oracle.compression leafCount values (2*node))
        (referenceHeap oracle.compression leafCount values (2*node+1)) pure
      simp only [bind_pure, fixed_oracle_run_pure] at final
      rw [final, reference_heap_parent _ _ _ _ branch.1 branch.2]
    · rename_i notBranch
      have lower : leafCount ≤ node := by omega
      have address : leafCount+(node-leafCount) = node := by omega
      rw [if_pos ⟨lower, inside⟩, leafExact]
      rw [← address, reference_heap_leaf _ _ _ _ (by omega), Nat.add_sub_cancel_left]

end CommitGolfCandidate
