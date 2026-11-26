import CommitGolfCandidate.HidingHeapQueries

import CommitGolfCandidate.TruncHidingDistribution

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 800000

def queryHeap (leafCount : Nat) (leaf : Nat → OracleComp World Digest) :
    Nat → Nat → OracleComp World Digest
  | 0, node =>
      if leafCount ≤ node ∧ node < 2*leafCount then leaf (node-leafCount) else pure 0
  | fuel+1, node =>
      if 0 < node ∧ node < leafCount then do
        let left ← queryHeap leafCount leaf fuel (2*node)
        let right ← queryHeap leafCount leaf fuel (2*node+1)
        storeNode node <$> hashParent left right
      else if leafCount ≤ node ∧ node < 2*leafCount then leaf (node-leafCount)
      else pure 0

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
        public_query_bound_bind (ih (2*node+1)) (fun right => (show PublicQueryBound (storeNode node <$> hashParent left right) 1 from by rw [map_eq_bind_pure_comp];exact public_query_bound_bind (hash_parent_bound left right) (fun _=> (show PublicQueryBound (pure _) 0 from trivial)))))
      simpa only [heapQueryBudget, Nat.add_assoc] using parent
    · split
      · exact (bounded _).mono (heap_query_budget_ge_leaf leafBudget (fuel+1))
      · trivial

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
      rw [fixed_oracle_run_map,final, reference_heap_parent _ _ _ _ branch.1 branch.2];rfl
    · rename_i notBranch
      have lower : leafCount ≤ node := by omega
      have address : leafCount+(node-leafCount) = node := by omega
      rw [if_pos ⟨lower, inside⟩, leafExact]
      rw [← address, reference_heap_leaf _ _ _ _ (by omega), Nat.add_sub_cancel_left]

end CommitGolfCandidate.Trunc
