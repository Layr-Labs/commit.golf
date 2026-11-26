import CommitGolfCandidate.HidingLeaf

/-! A bounded oracle computation for the reference heap. This is a security-proof
continuation, not a replacement for the submitted machine or its cycle accounting.
The heap is computed once (memoized), so the leaf hiding lemma charges each honest
compression exactly once. -/
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

def queryList {α β : Type} (query : α → OracleComp World β) : List α → OracleComp World (List β)
  | [] => pure []
  | head :: tail => do
      let value ← query head
      let values ← queryList query tail
      pure (value :: values)

theorem query_list_bound {α β : Type} (query : α → OracleComp World β)
    (budget : Nat) (bounded : ∀ input, PublicQueryBound (query input) budget) (inputs : List α) :
    PublicQueryBound (queryList query inputs) (inputs.length*budget) := by
  induction inputs with
  | nil => trivial
  | cons head tail ih =>
    have rest (value : β) := public_query_bound_bind ih
      (fun values => (show PublicQueryBound (pure (value :: values) : OracleComp World _) 0 from trivial))
    have result := public_query_bound_bind (bounded head) rest
    simpa only [queryList, List.length_cons, Nat.add_zero, Nat.add_mul, Nat.one_mul,
      Nat.add_comm] using result

theorem query_list_reference (oracle : Oracle) {α β : Type}
    (query : α → OracleComp World β) (values : α → β) (inputs : List α)
    (correct : ∀ input ∈ inputs, fixedOracleRun oracle (query input) = pure (values input)) :
    fixedOracleRun oracle (queryList query inputs) = pure (inputs.map values) := by
  induction inputs with
  | nil => exact fixed_oracle_run_pure _ _
  | cons head tail ih =>
    rw [queryList, fixed_oracle_run_bind, correct head List.mem_cons_self, pure_bind]
    rw [fixed_oracle_run_bind, ih (fun input member => correct input (List.mem_cons_of_mem _ member)), pure_bind]
    exact fixed_oracle_run_pure _ _

/-! A memoized computation of the whole heap: each leaf once, then each internal
node once in descending order. This is the honest commitment's own query count. -/

/-- Leaves placed at heap slots `leafCount .. 2*leafCount-1`; every other slot is zero. -/
def initialHeap (leafCount : Nat) (leaves : List Digest) (node : Nat) : Digest :=
  if leafCount ≤ node ∧ node < 2*leafCount then leaves.getD (node-leafCount) 0 else 0

/-- Pure fold: after `m` steps, nodes `leafCount-1` down to `leafCount-m` are combined. -/
def parentsFrom (compress : Compression) (leafCount : Nat) (heap : Nat → Digest) : Nat → Nat → Digest
  | 0 => heap
  | m+1 =>
      let current := parentsFrom compress leafCount heap m
      Function.update current (leafCount-1-m)
        (combine compress (current (2*(leafCount-1-m))) (current (2*(leafCount-1-m)+1)))

def queryParentsFrom (leafCount : Nat) (heap : Nat → Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure heap
  | m+1 => do
      let current ← queryParentsFrom leafCount heap m
      let digest ← hashParent (current (2*(leafCount-1-m))) (current (2*(leafCount-1-m)+1))
      pure (Function.update current (leafCount-1-m) digest)

theorem query_parents_from_bound (leafCount : Nat) (heap : Nat → Digest) (m : Nat) :
    PublicQueryBound (queryParentsFrom leafCount heap m) m := by
  induction m with
  | zero => trivial
  | succ m ih =>
    have step := public_query_bound_bind ih (fun current =>
      public_query_bound_bind (hash_parent_bound (current (2*(leafCount-1-m))) (current (2*(leafCount-1-m)+1)))
        (fun digest => (show PublicQueryBound
          (pure (Function.update current (leafCount-1-m) digest) : OracleComp World _) 0 from trivial)))
    exact step

theorem fixed_query_parents_from (oracle : Oracle) (leafCount : Nat) (heap : Nat → Digest) (m : Nat) :
    fixedOracleRun oracle (queryParentsFrom leafCount heap m) =
      pure (parentsFrom oracle.compression leafCount heap m) := by
  induction m with
  | zero => exact fixed_oracle_run_pure _ _
  | succ m ih =>
    rw [queryParentsFrom, fixed_oracle_run_bind, ih, pure_bind, fixed_hash_parent, fixed_oracle_run_pure]
    rfl

theorem reference_heap_outside (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (node : Nat) (outside : node = 0 ∨ 2*leafCount ≤ node) :
    referenceHeap compress leafCount leaf node = 0 := by
  rw [referenceHeap, dif_neg (by omega), if_neg (by omega)]

theorem parents_from_reference (compress : Compression) (leafCount : Nat) (leaf heap : Nat → Digest)
    (initial : ∀ node, leafCount ≤ node ∨ node = 0 → heap node = referenceHeap compress leafCount leaf node)
    (m : Nat) (enough : m+1 ≤ leafCount) :
    (∀ node, leafCount-m ≤ node → parentsFrom compress leafCount heap m node =
      referenceHeap compress leafCount leaf node) ∧
    (∀ node, node < leafCount-m → parentsFrom compress leafCount heap m node = heap node) := by
  induction m with
  | zero =>
    exact ⟨fun node above => initial node (Or.inl (by omega)), fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨upper, lower⟩ := ih (by omega)
    constructor
    · intro node above
      change Function.update (parentsFrom compress leafCount heap m) (leafCount-1-m) _ node = _
      by_cases same : node = leafCount-1-m
      · subst node
        rw [Function.update_self, upper _ (by omega), upper _ (by omega)]
        exact (reference_heap_parent _ _ _ _ (by omega) (by omega)).symm
      · rw [Function.update_of_ne same, upper _ (by omega)]
    · intro node below
      change Function.update (parentsFrom compress leafCount heap m) (leafCount-1-m) _ node = _
      rw [Function.update_of_ne (by omega), lower _ (by omega)]

theorem parents_from_complete (compress : Compression) (leafCount : Nat) (leaf heap : Nat → Digest)
    (initial : ∀ node, leafCount ≤ node ∨ node = 0 → heap node = referenceHeap compress leafCount leaf node)
    (positive : 0 < leafCount) :
    parentsFrom compress leafCount heap (leafCount-1) = referenceHeap compress leafCount leaf := by
  obtain ⟨upper, lower⟩ := parents_from_reference compress leafCount leaf heap initial (leafCount-1) (by omega)
  funext node
  by_cases zero : node = 0
  · subst node
    rw [lower 0 (by omega), initial 0 (Or.inr rfl)]
  · exact upper node (by omega)

/-- The whole heap, every leaf and internal node computed exactly once. -/
def queryAll (leafCount : Nat) (leaf : Nat → OracleComp World Digest) : OracleComp World (Nat → Digest) := do
  let leaves ← queryList leaf (List.range leafCount)
  queryParentsFrom leafCount (initialHeap leafCount leaves) (leafCount-1)

theorem query_all_bound (leafCount : Nat) (leaf : Nat → OracleComp World Digest)
    (leafBudget : Nat) (bounded : ∀ index, PublicQueryBound (leaf index) leafBudget) :
    PublicQueryBound (queryAll leafCount leaf) (leafCount*leafBudget+(leafCount-1)) := by
  have leaves := query_list_bound leaf leafBudget bounded (List.range leafCount)
  rw [List.length_range] at leaves
  exact public_query_bound_bind leaves (fun leaves => query_parents_from_bound leafCount _ _)

theorem query_all_reference (oracle : Oracle) (leafCount : Nat)
    (leaf : Nat → OracleComp World Digest) (values : Nat → Digest)
    (leafExact : ∀ index, fixedOracleRun oracle (leaf index) = pure (values index))
    (positive : 0 < leafCount) :
    fixedOracleRun oracle (queryAll leafCount leaf) =
      pure (referenceHeap oracle.compression leafCount values) := by
  rw [queryAll, fixed_oracle_run_bind,
    query_list_reference oracle leaf values _ (fun index _ => leafExact index), pure_bind,
    fixed_query_parents_from]
  congr 1
  apply parents_from_complete _ _ _ _ _ positive
  intro node cases
  unfold initialHeap
  split
  · rename_i inside
    have address : leafCount+(node-leafCount) = node := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some]
    rw [← address, reference_heap_leaf _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  · exact (reference_heap_outside _ _ _ _ (by omega)).symm

end CommitGolfCandidate
