import CommitGolfCandidate.S3HidingBase

/-! The public transcript of the tree computed through the oracle, used only in the security
proof: every leaf (two forward permutation queries), every group node (one forward query on
72 zero bytes and the four leaf digests of the group) and every internal node (one compression
query, reply truncated to 240 bits). Under a fixed oracle the computation returns
`referenceTranscript`. The part above the leaves (`s5QueryTail`) reads the leaves only through
their digests, so it also serves the second stage of the leaf-layer argument. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-! ### Single queries -/

/-- One forward permutation query. -/
def s5Forward (input : BitVec PERMUTATION_WIDTH) : OracleComp World (BitVec PERMUTATION_WIDTH) :=
  (liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World (BitVec PERMUTATION_WIDTH))

/-- One compression query. -/
def s5Compress (input : BitVec (256 + 256)) : OracleComp World Digest :=
  (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)

theorem fixed_s5_forward (oracle : Oracle) (input : BitVec PERMUTATION_WIDTH) {α : Type}
    (next : BitVec PERMUTATION_WIDTH → OracleComp World α) :
    fixedOracleRun oracle (s5Forward input >>= next) =
      fixedOracleRun oracle (next (oracle.permutation input)) :=
  fixed_oracle_run_public oracle (.inr (.inl input)) next

theorem fixed_s5_compress (oracle : Oracle) (input : BitVec (256 + 256)) {α : Type}
    (next : Digest → OracleComp World α) :
    fixedOracleRun oracle (s5Compress input >>= next) =
      fixedOracleRun oracle (next (oracle.compression input)) :=
  fixed_oracle_run_public oracle (.inl input) next

theorem s5_forward_bound (input : BitVec PERMUTATION_WIDTH) {α : Type}
    (next : BitVec PERMUTATION_WIDTH → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    PublicQueryBound (s5Forward input >>= next) (budget + 1) := by
  change 1 ≤ budget + 1 ∧ ∀ answer, PublicQueryBound (next answer) (budget + 1 - 1)
  exact ⟨by omega, fun answer => by simpa only [Nat.add_sub_cancel] using bounded answer⟩

theorem s5_compress_bound (input : BitVec (256 + 256)) {α : Type}
    (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    PublicQueryBound (s5Compress input >>= next) (budget + 1) := by
  change 1 ≤ budget + 1 ∧ ∀ answer, PublicQueryBound (next answer) (budget + 1 - 1)
  exact ⟨by omega, fun answer => by simpa only [Nat.add_sub_cancel] using bounded answer⟩

theorem s5_pure_bound {β : Type} (value : β) : PublicQueryBound (pure value : OracleComp World β) 0 := by
  trivial

/-! ### Leaves and group nodes -/

/-- The leaf hash: two forward permutation queries. -/
def s5QueryLeaf (salt : Digest) (value : Entry) : OracleComp World Digest :=
  s5Forward (s3First salt value) >>= fun first =>
    s5Forward (s3Second first value) >>= fun second => pure (BitVec.ofNat 256 second.toNat)

theorem fixed_s5_query_leaf (oracle : Oracle) (salt : Digest) (value : Entry) :
    fixedOracleRun oracle (s5QueryLeaf salt value) =
      pure (s3LeafDigest oracle.permutation salt value) := by
  unfold s5QueryLeaf
  rw [fixed_s5_forward, fixed_s5_forward, fixed_oracle_run_pure]
  rfl

theorem s5_query_leaf_bound (salt : Digest) (value : Entry) :
    PublicQueryBound (s5QueryLeaf salt value) 2 :=
  s5_forward_bound _ _ 1 fun _ => s5_forward_bound _ _ 0 fun _ => s5_pure_bound _

/-- A group node: one forward query on 72 zero bytes and the four leaf digests of the group. -/
def s5QueryGroup (leaf : Nat → Digest) (group : Nat) : OracleComp World Digest :=
  s5Forward (s6GroupInput (leaf (4*group)) (leaf (4*group+1)) (leaf (4*group+2))
    (leaf (4*group+3))) >>= fun reply => pure (BitVec.ofNat 256 reply.toNat)

theorem fixed_s5_query_group (oracle : Oracle) (leaf : Nat → Digest) (group : Nat) :
    fixedOracleRun oracle (s5QueryGroup leaf group) =
      pure (s6GroupValues oracle.permutation leaf group) := by
  unfold s5QueryGroup
  rw [fixed_s5_forward, fixed_oracle_run_pure]
  rfl

theorem s5_query_group_bound (leaf : Nat → Digest) (group : Nat) :
    PublicQueryBound (s5QueryGroup leaf group) 1 :=
  s5_forward_bound _ _ 0 fun _ => s5_pure_bound _

/-- The group nodes `count-1, .., 0` by forward queries, stored at heap nodes `2^22 + group`. -/
def s5QueryGroups (leaf : Nat → Digest) : Nat → (Nat → Digest) → OracleComp World (Nat → Digest)
  | 0, heap => pure heap
  | count+1, heap => s5QueryGroup leaf count >>= fun digest =>
      s5QueryGroups leaf count (Function.update heap (2^22+count) digest)

/-- The same nodes computed with a fixed permutation. -/
def s5Groups (permutation : Perm) (leaf : Nat → Digest) : Nat → (Nat → Digest) → (Nat → Digest)
  | 0, heap => heap
  | count+1, heap => s5Groups permutation leaf count
      (Function.update heap (2^22+count) (s6GroupValues permutation leaf count))

theorem fixed_s5_query_groups (oracle : Oracle) (leaf : Nat → Digest) :
    ∀ (count : Nat) (heap : Nat → Digest),
      fixedOracleRun oracle (s5QueryGroups leaf count heap) =
        pure (s5Groups oracle.permutation leaf count heap)
  | 0, heap => fixed_oracle_run_pure _ _
  | count+1, heap => by
    rw [s5QueryGroups, fixed_oracle_run_bind, fixed_s5_query_group, pure_bind,
      fixed_s5_query_groups oracle leaf count]
    rfl

theorem s5_query_groups_bound (leaf : Nat → Digest) : ∀ (count : Nat) (heap : Nat → Digest),
    PublicQueryBound (s5QueryGroups leaf count heap) count
  | 0, _ => trivial
  | count+1, heap => by
    rw [s5QueryGroups]
    refine (public_query_bound_bind (s5_query_group_bound leaf count) fun digest =>
      s5_query_groups_bound leaf count _).mono ?_
    omega

theorem s5_groups_apply (permutation : Perm) (leaf : Nat → Digest) :
    ∀ (count : Nat) (heap : Nat → Digest) (node : Nat),
      s5Groups permutation leaf count heap node =
        if 2^22 ≤ node ∧ node < 2^22+count then s6GroupValues permutation leaf (node-2^22)
        else heap node
  | 0, heap, node => by
    rw [s5Groups, if_neg (by omega)]
  | count+1, heap, node => by
    rw [s5Groups, s5_groups_apply permutation leaf count]
    by_cases lower : 2^22 ≤ node
    · by_cases upper : node < 2^22+count
      · rw [if_pos ⟨lower, upper⟩, if_pos ⟨lower, by omega⟩]
      · by_cases equal : node = 2^22+count
        · subst node
          rw [if_neg (by omega), Function.update_self, if_pos ⟨lower, by omega⟩, Nat.add_sub_cancel_left]
        · rw [if_neg (by omega), Function.update_of_ne equal, if_neg (by omega)]
    · rw [if_neg (by omega), Function.update_of_ne (by omega), if_neg (by omega)]

/-! ### Internal nodes -/

/-- Internal nodes `count, count-1, .., 1` by compression queries, each reply truncated. -/
def s5QueryParents : Nat → (Nat → Digest) → OracleComp World (Nat → Digest)
  | 0, heap => pure heap
  | count+1, heap => s5Compress (heap (2*(count+1)+1) ++ heap (2*(count+1))) >>= fun reply =>
      s5QueryParents count (Function.update heap (count+1) (s6Trunc reply))

/-- The same nodes computed with a fixed compression function. -/
def s5Parents (compress : Compression) : Nat → (Nat → Digest) → (Nat → Digest)
  | 0, heap => heap
  | count+1, heap => s5Parents compress count
      (Function.update heap (count+1) (combine compress (heap (2*(count+1))) (heap (2*(count+1)+1))))

theorem fixed_s5_query_parents (oracle : Oracle) : ∀ (count : Nat) (heap : Nat → Digest),
    fixedOracleRun oracle (s5QueryParents count heap) =
      pure (s5Parents (s6Compress oracle.compression) count heap)
  | 0, heap => fixed_oracle_run_pure _ _
  | count+1, heap => by
    rw [s5QueryParents, fixed_s5_compress, fixed_s5_query_parents oracle count]
    rfl

theorem s5_query_parents_bound : ∀ (count : Nat) (heap : Nat → Digest),
    PublicQueryBound (s5QueryParents count heap) count
  | 0, _ => trivial
  | count+1, heap => by
    rw [s5QueryParents]
    exact s5_compress_bound _ _ count fun reply => s5_query_parents_bound count _

theorem s5_parents_outside (compress : Compression) : ∀ (count : Nat) (heap : Nat → Digest)
    (node : Nat), (node = 0 ∨ count < node) → s5Parents compress count heap node = heap node
  | 0, _, _, _ => rfl
  | count+1, heap, node, outside => by
    rw [s5Parents, s5_parents_outside compress count _ node (by omega),
      Function.update_of_ne (show node ≠ count+1 by omega)]

theorem s5_parents_correct (compress : Compression) (leafCount : Nat) (values : Nat → Digest) :
    ∀ (count : Nat) (heap : Nat → Digest), count < leafCount →
      (∀ node, count < node → node < 2*leafCount →
        heap node = referenceHeap compress leafCount values node) →
      ∀ node, 0 < node → node < 2*leafCount →
        s5Parents compress count heap node = referenceHeap compress leafCount values node
  | 0, heap, _, ready => ready
  | count+1, heap, bounded, ready => by
    rw [s5Parents]
    apply s5_parents_correct compress leafCount values count _ (by omega)
    intro node greater inside
    by_cases equal : node = count+1
    · subst node
      rw [Function.update_self, ready _ (by omega) (by omega), ready _ (by omega) (by omega)]
      exact (reference_heap_parent compress leafCount values (count+1) (by omega) bounded).symm
    · rw [Function.update_of_ne equal]
      exact ready node (by omega) inside

theorem s5_parents_group_heap (compress : Compression) (permutation : Perm) (leaf : Nat → Digest) :
    s5Parents compress (2^22-1) (s5Groups permutation leaf (2^22) fun _ => 0) =
      referenceHeap compress (2^22) (s6GroupValues permutation leaf) := by
  funext node
  by_cases valid : 0 < node ∧ node < 2^23
  · refine s5_parents_correct compress (2^22) _ (2^22-1) _ (by norm_num) ?_ node valid.1
      (by norm_num; omega)
    intro slot greater inside
    obtain ⟨index, rfl⟩ : ∃ index, slot = 2^22 + index := ⟨slot - 2^22, by omega⟩
    rw [s5_groups_apply, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
      reference_heap_leaf _ _ _ _ (by omega)]
  · rw [s5_parents_outside compress _ _ node (by omega), s5_groups_apply, if_neg (by omega),
      referenceHeap, dif_neg (by omega), if_neg (by omega)]

/-! ### The transcript as a function of the heap -/

theorem s5_cap_child_bounds (height node : Nat)
    (lower : 256 ≤ node * 2^(height+1))
    (upper : (node+1) * 2^(height+1) ≤ 512) :
    0 < node ∧ node < 256 ∧
      256 ≤ 2*node*2^height ∧ (2*node+1)*2^height ≤ 512 ∧
      256 ≤ (2*node+1)*2^height ∧ (2*node+1+1)*2^height ≤ 512 := by
  have power : 0 < 2^height := Nat.two_pow_pos height
  rw [pow_succ] at lower upper
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The cap footer read off a consistent heap: the root of every unoccupied maximal subtree is
the heap node itself. -/
def s5CapFooterHeap (roots : Nat → Digest) (marked : Nat → Bool) : (height node : Nat) → List Digest
  | 0, node => if marked node then [] else [roots node]
  | height+1, node =>
      if capOccupied (capHeapView roots marked (height+1) node) then
        s5CapFooterHeap roots marked height (2*node) ++ s5CapFooterHeap roots marked height (2*node+1)
      else [roots node]

theorem s5_cap_proof_heap (compress : Compression) (roots : Nat → Digest)
    (parents : ∀ node, 0 < node → node < 256 →
      roots node = combine compress (roots (2*node)) (roots (2*node+1)))
    (marked : Nat → Bool) (height node : Nat)
    (lower : 256 ≤ node * 2^height) (upper : (node+1) * 2^height ≤ 512) :
    capProof compress (capHeapTree roots height node) (capHeapView roots marked height node) =
      s5CapFooterHeap roots marked height node := by
  induction height generalizing node with
  | zero =>
    cases h : marked node <;> simp [capHeapTree, capHeapView, s5CapFooterHeap, capProof,
      capOccupied, Tree.root, h]
  | succ height ih =>
    obtain ⟨_, _, ll, lu, rl, ru⟩ := s5_cap_child_bounds height node lower upper
    have root := cap_heap_tree_root compress roots parents (height+1) node lower upper
    by_cases occupied : capOccupied (capHeapView roots marked (height+1) node) = true
    · rw [s5CapFooterHeap, if_pos occupied, ← ih (2*node) ll lu, ← ih (2*node+1) rl ru]
      simp only [capHeapView] at occupied
      simp only [capHeapTree, capHeapView, capProof, occupied, ↓reduceIte]
    · rw [s5CapFooterHeap, if_neg occupied, ← root]
      simp only [capHeapView] at occupied
      simp only [capHeapTree, capHeapView, capProof, occupied, ↓reduceIte, Bool.false_eq_true]

/-- Commitment and proof read from a heap of the tree, the leaf digests and the salts. -/
def s5TreeTranscript (heap leaf : Nat → Digest) (salt : Index → Digest) (positions : Positions) :
    Commitment × Proof :=
  (heap 1, if positions.card = 0 then [] else
    referenceOpening heap leaf salt positions ++
      (s5CapFooterHeap heap (s6CapMarks positions) 8 1).flatMap digestBytes)

theorem s5_transcript_of_heap (compress : Compression) (groups leaf : Nat → Digest)
    (salt : Index → Digest) (positions : Positions) :
    s6TranscriptOf compress groups leaf salt positions =
      s5TreeTranscript (referenceHeap (s6Compress compress) (2^22) groups) leaf salt positions := by
  have footer := s5_cap_proof_heap (s6Compress compress) (referenceHeap (s6Compress compress) (2^22) groups)
    (fun node positive below => reference_heap_parent _ _ _ node positive (by omega))
    (s6CapMarks positions) 8 1 (by norm_num) (by norm_num)
  simp only [s6TranscriptOf, s5TreeTranscript, s6CapFooter, footer]

/-- The tree above the leaves, from all leaf digests: group nodes by forward queries, internal
nodes by compression queries. -/
def s5QueryTail (leaf : Nat → Digest) (salt : Index → Digest) (positions : Positions) :
    OracleComp World (Commitment × Proof) :=
  s5QueryGroups leaf (2^22) (fun _ => 0) >>= fun groups =>
    s5QueryParents (2^22-1) groups >>= fun heap =>
      pure (s5TreeTranscript heap leaf salt positions)

theorem fixed_s5_query_tail (oracle : Oracle) (leaf : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) :
    fixedOracleRun oracle (s5QueryTail leaf salt positions) =
      pure (s6TranscriptOf oracle.compression (s6GroupValues oracle.permutation leaf) leaf salt
        positions) := by
  unfold s5QueryTail
  rw [fixed_oracle_run_bind, fixed_s5_query_groups, pure_bind, fixed_oracle_run_bind,
    fixed_s5_query_parents, pure_bind, fixed_oracle_run_pure, s5_parents_group_heap,
    s5_transcript_of_heap]

theorem s5_query_tail_bound (leaf : Nat → Digest) (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (s5QueryTail leaf salt positions) (2^23) := by
  unfold s5QueryTail
  refine (public_query_bound_bind (s5_query_groups_bound leaf (2^22) _) fun groups =>
    public_query_bound_bind (s5_query_parents_bound (2^22-1) groups) fun heap =>
      s5_pure_bound (s5TreeTranscript heap leaf salt positions)).mono ?_
  norm_num

/-- The leaf hash of position `index` (no query outside the tree). -/
def s5QueryLeafAt (message : Message) (salt : Index → Digest) (index : Nat) : OracleComp World Digest :=
  if inside : index < LENGTH then s5QueryLeaf (salt ⟨index, inside⟩) (message ⟨index, inside⟩)
  else pure 0

theorem fixed_s5_query_leaf_at (oracle : Oracle) (message : Message) (salt : Index → Digest)
    (index : Nat) :
    fixedOracleRun oracle (s5QueryLeafAt message salt index) =
      pure (s6LeafValues oracle.permutation message salt index) := by
  unfold s5QueryLeafAt s6LeafValues
  split
  · exact fixed_s5_query_leaf oracle _ _
  · exact fixed_oracle_run_pure _ _

theorem s5_query_leaf_at_bound (message : Message) (salt : Index → Digest) (index : Nat) :
    PublicQueryBound (s5QueryLeafAt message salt index) 2 := by
  unfold s5QueryLeafAt
  split
  · exact s5_query_leaf_bound _ _
  · exact (s5_pure_bound _).mono (Nat.zero_le _)

/-- The leaves `count-1, .., 0`. -/
def s5QueryLeaves (message : Message) (salt : Index → Digest) :
    Nat → (Nat → Digest) → OracleComp World (Nat → Digest)
  | 0, leaf => pure leaf
  | count+1, leaf => s5QueryLeafAt message salt count >>= fun digest =>
      s5QueryLeaves message salt count (Function.update leaf count digest)

def s5Leaves (permutation : Perm) (message : Message) (salt : Index → Digest) :
    Nat → (Nat → Digest) → (Nat → Digest)
  | 0, leaf => leaf
  | count+1, leaf => s5Leaves permutation message salt count
      (Function.update leaf count (s6LeafValues permutation message salt count))

theorem fixed_s5_query_leaves (oracle : Oracle) (message : Message) (salt : Index → Digest) :
    ∀ (count : Nat) (leaf : Nat → Digest),
      fixedOracleRun oracle (s5QueryLeaves message salt count leaf) =
        pure (s5Leaves oracle.permutation message salt count leaf)
  | 0, leaf => fixed_oracle_run_pure _ _
  | count+1, leaf => by
    rw [s5QueryLeaves, fixed_oracle_run_bind, fixed_s5_query_leaf_at, pure_bind,
      fixed_s5_query_leaves oracle message salt count]
    rfl

theorem s5_query_leaves_bound (message : Message) (salt : Index → Digest) :
    ∀ (count : Nat) (leaf : Nat → Digest),
      PublicQueryBound (s5QueryLeaves message salt count leaf) (2*count)
  | 0, _ => trivial
  | count+1, leaf => by
    rw [s5QueryLeaves]
    refine (public_query_bound_bind (s5_query_leaf_at_bound message salt count) fun digest =>
      s5_query_leaves_bound message salt count _).mono ?_
    omega

theorem s5_leaves_apply (permutation : Perm) (message : Message) (salt : Index → Digest) :
    ∀ (count : Nat) (leaf : Nat → Digest) (index : Nat),
      s5Leaves permutation message salt count leaf index =
        if index < count then s6LeafValues permutation message salt index else leaf index
  | 0, leaf, index => by rw [s5Leaves, if_neg (by omega)]
  | count+1, leaf, index => by
    rw [s5Leaves, s5_leaves_apply permutation message salt count]
    by_cases below : index < count
    · rw [if_pos below, if_pos (by omega)]
    · by_cases equal : index = count
      · subst index
        rw [if_neg below, Function.update_self, if_pos (by omega)]
      · rw [if_neg below, Function.update_of_ne equal, if_neg (by omega)]

theorem s5_leaves_all (permutation : Perm) (message : Message) (salt : Index → Digest) :
    s5Leaves permutation message salt LENGTH (fun _ => 0) = s6LeafValues permutation message salt := by
  funext index
  rw [s5_leaves_apply]
  split
  · rfl
  · rename_i outside
    unfold s6LeafValues
    rw [dif_neg outside]

/-- Root and opening with every leaf, group node and internal node computed through the oracle. -/
def queryFullTranscript (message : Message) (salt : Index → Digest) (positions : Positions) :
    OracleComp World (Commitment × Proof) :=
  s5QueryLeaves message salt LENGTH (fun _ => 0) >>= fun leaf => s5QueryTail leaf salt positions

theorem query_full_transcript_reference (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryFullTranscript message salt positions) =
      pure (referenceTranscript oracle.compression oracle.permutation message salt positions) := by
  unfold queryFullTranscript
  rw [fixed_oracle_run_bind, fixed_s5_query_leaves, pure_bind, s5_leaves_all, fixed_s5_query_tail]
  rfl

theorem query_full_transcript_bound (message : Message) (salt : Index → Digest)
    (positions : Positions) :
    PublicQueryBound (queryFullTranscript message salt positions) (2^25 + 2^23) := by
  unfold queryFullTranscript
  refine (public_query_bound_bind (s5_query_leaves_bound message salt LENGTH _) fun leaf =>
    s5_query_tail_bound leaf salt positions).mono ?_
  norm_num [LENGTH, LOG_LENGTH]

attribute [irreducible] s5QueryTail queryFullTranscript

end CommitGolfCandidate
