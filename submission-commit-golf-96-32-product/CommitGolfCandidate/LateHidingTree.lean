import CommitGolfCandidate.LateHidingRun

/-! The one-pass honest transcript of the late-salt scheme.

Under a fixed oracle the monadic tree `Late.treeM Late.hash` is a pure function
of the compression table, computed with exactly the calls the abstract scheme
makes: four per leaf and one per internal node. `treeExceptM` is the same
one-pass program with a single leaf digest supplied from outside; it is the
continuation of the per-leaf hiding step and makes at most `5 * LENGTH` public
calls. The opening reads salts only at opened positions. -/
namespace CommitGolfCandidate.LateHiding
open CommitGolf OracleComp OracleSpec

/-! ### Leaves -/

/-- The three unsalted calls of one leaf, in program order. -/
def prehashM (value : Entry) : OracleComp World (Late.Digest × Late.Digest) := do
  let u ← Late.hash (Late.firstBlock value)
  let a ← Late.hash (Late.middleBlock value u)
  let b ← Late.hash (Late.lastBlock value)
  pure (a, b)

/-- The honest leaf is its three unsalted calls followed by the salted final row. -/
theorem leaf_eq_prehash (odd : Bool) (salt : Late.Salt) (value : Entry) :
    Late.leafM Late.hash odd salt value =
      prehashM value >>= fun ab => Late.hash (Late.finalBlock odd salt ab.1 ab.2) := by
  simp only [Late.leafM, prehashM, bind_assoc, pure_bind]

def prehash (compress : Compression) (value : Entry) : Late.Digest × Late.Digest :=
  (compress (Late.middleBlock value (compress (Late.firstBlock value))),
    compress (Late.lastBlock value))

def leafDigest (compress : Compression) (odd : Bool) (salt : Late.Salt) (value : Entry) :
    Late.Digest :=
  compress (Late.finalBlock odd salt (prehash compress value).1 (prehash compress value).2)

/-- The pure leaf is the abstract model's own leaf function. -/
theorem leaf_digest_eq (compress : Compression) (odd : Bool) (salt : Late.Salt) (value : Entry) :
    leafDigest compress odd salt value = Late.leaf compress odd salt value := rfl

theorem run_hash (oracle : Oracle) {α : Type} (input : Late.Block)
    (next : Late.Digest → OracleComp World α) :
    fixedOracleRun oracle (Late.hash input >>= next) =
      fixedOracleRun oracle (next (oracle.compression input)) :=
  fixed_oracle_run_public oracle (.inl input) next

theorem run_prehash (oracle : Oracle) {α : Type} (value : Entry)
    (next : Late.Digest × Late.Digest → OracleComp World α) :
    fixedOracleRun oracle (prehashM value >>= next) =
      fixedOracleRun oracle (next (prehash oracle.compression value)) := by
  unfold prehashM prehash
  simp only [bind_assoc, pure_bind, run_hash]

theorem run_leaf (oracle : Oracle) {α : Type} (odd : Bool) (salt : Late.Salt) (value : Entry)
    (next : Late.Digest → OracleComp World α) :
    fixedOracleRun oracle (Late.leafM Late.hash odd salt value >>= next) =
      fixedOracleRun oracle (next (leafDigest oracle.compression odd salt value)) := by
  rw [leaf_eq_prehash, bind_assoc, run_prehash, run_hash]
  rfl

theorem hash_bound (input : Late.Block) : PublicQueryBound (Late.hash input) 1 :=
  ⟨show 1 ≤ 1 from le_rfl, fun _ => trivial⟩

theorem prehash_bound (value : Entry) : PublicQueryBound (prehashM value) 3 :=
  public_query_bound_bind (hash_bound _) fun _ =>
    public_query_bound_bind (hash_bound _) fun _ =>
      public_query_bound_bind (hash_bound _) fun _ =>
        (show PublicQueryBound (pure _ : OracleComp World (Late.Digest × Late.Digest)) 0 from trivial)

theorem leaf_bound (odd : Bool) (salt : Late.Salt) (value : Entry) :
    PublicQueryBound (Late.leafM Late.hash odd salt value) 4 :=
  public_query_bound_bind (hash_bound _) fun _ =>
    public_query_bound_bind (hash_bound _) fun _ =>
      public_query_bound_bind (hash_bound _) fun _ => hash_bound _

/-! ### Lists of calls -/

theorem run_mapM (oracle : Oracle) {ι β : Type} (items : List ι)
    (f : ι → OracleComp World β) (g : ι → β)
    (each : ∀ (item : ι) {α : Type} (next : β → OracleComp World α),
      fixedOracleRun oracle (f item >>= next) = fixedOracleRun oracle (next (g item)))
    {α : Type} (next : List β → OracleComp World α) :
    fixedOracleRun oracle (items.mapM f >>= next) =
      fixedOracleRun oracle (next (items.map g)) := by
  induction items generalizing next with
  | nil => simp only [List.mapM_nil, pure_bind, List.map_nil]
  | cons item rest ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.map_cons]
    rw [each item, ih]

theorem mapM_bound {ι β γ : Type} (items : List ι) (f : ι → OracleComp World β) (each : Nat)
    (bounded : ∀ item, PublicQueryBound (f item) each)
    (next : List β → OracleComp World γ) (after : Nat)
    (nextBounded : ∀ results, results.length = items.length → PublicQueryBound (next results) after) :
    PublicQueryBound (items.mapM f >>= next) (each * items.length + after) := by
  induction items generalizing next with
  | nil => simpa using nextBounded [] rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    have tail (result : β) := ih (fun results => next (result :: results))
      (fun results size => nextBounded (result :: results) (by simp [size]))
    convert public_query_bound_bind (bounded item) tail using 1
    omega

/-! ### Internal nodes -/

def parents (compress : Compression) (height : Nat) : List Late.Digest → List Late.Digest
  | left :: right :: rest => cut height (compress (Late.parentBlock left right)) :: parents compress height rest
  | _ => []

def levels (compress : Compression) : Nat → List Late.Digest → Late.Levels
  | 0, layer => [layer]
  | depth + 1, layer => layer :: levels compress depth (parents compress (LOG_LENGTH - depth) layer)

theorem run_parents (oracle : Oracle) {α : Type} (height : Nat) (layer : List Late.Digest)
    (next : List Late.Digest → OracleComp World α) :
    fixedOracleRun oracle (Late.parentsM Late.hash height layer >>= next) =
      fixedOracleRun oracle (next (parents oracle.compression height layer)) := by
  match layer with
  | [] => simp only [Late.parentsM, parents, pure_bind]
  | [_] => simp only [Late.parentsM, parents, pure_bind]
  | left :: right :: rest =>
    simp only [Late.parentsM, parents, bind_assoc, pure_bind]
    rw [run_hash]
    exact run_parents oracle height rest _

theorem run_levels (oracle : Oracle) {α : Type} (depth : Nat) (layer : List Late.Digest)
    (next : Late.Levels → OracleComp World α) :
    fixedOracleRun oracle (Late.levelsM Late.hash depth layer >>= next) =
      fixedOracleRun oracle (next (levels oracle.compression depth layer)) := by
  induction depth generalizing layer next with
  | zero => simp only [Late.levelsM, levels, pure_bind]
  | succ depth ih =>
    simp only [Late.levelsM, levels, bind_assoc, pure_bind]
    rw [run_parents, ih]

theorem parents_bound {α : Type} (height : Nat) (layer : List Late.Digest)
    (next : List Late.Digest → OracleComp World α) (after : Nat)
    (nextBounded : ∀ above, above.length = layer.length / 2 → PublicQueryBound (next above) after) :
    PublicQueryBound (Late.parentsM Late.hash height layer >>= next) (layer.length / 2 + after) := by
  match layer with
  | [] => simpa [Late.parentsM] using nextBounded [] rfl
  | [_] => simpa [Late.parentsM] using nextBounded [] (by simp)
  | left :: right :: rest =>
    simp only [Late.parentsM, bind_assoc, pure_bind]
    have tail (parent : Late.Digest) := parents_bound height rest (fun above => next (cut height parent :: above)) after
      (fun above size => nextBounded (cut height parent :: above) (by simp only [List.length_cons, size]; omega))
    convert public_query_bound_bind (hash_bound (Late.parentBlock left right)) tail using 1
    simp only [List.length_cons]
    omega

/-- Every level halves, so the whole tower above a layer costs at most its length. -/
theorem levels_bound (depth : Nat) (layer : List Late.Digest) :
    PublicQueryBound (Late.levelsM Late.hash depth layer) layer.length := by
  induction depth generalizing layer with
  | zero => trivial
  | succ depth ih =>
    simp only [Late.levelsM]
    have above (upper : List Late.Digest) (size : upper.length = layer.length / 2) :
        PublicQueryBound (do let rest ← Late.levelsM Late.hash depth upper; pure (layer :: rest))
          (layer.length / 2) := by
      have chained := public_query_bound_bind (ih upper)
        (fun rest => (show PublicQueryBound (pure (layer :: rest) : OracleComp World Late.Levels) 0
          from trivial))
      rw [size, Nat.add_zero] at chained
      exact chained
    exact (parents_bound _ layer _ _ above).mono (by omega)

/-! ### The whole tree, and the tree with one leaf supplied -/

/-- Leaf digests in index order. -/
def leafLayer (compress : Compression) (message : Message) (salt : Late.SaltTape) :
    List Late.Digest :=
  (List.finRange LENGTH).map fun index =>
    leafDigest compress (index.val.testBit 0) (salt index) (message index)

/-- The retained levels of the honest one-pass tree. -/
def tree (compress : Compression) (message : Message) (salt : Late.SaltTape) : Late.Levels :=
  levels compress LOG_LENGTH (leafLayer compress message salt)

/-- Leaf digests with the one at `hidden` replaced by a supplied digest. -/
def leafLayerExcept (compress : Compression) (message : Message) (salt : Late.SaltTape)
    (hidden : Index) (digest : Late.Digest) : List Late.Digest :=
  (List.finRange LENGTH).map fun index =>
    if index = hidden then digest
    else leafDigest compress (index.val.testBit 0) (salt index) (message index)

/-- One-pass oracle program for the tree in which the leaf at `hidden` is not
hashed: its digest is an input. Every other leaf and every internal node is
computed exactly once. -/
def treeExceptM (message : Message) (salt : Late.SaltTape) (hidden : Index)
    (digest : Late.Digest) : OracleComp World Late.Levels := do
  let leaves ← (List.finRange LENGTH).mapM fun index =>
    if index = hidden then (pure digest : OracleComp World Late.Digest)
    else Late.leafM Late.hash (index.val.testBit 0) (salt index) (message index)
  Late.levelsM Late.hash LOG_LENGTH leaves

attribute [local irreducible] List.finRange

theorem run_tree (oracle : Oracle) {α : Type} (message : Message) (salt : Late.SaltTape)
    (next : Late.Levels → OracleComp World α) :
    fixedOracleRun oracle (Late.treeM Late.hash message salt >>= next) =
      fixedOracleRun oracle (next (tree oracle.compression message salt)) := by
  unfold Late.treeM tree leafLayer
  rw [bind_assoc, run_mapM oracle (List.finRange LENGTH) _
    (fun index => leafDigest oracle.compression (index.val.testBit 0) (salt index) (message index))
    (fun index _ next => run_leaf oracle _ _ _ next), run_levels]

theorem run_tree_except (oracle : Oracle) {α : Type} (message : Message) (salt : Late.SaltTape)
    (hidden : Index) (digest : Late.Digest) (next : Late.Levels → OracleComp World α) :
    fixedOracleRun oracle (treeExceptM message salt hidden digest >>= next) =
      fixedOracleRun oracle (next (levels oracle.compression LOG_LENGTH
        (leafLayerExcept oracle.compression message salt hidden digest))) := by
  unfold treeExceptM leafLayerExcept
  rw [bind_assoc, run_mapM oracle (List.finRange LENGTH) _
    (fun index => if index = hidden then digest
      else leafDigest oracle.compression (index.val.testBit 0) (salt index) (message index))
    (fun index _ next => by
      by_cases same : index = hidden
      · simp only [same, ite_true, pure_bind]
      · simp only [same, ite_false]
        exact run_leaf oracle _ _ _ next), run_levels]

/-- Supplying the hidden leaf's own digest gives the tree of the updated message
and salt tape; every other leaf is unchanged. -/
theorem leaf_layer_except_update (compress : Compression) (message : Message)
    (salt : Late.SaltTape) (hidden : Index) (value : Entry) (fresh : Late.Salt) :
    leafLayerExcept compress message salt hidden
        (leafDigest compress (hidden.val.testBit 0) fresh value) =
      leafLayer compress (Function.update message hidden value)
        (Function.update salt hidden fresh) := by
  unfold leafLayerExcept leafLayer
  apply List.map_congr_left
  intro index _
  by_cases same : index = hidden
  · subst index
    simp only [ite_true, Function.update_self]
  · simp only [same, ite_false, Function.update_of_ne same]

/-- The one-pass program with one leaf supplied makes at most `5 * LENGTH` public
calls: four for each hashed leaf and at most `LENGTH` for the internal nodes. -/
theorem tree_except_bound (message : Message) (salt : Late.SaltTape) (hidden : Index)
    (digest : Late.Digest) :
    PublicQueryBound (treeExceptM message salt hidden digest) (5 * LENGTH) := by
  have each (index : Index) : PublicQueryBound
      (if index = hidden then (pure digest : OracleComp World Late.Digest)
        else Late.leafM Late.hash (index.val.testBit 0) (salt index) (message index)) 4 := by
    split
    · trivial
    · exact leaf_bound _ _ _
  have total := mapM_bound (List.finRange LENGTH) _ 4 each
    (Late.levelsM Late.hash LOG_LENGTH) LENGTH (fun results size => by
      rw [List.length_finRange] at size
      rw [← size]
      exact levels_bound LOG_LENGTH results)
  rw [List.length_finRange] at total
  exact PublicQueryBound.mono total (by omega)

/-! ### Agreement with the abstract model's pure tree -/

theorem leaf_layer_eq (compress : Compression) (message : Message) (salt : Late.SaltTape) :
    leafLayer compress message salt = (List.finRange LENGTH).map fun index =>
      leafDigest compress (index.val.testBit 0) (salt index) (message index) := rfl

theorem parents_eq_model (compress : Compression) (height : Nat) (layer : List Late.Digest) :
    parents compress height layer = Late.parentsM (M := Id) compress height layer := by
  match layer with
  | [] => rfl
  | [_] => rfl
  | left :: right :: rest =>
    simp only [parents, Late.parentsM]
    rw [parents_eq_model compress height rest]
    rfl

theorem levels_eq_model (compress : Compression) (depth : Nat) (layer : List Late.Digest) :
    levels compress depth layer = Late.levelsM (M := Id) compress depth layer := by
  induction depth generalizing layer with
  | zero => rfl
  | succ depth ih =>
    simp only [levels, Late.levelsM]
    rw [ih, parents_eq_model]
    rfl

private theorem mapM_id_eq {ι β : Type} (items : List ι) (f : ι → Id β) (g : ι → β)
    (each : ∀ item, f item = g item) : items.mapM (m := Id) f = items.map g := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.mapM_cons, List.map_cons, ← each item, ← ih]
    rfl

/-- `tree` is the abstract model's `treeM` evaluated in the identity monad. -/
theorem tree_eq_model (compress : Compression) (message : Message) (salt : Late.SaltTape) :
    tree compress message salt = Late.treeM (M := Id) compress message salt := by
  unfold tree Late.treeM
  rw [levels_eq_model, leaf_layer_eq, ← mapM_id_eq (List.finRange LENGTH)
    (fun index => Late.leafM (M := Id) compress (index.val.testBit 0) (salt index) (message index))
    (fun index => leafDigest compress (index.val.testBit 0) (salt index) (message index))
    (fun _ => rfl)]
  rfl

-- The lists over all `LENGTH` leaves are used only through the lemmas above. Unfolding
-- them during unification would enumerate 2^24 indices.
attribute [irreducible] leafLayer leafLayerExcept treeExceptM

/-! ### Openings -/

/-- The serialized proof reads salts only at the positions actually opened. -/
theorem opening_salt_congr (retained : Late.Levels) (left right : Late.SaltTape)
    (positions : Positions) (agree : ∀ index ∈ positions, left index = right index) :
    Late.opening retained left positions = Late.opening retained right positions := by
  have records (depth : Nat) :
      (positions.sort (· ≤ ·)).flatMap (Late.record retained left depth) =
        (positions.sort (· ≤ ·)).flatMap (Late.record retained right depth) := by
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro index member
    have opened : index ∈ positions := by simpa only [Finset.mem_sort] using member
    unfold Late.record
    rw [agree index opened]
  have batch :
      (positions.sort (· ≤ ·)).flatMap (Late.batchRecord retained left) =
        (positions.sort (· ≤ ·)).flatMap (Late.batchRecord retained right) := by
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro index member
    have opened : index ∈ positions := by simpa only [Finset.mem_sort] using member
    unfold Late.batchRecord
    rw [agree index opened]
  unfold Late.opening
  simp only [records, batch]

theorem opening_hidden_salt (retained : Late.Levels) (salt : Late.SaltTape)
    (positions : Positions) (hidden : Index) (unopened : hidden ∉ positions)
    (first second : Late.Salt) :
    Late.opening retained (Function.update salt hidden first) positions =
      Late.opening retained (Function.update salt hidden second) positions := by
  apply opening_salt_congr
  intro index member
  have different : index ≠ hidden := by
    intro same
    subst index
    exact unopened member
  rw [Function.update_of_ne different, Function.update_of_ne different]

end CommitGolfCandidate.LateHiding
