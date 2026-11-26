import CommitGolfCandidate.S4HidingTree
import CommitGolfCandidate.MidHidingObserver

/-! All unopened leaf digests become fresh in one step.

After the three unsalted calls of every leaf have been answered, each leaf's
final row is a fixed function of the pair words. Four games share one table,
one draw of pair words and one vector `fresh` of independent digests.

| game | table | leaf layer |
| --- | --- | --- |
| real | plain | read at every row |
| all programmed | every row answers its fresh digest | `fresh` |
| opened programmed | opened rows answer their fresh digest | `fresh` |
| ideal | plain | read at opened rows, `fresh` elsewhere |

Real and all-programmed agree exactly when the rows are distinct and uncached
(`GoodRows`), and so do ideal and opened-programmed. In between, the tree is the
same unless some row is an input the tree reads. Those inputs are computed from
`fresh` and the plain table, so no salt enters them and a union bound over the
pair words applies. With equal trees the two programmed games differ only in the
answers at unopened rows, and the observer finds one with probability at most
`8 * budget / 2^128`, once a midpoint shared by five pairs is excluded.

The decomposition follows dadon's b4f31491 (`MoonHiding`, section 5). Programming
the opened rows as well is what removes his query-level tree invariant. -/
namespace CommitGolfCandidate.S4Hiding
open CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance idealDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

attribute [local irreducible] List.finRange

/-! ### What the tree reads -/

/-- The compression inputs that `levels` reads, in program order. -/
def rowsRead (H : Compression) : Nat → List Late.Digest → List Late.Block
  | 0, _ => []
  | d+1, ns => (List.range (S4.width (23-d+1))).map (fun j => S4.readRow (23-d) ns j) ++
      rowsRead H d (parents H (23-d) ns)

theorem rows_read_length (H : Compression) (d : Nat) (ns : List Late.Digest) :
    (rowsRead H d ns).length = S4.parentCost d := by
  induction d generalizing ns with
  | zero => rfl
  | succ d ih =>
    rw [rowsRead, List.length_append, List.length_map, List.length_range, ih]
    rfl

/-- A table that agrees with `H` on every input the tree reads under `H` builds the same tree. -/
theorem levels_congr (H H' : Compression) (d : Nat) (ns : List Late.Digest)
    (same : ∀ x ∈ rowsRead H d ns, H' x = H x) :
    levels H' d ns = levels H d ns := by
  induction d generalizing ns with
  | zero => rfl
  | succ d ih =>
    have here : parents H' (23-d) ns = parents H (23-d) ns := by
      unfold parents
      apply List.map_congr_left
      intro j member
      rw [same (S4.readRow (23-d) ns j) (by
        rw [rowsRead]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨j, member, rfl⟩))]
    have rest := ih (parents H (23-d) ns) (fun x member => same x (by
      rw [rowsRead]
      exact List.mem_append_right _ member))
    simp only [levels]
    rw [here, rest]

/-! ### Games -/

/-- What the observer computes when the tree stands on a given leaf layer. -/
def viewFrom {α : Type} (oracle : Oracle) (layer : List Late.Digest) (salt : Late.SaltTape)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  fixedOracleRun oracle
    (observe (Late.node (levels oracle.compression 24 layer) LOG_LENGTH 0)
      (S4.actualOpening (levels oracle.compression 24 layer) salt positions))

/-- The second half of the game for a table under the cache and a leaf layer given leaf by leaf. -/
def game {α : Type} (permutation : Perm) (cache : CompressionCache) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (salt : Late.SaltTape)
    (table : Compression) (leaf : Index → Late.Digest) : ProbComp α :=
  viewFrom ⟨tableExtending cache table, permutation⟩ ((List.finRange LENGTH).map leaf) salt
    positions observe

/-- The game after the unsalted calls: every leaf digest is the table's answer at its row. -/
def realAfter {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let words ← $ᵗ (PairIndex → Late.PairCoins)
  game permutation cache positions observe (unpackTape words) table
    (fun i => fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)))

/-- The ideal game after the unsalted calls: unopened leaves have fresh digests. -/
def idealAfter {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let words ← $ᵗ (PairIndex → Late.PairCoins)
  let fresh ← $ᵗ (Index → Late.Digest)
  game permutation cache positions observe (unpackTape words) table
    (fun i => if i ∈ positions then
      fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)) else fresh i)

/-- Pair words, fresh digests and a table, drawn once for all intermediate games. -/
abbrev Key := (PairIndex → Late.PairCoins) × (Index → Late.Digest) × Compression

def keyDraw : ProbComp Key := do
  let words ← $ᵗ (PairIndex → Late.PairCoins)
  let fresh ← $ᵗ (Index → Late.Digest)
  let table ← $ᵗ Compression
  pure (words, fresh, table)

theorem key_bind {β : Type} (body : Key → ProbComp β) :
    keyDraw >>= body =
      (do let words ← $ᵗ (PairIndex → Late.PairCoins)
          let fresh ← $ᵗ (Index → Late.Digest)
          let table ← $ᵗ Compression
          body (words, fresh, table)) := by
  simp only [keyDraw, bind_assoc, pure_bind]

/-- The game in which the rows of the leaves in `S` answer their fresh digests. -/
noncomputable def programmedGame {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (S : Finset Index) (k : Key) :
    ProbComp α :=
  game permutation cache positions observe (unpackTape k.1)
    (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 S) k.2.1

/-- The observing stage of the opened-programmed game, with a flag for calls on unopened rows. -/
noncomputable def flaggedIdeal {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (k : Key) : ProbComp (α × Unit × Bool) :=
  flaggedRun
    ⟨tableExtending cache (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 positions),
      permutation⟩
    (marksInput fun x => decide (∃ i ∉ positions, rowOf ab (unpackTape k.1) i = x))
    (observe
      (Late.node (levels (tableExtending cache
        (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 positions)) 24
        ((List.finRange LENGTH).map k.2.1)) LOG_LENGTH 0)
      (S4.actualOpening (levels (tableExtending cache
        (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 positions)) 24
        ((List.finRange LENGTH).map k.2.1)) (unpackTape k.1) positions))

/-- Some row is an input that the tree on the fresh layer reads under the plain table. -/
def Reads (cache : CompressionCache) (ab : Index → Late.Digest × Late.Digest) (k : Key) : Prop :=
  ∃ i : Index, rowOf ab (unpackTape k.1) i ∈
    rowsRead (tableExtending cache k.2.2) 24 ((List.finRange LENGTH).map k.2.1)

/-! ### Programmed tables -/

private theorem programmed_off (cache : CompressionCache) (rows : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (S : Finset Index) (x : Late.Block)
    (apart : ∀ i, rows i ≠ x) :
    tableExtending cache (reprogramFinset rows table fresh S) x = tableExtending cache table x := by
  change (cache x).getD (reprogramFinset rows table fresh S x) = (cache x).getD (table x)
  rw [reprogramFinset_not_mem rows table fresh S x (fun i _ => apart i)]

private theorem programmed_tree (cache : CompressionCache) (rows : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (S : Finset Index)
    (layer : List Late.Digest)
    (clear : ∀ i, rows i ∉ rowsRead (tableExtending cache table) 24 layer) :
    levels (tableExtending cache (reprogramFinset rows table fresh S)) 24 layer =
      levels (tableExtending cache table) 24 layer :=
  levels_congr _ _ 24 layer (fun x member =>
    programmed_off cache rows table fresh S x (fun i same => clear i (same ▸ member)))

private theorem programmed_at (cache : CompressionCache) (rows : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (S : Finset Index)
    (inj : Set.InjOn rows (S : Set Index)) (empty : ∀ i, cache (rows i) = none)
    (i : Index) (hi : i ∈ S) :
    fromOut (tableExtending cache (reprogramFinset rows table fresh S) (rows i)) = fresh i := by
  change fromOut ((cache (rows i)).getD (reprogramFinset rows table fresh S (rows i))) = fresh i
  rw [empty i, reprogramFinset_mem rows table fresh S inj i hi]
  rfl

private theorem choose_congr {ι : Type} {p q : ι → Prop} (e : p = q)
    (hp : ∃ i, p i) (hq : ∃ i, q i) : Classical.choose hp = Classical.choose hq := by
  subst e
  rfl

/-- Programming depends on the cells of the programmed leaves only. -/
private theorem reprogram_congr (cell cell' : Index → Late.Block) (table : Compression)
    (fresh : Index → Late.Digest) (S : Finset Index) (same : ∀ i ∈ S, cell i = cell' i) :
    reprogramFinset cell table fresh S = reprogramFinset cell' table fresh S := by
  funext x
  have e : (fun i : Index => i ∈ S ∧ cell i = x) = (fun i => i ∈ S ∧ cell' i = x) :=
    funext fun i => propext
      ⟨fun h => ⟨h.1, (same i h.1).symm.trans h.2⟩, fun h => ⟨h.1, (same i h.1).trans h.2⟩⟩
  unfold reprogramFinset
  by_cases h : ∃ i ∈ S, cell i = x
  · have h' : ∃ i ∈ S, cell' i = x := by
      obtain ⟨i, hi, hx⟩ := h
      exact ⟨i, hi, (same i hi).symm.trans hx⟩
    rw [dite_eq_left h, dite_eq_left h', choose_congr e h h']
  · have h' : ¬ ∃ i ∈ S, cell' i = x := by
      rintro ⟨i, hi, hx⟩
      exact h ⟨i, hi, (same i hi).trans hx⟩
    rw [dite_eq_right h, dite_eq_right h']

/-! ### The two exact steps -/

/-- Real equals all-programmed when the rows are distinct and uncached. -/
private theorem real_eq_programmed {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α)
    (words : PairIndex → Late.PairCoins) (good : GoodRows cache ab words) :
    𝒟[do let _fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         game permutation cache positions observe (unpackTape words) table
           (fun i => fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)))] =
    𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         programmedGame permutation cache ab positions observe Finset.univ (words, fresh, table)] := by
  have inj : Set.InjOn (rowOf ab (unpackTape words)) ((Finset.univ : Finset Index) : Set Index) :=
    fun _ _ _ _ h => good.2 h
  have programmed := reprogramFinset_dist (rowOf ab (unpackTape words)) Finset.univ inj
    (fun tb _ => game permutation cache positions observe (unpackTape words) tb
      (fun i => fromOut (tableExtending cache tb (rowOf ab (unpackTape words) i))))
  refine programmed.symm.trans ?_
  apply _root_.evalDist_bind_congr; intro fresh
  apply _root_.evalDist_bind_congr; intro table
  have layer : (fun i => fromOut (tableExtending cache
      (reprogramFinset (rowOf ab (unpackTape words)) table fresh Finset.univ)
      (rowOf ab (unpackTape words) i))) = fresh :=
    funext fun i => programmed_at cache _ table fresh Finset.univ inj good.1 i (Finset.mem_univ i)
  exact congrArg (fun leaf => 𝒟[game permutation cache positions observe (unpackTape words)
    (reprogramFinset (rowOf ab (unpackTape words)) table fresh Finset.univ) leaf]) layer

/-- Ideal equals opened-programmed when the rows are distinct and uncached. -/
private theorem ideal_eq_programmed {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α)
    (words : PairIndex → Late.PairCoins) (good : GoodRows cache ab words) :
    𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         programmedGame permutation cache ab positions observe positions (words, fresh, table)] =
    𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         game permutation cache positions observe (unpackTape words) table
           (fun i => if i ∈ positions then
             fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)) else fresh i)] := by
  have inj : Set.InjOn (rowOf ab (unpackTape words)) ((positions : Finset Index) : Set Index) :=
    fun _ _ _ _ h => good.2 h
  have programmed := reprogramFinset_dist (rowOf ab (unpackTape words)) positions inj
    (fun tb lr => game permutation cache positions observe (unpackTape words) tb
      (fun i => if i ∈ positions then
        fromOut (tableExtending cache tb (rowOf ab (unpackTape words) i)) else lr i))
  have left :
      𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
           let table ← $ᵗ Compression
           programmedGame permutation cache ab positions observe positions (words, fresh, table)] =
      𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
           let table ← $ᵗ Compression
           game permutation cache positions observe (unpackTape words)
             (reprogramFinset (rowOf ab (unpackTape words)) table fresh positions)
             (fun i => if i ∈ positions then
               fromOut (tableExtending cache
                 (reprogramFinset (rowOf ab (unpackTape words)) table fresh positions)
                 (rowOf ab (unpackTape words) i)) else fresh i)] := by
    apply _root_.evalDist_bind_congr; intro fresh
    apply _root_.evalDist_bind_congr; intro table
    have layer : fresh = (fun i => if i ∈ positions then
        fromOut (tableExtending cache
          (reprogramFinset (rowOf ab (unpackTape words)) table fresh positions)
          (rowOf ab (unpackTape words) i)) else fresh i) := by
      funext i
      by_cases opened : i ∈ positions
      · simp only [opened, ↓reduceIte]
        exact (programmed_at cache _ table fresh positions inj good.1 i opened).symm
      · simp only [opened, ↓reduceIte]
    exact congrArg (fun leaf => 𝒟[game permutation cache positions observe (unpackTape words)
      (reprogramFinset (rowOf ab (unpackTape words)) table fresh positions) leaf]) layer
  refine left.trans (programmed.trans ?_)
  apply _root_.evalDist_bind_congr; intro fresh
  apply _root_.evalDist_bind_congr; intro table
  have layer : (fun i => if i ∈ positions then
      fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)) else
        (if i ∈ positions then
          fromOut (table (rowOf ab (unpackTape words) i)) else fresh i)) =
      (fun i => if i ∈ positions then
        fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)) else fresh i) := by
    funext i
    by_cases opened : i ∈ positions <;> simp only [opened, ↓reduceIte]
  exact congrArg (fun leaf => 𝒟[game permutation cache positions observe (unpackTape words)
    table leaf]) layer

/-! ### The oracle change -/

/-- With good rows that the tree does not read, the two programmed games differ
only when the observer calls an unopened row. -/
private theorem programmed_pointwise {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (k : Key)
    (good : GoodRows cache ab k.1) (clear : ¬ Reads cache ab k) :
    measureTVDist
      (programmedGame permutation cache ab positions observe Finset.univ k)
      (programmedGame permutation cache ab positions observe positions k) ≤
      (prEvent ((fun result : α × Unit × Bool => result.2.2 = true) <$>
        flaggedIdeal permutation cache ab positions observe k)).toReal := by
  have injAll : Set.InjOn (rowOf ab (unpackTape k.1))
      ((Finset.univ : Finset Index) : Set Index) := fun _ _ _ _ h => good.2 h
  have injOpen : Set.InjOn (rowOf ab (unpackTape k.1))
      ((positions : Finset Index) : Set Index) := fun _ _ _ _ h => good.2 h
  have unread : ∀ i, rowOf ab (unpackTape k.1) i ∉
      rowsRead (tableExtending cache k.2.2) 24 ((List.finRange LENGTH).map k.2.1) :=
    fun i member => clear ⟨i, member⟩
  have treeAll := programmed_tree cache (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 Finset.univ
    ((List.finRange LENGTH).map k.2.1) unread
  have treeOpen := programmed_tree cache (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 positions
    ((List.finRange LENGTH).map k.2.1) unread
  have agree : ∀ query,
      marksInput (fun x => decide (∃ i ∉ positions, rowOf ab (unpackTape k.1) i = x)) query =
        false →
      (⟨tableExtending cache (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 positions),
        permutation⟩ : Oracle).world query =
      (⟨tableExtending cache (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 Finset.univ),
        permutation⟩ : Oracle).world query := by
    intro query unmarked
    rcases query with coins | publicQuery
    · simp only [Oracle.world, QueryImpl.add_apply_inl]
    · rcases publicQuery with x | permQuery
      · have hidden : ¬ ∃ i ∉ positions, rowOf ab (unpackTape k.1) i = x :=
          of_decide_eq_false unmarked
        simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_inj]
        change (cache x).getD (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 positions x) =
          (cache x).getD (reprogramFinset (rowOf ab (unpackTape k.1)) k.2.2 k.2.1 Finset.univ x)
        by_cases isRow : ∃ i, rowOf ab (unpackTape k.1) i = x
        · obtain ⟨i, rfl⟩ := isRow
          have opened : i ∈ positions := by
            by_contra closed
            exact hidden ⟨i, closed, rfl⟩
          rw [reprogramFinset_mem _ k.2.2 k.2.1 positions injOpen i opened,
            reprogramFinset_mem _ k.2.2 k.2.1 Finset.univ injAll i (Finset.mem_univ i)]
        · rw [reprogramFinset_not_mem _ k.2.2 k.2.1 positions x (fun i _ same => isRow ⟨i, same⟩),
            reprogramFinset_not_mem _ k.2.2 k.2.1 Finset.univ x (fun i _ same => isRow ⟨i, same⟩)]
      · rcases permQuery with forward | inverse <;>
          simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr]
  have distance := change_distance_le_hit _ _ _ agree
    (observe
      (Late.node (levels (tableExtending cache k.2.2) 24 ((List.finRange LENGTH).map k.2.1))
        LOG_LENGTH 0)
      (S4.actualOpening (levels (tableExtending cache k.2.2) 24 ((List.finRange LENGTH).map k.2.1))
        (unpackTape k.1) positions))
  rw [measureTVDist_comm]
  unfold programmedGame game viewFrom flaggedIdeal
  dsimp only
  rw [treeAll, treeOpen]
  exact distance

/-- The two programmed games, averaged over one common draw. -/
private theorem programmed_distance {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) :
    measureTVDist
      (keyDraw >>= programmedGame permutation cache ab positions observe Finset.univ)
      (keyDraw >>= programmedGame permutation cache ab positions observe positions) ≤
      (prEvent ((fun result : α × Unit × Bool => result.2.2 = true) <$>
        (keyDraw >>= flaggedIdeal permutation cache ab positions observe))).toReal +
      (prEvent ((fun k : Key => ¬ (GoodRows cache ab k.1 ∧ ¬ Reads cache ab k)) <$>
        keyDraw)).toReal := by
  classical
  have first := distance_bind_le_averaged_bad keyDraw
    (programmedGame permutation cache ab positions observe Finset.univ)
    (fun k => if GoodRows cache ab k.1 ∧ ¬ Reads cache ab k then
      programmedGame permutation cache ab positions observe positions k else
      programmedGame permutation cache ab positions observe Finset.univ k)
    (flaggedIdeal permutation cache ab positions observe)
    (fun k => by
      by_cases clean : GoodRows cache ab k.1 ∧ ¬ Reads cache ab k
      · rw [ite_eq_left_of_eq_true _ _ (eq_true clean)]
        exact programmed_pointwise permutation cache ab positions observe k clean.1 clean.2
      · rw [ite_eq_right_of_eq_false _ _ (eq_false clean), measureTVDist_self]
        exact ENNReal.toReal_nonneg)
  have second := measureTVDist_bind_left_le_prEvent_of_evalDistEq keyDraw
    (fun k => if GoodRows cache ab k.1 ∧ ¬ Reads cache ab k then
      programmedGame permutation cache ab positions observe positions k else
      programmedGame permutation cache ab positions observe Finset.univ k)
    (programmedGame permutation cache ab positions observe positions)
    (fun k => ¬ (GoodRows cache ab k.1 ∧ ¬ Reads cache ab k))
    (fun k clean => EvalDistEq.of_evalDist_eq (by
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Classical.not_not.mp clean))]))
  exact (measureTVDist_triangle _ _ _).trans (add_le_add first second)

/-! ### The three events -/

/-- The tree's inputs on a fresh layer do not depend on the salts, so a row is
among them with probability at most `parents * N / 2^192`. -/
private theorem reads_le (cache : CompressionCache) (ab : Index → Late.Digest × Late.Digest) :
    prEvent ((fun k : Key => Reads cache ab k) <$> keyDraw) ≤
      ((S4.parentCost 24 * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  rw [prEvent_map_eq_id_bind, key_bind]
  have swap :
      𝒟[do let words ← $ᵗ (PairIndex → Late.PairCoins)
           let fresh ← $ᵗ (Index → Late.Digest)
           let table ← $ᵗ Compression
           (pure (Reads cache ab (words, fresh, table)) : ProbComp Prop)] =
      𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
           let table ← $ᵗ Compression
           let words ← $ᵗ (PairIndex → Late.PairCoins)
           (pure (Reads cache ab (words, fresh, table)) : ProbComp Prop)] := by
    rw [distribution_bind_comm ($ᵗ (PairIndex → Late.PairCoins)) ($ᵗ (Index → Late.Digest))]
    apply _root_.evalDist_bind_congr; intro fresh
    exact distribution_bind_comm ($ᵗ (PairIndex → Late.PairCoins)) ($ᵗ Compression) _
  refine (le_of_eq ((EvalDistEq.of_evalDist_eq swap).prEvent_eq id)).trans ?_
  apply prEvent_bind_le_of_forall_le; intro fresh
  apply prEvent_bind_le_of_forall_le; intro table
  have listed := rows_in_list_le ab
    (rowsRead (tableExtending cache table) 24 ((List.finRange LENGTH).map fresh))
  rw [rows_read_length, prEvent_map_eq_id_bind] at listed
  exact listed

/-- Bad rows or a row among the tree's inputs. -/
private theorem unclean_le (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ k, cache k ≠ none → k ∈ keys) (ab : Index → Late.Digest × Late.Digest) :
    prEvent ((fun k : Key => ¬ (GoodRows cache ab k.1 ∧ ¬ Reads cache ab k)) <$> keyDraw) ≤
      ((keys.card * LENGTH + LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 +
        ((S4.parentCost 24 * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  have bad : prEvent ((fun k : Key => ¬ GoodRows cache ab k.1) <$> keyDraw) ≤
      ((keys.card * LENGTH + LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
    rw [prEvent_map_eq_id_bind, key_bind]
    have drop :
        𝒟[do let words ← $ᵗ (PairIndex → Late.PairCoins)
             let _fresh ← $ᵗ (Index → Late.Digest)
             let _table ← $ᵗ Compression
             (pure (¬ GoodRows cache ab words) : ProbComp Prop)] =
        𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
            (pure (¬ GoodRows cache ab words) : ProbComp Prop)] := by
      apply _root_.evalDist_bind_congr; intro words
      exact (OracleComp.evalDist_bind_const ($ᵗ (Index → Late.Digest)) _).trans
        (OracleComp.evalDist_bind_const ($ᵗ Compression) _)
    refine (le_of_eq ((EvalDistEq.of_evalDist_eq drop).prEvent_eq id)).trans ?_
    have rows := bad_rows_le cache keys covered ab
    rw [prEvent_map_eq_id_bind] at rows
    exact rows
  refine (prEvent_mono_of_support keyDraw _
    (fun k => ¬ GoodRows cache ab k.1 ∨ Reads cache ab k) ?_).trans
    ((prEvent_or_le keyDraw _ _).trans (add_le_add bad (reads_le cache ab)))
  intro k _ dirty
  by_cases good : GoodRows cache ab k.1
  · right
    by_contra clear
    exact dirty ⟨good, clear⟩
  · exact Or.inl good

/-- The observer of the opened-programmed game calls an unopened row with
probability at most `8 * budget / 2^128`, apart from a shared midpoint. Its
view does not depend on the private halves of unopened leaves, so they can be
drawn after its calls are fixed. -/
private theorem flag_le {α : Type} (permutation : Perm) (cache : CompressionCache)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    prEvent ((fun result : α × Unit × Bool => result.2.2 = true) <$>
      (keyDraw >>= flaggedIdeal permutation cache ab positions observe)) ≤
      (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 + ((8 * budget : Nat) : ENNReal) / 2 ^ 128 := by
  let : MeasurableSpace (α × Unit × Bool) := ⊤
  rw [key_bind]
  have merged := merge_uniform_bind positions (fun words =>
    do let fresh ← $ᵗ (Index → Late.Digest)
       let table ← $ᵗ Compression
       flaggedIdeal permutation cache ab positions observe (words, fresh, table))
  refine (le_of_eq ((EvalDistEq.of_evalDist_eq merged).prEvent_eq
    (fun result => result.2.2 = true)).symm).trans ?_
  apply prEvent_bind_le_of_forall_le; intro sLOpen
  refine (prEvent_bind_le_prEvent_add_of_support _ _ BadMidpoint _ ?_).trans
    (add_le_add badMidpoint_le le_rfl)
  intro sM _ goodMid
  apply prEvent_bind_le_of_forall_le; intro sROpen
  -- The revealed words stand in for the merged ones wherever only opened leaves are read.
  have traced : ∀ (sLHid sRHid : PairIndex → BitVec 128) (fresh : Index → Late.Digest)
      (table : Compression),
      flaggedIdeal permutation cache ab positions observe
        (mergeWords positions sLOpen sM sROpen sLHid sRHid, fresh, table) =
      (fun result : α × List Late.Block => (result.1, (), result.2.any (fun x =>
        decide (∃ i ∉ positions, rowOf ab
          (unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid)) i = x)))) <$>
        fixedOracleRun
          ⟨tableExtending cache (reprogramFinset
            (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh positions),
            permutation⟩
          (traceCompression (observe
            (Late.node (levels (tableExtending cache (reprogramFinset
              (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh positions)) 24
              ((List.finRange LENGTH).map fresh)) LOG_LENGTH 0)
            (S4.actualOpening (levels (tableExtending cache (reprogramFinset
              (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh positions)) 24
              ((List.finRange LENGTH).map fresh))
              (unpackTape (combineWords sLOpen sM sROpen)) positions))) := by
    intro sLHid sRHid fresh table
    have cells : reprogramFinset
        (rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid))) table fresh
        positions =
        reprogramFinset (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
          positions :=
      reprogram_congr _ _ table fresh positions (fun i opened => by
        unfold rowOf
        rw [unpack_merge_opened positions sLOpen sM sROpen sLHid sRHid i opened])
    have shown : ∀ retained : Late.Levels,
        S4.actualOpening retained
          (unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid)) positions =
        S4.actualOpening retained (unpackTape (combineWords sLOpen sM sROpen)) positions :=
      fun retained => S4.actualOpening_salt_congr retained _ _ positions
        (fun i opened => unpack_merge_opened positions sLOpen sM sROpen sLHid sRHid i opened)
    unfold flaggedIdeal
    dsimp only
    rw [cells, shown, flagged_run_trace]
    simp only [Bool.false_or]
  simp only [traced]
  -- Draw the private halves after the observer has run.
  have swap :
      𝒟[do let sLHid ← $ᵗ (PairIndex → BitVec 128)
           let sRHid ← $ᵗ (PairIndex → BitVec 128)
           let fresh ← $ᵗ (Index → Late.Digest)
           let table ← $ᵗ Compression
           (fun result : α × List Late.Block => (result.1, (), result.2.any (fun x =>
             decide (∃ i ∉ positions, rowOf ab
               (unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid)) i = x)))) <$>
             fixedOracleRun
               ⟨tableExtending cache (reprogramFinset
                 (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh positions),
                 permutation⟩
               (traceCompression (observe
                 (Late.node (levels (tableExtending cache (reprogramFinset
                   (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
                   positions)) 24 ((List.finRange LENGTH).map fresh)) LOG_LENGTH 0)
                 (S4.actualOpening (levels (tableExtending cache (reprogramFinset
                   (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
                   positions)) 24 ((List.finRange LENGTH).map fresh))
                   (unpackTape (combineWords sLOpen sM sROpen)) positions)))] =
      𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
           let table ← $ᵗ Compression
           let traced ← fixedOracleRun
               ⟨tableExtending cache (reprogramFinset
                 (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh positions),
                 permutation⟩
               (traceCompression (observe
                 (Late.node (levels (tableExtending cache (reprogramFinset
                   (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
                   positions)) 24 ((List.finRange LENGTH).map fresh)) LOG_LENGTH 0)
                 (S4.actualOpening (levels (tableExtending cache (reprogramFinset
                   (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
                   positions)) 24 ((List.finRange LENGTH).map fresh))
                   (unpackTape (combineWords sLOpen sM sROpen)) positions)))
           let p ← $ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128))
           (pure (traced.1, (), traced.2.any (fun x =>
             decide (∃ i ∉ positions, rowOf ab
               (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x))) :
             ProbComp (α × Unit × Bool))] := by
    refine (prod_uniform_bind (fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
      do let fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         (fun result : α × List Late.Block => (result.1, (), result.2.any (fun x =>
           decide (∃ i ∉ positions, rowOf ab
             (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x)))) <$>
           fixedOracleRun
             ⟨tableExtending cache (reprogramFinset
               (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh positions),
               permutation⟩
             (traceCompression (observe
               (Late.node (levels (tableExtending cache (reprogramFinset
                 (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
                 positions)) 24 ((List.finRange LENGTH).map fresh)) LOG_LENGTH 0)
               (S4.actualOpening (levels (tableExtending cache (reprogramFinset
                 (rowOf ab (unpackTape (combineWords sLOpen sM sROpen))) table fresh
                 positions)) 24 ((List.finRange LENGTH).map fresh))
                 (unpackTape (combineWords sLOpen sM sROpen)) positions))))).trans ?_
    rw [distribution_bind_comm ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))
      ($ᵗ (Index → Late.Digest))]
    apply _root_.evalDist_bind_congr; intro fresh
    rw [distribution_bind_comm ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))
      ($ᵗ Compression)]
    apply _root_.evalDist_bind_congr; intro table
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    exact distribution_bind_comm
      ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128))) _ _
  refine (le_of_eq ((EvalDistEq.of_evalDist_eq swap).prEvent_eq
    (fun result => result.2.2 = true))).trans ?_
  apply prEvent_bind_le_of_forall_le; intro fresh
  apply prEvent_bind_le_of_forall_le; intro table
  apply prEvent_bind_le_of_forall_le_of_support; intro traced reached
  have short := trace_run_length _ _ budget (bounded _ _) traced reached
  have asMap :
      (do let p ← $ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128))
          (pure (traced.1, (), traced.2.any (fun x =>
            decide (∃ i ∉ positions, rowOf ab
              (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x))) :
            ProbComp (α × Unit × Bool))) =
      (fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        (traced.1, (), traced.2.any (fun x =>
          decide (∃ i ∉ positions, rowOf ab
            (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x)))) <$>
        ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128))) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [asMap, prEvent_map]
  exact (trace_hit ab positions sLOpen sM sROpen goodMid traced.2).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left 8 short)) _)

/-! ### The step -/

/-- Loss of the step for a cache with `known` keys and an observer with `budget` calls. -/
noncomputable def afterLoss (known budget : Nat) : ℝ :=
  3 * (((known * LENGTH + LENGTH * LENGTH : Nat) : ℝ) / 2 ^ 192) +
    ((S4.parentCost 24 * LENGTH : Nat) : ℝ) / 2 ^ 192 +
    (((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
    ((8 * budget : Nat) : ℝ) / 2 ^ 128

/-- **All unopened leaf digests are fresh at once.** After the unsalted calls,
the real game and the ideal game are within `afterLoss`. -/
theorem after_distance {α : Type} (permutation : Perm) (cache : CompressionCache)
    (keys : Finset Late.Block) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    measureTVDist (realAfter permutation cache ab positions observe)
      (idealAfter permutation cache ab positions observe) ≤ afterLoss keys.card budget := by
  have realForm : 𝒟[realAfter permutation cache ab positions observe] =
      𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
          (do let _fresh ← $ᵗ (Index → Late.Digest)
              let table ← $ᵗ Compression
              game permutation cache positions observe (unpackTape words) table
                (fun i => fromOut (tableExtending cache table (rowOf ab (unpackTape words) i))))] := by
    unfold realAfter
    rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ (PairIndex → Late.PairCoins))]
    apply _root_.evalDist_bind_congr; intro words
    exact (OracleComp.evalDist_bind_const ($ᵗ (Index → Late.Digest)) _).symm
  have idealForm : 𝒟[idealAfter permutation cache ab positions observe] =
      𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
          (do let fresh ← $ᵗ (Index → Late.Digest)
              let table ← $ᵗ Compression
              game permutation cache positions observe (unpackTape words) table
                (fun i => if i ∈ positions then
                  fromOut (tableExtending cache table (rowOf ab (unpackTape words) i))
                  else fresh i))] := by
    unfold idealAfter
    rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ (PairIndex → Late.PairCoins))]
    apply _root_.evalDist_bind_congr; intro words
    exact distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Late.Digest)) _
  have step1 := measureTVDist_bind_left_le_prEvent_of_evalDistEq
    ($ᵗ (PairIndex → Late.PairCoins))
    (fun words => do
      let _fresh ← $ᵗ (Index → Late.Digest)
      let table ← $ᵗ Compression
      game permutation cache positions observe (unpackTape words) table
        (fun i => fromOut (tableExtending cache table (rowOf ab (unpackTape words) i))))
    (fun words => do
      let fresh ← $ᵗ (Index → Late.Digest)
      let table ← $ᵗ Compression
      programmedGame permutation cache ab positions observe Finset.univ (words, fresh, table))
    (fun words => ¬ GoodRows cache ab words)
    (fun words good => EvalDistEq.of_evalDist_eq
      (real_eq_programmed permutation cache ab positions observe words (Classical.not_not.mp good)))
  have step3 := measureTVDist_bind_left_le_prEvent_of_evalDistEq
    ($ᵗ (PairIndex → Late.PairCoins))
    (fun words => do
      let fresh ← $ᵗ (Index → Late.Digest)
      let table ← $ᵗ Compression
      programmedGame permutation cache ab positions observe positions (words, fresh, table))
    (fun words => do
      let fresh ← $ᵗ (Index → Late.Digest)
      let table ← $ᵗ Compression
      game permutation cache positions observe (unpackTape words) table
        (fun i => if i ∈ positions then
          fromOut (tableExtending cache table (rowOf ab (unpackTape words) i)) else fresh i))
    (fun words => ¬ GoodRows cache ab words)
    (fun words good => EvalDistEq.of_evalDist_eq
      (ideal_eq_programmed permutation cache ab positions observe words (Classical.not_not.mp good)))
  have step2 := programmed_distance permutation cache ab positions observe
  rw [key_bind (programmedGame permutation cache ab positions observe Finset.univ),
    key_bind (programmedGame permutation cache ab positions observe positions)] at step2
  have bad := bad_rows_le cache keys covered ab
  have unclean := unclean_le cache keys covered ab
  have flag := flag_le permutation cache ab positions observe budget bounded
  have finite192 : ∀ n : Nat, ((n : Nat) : ENNReal) / 2 ^ 192 ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)
  have real192 : ∀ n : Nat, (((n : Nat) : ENNReal) / 2 ^ 192).toReal = ((n : Nat) : ℝ) / 2 ^ 192 :=
    fun n => by
      simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat]
  have badReal := ENNReal.toReal_mono (finite192 _) bad
  rw [real192] at badReal
  have uncleanReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨finite192 _, finite192 _⟩) unclean
  rw [ENNReal.toReal_add (finite192 _) (finite192 _), real192, real192] at uncleanReal
  have finiteMid : (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)
  have finiteObs : ((8 * budget : Nat) : ENNReal) / 2 ^ 128 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)
  have flagReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finiteMid, finiteObs⟩) flag
  rw [ENNReal.toReal_add finiteMid finiteObs] at flagReal
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at flagReal
  rw [measureTVDist, realForm, idealForm, ← measureTVDist]
  have total := (measureTVDist_triangle _ _ _).trans (add_le_add step1
    ((measureTVDist_triangle _ _ _).trans (add_le_add step2 step3)))
  refine total.trans ?_
  unfold afterLoss
  linarith

end CommitGolfCandidate.S4Hiding
