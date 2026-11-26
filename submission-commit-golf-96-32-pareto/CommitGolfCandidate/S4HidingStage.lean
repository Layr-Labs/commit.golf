import CommitGolfCandidate.S4HidingIdeal

/-! Two messages that agree on the opened positions give close observations.

`observation` is the second half of the hiding game after the first stage has
fixed a cache: a fresh table extending that cache, uniform pair words, the
honest one-pass tree and opening, and the observing stage with the same oracle.
`idealObservation` is the same game with a fresh digest at every unopened leaf.
It reads the message only at opened positions.

The three unsalted calls of all leaves are run first under lazy sampling. They
add `3 * LENGTH` entries to the cache and fix both content digests of every
leaf, so that the final rows are fixed functions of the pair words and
`after_distance` applies. In the ideal game the unsalted calls of unopened
leaves have no effect and fold back into the table. The staging follows
dadon's b4f31491 (`realObs0_stage`, `idealObs0_stage`), with the digests handed
to the continuation as values. -/
namespace CommitGolfCandidate.S4Hiding
open CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance stageDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

attribute [local irreducible] List.finRange

/-! ### The games -/

/-- What the observer computes from the honest root and opening under one fixed
oracle and one salt tape. -/
def view {α : Type} (oracle : Oracle) (message : Message) (salt : Late.SaltTape)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  fixedOracleRun oracle
    (observe (Late.node (tree oracle.compression message salt) LOG_LENGTH 0)
      (S4.actualOpening (tree oracle.compression message salt) salt positions))

/-- The hiding game after a first stage that left `cache`. -/
def observation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let words ← $ᵗ (PairIndex → Late.PairCoins)
  view ⟨tableExtending cache table, permutation⟩ message (unpackTape words) positions observe

/-- Leaf digests with a fresh digest at every unopened leaf. -/
def mixedLayer (H : Compression) (message : Message) (salt : Late.SaltTape)
    (fresh : Index → Late.Digest) (positions : Positions) : List Late.Digest :=
  (List.finRange LENGTH).map fun i =>
    if i ∈ positions then leafDigest H (i.val.testBit 0) (salt i) (message i) else fresh i

/-- The game in which every unopened leaf digest is a fresh uniform digest. It
does not mention the message outside the opened positions. -/
def idealObservation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let words ← $ᵗ (PairIndex → Late.PairCoins)
  let fresh ← $ᵗ (Index → Late.Digest)
  viewFrom ⟨tableExtending cache table, permutation⟩
    (mixedLayer (tableExtending cache table) message (unpackTape words) fresh positions)
    (unpackTape words) positions observe

theorem ideal_observation_congr {α : Type} (permutation : Perm) (cache : CompressionCache)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α) :
    idealObservation permutation cache left positions observe =
      idealObservation permutation cache right positions observe := by
  have layers : ∀ (H : Compression) (salt : Late.SaltTape) (fresh : Index → Late.Digest),
      mixedLayer H left salt fresh positions = mixedLayer H right salt fresh positions := by
    intro H salt fresh
    unfold mixedLayer
    apply List.map_congr_left
    intro i _
    by_cases opened : i ∈ positions
    · simp only [opened, ↓reduceIte, agree i opened]
    · simp only [opened, ↓reduceIte]
  unfold idealObservation
  simp only [layers]

/-! ### The unsalted calls of all leaves -/

/-- The three unsalted calls of every leaf, in index order. -/
def preludeM (message : Message) : OracleComp World (List (Late.Digest × Late.Digest)) :=
  (List.finRange LENGTH).mapM fun i => prehashM (message i)

def prelude (H : Compression) (message : Message) : List (Late.Digest × Late.Digest) :=
  (List.finRange LENGTH).map fun i => prehash H (message i)

theorem run_prelude (oracle : Oracle) (message : Message) {α : Type}
    (next : List (Late.Digest × Late.Digest) → OracleComp World α) :
    fixedOracleRun oracle (preludeM message >>= next) =
      fixedOracleRun oracle (next (prelude oracle.compression message)) := by
  unfold preludeM prelude
  exact run_mapM oracle (List.finRange LENGTH) _
    (fun i => prehash oracle.compression (message i))
    (fun i _ next => run_prehash oracle (message i) next) next

theorem prelude_bound (message : Message) : PublicQueryBound (preludeM message) (3 * LENGTH) := by
  have total := mapM_bound (List.finRange LENGTH) (fun i => prehashM (message i)) 3
    (fun i => prehash_bound (message i))
    (fun results => (pure results : OracleComp World (List (Late.Digest × Late.Digest)))) 0
    (fun _ _ => trivial)
  rw [List.length_finRange] at total
  simpa only [preludeM, bind_pure, Nat.add_zero] using total

/-- The two content digests of leaf `i`, read from the list the unsalted calls return. -/
def abOf (ab : List (Late.Digest × Late.Digest)) (i : Index) : Late.Digest × Late.Digest :=
  ab[i.val]?.getD (0, 0)

theorem ab_of_prelude (H : Compression) (message : Message) (i : Index) :
    abOf (prelude H message) i = prehash H (message i) := by
  unfold abOf prelude
  have inside : i.val < (List.finRange LENGTH).length := by
    rw [List.length_finRange]
    exact i.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem inside, List.getElem_finRange,
    Option.map_some, Option.getD_some]
  congr 1

/-- Everything after the unsalted calls in the real game, as an oracle program. -/
def realRestM {α : Type} (ab : List (Late.Digest × Late.Digest)) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let words ← (liftM ($ᵗ (PairIndex → Late.PairCoins)) :
    OracleComp World (PairIndex → Late.PairCoins))
  let leaves ← (List.finRange LENGTH).mapM fun i =>
    Late.hash (rowOf (abOf ab) (unpackTape words) i)
  let retained ← S4.levelsM S4.active Late.hash 24 leaves
  observe (Late.node retained LOG_LENGTH 0) (S4.actualOpening retained (unpackTape words) positions)

theorem run_real_rest {α : Type} (oracle : Oracle) (ab : List (Late.Digest × Late.Digest))
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) :
    fixedOracleRun oracle (realRestM ab positions observe) =
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        viewFrom oracle
          ((List.finRange LENGTH).map fun i =>
            fromOut (oracle.compression (rowOf (abOf ab) (unpackTape words) i)))
          (unpackTape words) positions observe) := by
  unfold realRestM
  rw [run_coins_bind]
  apply bind_congr
  intro words
  rw [run_mapM oracle (List.finRange LENGTH) _
    (fun i => fromOut (oracle.compression (rowOf (abOf ab) (unpackTape words) i)))
    (fun i _ next => run_hash oracle _ next), run_levels]
  rfl

/-- Everything after the unsalted calls in the ideal game: unopened leaves are not hashed. -/
def idealRestM {α : Type} (ab : List (Late.Digest × Late.Digest)) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let words ← (liftM ($ᵗ (PairIndex → Late.PairCoins)) :
    OracleComp World (PairIndex → Late.PairCoins))
  let fresh ← (liftM ($ᵗ (Index → Late.Digest)) : OracleComp World (Index → Late.Digest))
  let leaves ← (List.finRange LENGTH).mapM fun i =>
    if i ∈ positions then Late.hash (rowOf (abOf ab) (unpackTape words) i)
    else (pure (fresh i) : OracleComp World Late.Digest)
  let retained ← S4.levelsM S4.active Late.hash 24 leaves
  observe (Late.node retained LOG_LENGTH 0) (S4.actualOpening retained (unpackTape words) positions)

theorem run_ideal_rest {α : Type} (oracle : Oracle) (ab : List (Late.Digest × Late.Digest))
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) :
    fixedOracleRun oracle (idealRestM ab positions observe) =
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        ($ᵗ (Index → Late.Digest)) >>= fun fresh =>
          viewFrom oracle
            ((List.finRange LENGTH).map fun i =>
              if i ∈ positions then
                fromOut (oracle.compression (rowOf (abOf ab) (unpackTape words) i))
              else fresh i)
            (unpackTape words) positions observe) := by
  unfold idealRestM
  rw [run_coins_bind]
  apply bind_congr
  intro words
  rw [run_coins_bind]
  apply bind_congr
  intro fresh
  rw [run_mapM oracle (List.finRange LENGTH) _
    (fun i => if i ∈ positions then
      fromOut (oracle.compression (rowOf (abOf ab) (unpackTape words) i)) else fresh i)
    (fun i _ next => by
      by_cases opened : i ∈ positions
      · simp only [opened, ↓reduceIte]
        exact run_hash oracle _ next
      · simp only [opened, ↓reduceIte, pure_bind]), run_levels]
  rfl

/-! ### Staging -/

/-- The honest leaf digest is the table's answer at the leaf's final row. -/
private theorem leaf_digest_row (H : Compression) (message : Message) (salt : Late.SaltTape)
    (i : Index) :
    leafDigest H (i.val.testBit 0) (salt i) (message i) =
      fromOut (H (rowOf (abOf (prelude H message)) salt i)) := by
  unfold rowOf
  rw [ab_of_prelude]
  rfl

theorem observation_staged {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) :
    𝒟[observation permutation cache message positions observe] =
      𝒟[do let result ← compressionRun permutation (preludeM message) cache
           realAfter permutation result.2 (abOf result.1) positions observe] := by
  have asProgram : ∀ table : Compression,
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        view ⟨tableExtending cache table, permutation⟩ message (unpackTape words) positions
          observe) =
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (preludeM message >>= fun ab => realRestM ab positions observe) := by
    intro table
    rw [run_prelude, run_real_rest]
    apply bind_congr
    intro words
    unfold view tree viewFrom
    rw [leaf_layer_eq]
    have layer : (fun index : Index =>
        leafDigest (tableExtending cache table) (index.val.testBit 0) (unpackTape words index)
          (message index)) =
        (fun i => fromOut (tableExtending cache table
          (rowOf (abOf (prelude (tableExtending cache table) message)) (unpackTape words) i))) :=
      funext fun i => leaf_digest_row _ message (unpackTape words) i
    rw [layer]
  trans 𝒟[do let table ← $ᵗ Compression
             fixedOracleRun ⟨tableExtending cache table, permutation⟩
               (preludeM message >>= fun ab => realRestM ab positions observe)]
  · unfold observation
    apply _root_.evalDist_bind_congr
    intro table
    rw [asProgram]
  · rw [staged_sampling permutation cache (preludeM message)
      (fun ab => realRestM ab positions observe)]
    apply _root_.evalDist_bind_congr
    intro result
    unfold realAfter
    apply _root_.evalDist_bind_congr
    intro table
    rw [run_real_rest]
    rfl

theorem ideal_staged {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) :
    𝒟[idealObservation permutation cache message positions observe] =
      𝒟[do let result ← compressionRun permutation (preludeM message) cache
           idealAfter permutation result.2 (abOf result.1) positions observe] := by
  have asProgram : ∀ table : Compression,
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        ($ᵗ (Index → Late.Digest)) >>= fun fresh =>
          viewFrom ⟨tableExtending cache table, permutation⟩
            (mixedLayer (tableExtending cache table) message (unpackTape words) fresh positions)
            (unpackTape words) positions observe) =
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (preludeM message >>= fun ab => idealRestM ab positions observe) := by
    intro table
    rw [run_prelude, run_ideal_rest]
    apply bind_congr
    intro words
    apply bind_congr
    intro fresh
    have layer : mixedLayer (tableExtending cache table) message (unpackTape words) fresh
        positions =
        (List.finRange LENGTH).map (fun i => if i ∈ positions then
          fromOut (tableExtending cache table
            (rowOf (abOf (prelude (tableExtending cache table) message)) (unpackTape words) i))
          else fresh i) := by
      unfold mixedLayer
      apply List.map_congr_left
      intro i _
      by_cases opened : i ∈ positions
      · simp only [opened, ↓reduceIte]
        exact leaf_digest_row _ message (unpackTape words) i
      · simp only [opened, ↓reduceIte]
    rw [layer]
  trans 𝒟[do let table ← $ᵗ Compression
             fixedOracleRun ⟨tableExtending cache table, permutation⟩
               (preludeM message >>= fun ab => idealRestM ab positions observe)]
  · unfold idealObservation
    apply _root_.evalDist_bind_congr
    intro table
    rw [asProgram]
  · rw [staged_sampling permutation cache (preludeM message)
      (fun ab => idealRestM ab positions observe)]
    apply _root_.evalDist_bind_congr
    intro result
    unfold idealAfter
    apply _root_.evalDist_bind_congr
    intro table
    rw [run_ideal_rest]
    rfl

/-! ### The distance -/

theorem after_loss_nonneg (known budget : Nat) : 0 ≤ afterLoss known budget := by
  unfold afterLoss
  positivity

theorem after_loss_mono {known larger : Nat} (le : known ≤ larger) (budget : Nat) :
    afterLoss known budget ≤ afterLoss larger budget := by
  unfold afterLoss
  have cast : ((known * LENGTH + LENGTH * LENGTH : Nat) : ℝ) ≤
      ((larger * LENGTH + LENGTH * LENGTH : Nat) : ℝ) :=
    Nat.cast_le.mpr (Nat.add_le_add_right (Nat.mul_le_mul_right LENGTH le) _)
  have scaled := div_le_div_of_nonneg_right cast (by positivity : (0 : ℝ) ≤ 2 ^ 192)
  linarith

/-- A bound on the continuations at every reachable draw bounds the distance
after the draw. Stated for an arbitrary draw, so that the reachability
hypothesis has the form `x ∈ support mx` at the use site. -/
private theorem distance_bind_of_support {β γ : Type} (mx : ProbComp β) (f g : β → ProbComp γ)
    {δ : ℝ} (nonneg : 0 ≤ δ)
    (h : ∀ x ∈ support mx, measureTVDist (f x) (g x) ≤ δ) :
    measureTVDist (mx >>= f) (mx >>= g) ≤ δ := by
  rw [bind_eq_attach_bind mx, bind_eq_attach_bind mx]
  exact measureTVDist_bind_left_le_of_forall_le _ _ _ nonneg (fun x => h x.1 x.2)

/-- The real game is close to the ideal game, for one message. The unsalted
calls add `3 * LENGTH` keys to the first stage's cache. -/
theorem observation_ideal_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    measureTVDist (observation permutation cache message positions observe)
      (idealObservation permutation cache message positions observe) ≤
      afterLoss (keys.card + 3 * LENGTH) budget := by
  have real := observation_staged permutation cache message positions observe
  have ideal := ideal_staged permutation cache message positions observe
  rw [measureTVDist, real, ideal, ← measureTVDist]
  apply distance_bind_of_support _ _ _ (after_loss_nonneg _ _)
  intro result reached
  obtain ⟨known, size, covers⟩ := cache_covered permutation (preludeM message) (3 * LENGTH)
    (prelude_bound message) cache keys covered result reached
  exact (after_distance permutation result.2 known covers (abOf result.1) positions observe
    budget bounded).trans (after_loss_mono size budget)

/-- Statistical hiding for two fixed messages agreeing on the opened set,
conditional on any finite cache of earlier oracle answers. Each message is
compared with the ideal game, which the two messages share. -/
theorem observation_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    measureTVDist (observation permutation cache left positions observe)
      (observation permutation cache right positions observe) ≤
      2 * afterLoss (keys.card + 3 * LENGTH) budget := by
  have leftSide := observation_ideal_distance permutation cache keys covered left positions
    observe budget bounded
  have rightSide := observation_ideal_distance permutation cache keys covered right positions
    observe budget bounded
  rw [ideal_observation_congr permutation cache left right positions agree observe] at leftSide
  rw [measureTVDist_comm] at rightSide
  exact ((measureTVDist_triangle _ _ _).trans (add_le_add leftSide rightSide)).trans
    (le_of_eq (by ring))

end CommitGolfCandidate.S4Hiding
