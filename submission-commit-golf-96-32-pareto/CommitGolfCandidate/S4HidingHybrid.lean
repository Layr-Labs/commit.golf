import CommitGolfCandidate.S4HidingTree
import CommitGolfCandidate.LateHidingLeaf

/-! Two messages that agree on the opened positions give close observations.

`observation` is the second half of the hiding game after the first stage has
fixed a cache: a fresh table extending that cache, a uniform salt tape, the
honest one-pass tree and opening, and the observing stage with the same oracle.
One unopened coordinate is changed at a time. Its salt is absent from the
opening, so the rest of the game is a continuation that receives only the
leaf's digest, namely the one-pass tree with that leaf supplied followed by the
observer. `hidden_leaf_distance` replaces the digest by a fresh one, which no
longer depends on the coordinate. The coordinate hybrid follows the base tree's
`HidingCoordinate` and `HidingHybrid` (dadon's c9b8af82), with the one-pass
tree in place of its per-proof-byte recomputation. -/
namespace CommitGolfCandidate.S4Hiding
open CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance hybridDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

attribute [local irreducible] List.finRange

/-- Resampling one coordinate of a uniform function preserves its distribution,
also for randomized continuations. Stated generically to avoid expanding the
challenge's enormous finite salt space during elaboration. -/
theorem uniform_coordinate_bind {D R α : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    𝒟[do let values ← $ᵗ (D → R)
         let value ← $ᵗ R
         next (Function.update values index value)] =
    𝒟[do let values ← $ᵗ (D → R); next values] := by
  have marginal : 𝒟[do let value ← $ᵗ R
                        let values ← $ᵗ (D → R)
                        pure (Function.update values index value)] = 𝒟[$ᵗ (D → R)] := by
    simpa only [bind_pure] using evalDist_uniformSample_bind_update_map
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index
      (fun values : D → R => values)
  trans 𝒟[do let value ← $ᵗ R
              let values ← $ᵗ (D → R)
              next (Function.update values index value)]
  · exact distribution_bind_comm _ _ _
  · trans 𝒟[(do let value ← $ᵗ R
                let values ← $ᵗ (D → R)
                pure (Function.update values index value)) >>= next]
    · simp only [bind_assoc, pure_bind]
    · rw [evalDist_bind_of_discrete, marginal, ← evalDist_bind_of_discrete]

/-- What the observer computes from the honest root and opening under one fixed
oracle and one salt tape. -/
def view {α : Type} (oracle : Oracle) (message : Message) (salt : Late.SaltTape)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  fixedOracleRun oracle
    (observe (Late.node (tree oracle.compression message salt) LOG_LENGTH 0)
      (S4.opening S4.active (tree oracle.compression message salt) salt positions))

/-- The hiding game after a first stage that left `cache`. -/
def observation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let salt ← $ᵗ Late.SaltTape
  view ⟨tableExtending cache table, permutation⟩ message salt positions observe

/-- Everything after one hidden leaf, as an oracle program in that leaf's digest:
the one-pass tree with the leaf supplied, the opening, and the observer. -/
def observeExcept {α : Type} (message : Message) (salt : Late.SaltTape) (positions : Positions)
    (hidden : Index) (observe : Commitment → Proof → OracleComp World α) (digest : Late.Digest) :
    OracleComp World α := do
  let retained ← treeExceptM message salt hidden digest
  observe (Late.node retained LOG_LENGTH 0)
    (S4.opening S4.active retained (Function.update salt hidden 0) positions)

theorem observe_except_bound {α : Type} (message : Message) (salt : Late.SaltTape)
    (positions : Positions) (hidden : Index) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (digest : Late.Digest) :
    PublicQueryBound (observeExcept message salt positions hidden observe digest)
      (5 * LENGTH + budget) :=
  public_query_bound_bind (tree_except_bound message salt hidden digest)
    (fun _ => bounded _ _)

/-- Supplying the hidden leaf's own digest recovers the honest view for the
updated message and salt tape. The opening never reads the hidden salt. -/
theorem observe_except_view {α : Type} (oracle : Oracle) (message : Message)
    (salt : Late.SaltTape) (positions : Positions) (hidden : Index) (unopened : hidden ∉ positions)
    (observe : Commitment → Proof → OracleComp World α) (value : Entry) (fresh : Late.Salt) :
    fixedOracleRun oracle (observeExcept message salt positions hidden observe
        (leafDigest oracle.compression (hidden.val.testBit 0) fresh value)) =
      view oracle (Function.update message hidden value) (Function.update salt hidden fresh)
        positions observe := by
  unfold observeExcept view tree
  rw [run_tree_except, leaf_layer_except_update,
    opening_hidden_salt _ salt positions hidden unopened 0 fresh]

/-- The full salt tape may be sampled by drawing all other randomness before
the hidden coordinate. No salt is conditioned on the public transcript. -/
theorem observation_split {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (hidden : Index) :
    𝒟[observation permutation cache message positions observe] =
      𝒟[do let salt ← $ᵗ Late.SaltTape
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Late.Salt
           view ⟨tableExtending cache table, permutation⟩ message
             (Function.update salt hidden fresh) positions observe] := by
  unfold observation
  trans 𝒟[do let table ← $ᵗ Compression
              let salt ← $ᵗ Late.SaltTape
              let fresh ← $ᵗ Late.Salt
              view ⟨tableExtending cache table, permutation⟩ message
                (Function.update salt hidden fresh) positions observe]
  · apply _root_.evalDist_bind_congr
    intro table
    exact (uniform_coordinate_bind hidden (fun salt =>
      view ⟨tableExtending cache table, permutation⟩ message salt positions observe)).symm
  · exact distribution_bind_comm _ _ _

theorem observation_update {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (hidden : Index) (unopened : hidden ∉ positions) (value : Entry) :
    𝒟[observation permutation cache (Function.update message hidden value) positions observe] =
      𝒟[do let salt ← $ᵗ Late.SaltTape
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Late.Salt
           let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
           fixedOracleRun oracle (observeExcept message salt positions hidden observe
             (leafDigest oracle.compression (hidden.val.testBit 0) fresh value))] := by
  rw [observation_split permutation cache _ positions observe hidden]
  apply _root_.evalDist_bind_congr
  intro salt
  apply _root_.evalDist_bind_congr
  intro table
  apply _root_.evalDist_bind_congr
  intro fresh
  rw [observe_except_view _ message salt positions hidden unopened]

/-- The game in which the hidden coordinate's leaf digest is a fresh uniform
digest. It does not mention the coordinate's value. -/
def idealObservation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) (hidden : Index) : ProbComp α := do
  let salt ← $ᵗ Late.SaltTape
  let table ← $ᵗ Compression
  let answer ← $ᵗ Late.Digest
  fixedOracleRun ⟨tableExtending cache table, permutation⟩
    (observeExcept message salt positions hidden observe answer)

theorem observation_ideal_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (hidden : Index) (unopened : hidden ∉ positions) (value : Entry) :
    measureTVDist
      (observation permutation cache (Function.update message hidden value) positions observe)
      (idealObservation permutation cache message positions observe hidden) ≤
      ((keys.card + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192 := by
  have distance := measureTVDist_bind_left_le_of_forall_le ($ᵗ Late.SaltTape)
    (fun salt => do
      let table ← $ᵗ Compression
      let fresh ← $ᵗ Late.Salt
      let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
      fixedOracleRun oracle (observeExcept message salt positions hidden observe
        (leafDigest oracle.compression (hidden.val.testBit 0) fresh value)))
    (fun salt => do
      let table ← $ᵗ Compression
      let answer ← $ᵗ Late.Digest
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (observeExcept message salt positions hidden observe answer))
    (by positivity)
    (fun salt => hidden_leaf_distance permutation cache keys covered (hidden.val.testBit 0) value
      (observeExcept message salt positions hidden observe) (5 * LENGTH + budget)
      (observe_except_bound message salt positions hidden observe budget bounded))
  unfold idealObservation
  simpa only [measureTVDist,
    observation_update permutation cache message positions observe hidden unopened] using distance

/-- A complete root-and-opening observation changes little when one unopened
message coordinate changes. This includes the oracle work of the honest tree. -/
theorem coordinate_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (hidden : Index) (unopened : hidden ∉ positions) (left right : Entry) :
    measureTVDist
      (observation permutation cache (Function.update message hidden left) positions observe)
      (observation permutation cache (Function.update message hidden right) positions observe) ≤
      2 * (((keys.card + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192) := by
  have leftSide := observation_ideal_distance permutation cache keys covered message positions
    observe budget bounded hidden unopened left
  have rightSide := observation_ideal_distance permutation cache keys covered message positions
    observe budget bounded hidden unopened right
  rw [measureTVDist_comm] at rightSide
  refine ((measureTVDist_triangle _
    (idealObservation permutation cache message positions observe hidden) _).trans
      (add_le_add leftSide rightSide)).trans ?_
  exact le_of_eq (by ring)

/-! ### Hybrid over the message coordinates -/

def hybridMessage (left right : Message) (indices : List Index) : Message :=
  fun index => if index ∈ indices then right index else left index

theorem hybrid_message_nil (left right : Message) : hybridMessage left right [] = left := by
  funext index
  simp [hybridMessage]

theorem hybrid_message_cons (left right : Message) (index : Index) (indices : List Index) :
    hybridMessage left right (index :: indices) =
      Function.update (hybridMessage left right indices) index (right index) := by
  funext requested
  by_cases same : requested = index
  · subst requested
    simp [hybridMessage]
  · simp [hybridMessage, same]

theorem observation_hybrid {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (indices : List Index) :
    measureTVDist (observation permutation cache left positions observe)
      (observation permutation cache (hybridMessage left right indices) positions observe) ≤
      (indices.length : ℝ) *
        (2 * (((keys.card + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192)) := by
  let loss : ℝ := 2 * (((keys.card + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192)
  have nonnegative : 0 ≤ loss := by positivity
  change _ ≤ (indices.length : ℝ) * loss
  induction indices with
  | nil => simp only [hybrid_message_nil, measureTVDist_self, List.length_nil, Nat.cast_zero,
      zero_mul, le_refl]
  | cons index indices ih =>
    have step : measureTVDist
        (observation permutation cache (hybridMessage left right indices) positions observe)
        (observation permutation cache (hybridMessage left right (index :: indices)) positions
          observe) ≤ loss := by
      rw [hybrid_message_cons]
      by_cases opened : index ∈ positions
      · have same : right index = hybridMessage left right indices index := by
          unfold hybridMessage
          split
          · rfl
          · exact (agree index opened).symm
        rw [same, Function.update_eq_self, measureTVDist_self]
        exact nonnegative
      · have changed := coordinate_distance permutation cache keys covered
          (hybridMessage left right indices) positions observe budget bounded index opened
          (hybridMessage left right indices index) (right index)
        simpa only [Function.update_eq_self] using changed
    refine ((measureTVDist_triangle _ _ _).trans (add_le_add ih step)).trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)

/-- Statistical hiding for two fixed messages agreeing on the opened set,
conditional on any finite cache of earlier oracle answers. Each of the `LENGTH`
coordinates costs two single-leaf steps. -/
theorem observation_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    measureTVDist (observation permutation cache left positions observe)
      (observation permutation cache right positions observe) ≤
      (LENGTH : ℝ) * (2 * (((keys.card + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192)) := by
  have all : hybridMessage left right (Finset.univ.toList : List Index) = right := by
    funext index
    simp [hybridMessage]
  have result := observation_hybrid permutation cache keys covered left right positions agree
    observe budget bounded (Finset.univ.toList : List Index)
  simpa only [all, Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using result

end CommitGolfCandidate.S4Hiding
