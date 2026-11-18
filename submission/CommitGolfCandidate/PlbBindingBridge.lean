import CommitGolfCandidate.TwoPermutationBindingBridge
import CommitGolfCandidate.OverlapInputs
import CommitGolfCandidate.PermLean.LeafB

/-! # Binding with the overlap leaf in the replay framework

The overlap leaf of position `i` with salt words `nonce` and value words `m`:
`X = 0^8 ‖ m[0..192)` (`Overlap.firstInput`), `W = tag(i) ‖ P(X)[168..200) ‖ nonce ‖ m[112..256)`
(`Overlap.secondInput`), digest `P(W)[0..32)`.

This module replaces the two-call leaf event of `TwoPermutationBindingBridge` (`LeafWitness`,
`fixed_compression_leaf_bound`) by the overlap-leaf event `PlbLeafWitness` and keeps everything
else: the projected compression witness and its bound, the replay accounting and the exact
`q / 2^120` binding clause (`plb_scheme_binding_of_replay`).

The leaf bound `plb_fixed_leaf_bound` is the hazard argument of `PermLean.LeafB`: along the run, a
fresh forward reply must not repeat an earlier digest or link slice, and a fresh inverse reply must
not link to an earlier output or repeat an earlier overlap slice. Each step fails with probability
at most `(3k+1)·2^1344 / (2^1600 - k)` after `k` fresh evaluations, so `q + 2^31` public queries
fail with probability at most `q / 2^122`. The 32 bytes `m[112..144)` read by both calls rule out
chains started by inverse queries; recorded inverse rows are logged like forward rows. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate OracleComp.DeferredSampling
open TwoPermutationPrototype.RV64 (packBuffer replyWords)
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-! ## Rows and witnesses -/

/-- The first call `X ↦ P(X)` of the overlap leaf with value words `message`. -/
def plbFirstRow (perm : Block → Block) (message : Words 32) : Row :=
  let input := packBuffer (Overlap.firstInput message)
  (input, perm input)

/-- The second call `W ↦ P(W)` of the overlap leaf at `index` with salt words `nonce`. -/
def plbSecondRow (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32)
    (firstReply : Block) : Row :=
  let input := packBuffer (Overlap.secondInput index.val nonce (replyWords firstReply) message)
  (input, perm input)

/-- Two recorded overlap leaves at one position with different values and one digest. -/
def PlbLeafWitness (rows : List PublicRow) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := plbFirstRow perm message₀
    let a₁ := plbFirstRow perm message₁
    let b₀ := plbSecondRow perm index nonce₀ message₀ a₀.2
    let b₁ := plbSecondRow perm index nonce₁ message₁ a₁.2
    PublicRow.permutation a₀.1 a₀.2 ∈ rows ∧ PublicRow.permutation a₁.1 a₁.2 ∈ rows ∧
      PublicRow.permutation b₀.1 b₀.2 ∈ rows ∧ PublicRow.permutation b₁.1 b₁.2 ∈ rows ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

def PlbReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ PlbLeafWitness rows

theorem PlbReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : PlbReplayEvidence earlier) : PlbReplayEvidence later := by
  rcases evidence with ⟨x, y, value, value', left, right, different, equal⟩ |
    ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁, a₀, a₁, b₀, b₁, digest, conflict⟩
  · exact Or.inl ⟨x, y, value, value', contained _ left, contained _ right, different, equal⟩
  · exact Or.inr ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁,
      contained _ a₀, contained _ a₁, contained _ b₀, contained _ b₁, digest, conflict⟩

/-! ## Slices of the packed inputs -/

private theorem plb_slices_eq_of_words {leftWidth rightWidth : Nat}
    (left : BitVec leftWidth) (right : BitVec rightWidth) (leftOffset rightOffset words : Nat)
    (same : ∀ j < words, left.extractLsb' (64 * (leftOffset + j)) 64 =
      right.extractLsb' (64 * (rightOffset + j)) 64) :
    left.extractLsb' (64 * leftOffset) (64 * words) =
      right.extractLsb' (64 * rightOffset) (64 * words) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have eq := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) (same (bit / 64) (by omega))
  have lhs : 64 * (leftOffset + bit / 64) + bit % 64 = 64 * leftOffset + bit := by omega
  have rhs : 64 * (rightOffset + bit / 64) + bit % 64 = 64 * rightOffset + bit := by omega
  simpa [show bit % 64 < 64 by omega, inside, lhs, rhs] using eq

/-- The link: words 1..4 of `W` are words 21..24 of the first reply. -/
theorem plb_link (index : Index) (nonce : Words 2) (message : Words 32) (firstReply : Block) :
    PermLean.vB.link₂ (packBuffer (Overlap.secondInput index.val nonce (replyWords firstReply) message)) =
      PermLean.vB.link₁ firstReply := by
  apply plb_slices_eq_of_words _ _ 1 21 4
  intro word inside
  let i : Fin 25 := ⟨1 + word, by omega⟩
  have packed := packed_word (Overlap.secondInput index.val nonce (replyWords firstReply) message) i
  change (packBuffer _).extractLsb' (64 * i.val) 64 = _
  rw [packed]
  have below : 1 + word < 5 := by omega
  simp [Overlap.secondInput, replyWords, i, below, show 1 + word + 20 = 21 + word by omega]
  rfl

/-- The overlap: words 7..10 of `W` and words 15..18 of `X` are value words 14..17. -/
theorem plb_overlap (index : Index) (nonce : Words 2) (message : Words 32) (firstReply : Block) :
    PermLean.vB.overlap₂ (packBuffer (Overlap.secondInput index.val nonce (replyWords firstReply) message)) =
      PermLean.vB.overlap₁ (packBuffer (Overlap.firstInput message)) := by
  apply plb_slices_eq_of_words _ _ 7 15 4
  intro word inside
  let i : Fin 25 := ⟨7 + word, by omega⟩
  let i' : Fin 25 := ⟨15 + word, by omega⟩
  have packed := packed_word (Overlap.secondInput index.val nonce (replyWords firstReply) message) i
  have packed' := packed_word (Overlap.firstInput message) i'
  change (packBuffer _).extractLsb' (64 * i.val) 64 = (packBuffer _).extractLsb' (64 * i'.val) 64
  rw [packed, packed']
  have notLink : ¬ 7 + word < 5 := by omega
  have notSalt : ¬ 7 + word < 7 := by omega
  simp [Overlap.secondInput, Overlap.firstInput, i, i', notLink, notSalt,
    show 7 + word + 7 = 15 + word - 1 by omega]

/-- The two inputs of a leaf determine its value words. -/
theorem plb_inputs_injective {index : Index} {nonce₀ nonce₁ : Words 2} {message₀ message₁ : Words 32}
    {y₀ y₁ : Block}
    (first : packBuffer (Overlap.firstInput message₀) = packBuffer (Overlap.firstInput message₁))
    (second : packBuffer (Overlap.secondInput index.val nonce₀ (replyWords y₀) message₀) =
      packBuffer (Overlap.secondInput index.val nonce₁ (replyWords y₁) message₁)) :
    message₀ = message₁ := by
  have inputsA := packBuffer_injective first
  have inputsB := packBuffer_injective second
  funext position
  by_cases head : position.val < 24
  · have word := congrFun inputsA (⟨position.val + 1, by omega⟩ : Fin 25)
    have notZero : position.val + 1 ≠ 0 := by omega
    simpa [Overlap.firstInput, notZero] using word
  · have word := congrFun inputsB (⟨position.val - 7, by omega⟩ : Fin 25)
    have notZero : position.val - 7 ≠ 0 := by omega
    have notLink : ¬ position.val - 7 < 5 := by omega
    have notSalt : ¬ position.val - 7 < 7 := by omega
    have offset : position.val - 7 + 7 = position.val := by omega
    simpa [Overlap.secondInput, notZero, notLink, notSalt, offset] using word

/-! ## Recorded rows are logged by the hazard run -/

theorem plb_run_map (H : PermLean.Hazard) (C : Compression) (σ : Perm) {α β : Type}
    (f : α → β) (comp : OracleComp World α) (s : PermLean.State) :
    PermLean.run H C σ (f <$> comp) s = (fun r => (f r.1, r.2)) <$> PermLean.run H C σ comp s := by
  simp only [map_eq_bind_pure_comp, PermLean.run_bind, Function.comp_def, PermLean.run_pure]

theorem plb_inverse_step (H : PermLean.Hazard) (C : Compression) (σ : Perm) (s : PermLean.State)
    (y : Block) (mid : Block × PermLean.State)
    (hmid : mid ∈ support (PermLean.step H C σ s (.inr (.inr (.inr y))))) :
    mid.1 = σ.symm y ∧ y ∈ mid.2.1.outputs := by
  simp only [PermLean.step, support_pure, Set.mem_singleton_iff] at hmid
  subst hmid
  refine ⟨rfl, ?_⟩
  by_cases known : y ∈ s.1.outputs
  · simp only [known, ite_true]
  · simp only [known, ite_false, PermLean.Log.outputs, List.map_append, List.mem_append]
    simp

/-- Every permutation row recorded by `recordRows` is a true evaluation of `σ`, and its input or
its output is in the final hazard log (forward rows log the input, inverse rows the output). -/
theorem plb_record_rows_logged (H : PermLean.Hazard) (C : Compression) (σ : Perm) {α : Type}
    (program : OracleComp World α) :
    ∀ (s : PermLean.State) (r : (α × List PublicRow) × PermLean.State),
      r ∈ support (PermLean.run H C σ (recordRows program) s) →
      ∀ x y, PublicRow.permutation x y ∈ r.1.2 → σ x = y ∧ (x ∈ r.2.1.inputs ∨ y ∈ r.2.1.outputs) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    intro s r reached x y row
    rw [record_rows_pure, PermLean.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    simp at row
  | query_bind t next ih =>
    intro s r reached x y row
    rw [record_rows_query, PermLean.run_query_bind] at reached
    obtain ⟨mid, stepped, rest⟩ := (mem_support_bind_iff _ _ _).mp reached
    rw [plb_run_map, support_map] at rest
    obtain ⟨inner, ran, rfl⟩ := rest
    have grows := (PermLean.run_spec H C σ _ mid.2 inner ran).2
    rcases List.mem_append.mp row with here | later
    · rcases t with coins | input | input | output
      · simp [queryRows] at here
      · simp [queryRows] at here
      · obtain ⟨answer, logged, -⟩ := PermLean.forward_step H C σ s input mid stepped
        simp only [queryRows, List.mem_singleton, PublicRow.permutation.injEq] at here
        obtain ⟨rfl, rfl⟩ := here
        refine ⟨answer.symm, Or.inl ?_⟩
        obtain ⟨e, he, hx⟩ := List.mem_map.mp logged
        exact List.mem_map.mpr ⟨e, grows.subset he, hx⟩
      · obtain ⟨answer, logged⟩ := plb_inverse_step H C σ s output mid stepped
        simp only [queryRows, List.mem_singleton, PublicRow.permutation.injEq] at here
        obtain ⟨rfl, rfl⟩ := here
        refine ⟨by rw [answer]; exact σ.apply_symm_apply _, Or.inr ?_⟩
        obtain ⟨e, he, hy⟩ := List.mem_map.mp logged
        exact List.mem_map.mpr ⟨e, grows.subset he, hy⟩
    · exact ih mid.1 mid.2 inner ran x y later

/-! ## The leaf event raises the hazard flag -/

theorem plb_leaf_flag (C : Compression) (σ : Perm) {α : Type} (program : OracleComp World α)
    (r : (α × List PublicRow) × PermLean.State)
    (reached : r ∈ support (PermLean.run PermLean.leafHazardB C σ (recordRows program) ([], false)))
    (hit : PlbLeafWitness r.1.2) : r.2.2 = true := by
  apply PermLean.flag_of_unclean PermLean.leafHazardB C σ (recordRows program) r reached
  intro clean
  have consistent := PermLean.run_consistent PermLean.leafHazardB C σ (recordRows program) r reached
  have entry : ∀ x y, PublicRow.permutation x y ∈ r.1.2 →
      ∃ e ∈ r.2.1, e.input = x ∧ e.output = y := by
    intro x y row
    obtain ⟨value, present⟩ :=
      plb_record_rows_logged PermLean.leafHazardB C σ program ([], false) r reached x y row
    rcases present with known | known
    · obtain ⟨e, he, hx⟩ := List.mem_map.mp known
      exact ⟨e, he, hx, by rw [← consistent e he, hx, value]⟩
    · obtain ⟨e, he, hy⟩ := List.mem_map.mp known
      refine ⟨e, he, σ.injective ?_, hy⟩
      rw [consistent e he, hy, value]
  obtain ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁, a₀, a₁, b₀, b₁, digest, conflict⟩ := hit
  obtain ⟨e₁, m₁, i₁, o₁⟩ := entry _ _ a₀
  obtain ⟨e₁', m₁', i₁', o₁'⟩ := entry _ _ a₁
  obtain ⟨e₂, m₂, i₂, o₂⟩ := entry _ _ b₀
  obtain ⟨e₂', m₂', i₂', o₂'⟩ := entry _ _ b₁
  refine PermLean.vB.chain_collision (PermLean.clean_leafB clean) m₁ m₂ m₁' m₂' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [i₂, o₁]
    exact plb_link index nonce₀ msg₀ (plbFirstRow perm msg₀).2
  · rw [i₂', o₁']
    exact plb_link index nonce₁ msg₁ (plbFirstRow perm msg₁).2
  · rw [i₂, i₁]
    exact plb_overlap index nonce₀ msg₀ (plbFirstRow perm msg₀).2
  · rw [i₂', i₁']
    exact plb_overlap index nonce₁ msg₁ (plbFirstRow perm msg₁).2
  · by_contra both
    rw [not_or, not_not, not_not] at both
    exact conflict (plb_inputs_injective (i₁.symm.trans (both.1.trans i₁'))
      (i₂.symm.trans (both.2.trans i₂')))
  · rw [o₂, o₂']
    exact digest

/-! ## Budget -/

/-- With `calls ≤ q + 2^31` and `1 ≤ q ≤ 2^120`, the overlap-leaf hazard has probability at most
`q / 2^122`, the share the replay framework reserves for the leaf event. -/
theorem plb_leaf_budget {q calls : Nat} (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) :
    PermLean.hazardBudget PermLean.leafHazardB 0 calls ≤ (q : ENNReal) / 2 ^ 122 := by
  obtain ⟨linear, square, maximum⟩ := replay_budget_arithmetic positive small withReplay
  have card : Fintype.card PermLean.Word = 2 ^ PERMUTATION_WIDTH := Fintype.card_bitVec _
  have width : 256 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
  have each : ∀ j < calls, PermLean.leafHazardB.bound (0 + j) ≤ (3 * calls + 1) * PermLean.wide := by
    intro j hj
    show (3 * (0 + j) + 1) * PermLean.wide ≤ (3 * calls + 1) * PermLean.wide
    exact Nat.mul_le_mul_right _ (by omega)
  have room : 2 * (0 + calls) ≤ Fintype.card PermLean.Word := by
    rw [card]
    calc 2 * (0 + calls) ≤ 2 ^ 122 := by omega
      _ ≤ 2 ^ PERMUTATION_WIDTH := Nat.pow_le_pow_right (by norm_num) (by omega)
  have budget := PermLean.hazardBudget_le PermLean.leafHazardB 0 calls
    ((3 * calls + 1) * PermLean.wide) each room
  have smallPart : calls * (2 * (3 * calls + 1)) ≤ q * 2 ^ 134 := by
    have expand : calls * (2 * (3 * calls + 1)) = 6 * (calls * calls) + 2 * calls := by ring
    rw [expand]
    omega
  have integer : calls * (2 * ((3 * calls + 1) * PermLean.wide)) ≤
      q * 2 ^ (PERMUTATION_WIDTH - 122) := by
    have shape : calls * (2 * ((3 * calls + 1) * PermLean.wide)) =
        (calls * (2 * (3 * calls + 1))) * PermLean.wide := by ring
    have power : 2 ^ (PERMUTATION_WIDTH - 122) = 2 ^ 134 * PermLean.wide := by
      rw [PermLean.wide_eq, ← pow_add, show 134 + (PERMUTATION_WIDTH - 256) = PERMUTATION_WIDTH - 122 by
        omega]
    rw [shape, power]
    calc calls * (2 * (3 * calls + 1)) * PermLean.wide ≤ q * 2 ^ 134 * PermLean.wide :=
          Nat.mul_le_mul_right _ smallPart
      _ = q * (2 ^ 134 * PermLean.wide) := Nat.mul_assoc _ _ _
  refine budget.trans ?_
  rw [card, ← mul_div_assoc, ← Nat.cast_mul]
  calc ((calls * (2 * ((3 * calls + 1) * PermLean.wide)) : ℕ) : ENNReal) /
        ((2 ^ PERMUTATION_WIDTH : ℕ) : ENNReal)
      ≤ ((q * 2 ^ (PERMUTATION_WIDTH - 122) : ℕ) : ENNReal) / ((2 ^ PERMUTATION_WIDTH : ℕ) : ENNReal) :=
        ENNReal.div_le_div_right (by exact_mod_cast integer) _
    _ = (q : ENNReal) / 2 ^ 122 := by
        have split : PERMUTATION_WIDTH = 122 + (PERMUTATION_WIDTH - 122) := by omega
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
        conv_lhs => rw [show (2 : ENNReal) ^ PERMUTATION_WIDTH =
          2 ^ 122 * 2 ^ (PERMUTATION_WIDTH - 122) by rw [← pow_add, ← split]]
        exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-! ## The leaf bound for a fixed compression table -/

/-- **The overlap-leaf event**, for every fixed compression table and a uniform permutation with
forward and inverse queries: the replacement of `fixed_compression_leaf_bound`. -/
theorem plb_fixed_leaf_bound {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress, p⟩ (recordRows program))}[
      PlbLeafWitness result.2] ≤ (q : ENNReal) / 2 ^ 122 :=
  (PermLean.perm_event_bound PermLean.leafHazardB compress (recordRows program) calls bounded
    (fun result => PlbLeafWitness result.2)
    (fun σ r reached hit => plb_leaf_flag compress σ program r reached hit)).trans
    (plb_leaf_budget positive small withReplay)

/-! ## The replay reduction with the overlap leaf -/

private theorem plb_event_budget_sum (q : Nat) :
    3 * (q : ENNReal) / (4 * 2 ^ 120) + (q : ENNReal) / 2 ^ 122 = (q : ENNReal) / 2 ^ 120 := by
  have same : (2 : ENNReal) ^ 122 = 4 * 2 ^ 120 := by
    rw [show (122 : Nat) = 2 + 120 by decide, pow_add]
    norm_num
  rw [same, ← ENNReal.add_div]
  have scaled : 3 * (q : ENNReal) + (q : ENNReal) = 4 * (q : ENNReal) := by ring
  rw [scaled, mul_comm 4 (q : ENNReal), mul_comm 4 ((2 : ENNReal) ^ 120)]
  exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

theorem plb_sampled_replay_bound {α : Type} (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      PlbReplayEvidence result.2] ≤ (q : ENNReal) / 2 ^ 120 := by
  unfold PlbReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans_eq (plb_event_budget_sum q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (recordRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small withReplay bounded
  · simp only [Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      plb_fixed_leaf_bound compress program q calls positive small withReplay bounded

/-- The checker-replay interface of `BindingReplayRefines`, with the overlap-leaf witness. -/
structure PlbBindingReplayRefines (scheme : Scheme) where
  replay : Scheme.Claim → OracleComp World Unit
  bounded : ∀ claim, PublicQueryBound (replay claim) (2 ^ 31)
  extracts : ∀ oracle claim, scheme.Breaks oracle claim →
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (replay claim))), PlbReplayEvidence result.2

theorem plb_bounded_replay_queries (scheme : Scheme) (spec : PlbBindingReplayRefines scheme)
    (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (recordRows (boundedReplay spec.replay adversary budget)) (budget + 2 ^ 31) := by
  apply record_rows_bound
  apply public_query_bound_bind (limit_public_bound adversary budget)
  intro limited
  cases limited with
  | none => trivial
  | some claim => exact spec.bounded claim

private theorem plb_replay_dominated (scheme : Scheme) (spec : PlbBindingReplayRefines scheme)
    (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    Pr{let result ← oracle.run adversary}[scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] ≤
      Pr{let result ← fixedOracleRun oracle (recordRows (boundedReplay spec.replay adversary budget))}[
        PlbReplayEvidence result.2] := by
  classical
  let limited := limitPublicQueries adversary budget
  let start := fixedOracleRun oracle (recordRows limited)
  let good (limited : Option Scheme.Claim) := ∃ claim, limited = some claim ∧ scheme.Breaks oracle claim
  have projected : Prod.fst <$> start = fixedOracleRun oracle limited := by
    rw [← fixed_oracle_run_map, record_rows_erase]
  have prefixWin :
      Pr{let result ← start}[good result.1] =
        Pr{let result ← oracle.run adversary}[scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] := by
    rw [← limit_public_probability oracle adversary budget (scheme.Breaks oracle)]
    have event := congrArg (fun x : ProbComp (Option Scheme.Claim) => Pr{let result ← x}[good result]) projected
    simpa only [prEvent_map, fixedOracleRun, Function.comp_def, good, limited] using event
  rw [← prefixWin]
  unfold boundedReplay
  rw [record_rows_bind, fixed_oracle_run_bind]
  change Pr{let result ← start}[good result.1] ≤ _
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨outcome, trace⟩
  by_cases winning : good outcome
  · obtain ⟨claim, fixed, breaks⟩ := winning
    subst outcome
    have sure :
      Pr{let result ← fixedOracleRun oracle (recordRows (replayOption spec.replay (some claim)) >>= fun next =>
        pure (next.1, trace ++ next.2))}[PlbReplayEvidence result.2] = 1 := by
      rw [fixed_oracle_run_bind]
      apply prEvent_eq_one_of_forall_mem_support
      intro result reached
      obtain ⟨next, called, same⟩ := (mem_support_bind_iff _ _ _).mp reached
      rw [fixed_oracle_run_pure] at same
      simp only [support_pure, Set.mem_singleton_iff] at same
      subst result
      exact (spec.extracts oracle claim breaks next called).mono
        (fun row present => List.mem_append_right trace present)
    have win : good (some claim) := ⟨claim, rfl, breaks⟩
    simp only [win, ite_true, sure, mul_one, start, limited]
    exact le_rfl
  · simp [winning]

/-- **Binding with the overlap leaf.** The exact all-`q` binding clause follows from an executable
checker replay whose recorded rows expose a projected compression collision or an overlap-leaf
collision whenever both conflicting openings are accepted. -/
theorem plb_scheme_binding_of_replay (scheme : Scheme) (spec : PlbBindingReplayRefines scheme) :
    scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · apply (prEvent_le_one _).trans
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
    simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ budget from Nat.cast_le.mpr large)
  · have small : budget ≤ 2 ^ 120 := by
      change ¬ 2 ^ 120 ≤ budget at large
      omega
    have reduced :
        Pr{let (oracle, claim, calls) ← Scheme.bindingGame adversary}[
          scheme.Breaks oracle claim ∧ calls ≤ budget] ≤
        Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (recordRows (boundedReplay spec.replay adversary budget)))}[
          PlbReplayEvidence result.2] := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul_of_nonneg_left _ zero_le
      simp only [prEvent_map]
      exact plb_replay_dominated scheme spec oracle adversary budget
    exact reduced.trans (plb_sampled_replay_bound (boundedReplay spec.replay adversary budget) budget
      (budget + 2 ^ 31) positive small le_rfl (plb_bounded_replay_queries scheme spec adversary budget))

end TwoPermutationPrototype.Sampling
