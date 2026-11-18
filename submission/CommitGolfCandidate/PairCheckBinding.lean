import CommitGolfCandidate.QuadBinding
import CommitGolfCandidate.TwoPermutationPinnedPeerLayout
import CommitGolfCandidate.PairLeafModel

/-! # Pair-heads checker binding

The pair-heads analog of `QuadBinding`: an accepted opening records the two leaf calls of its leaf (even shape at even
indices, pinned shape at odd indices), the quartet node and the projected upper path. Two conflicting accepted openings
give `PairQuadReplayEvidence` (compression, odd-leaf, even-leaf or quartet collision), whose probability is at most
`3q/2^122 + q/2^124 + q/2^124 + q/2^124 ≤ q/2^120` (the even term is the hypothesis `EvenLeafSmallBound`). -/

namespace TwoPermutationPrototype.PairCk
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker
open TwoPermutationPrototype.Packed (ProjectedPath)
set_option maxRecDepth 8192

/-! ## Parity-dispatched leaf rows -/

def pairFirstRow (perm : Block → Block) (index : Index) (message : Words 32) : Row :=
  if index.val % 2 = 0 then evenFirstRow perm message else pinnedFirstRow perm message

def pairSecondRow (perm : Block → Block) (index : Index) (nonce : Words 2) (firstReply : Block)
    (message : Words 32) : Row :=
  if index.val % 2 = 0 then evenSecondRow perm index nonce firstReply message
  else pinnedSecondRow perm index nonce firstReply message

theorem pair_rows_digest (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32) :
    outputDigest (pairSecondRow perm index nonce (pairFirstRow perm index message).2 message).2 =
      pairLeafDigest perm index nonce message := by
  unfold pairSecondRow pairFirstRow pairLeafDigest
  by_cases even : index.val % 2 = 0
  · simp only [if_pos even]; rfl
  · simp only [if_neg even]; rfl

/-! ## Evidence and its probability -/

def PairQuadReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ PinnedLeafWitness rows ∨ EvenLeafWitness rows ∨ QuadWitness rows

theorem PairQuadReplayEvidence.mono {before after : List PublicRow} (included : ∀ row ∈ before, row ∈ after)
    (proof : PairQuadReplayEvidence before) : PairQuadReplayEvidence after := by
  rcases proof with comp | leaf | even | q
  · have small : PairReplayEvidence before := Or.inl comp
    rcases small.mono included with c | l | e
    · exact Or.inl c
    · exact Or.inr (Or.inl l)
    · exact Or.inr (Or.inr (Or.inl e))
  · have small : PairReplayEvidence before := Or.inr (Or.inl leaf)
    rcases small.mono included with c | l | e
    · exact Or.inl c
    · exact Or.inr (Or.inl l)
    · exact Or.inr (Or.inr (Or.inl e))
  · have small : PairReplayEvidence before := Or.inr (Or.inr even)
    rcases small.mono included with c | l | e
    · exact Or.inl c
    · exact Or.inr (Or.inl l)
    · exact Or.inr (Or.inr (Or.inl e))
  · obtain ⟨x,y,h,ax,ay,rx,ry,equal⟩ := q
    exact Or.inr (Or.inr (Or.inr ⟨x,y,h,ax,ay,included _ rx,included _ ry,equal⟩))

private theorem three_small_terms (q : Nat) :
    (q : ENNReal)/2^124 + ((q : ENNReal)/2^124 + (q : ENNReal)/2^124) ≤ (q : ENNReal)/2^122 := by
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  calc
    ((q : ENNReal) + (q + q)) / 2^124 ≤ (4 * (q : ENNReal))/2^124 := by
      apply ENNReal.div_le_div_right
      calc (q : ENNReal) + (q + q) = 3 * (q : ENNReal) := by ring
        _ ≤ 4 * (q : ENNReal) := mul_le_mul' (by norm_num) le_rfl
    _ = (q : ENNReal)/2^122 := by
      rw [show (2 : ENNReal)^124 = 4 * 2^122 by rw [show (124 : Nat) = 2+122 by decide, pow_add]; norm_num]
      exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by finiteness)

theorem pair_quad_replay_bound {α : Type} (layout : PeerLeafLayout) (even : EvenLeafSmallBound)
    (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120)
    (replayed : calls ≤ q+2^31) (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      PairQuadReplayEvidence result.2] ≤ (q : ENNReal)/2^120 := by
  let execution := Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program)
  let A : (α × List PublicRow) → Prop := fun result => CompressionWitness result.2
  let B : (α × List PublicRow) → Prop := fun result => PinnedLeafWitness result.2
  let E : (α × List PublicRow) → Prop := fun result => EvenLeafWitness result.2
  let C : (α × List PublicRow) → Prop := fun result => QuadWitness result.2
  change Pr{let result ← execution}[A result ∨ B result ∨ E result ∨ C result] ≤ _
  have termA : Pr{let result ← execution}[A result] ≤ 3 * (q : ENNReal) / (4 * 2^120) := by
    have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress,perm⟩ (recordRows program)))
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq A]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small replayed bounded
  have termB : Pr{let result ← execution}[B result] ≤ (q : ENNReal)/2^124 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      fixed_compression_pinned_leaf_bound_small layout compress program q calls positive small replayed bounded
  have termE : Pr{let result ← execution}[E result] ≤ (q : ENNReal)/2^124 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      even compress program q calls positive small replayed bounded
  have termC : Pr{let result ← execution}[C result] ≤ (q : ENNReal)/2^124 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      fixed_compression_quad_bound compress program q calls positive small replayed bounded
  have tail : Pr{let result ← execution}[B result ∨ E result ∨ C result] ≤ (q : ENNReal)/2^122 :=
    (prEvent_or_le execution B (fun r => E r ∨ C r)).trans
      ((add_le_add termB ((prEvent_or_le execution E C).trans (add_le_add termE termC))).trans
        (three_small_terms q))
  exact (prEvent_or_le execution A (fun r => B r ∨ E r ∨ C r)).trans
    ((add_le_add termA tail).trans_eq (event_budget_sum q))

/-! ## Accepted openings and conflicts -/

structure PairRecordedQuartetOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (pairFirstRow oracle.permutation index (entryWords entry)).1
    (pairFirstRow oracle.permutation index (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pairSecondRow oracle.permutation index nonce
      (pairFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).1
    (pairSecondRow oracle.permutation index nonce
      (pairFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).2 ∈ rows
  quartet : BitVec 1024
  reply : Block
  child : quartet.extractLsb' (256 * (index.val % 4)) 256 =
    outputDigest (pairSecondRow oracle.permutation index nonce
      (pairFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).2
  parentRow : PublicRow.permutation (quadNodeCall.enc quartet) reply ∈ rows
  upper : ProjectedPath rows (LENGTH / 4 + index.val / 4) (LOG_LENGTH - 2) (quadNodeCall.trunc reply) root

private theorem pair_leaf_conflict (oracle : Oracle) (index : Index) (rows₀ rows₁ : List PublicRow)
    (nonce₀ nonce₁ : Words 2) (m₀ m₁ : Words 32) (different : m₀ ≠ m₁)
    (f₀ : PublicRow.permutation (pairFirstRow oracle.permutation index m₀).1
      (pairFirstRow oracle.permutation index m₀).2 ∈ rows₀)
    (f₁ : PublicRow.permutation (pairFirstRow oracle.permutation index m₁).1
      (pairFirstRow oracle.permutation index m₁).2 ∈ rows₁)
    (s₀ : PublicRow.permutation
      (pairSecondRow oracle.permutation index nonce₀ (pairFirstRow oracle.permutation index m₀).2 m₀).1
      (pairSecondRow oracle.permutation index nonce₀ (pairFirstRow oracle.permutation index m₀).2 m₀).2 ∈ rows₀)
    (s₁ : PublicRow.permutation
      (pairSecondRow oracle.permutation index nonce₁ (pairFirstRow oracle.permutation index m₁).2 m₁).1
      (pairSecondRow oracle.permutation index nonce₁ (pairFirstRow oracle.permutation index m₁).2 m₁).2 ∈ rows₁)
    (same : outputDigest
        (pairSecondRow oracle.permutation index nonce₀ (pairFirstRow oracle.permutation index m₀).2 m₀).2 =
      outputDigest
        (pairSecondRow oracle.permutation index nonce₁ (pairFirstRow oracle.permutation index m₁).2 m₁).2) :
    PinnedLeafWitness (rows₀ ++ rows₁) ∨ EvenLeafWitness (rows₀ ++ rows₁) := by
  by_cases even : index.val % 2 = 0
  · simp only [pairFirstRow, pairSecondRow, if_pos even] at f₀ f₁ s₀ s₁ same
    exact Or.inr ⟨oracle.permutation, index, nonce₀, nonce₁, m₀, m₁,
      List.mem_append_left _ f₀, List.mem_append_right _ f₁,
      List.mem_append_left _ s₀, List.mem_append_right _ s₁, same, different⟩
  · simp only [pairFirstRow, pairSecondRow, if_neg even] at f₀ f₁ s₀ s₁ same
    exact Or.inl ⟨oracle.permutation, index, nonce₀, nonce₁, m₀, m₁,
      List.mem_append_left _ f₀, List.mem_append_right _ f₁,
      List.mem_append_left _ s₀, List.mem_append_right _ s₁, same, different⟩

theorem pair_recorded_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (v w : Entry) (different : v ≠ w) (rows₀ rows₁ : List PublicRow)
    (left : PairRecordedQuartetOpening oracle index v root rows₀)
    (right : PairRecordedQuartetOpening oracle index w root rows₁) :
    PairQuadReplayEvidence (rows₀ ++ rows₁) := by
  rcases (left.upper.mono (fun _ h => List.mem_append_left _ h)).compare
    (right.upper.mono (fun _ h => List.mem_append_right _ h)) with collision | sameParent
  · exact Or.inl collision
  · by_cases sameInput : left.quartet = right.quartet
    · have sameLeaf := left.child.symm.trans
        ((congrArg (fun x : BitVec 1024 => x.extractLsb' (256 * (index.val % 4)) 256) sameInput).trans
          right.child)
      rcases pair_leaf_conflict oracle index rows₀ rows₁ left.nonce right.nonce (entryWords v) (entryWords w)
          (fun same => different (entry_words_injective same)) left.first right.first left.second right.second
          sameLeaf with pinned | even
      · exact Or.inr (Or.inl pinned)
      · exact Or.inr (Or.inr (Or.inl even))
    · exact Or.inr (Or.inr (Or.inr ⟨left.quartet, right.quartet, sameInput, left.reply, right.reply,
        List.mem_append_left _ left.parentRow, List.mem_append_right _ right.parentRow, sameParent⟩))

def AcceptedPairQuartetTrace (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observation := checkObservation s oracle input
    observation.1.1.exit = .success →
      observation.2 ≤ 2^30 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (PairRecordedQuartetOpening oracle index.val (input.values index) input.commitment observation.1.2)

private theorem limited_pair_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^30) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^30))) =
      pure (some (checkObservation s oracle input).1.1, (checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^30)).record.fixed oracle, coinFree.limit_recorded oracle _ fits]
  rfl

theorem pair_replay_extracts (s : Submission) (refines : AcceptedPairQuartetTrace s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))),
      PairQuadReplayEvidence result.2 := by
  obtain ⟨⟨index, member₀, member₁, conflict⟩, accepted₀, accepted₁⟩ := breaks
  let left := leftCheck claim
  let right := rightCheck claim
  obtain ⟨fits₀, path₀⟩ := refines oracle left (checked_acceptance s oracle left accepted₀)
  obtain ⟨fits₁, path₁⟩ := refines oracle right (checked_acceptance s oracle right accepted₁)
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((), (checkObservation s oracle left).1.2 ++ (checkObservation s oracle right).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check left) (2^30)
        let _ ← limitPublicQueries (s.run .check right) (2^30)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check right) (2^30); pure ())) =
        pure ((), (checkObservation s oracle right).1.2) := by
      rw [record_rows_bind, fixed_oracle_run_bind, limited_pair_check s oracle right fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, limited_pair_check s oracle left fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure, Set.mem_singleton_iff] at found
  subst result
  exact pair_recorded_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index, member₀⟩).some (path₁ ⟨index, member₁⟩).some

theorem pair_scheme_binding (s : Submission) (even : EvenLeafSmallBound) (refines : AcceptedPairQuartetTrace s) :
    s.scheme.Binding :=
  scheme_binding_of_replay_with s.scheme
    ⟨checkerReplay s, checker_replay_bounded s, pair_replay_extracts s refines⟩
    (fun h proof => PairQuadReplayEvidence.mono h proof)
    (pair_quad_replay_bound ⟨pinnedPeerSalt, pinned_first_peer, pinned_second_peer⟩ even)

end TwoPermutationPrototype.PairCk
