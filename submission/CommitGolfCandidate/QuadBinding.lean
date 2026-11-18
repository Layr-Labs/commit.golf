import CommitGolfCandidate.QuadReplay
import CommitGolfCandidate.TwoPermutationPackedPaths
import CommitGolfCandidate.K3T238Replay

namespace TwoPermutationPrototype.Quartet
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker
open TwoPermutationPrototype.Packed (ProjectedPath)
set_option maxRecDepth 8192

/-- What an accepting check records for one opened position: both leaf calls, the quartet call of
the position's group (the leaf digest in slot `index % 4` of the window `0^72 ‖ d0 d1 d2 d3`), and a
projected path from the group node (`quartetNode (index / 4)`) to the root. -/
structure RecordedQuartetOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (pinnedFirstRow oracle.permutation index (entryWords entry)).1
    (pinnedFirstRow oracle.permutation index (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).1
    (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).2 ∈ rows
  quartet : BitVec 1024
  reply : Block
  child : quartet.extractLsb' (256 * (index.val % 4)) 256 =
    outputDigest (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation index (entryWords entry)).2 (entryWords entry)).2
  parentRow : PublicRow.permutation (quartetEncode quartet) reply ∈ rows
  upper : ProjectedPath rows (LENGTH / 4 + index.val / 4) (LOG_LENGTH - 2) (quartetNode (index.val / 4) reply) root

theorem quartet_recorded_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (v w : Entry) (different : v ≠ w) (rows₀ rows₁ : List PublicRow)
    (left : RecordedQuartetOpening oracle index v root rows₀)
    (right : RecordedQuartetOpening oracle index w root rows₁) :
    QuadReplayEvidence238 (rows₀ ++ rows₁) := by
  rcases (left.upper.mono (fun _ h => List.mem_append_left _ h)).compare
    (right.upper.mono (fun _ h => List.mem_append_right _ h)) with collision | sameParent
  · exact Or.inl (by first | exact collision | exact collision.to238)
  · by_cases sameInput : left.quartet = right.quartet
    · have sameLeaf := left.child.symm.trans
        ((congrArg (fun x : BitVec 1024 => x.extractLsb' (256 * (index.val % 4)) 256) sameInput).trans
          right.child)
      exact Or.inr (Or.inl ⟨oracle.permutation, index, left.nonce, right.nonce, entryWords v, entryWords w,
        List.mem_append_left _ left.first, List.mem_append_right _ right.first,
        List.mem_append_left _ left.second, List.mem_append_right _ right.second,
        sameLeaf, fun same => different (entry_words_injective same)⟩)
    · exact Or.inr (Or.inr ⟨index.val / 4, left.quartet, right.quartet, sameInput, left.reply, right.reply,
        List.mem_append_left _ left.parentRow, List.mem_append_right _ right.parentRow, sameParent⟩)

def AcceptedQuartetTrace (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observation := checkObservation s oracle input
    observation.1.1.exit = .success →
      observation.2 ≤ 2^30 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (RecordedQuartetOpening oracle index.val (input.values index) input.commitment observation.1.2)

private theorem limited_quartet_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^30) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^30))) =
      pure (some (checkObservation s oracle input).1.1, (checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^30)).record.fixed oracle, coinFree.limit_recorded oracle _ fits]
  rfl

theorem quartet_replay_extracts (s : Submission) (refines : AcceptedQuartetTrace s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), QuadReplayEvidence238 result.2 := by
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
      rw [record_rows_bind, fixed_oracle_run_bind, limited_quartet_check s oracle right fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, limited_quartet_check s oracle left fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure, Set.mem_singleton_iff] at found
  subst result
  exact quartet_recorded_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index, member₀⟩).some (path₁ ⟨index, member₁⟩).some

/-- Binding from accepted checks: tree conflicts at 238 bits (product-form birthday), leaf conflicts
through the sharp leaf layout, quartet conflicts under both node truncations (`K3T238Replay`). -/
theorem quartet_scheme_binding (s : Submission) (layout : PeerLeafLayoutSharp) (refines : AcceptedQuartetTrace s) :
    s.scheme.Binding :=
  scheme_binding_of_replay_with s.scheme
    ⟨checkerReplay s, checker_replay_bounded s, quartet_replay_extracts s refines⟩
    (fun h proof => quad_evidence238_mono h proof) (quad_replay_bound_t238_of_layout layout)

end TwoPermutationPrototype.Quartet
