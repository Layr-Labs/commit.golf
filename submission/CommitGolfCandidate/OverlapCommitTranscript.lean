import CommitGolfCandidate.OverlapCheckerRows
import CommitGolfCandidate.TwoPermutationOpeningTranscript
import CommitGolfCandidate.TwoPermutationCheckerReplay

namespace TwoPermutationPrototype.Overlap
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening OracleComp
local instance overlapDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def AcceptedTraceRefines (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := Checker.checkObservation s oracle input
    observed.1.1.exit = .success → observed.2 ≤ 2^30 ∧
      ∀ i : {i // i ∈ input.positions},
        Nonempty (Overlap.RecordedOpening oracle i.val (input.values i) input.commitment observed.1.2)

end TwoPermutationPrototype.Overlap

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

private theorem overlap_recorded_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (v w : Entry) (different : v ≠ w) (xs ys : List PublicRow)
    (a : Overlap.RecordedOpening oracle index v root xs)
    (b : Overlap.RecordedOpening oracle index w root ys) : PlbReplayEvidence (xs++ys) := by
  rcases (a.path.mono (fun _ h => List.mem_append_left _ h)).compare
    (b.path.mono (fun _ h => List.mem_append_right _ h)) with hash | equal
  · exact Or.inl hash
  · exact Or.inr ⟨oracle.permutation,index,a.nonce,b.nonce,entryWords v,entryWords w,
      List.mem_append_left _ a.first,List.mem_append_right _ b.first,List.mem_append_left _ a.second,
      List.mem_append_right _ b.second,equal,fun e => different (entry_words_injective e)⟩

theorem overlap_replay_extracts (s : Submission) (refines : Overlap.AcceptedTraceRefines s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), PlbReplayEvidence result.2 := by
  obtain ⟨⟨index, member₀, member₁, conflict⟩, accepted₀, accepted₁⟩ := breaks
  let x := leftCheck claim
  let y := rightCheck claim
  have good₀ := checked_acceptance s oracle x accepted₀
  have good₁ := checked_acceptance s oracle y accepted₁
  obtain ⟨fits₀, path₀⟩ := refines oracle x good₀
  obtain ⟨fits₁, path₁⟩ := refines oracle y good₁
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((), (checkObservation s oracle x).1.2 ++ (checkObservation s oracle y).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check x) (2^30)
        let _ ← limitPublicQueries (s.run .check y) (2^30)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check y) (2^30); pure ())) =
        pure ((), (checkObservation s oracle y).1.2) := by
      rw [record_rows_bind, fixed_oracle_run_bind, one_limited_check s oracle y fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, one_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure, Set.mem_singleton_iff] at found
  subst result
  exact overlap_recorded_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index, member₀⟩).some (path₁ ⟨index, member₁⟩).some

theorem overlap_binding (s : Submission) (specified : Overlap.AcceptedTraceRefines s) : s.scheme.Binding :=
  plb_scheme_binding_of_replay s.scheme
    ⟨checkerReplay s,checker_replay_bounded s,overlap_replay_extracts s specified⟩

end TwoPermutationPrototype.Checker
