import CommitGolfCandidate.QuadBindingProbability
import CommitGolfCandidate.TwoPermutationPackedPaths

/-! Deterministic binding extraction for quad openings. The binary path begins
at heap node (LENGTH+i)/4 and has 22 projected-compression steps to the root. -/
namespace TwoPermutationPrototype.Quad
open CommitGolf CommitGolf.Riscv CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker OracleComp
open TwoPermutationPrototype.Packed (ProjectedPath)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private theorem append_parts {a b : Nat} {x x' : BitVec a} {y y' : BitVec b}
    (eq : x ++ y = x' ++ y') : x=x' ∧ y=y' := by
  constructor
  · have hit := congrArg (fun v : BitVec (a+b) => v.extractLsb' b a) eq
    exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)
  · have hit := congrArg (fun v : BitVec (a+b) => v.extractLsb' 0 b) eq
    exact BitVec.extractLsb'_append_eq_right.symm.trans (hit.trans BitVec.extractLsb'_append_eq_right)

/-- Slot extraction is injective; equal quad inputs force every leaf digest equal. -/
theorem quad_children_equal {c d : Fin 4 → BitVec 256} (same : quadInput c = quadInput d) : c=d := by
  have h := (append_parts same).1
  obtain ⟨h,h0⟩ := append_parts h
  obtain ⟨h,h1⟩ := append_parts h
  obtain ⟨h3,h2⟩ := append_parts h
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

structure QuadOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (pinnedFirstRow oracle.permutation (entryWords entry)).1
    (pinnedFirstRow oracle.permutation (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).1
    (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2 ∈ rows
  children : Fin 4 → BitVec 256
  opened : children ⟨index.val%4,Nat.mod_lt _ (by decide)⟩ =
    outputDigest (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2
  answer : Block
  quad : PublicRow.permutation (quadInput children) answer ∈ rows
  path : ProjectedPath rows ((LENGTH+index.val)/4) 22 (answer.extractLsb' 0 256) root

def QuadOpening.mono {oracle : Oracle} {index : Index} {entry : Entry} {root : Commitment}
    {earlier later : List PublicRow} (opening : QuadOpening oracle index entry root earlier)
    (contained : ∀ row ∈ earlier, row ∈ later) : QuadOpening oracle index entry root later where
  nonce := opening.nonce
  first := contained _ opening.first
  second := contained _ opening.second
  children := opening.children
  opened := opening.opened
  answer := opening.answer
  quad := contained _ opening.quad
  path := opening.path.mono contained

theorem quad_openings_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (value₀ value₁ : Entry) (conflict : value₀ ≠ value₁)
    (rows₀ rows₁ : List PublicRow) (left : QuadOpening oracle index value₀ root rows₀)
    (right : QuadOpening oracle index value₁ root rows₁) : QuadReplayEvidence (rows₀++rows₁) := by
  rcases (left.path.mono (fun _ h => List.mem_append_left _ h)).compare
    (right.path.mono (fun _ h => List.mem_append_right _ h)) with hash | sameQuad
  · exact Or.inl hash
  · by_cases sameInput : quadInput left.children = quadInput right.children
    · have children := quad_children_equal sameInput
      have sameLeaf := left.opened.symm.trans
        ((congrFun children ⟨index.val%4,Nat.mod_lt _ (by decide)⟩).trans right.opened)
      exact Or.inr (Or.inl ⟨oracle.permutation,index,left.nonce,right.nonce,entryWords value₀,entryWords value₁,
        List.mem_append_left _ left.first,List.mem_append_right _ right.first,
        List.mem_append_left _ left.second,List.mem_append_right _ right.second,
        sameLeaf,fun h => conflict (entry_words_injective h)⟩)
    · exact Or.inr (Or.inr ⟨_,_,left.answer,right.answer,
        List.mem_append_left _ left.quad,List.mem_append_right _ right.quad,
        fun eq => sameInput (congrArg quadEncode eq),sameQuad⟩)

def QuadAcceptedTrace (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := checkObservation s oracle input
    observed.1.1.exit = .success → observed.2 ≤ 2^30 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (QuadOpening oracle index.val (input.values index) input.commitment observed.1.2)

private theorem quad_limited_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^30) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^30))) =
      pure (some (checkObservation s oracle input).1.1,(checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^30)).record.fixed oracle,coinFree.limit_recorded oracle _ fits]
  rfl

theorem quad_replay_extracts (s : Submission) (refines : QuadAcceptedTrace s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), QuadReplayEvidence result.2 := by
  obtain ⟨⟨index,member₀,member₁,conflict⟩,accepted₀,accepted₁⟩ := breaks
  let x := leftCheck claim
  let y := rightCheck claim
  have good₀ := checked_acceptance s oracle x accepted₀
  have good₁ := checked_acceptance s oracle y accepted₁
  obtain ⟨fits₀,path₀⟩ := refines oracle x good₀
  obtain ⟨fits₁,path₁⟩ := refines oracle y good₁
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((),(checkObservation s oracle x).1.2++(checkObservation s oracle y).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check x) (2^30)
        let _ ← limitPublicQueries (s.run .check y) (2^30)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check y) (2^30); pure ())) =
        pure ((), (checkObservation s oracle y).1.2) := by
      rw [record_rows_bind, fixed_oracle_run_bind, quad_limited_check s oracle y fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, quad_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure,Set.mem_singleton_iff] at found
  subst result
  exact quad_openings_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index,member₀⟩).some (path₁ ⟨index,member₁⟩).some

def quad_binding_replay (s : Submission) (specified : QuadAcceptedTrace s) :
    BindingReplayEvidence s.scheme QuadReplayEvidence :=
  ⟨checkerReplay s,checker_replay_bounded s,quad_replay_extracts s specified⟩

/-- The final all-budget Binding clause needs only the machine's accepted-trace
extraction theorem, and makes no assumption about commit or opening images. -/
theorem binding_of_quad_trace (candidate : Submission) (trace : QuadAcceptedTrace candidate) :
    candidate.scheme.Binding :=
  scheme_binding_of_replay_with candidate.scheme (quad_binding_replay candidate trace)
    (fun contained hit => hit.mono contained) quad_replay_bound

end TwoPermutationPrototype.Quad
