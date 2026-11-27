import CommitGolfCandidate.S4HidingGame

/-! Using `Late.late_hiding` for a machine-derived scheme.

Hiding depends on a scheme only through the distribution of its public
transcript (commitment and proof, trapdoor discarded) under each fixed oracle.
A machine scheme whose transcript is equal in distribution to the abstract
scheme's therefore inherits `late_hiding` with the same error and the same
shared query budget. The abstract transcript is given in closed form: the
per-pair coin draws (equivalently uniform pair words, read as a salt tape whose
two salts per pair share a midpoint) followed by the pure one-pass tree and its
opening. Hypotheses are stated with `=ᵈ`, which needs no
measurable structure on `Commitment × Proof`. Nothing here is needed for
`late_hiding` itself. -/
namespace CommitGolfCandidate.S4Hiding
open CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance transferDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec

attribute [local irreducible] List.finRange List.range

/-- The public transcript of a scheme: its commitment and one opening. -/
def transcript (scheme : Scheme) (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let committed ← scheme.commit message
  let proof ← scheme.opening committed.2 positions
  pure (committed.1, proof)

theorem experiment_transcript (scheme : Scheme) {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment scheme adversary selectSecond =
      (do let challenge ← adversary.choose
          let shown ← transcript scheme
            (if selectSecond then challenge.message₁ else challenge.message₀) challenge.positions
          adversary.observe challenge.aux shown.1 shown.2) := by
  simp only [Hiding.hidingExperiment, transcript, bind_assoc, pure_bind]

/-- Transcripts equal in distribution under every fixed oracle give hiding
experiments equal in distribution, for every adversary and either selector. -/
theorem experiment_distribution_congr (machine model : Scheme)
    (same : ∀ (oracle : Oracle) (message : Message) (positions : Positions),
      fixedOracleRun oracle (transcript machine message positions) =ᵈ
        fixedOracleRun oracle (transcript model message positions))
    {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment machine adversary selectSecond) =ᵈ
      Hiding.runHiding (Hiding.hidingExperiment model adversary selectSecond) := by
  rw [experiment_transcript, experiment_transcript, run_hiding_fixed, run_hiding_fixed]
  apply EvalDistEq.bind_right
  intro oracle
  rw [run_bind, run_bind]
  apply EvalDistEq.bind_right
  intro challenge
  rw [run_bind, run_bind]
  exact (same oracle _ _).bind_left _

/-- Hiding is a property of the transcript distribution under each fixed oracle. -/
theorem hiding_transfer (machine model : Scheme) (error : Nat → Nat → ℝ)
    (same : ∀ (oracle : Oracle) (message : Message) (positions : Positions),
      fixedOracleRun oracle (transcript machine message positions) =ᵈ
        fixedOracleRun oracle (transcript model message positions))
    (secure : model.Hiding error) : machine.Hiding error := by
  refine ⟨secure.1, ?_⟩
  intro openingSize queryBudget small State Output adversary bounded
  have result := secure.2 openingSize queryBudget small State Output adversary bounded
  have equal (selectSecond : Bool) :=
    (experiment_distribution_congr machine model same adversary selectSecond).evalDist_eq
      (α := Output)
  simpa only [measureTVDist, equal] using result

/-- The abstract transcript under a fixed oracle, exactly: the scheme's own coin
draws, then the pure one-pass tree and its opening. -/
theorem model_transcript_run (check : Late.Checker) (oracle : Oracle) (message : Message)
    (positions : Positions) :
    fixedOracleRun oracle (transcript (S4.scheme S4.active check) message positions) =
      (fixedOracleRun oracle Late.sampleSalts >>= fun salt =>
        pure (Late.node (tree oracle.compression message salt) LOG_LENGTH 0,
          S4.actualOpening (tree oracle.compression message salt) salt positions)) := by
  unfold transcript
  simp only [S4.scheme, bind_assoc, pure_bind]
  rw [run_bind]
  apply bind_congr
  intro salt
  rw [run_tree]
  exact fixed_oracle_run_pure _ _

/-- The abstract transcript under a fixed oracle, in distribution: uniform pair
words, then the pure one-pass tree and its opening on the salt tape they give. -/
theorem model_transcript_words (check : Late.Checker) (oracle : Oracle)
    (message : Message) (positions : Positions) :
    fixedOracleRun oracle (transcript (S4.scheme S4.active check) message positions) =ᵈ
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        (pure (Late.node (tree oracle.compression message (unpackTape words)) LOG_LENGTH 0,
          S4.actualOpening (tree oracle.compression message (unpackTape words))
            (unpackTape words) positions) : ProbComp (Commitment × Proof))) := by
  rw [model_transcript_run]
  have assoc : ∀ next : Late.SaltTape → ProbComp (Commitment × Proof),
      ((($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        (pure (unpackTape words) : ProbComp Late.SaltTape)) >>= next) =
      (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words => next (unpackTape words)) := by
    intro next
    rw [bind_assoc]
    simp only [pure_bind]
  refine ((sample_salts_words oracle).bind_left _).trans ?_
  exact EvalDistEq.of_evalDist_eq (congrArg (fun computation => 𝒟[computation]) (assoc _))

/-- Hiding for any scheme whose transcript is distributed as the abstract
late-salt scheme's under every fixed oracle. This is how a machine certificate
consumes `Late.late_hiding`. -/
theorem machine_hiding (check : Late.Checker) (machine : Scheme)
    (same : ∀ (oracle : Oracle) (message : Message) (positions : Positions),
      fixedOracleRun oracle (transcript machine message positions) =ᵈ
        fixedOracleRun oracle (transcript (S4.scheme S4.active check) message positions)) :
    machine.Hiding HIDING_ERROR :=
  hiding_transfer machine (S4.scheme S4.active check) HIDING_ERROR same (S4Hiding.scheme_hiding check)

/-- The same, against the closed form: uniform pair words followed by the pure
one-pass tree and its opening. No abstract scheme appears in the hypothesis. -/
theorem machine_hiding_of_words (machine : Scheme)
    (same : ∀ (oracle : Oracle) (message : Message) (positions : Positions),
      fixedOracleRun oracle (transcript machine message positions) =ᵈ
        (($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
          (pure (Late.node (tree oracle.compression message (unpackTape words)) LOG_LENGTH 0,
            S4.actualOpening (tree oracle.compression message (unpackTape words))
              (unpackTape words) positions) : ProbComp (Commitment × Proof)))) :
    machine.Hiding HIDING_ERROR :=
  machine_hiding machine.check machine (fun oracle message positions =>
    (same oracle message positions).trans
      (model_transcript_words machine.check oracle message positions).symm)

end CommitGolfCandidate.S4Hiding
