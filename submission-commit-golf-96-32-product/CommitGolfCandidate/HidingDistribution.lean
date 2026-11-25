import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingMachine
import CommitGolfCandidate.HidingSalts
import CommitGolfCandidate.CompressionSampling

/-! Exact reduction of the machine hiding game to a salted-tree experiment. This
is equality of distributions, not yet a statistical-distance bound. Both adversary
stages retain their original coins, public oracle access, and shared oracle. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingDistributionDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf CommitGolf.Riscv OracleComp OracleComp.DeferredSampling

theorem fixed_oracle_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

theorem fixed_oracle_run_map (oracle : Oracle) {α β : Type}
    (f : α → β) (computation : OracleComp World α) :
    fixedOracleRun oracle (f <$> computation) = f <$> fixedOracleRun oracle computation := by
  simp only [fixedOracleRun, oracle_run_map, Functor.map_map]

/-- The actual commitment followed by its actual opening, returning precisely
the public transcript seen by the adversary. The private trapdoor is discarded. -/
def honestTranscript (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← submission.scheme.commit message
  let proof ← submission.scheme.opening trapdoor positions
  return (root, proof)

/-- Public transcript of the mathematical salted tree for one fixed salt vector:
the chain over the 128 cap nodes and the serialized cap-and-records proof. -/
def referenceTranscript (compress : Compression) (message : Message)
    (salt : Index → Digest) (positions : Positions) : Commitment × Proof :=
  let heap := saltedHeap compress message salt
  (capRoot compress (referenceCap heap), referenceOpening heap salt positions)

private theorem scheme_commit_map (program : Submission) (message : Message) :
    program.scheme.commit message = program.readCommit <$> program.run .commit message := rfl

attribute [local irreducible] commitFinalResult submission readBuffer saltedHeap referenceOpening capRoot referenceCap
  openingResult openingInitializedState openingPositionState openingExitState

private theorem final_transcript (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) (width : bits = 256*LENGTH) (positions : Positions) :
    let result := (commitFinalResult oracle message answer).1
    let (root, trapdoor) := submission.readCommit result
    (root, submission.readProof (openingResult trapdoor positions)) =
      referenceTranscript oracle.compression message
        (fun index => answer.extractLsb' (256*index.val) 256) positions := by
  have contents := commit_final_contents oracle message answer width
  apply Prod.ext
  · have root := committed_root_reference oracle message _ contents.1 _ contents.2
    exact root
  · exact opening_reference_bytes oracle message _ contents.1 _ contents.2 positions

/-- For every fixed oracle and input, the actual transcript is exactly a fresh
salt draw followed by the reference tree computation. This covers all proof bytes. -/
theorem honest_transcript_distribution (oracle : Oracle) (message : Message)
    (positions : Positions) :
    fixedOracleRun oracle (honestTranscript message positions) =
      (commitSaltCoins message >>= fun answer => pure (referenceTranscript oracle.compression message
        (fun index => answer.extractLsb' (256*index.val) 256) positions)) := by
  have finish (root : Commitment) (trapdoor : submission.scheme.Trapdoor) :
      fixedOracleRun oracle (do
        let proof ← submission.scheme.opening trapdoor positions
        pure (root, proof)) =
      pure (root, submission.readProof (openingResult trapdoor positions)) := by
    have opened := opening_scheme_execution trapdoor positions
    erw [opened, pure_bind, fixed_oracle_run_pure]
  unfold honestTranscript
  rw [fixed_oracle_run_bind]
  simp only [finish]
  change (fixedOracleRun oracle (submission.scheme.commit message) >>= fun value =>
    pure (value.1, submission.readProof (openingResult value.2 positions))) = _
  rw [scheme_commit_map]
  change (fixedOracleRun oracle
    (submission.readCommit <$> submission.run .commit (message : Input submission.sizes .commit)) >>=
      fun value : Commitment × BitVec (8*submission.sizes.trapdoor) =>
        pure (value.1, submission.readProof (openingResult value.2 positions))) = _
  rw [fixed_oracle_run_map, bind_map_left]
  unfold fixedOracleRun
  rw [bind_map_left, commit_run_distribution, bind_assoc]
  apply bind_congr
  intro answer
  simp only [pure_bind]
  congr 1
  exact final_transcript oracle message answer (commit_salt_width message) positions

/-- The reference game retains both oracle-adaptive adversary stages; only honest
machine execution is replaced by its proved transcript formula. -/
def referenceHiding {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) : ProbComp Output := do
  let challenge ← fixedOracleRun oracle adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let salt ← $ᵗ (Index → Digest)
  let (root, proof) := referenceTranscript oracle.compression message salt challenge.positions
  fixedOracleRun oracle (adversary.observe challenge.aux root proof)

private theorem hiding_experiment_transcript {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment submission.scheme adversary selectSecond =
      (do let challenge ← adversary.choose
          let message := if selectSecond then challenge.message₁ else challenge.message₀
          let (root, proof) ← honestTranscript message challenge.positions
          adversary.observe challenge.aux root proof) := by
  simp only [Hiding.hidingExperiment, honestTranscript, bind_assoc, pure_bind]

/-- Distributional equality for each fixed shared oracle, including the change
from packed random bits to independent salts. No query bound is needed here. -/
theorem hiding_fixed_reference {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) :
    𝒟[fixedOracleRun oracle (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[referenceHiding oracle adversary selectSecond] := by
  rw [hiding_experiment_transcript, fixed_oracle_run_bind]
  unfold referenceHiding
  apply _root_.evalDist_bind_congr
  intro challenge
  rw [fixed_oracle_run_bind, honest_transcript_distribution, bind_assoc]
  simp only [pure_bind]
  exact commit_salts_uniform (if selectSecond then challenge.message₁ else challenge.message₀)
    (fun salt => fixedOracleRun oracle (adversary.observe challenge.aux
      (referenceTranscript oracle.compression
        (if selectSecond then challenge.message₁ else challenge.message₀) salt challenge.positions).1
      (referenceTranscript oracle.compression
        (if selectSecond then challenge.message₁ else challenge.message₀) salt challenge.positions).2))

/-- The original hiding game and the reference game are the same distribution.
The final hiding proof must still bound the distance between the two selectors. -/
theorem hiding_reference_distribution {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[Oracle.sample >>= fun oracle => referenceHiding oracle adversary selectSecond] := by
  unfold Hiding.runHiding
  apply _root_.evalDist_bind_congr
  intro oracle
  have same : (do
      let (output, _) ← oracle.run (Hiding.hidingExperiment submission.scheme adversary selectSecond)
      pure output) =
      fixedOracleRun oracle (Hiding.hidingExperiment submission.scheme adversary selectSecond) := by
    unfold fixedOracleRun
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro result
    cases result
    rfl
  rw [same]
  exact hiding_fixed_reference oracle adversary selectSecond

/-- The exact statistical distance required by the certificate is the distance
between the reference games. This transfers any proved reference bound directly
to the actual submitted RISC-V programs. -/
theorem hiding_distance_reference {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) :
    measureTVDist
      (Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary false))
      (Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary true)) =
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary true) := by
  simp only [measureTVDist, hiding_reference_distribution]

end CommitGolfCandidate
