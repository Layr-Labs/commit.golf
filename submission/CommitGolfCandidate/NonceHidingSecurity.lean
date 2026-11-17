import CommitGolfCandidate.NonceOpeningBytes
import CommitGolfCandidate.CapHidingSecurity

/-! Statistical hiding of the concrete codec images. The commitment machine
is identical to the promoted cap machine, and the actual opening execution
only applies a pure deterministic transformation to its emitted proof. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def noncePostprocess (positions : Positions) (proof : Proof) : Proof :=
  NonceCodec.compact positions.card proof

theorem nonce_compressed_opening_scheme (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.scheme.opening trapdoor positions=
      noncePostprocess positions <$> capProgram.scheme.opening trapdoor positions := by
  change (nonceCompressedProgram.readProof <$> nonceCompressedProgram.run .opening
      (trapdoor, positions)) =
    noncePostprocess positions <$> (capProgram.readProof <$> capProgram.run .opening
      (trapdoor, positions))
  rw [nonce_compressed_opening_run, nonce_old_opening_run]
  simp only [map_pure]
  exact congrArg (pure : Proof → OracleComp World Proof) (nonce_opening_proof_compaction trapdoor positions)

private theorem nonce_shared_commit_hiding {Trapdoor State Output : Type} {openingSize : Nat}
    (commit : Message → OracleComp World (Commitment × Trapdoor))
    (left right : Trapdoor → Positions → OracleComp World Proof)
    (mapped : ∀ trapdoor positions, left trapdoor positions =
      noncePostprocess positions <$> right trapdoor positions)
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    (do let challenge ← adversary.choose
        let committed ← commit (if selectSecond then challenge.message₁ else challenge.message₀)
        let proof ← left committed.2 challenge.positions
        adversary.observe challenge.aux committed.1 proof) =
    (do let challenge ← adversary.choose
        let committed ← commit (if selectSecond then challenge.message₁ else challenge.message₀)
        let proof ← right committed.2 challenge.positions
        adversary.observe challenge.aux committed.1 (noncePostprocess challenge.positions proof)) := by
  simp only [mapped, bind_map_left]

theorem nonce_hiding_experiment_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond =
      Hiding.hidingExperiment capProgram.scheme
        (capTransformAdversary noncePostprocess adversary) selectSecond := by
  simp only [Hiding.hidingExperiment, capTransformAdversary, bind_map_left,
    capLiftHidingChallenge, nonce_compressed_commit_same]
  exact nonce_shared_commit_hiding (Trapdoor := BitVec (8*capProgram.sizes.trapdoor))
    capProgram.scheme.commit
    nonceCompressedProgram.scheme.opening capProgram.scheme.opening
    nonce_compressed_opening_scheme adversary selectSecond

theorem nonce_compressed_hiding : nonceCompressedProgram.scheme.Hiding HIDING_ERROR := by
  constructor
  · exact cap_program_hiding.1
  · intro openingSize budget possible State Output adversary bounded
    have distance:=cap_program_hiding.2 openingSize budget possible
      (State × Positions) Output (capTransformAdversary noncePostprocess adversary)
      (cap_transform_query_bound noncePostprocess adversary bounded)
    simpa only [←nonce_hiding_experiment_eq] using distance

end CommitGolfCandidate
