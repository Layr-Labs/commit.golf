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

private theorem opening_map (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    program.scheme.opening trapdoor positions=
      program.readProof <$> program.run .opening (trapdoor,positions) := rfl

theorem nonce_compressed_opening_scheme (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.scheme.opening trapdoor positions=
      noncePostprocess positions <$> capProgram.scheme.opening trapdoor positions := by
  erw [opening_map nonceCompressedProgram,opening_map capProgram,
    nonce_compressed_opening_run,nonce_old_opening_run]
  simp only [map_pure]
  exact congrArg (pure : Proof → OracleComp World Proof) (nonce_opening_proof_compaction trapdoor positions)

theorem nonce_hiding_experiment_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond=
      Hiding.hidingExperiment capProgram.scheme
        (capTransformAdversary noncePostprocess adversary) selectSecond := by
  unfold Hiding.hidingExperiment
  simp only [capTransformAdversary,bind_map_left,capLiftHidingChallenge]
  apply bind_congr
  intro challenge
  rw [nonce_compressed_commit_same]
  apply bind_congr
  rintro ⟨root,trapdoor⟩
  erw [nonce_compressed_opening_scheme,bind_map_left]

theorem nonce_compressed_hiding : nonceCompressedProgram.scheme.Hiding HIDING_ERROR := by
  constructor
  · exact cap_program_hiding.1
  · intro openingSize budget possible State Output adversary bounded
    have distance:=cap_program_hiding.2 openingSize budget possible
      (State × Positions) Output (capTransformAdversary noncePostprocess adversary)
      (cap_transform_query_bound noncePostprocess adversary bounded)
    simpa only [←nonce_hiding_experiment_eq] using distance

end CommitGolfCandidate
