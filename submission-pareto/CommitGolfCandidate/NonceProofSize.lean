import CommitGolfCandidate.NonceOpeningResources

/-! The scored proof-size bound for the scheme derived from the actual codec
images. Commitment coins may yield any trapdoor; the opening bound holds for
every such value before the checker result is evaluated. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

private theorem opening_map (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    program.scheme.opening trapdoor positions=
      program.readProof <$> program.run .opening (trapdoor,positions) := rfl

theorem nonce_opening_pure (trapdoor : BitVec (8*nonceCompressedProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.scheme.opening trapdoor positions=
      pure (nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)) := by
  erw [opening_map nonceCompressedProgram trapdoor positions,nonce_compressed_opening_run]
  rfl

private theorem oracle_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α)=pure (value,0) := by
  simp [Oracle.run]
  rfl

theorem nonce_program_proof_size : nonceCompressedProgram.scheme.ProofSize 75776 := by
  intro oracle message positions batch
  unfold Scheme.honest
  apply le_antisymm (prEvent_le_one _)
  apply le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _)
  rintro ⟨⟨root,trapdoor⟩,calls⟩ _
  dsimp only
  erw [nonce_opening_pure,oracle_pure]
  simp [nonce_compressed_batch_bytes trapdoor positions batch]

end CommitGolfCandidate
