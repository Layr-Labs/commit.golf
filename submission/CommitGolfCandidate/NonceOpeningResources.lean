import CommitGolfCandidate.NonceOpeningBytes
import CommitGolfCandidate.CapOpenResources

/-! Worst-case scored-batch resources of the concrete compressed opener.
The retained traversal emits at most128 boundary digests, and the compactor's
exact additional cycles include every record and footer word instruction. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_batch_footer_bound (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (batch : positions.card=BATCH) :
    nonceOldFooterWords trapdoor positions ≤ 512 := by
  have positive : 0 < positions.card := by rw [batch]; decide
  have boundary:=cap_open_requested_boundary_bound positions positive
  unfold nonceOldFooterWords
  rw [if_neg (by omega : positions.card ≠ 0)]
  simp only [capOpenBoundaryDigests,List.length_map]
  omega

theorem nonce_batch_codec_cycles (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (batch : positions.card=BATCH) :
    nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions) ≤ 54542 := by
  have footer:=nonce_batch_footer_bound trapdoor positions batch
  rw [batch]
  unfold nonceCodecCycles
  simp only [BATCH]
  split <;> omega

theorem nonce_compressed_batch_cycles (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (batch : positions.card=BATCH) :
    (nonceCompressedOpeningResult trapdoor positions).cycles ≤ 92441 := by
  have positive : 0 < positions.card := by rw [batch]; decide
  have retained : (nonceOldOpeningResult trapdoor positions).cycles ≤ 37899 := by
    unfold nonceOldOpeningResult
    rw [if_neg (by omega : positions.card ≠ 0)]
    exact cap_open_result_batch_cycles trapdoor positions batch
  have codec:=nonce_batch_codec_cycles trapdoor positions batch
  change (nonceOldOpeningResult trapdoor positions).cycles+
    nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions) ≤ 92441
  omega

theorem nonce_compressed_batch_bytes (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (batch : positions.card=BATCH) :
    (nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)).length ≤ 72704 := by
  have footer:=nonce_batch_footer_bound trapdoor positions batch
  rw [nonce_compressed_result_read_proof]
  simp only [nonceMemoryBytes,List.length_map,List.length_range]
  rw [batch]
  simp only [BATCH]
  omega

private theorem oracle_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α)=pure (value,0) := by
  simp [Oracle.run]
  rfl

theorem nonce_opening_program_termination (oracle : Oracle)
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$>
      oracle.run (nonceCompressedProgram.run .opening (trapdoor,positions)))=1 := by
  rw [nonce_compressed_opening_run,oracle_pure]
  simp [nonceCompressedOpeningResult,nonceCodecResult,Execution.charge]

theorem nonce_opening_batch_resources (oracle : Oracle)
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (batch : positions.card=BATCH) :
    prEvent ((fun result => result.1.exit=Exit.success ∧ result.1.cycles ≤ 92441 ∧
      result.2=0 ∧ (nonceCompressedProgram.readProof result.1).length ≤ 72704) <$>
      oracle.run (nonceCompressedProgram.run .opening (trapdoor,positions)))=1 := by
  rw [nonce_compressed_opening_run,oracle_pure]
  simp only [map_pure,nonce_compressed_batch_cycles trapdoor positions batch,
    nonce_compressed_batch_bytes trapdoor positions batch]
  simp [nonceCompressedOpeningResult,nonceCodecResult,Execution.charge]

end CommitGolfCandidate
