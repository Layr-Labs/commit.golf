import CommitGolfCandidate.S3HidingTransfer
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.CapOpenProgramRun
import CommitGolfCandidate.CapHonestOpening
import CommitGolfCandidate.NonceOpeningResult
import CommitGolfCandidate.NonceOpeningBridge
import CommitGolfCandidate.NonceOpeningBytes

/-! Identify the returned commitment and every transmitted proof byte with the
reference tree (tagged leaves, group nodes, truncated internal nodes). For a
committed state the cap opener emits the cap-level proof of `referenceTranscript`;
the compaction pass then applies the pure transformation `noncePostprocess`. This
removes machine memory from the remaining privacy argument, without replacing the
machine-derived scheme being certified. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The pure transformation applied by the opening's compaction pass. -/
def noncePostprocess (positions : Positions) (proof : Proof) : Proof :=
  s6Pack positions.card proof

private theorem opening_map (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    program.scheme.opening trapdoor positions =
      program.readProof <$> program.run .opening (trapdoor,positions) := rfl

/-- The submitted opening is the cap opening followed by the compaction pass. -/
theorem nonce_compressed_opening_scheme (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.scheme.opening trapdoor positions =
      noncePostprocess positions <$> capProgram.scheme.opening trapdoor positions := by
  erw [opening_map nonceCompressedProgram, opening_map capProgram,
    nonce_compressed_opening_run, nonce_old_opening_run]
  simp only [map_pure]
  exact congrArg (pure : Proof → OracleComp World Proof)
    (nonce_opening_proof_compaction trapdoor positions)

/-- The submitted commitment phase is the cap program's (and the base program's). -/
theorem nonce_compressed_commit_run (message : Message) :
    nonceCompressedProgram.run .commit message = submission.run .commit message := rfl

/-- The returned root of a committed state is the reference root. -/
theorem committed_root_reference (oracle : Oracle) (message : Message) (state : MachineState)
    (correct : CommittedState oracle message state) (positions : Positions) :
    readBuffer state nonceCompressedProgram.layout.commitment DIGEST_BYTES =
      (referenceTranscript oracle.compression oracle.permutation message
        (expandTaggedVector (committedNonce state)) positions).1 :=
  correct.1.trans (correct.2.1 1 (by decide) (by decide))

/-- The cap-level opening of a committed state emits the cap-level reference proof,
for arbitrary opening sets including the empty set. -/
theorem cap_opening_reference (oracle : Oracle) (message : Message) (state : MachineState)
    (correct : CommittedState oracle message state) (positions : Positions) :
    capProgram.scheme.opening
        (readBuffer state capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      pure (referenceTranscript oracle.compression oracle.permutation message
        (expandTaggedVector (committedNonce state)) positions).2 := by
  by_cases empty : positions.card = 0
  · rw [cap_open_empty_scheme_bytes _ _ empty, reference_transcript_proof, if_pos empty]
  · rw [cap_open_nonempty_scheme_bytes _ _ (Nat.pos_of_ne_zero empty),
      cap_honest_opening_transcript oracle message state correct positions (Nat.pos_of_ne_zero empty)]

/-- All bytes emitted by the submitted opening image for a committed state are the
transformed reference proof, for arbitrary opening sets including the empty set. -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message) (state : MachineState)
    (correct : CommittedState oracle message state) (positions : Positions) :
    nonceCompressedProgram.scheme.opening
        (readBuffer state nonceCompressedProgram.layout.trapdoor nonceCompressedProgram.sizes.trapdoor)
        positions =
      pure (noncePostprocess positions (referenceTranscript oracle.compression oracle.permutation
        message (expandTaggedVector (committedNonce state)) positions).2) := by
  have delivered := nonce_compressed_opening_scheme
    (readBuffer state capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions
  rw [cap_opening_reference oracle message state correct positions, map_pure] at delivered
  exact delivered

end CommitGolfCandidate
