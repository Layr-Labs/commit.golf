import CommitGolfCandidate.NonceCompressedPrograms
import CommitGolfCandidate.CapAdmission

namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem nonce_compressed_admission : nonceCompressedProgram.Admission := by
  intro phase
  cases phase with
  | commit => exact cap_program_admission .commit
  | opening => decide
  | check => decide

theorem nonce_compressed_initial_same (phase : Program)
    (input : Input nonceCompressedProgram.sizes phase) :
    nonceCompressedProgram.initialState phase input =
      capProgram.initialState phase input := by
  cases phase <;> rfl

theorem nonce_compressed_commit_same (message : Message) :
    nonceCompressedProgram.scheme.commit message=capProgram.scheme.commit message := rfl

end CommitGolfCandidate
