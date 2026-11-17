import CommitGolfCandidate.NonceCompressedAdmission
import CommitGolfCandidate.NonceTermination
import CommitGolfCandidate.NonceHonestObservations
import CommitGolfCandidate.NonceProofSize
import CommitGolfCandidate.NonceBindingSecurity
import CommitGolfCandidate.NonceHidingSecurity

namespace CommitGolfCandidate
open CommitGolf

theorem nonce_certificate : Certificate nonceCompressedProgram 72704 1728053684 99225 where
  admission := nonce_compressed_admission
  machineSuccess := nonce_program_machine_success
  termination := nonce_program_termination
  completeness := nonce_compressed_completeness
  honestBudgets := nonce_compressed_budgets
  proofSize := nonce_program_proof_size
  proverCycles := nonce_program_prover_cycles
  binding := nonce_compressed_binding
  hidingProperty := nonce_compressed_hiding
end CommitGolfCandidate
