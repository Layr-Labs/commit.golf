import CommitGolfCandidate.CapAdmission
import CommitGolfCandidate.CapMachine
import CommitGolfCandidate.CapCompleteness
import CommitGolfCandidate.CapBudgets
import CommitGolfCandidate.CapBindingSecurity
import CommitGolfCandidate.CapHidingSecurity

namespace CommitGolfCandidate
open CommitGolf

theorem cap_certificate : Certificate capProgram 73728 1728053684 43531 where
  admission := cap_program_admission
  machineSuccess := cap_program_machine_success
  termination := cap_program_termination
  completeness := cap_program_completeness
  honestBudgets := cap_program_honest_budgets
  proofSize := cap_program_proof_size
  proverCycles := cap_program_prover_cycles
  binding := cap_program_binding
  hidingProperty := cap_program_hiding

end CommitGolfCandidate
