import CommitGolfCandidate.Layout2Writer2Program
namespace CommitGolfCandidate.Layout2Writer2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
theorem correct_phase_3 : ∀ q : Fin 4, correct 3 q := by decide +kernel
end CommitGolfCandidate.Layout2Writer2
