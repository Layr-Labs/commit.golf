import CommitGolfCandidate.Layout2Writer3Program
namespace CommitGolfCandidate.Layout2Writer3
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer Layout2Writer2
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
theorem correct3_phase_0 : ∀ q : Fin 4, correct3 0 q := by decide +kernel
end CommitGolfCandidate.Layout2Writer3
