import CommitGolfCandidate.LateModel
import CommitGolfCandidate.LateCode
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def pcAt (i : Nat) := BitVec.ofNat 64 (4096+4*i)

end CommitGolfCandidate.Late
