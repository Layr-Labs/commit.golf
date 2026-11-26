import CommitGolfCandidate.S5RootJudge
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def CapJudgment := ∀ (o : Oracle) (x : CheckInput) (s : MachineState),s.pc=pcAt 1094 →
    CapEnv x s → Evidence o.compression x 0 s → Cache s (capVal o.compression x 0) →
    Outcome o s (∃ q,rootMatches o.compression x q) 5000 72

end CommitGolfCandidate.S5Machine.Check
